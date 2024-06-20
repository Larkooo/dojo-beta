use std::collections::HashMap;
use std::future::Future;
use std::pin::Pin;
use std::str::FromStr;
use std::sync::Arc;
use std::task::{Context, Poll};

use futures::Stream;
use futures_util::StreamExt;
use rand::Rng;
use starknet_crypto::FieldElement;
use tokio::sync::mpsc::{channel, Receiver, Sender};
use tokio::sync::RwLock;
use torii_core::error::{Error, ParseError};
use torii_core::simple_broker::SimpleBroker;
use torii_core::sql::FELT_DELIMITER;
use torii_core::types::Event;
use tracing::{error, trace};

use crate::proto;
use crate::proto::world::SubscribeEventsResponse;

pub(crate) const LOG_TARGET: &str = "torii::grpc::server::subscriptions::event";

pub struct EventsSubscriber {
    /// Event keys that the subscriber is interested in
    keys: Vec<FieldElement>,
    /// The channel to send the response back to the subscriber.
    sender: Sender<Result<proto::world::SubscribeEventsResponse, tonic::Status>>,
}

#[derive(Default)]
pub struct EventsManager {
    subscribers: RwLock<HashMap<usize, EventsSubscriber>>,
}

impl EventsManager {
    pub async fn add_subscriber(
        &self,
        keys: Vec<FieldElement>,
    ) -> Result<Receiver<Result<proto::world::SubscribeEventsResponse, tonic::Status>>, Error> {
        let id = rand::thread_rng().gen::<usize>();
        let (sender, receiver) = channel(1);

        // NOTE: unlock issue with firefox/safari
        // initially send empty stream message to return from
        // initial subscribe call
        let _ = sender.send(Ok(SubscribeEventsResponse { event: None })).await;

        self.subscribers.write().await.insert(id, EventsSubscriber { keys, sender });

        Ok(receiver)
    }

    pub(super) async fn remove_subscriber(&self, id: usize) {
        self.subscribers.write().await.remove(&id);
    }
}

#[must_use = "Service does nothing unless polled"]
pub struct Service {
    subs_manager: Arc<EventsManager>,
    simple_broker: Pin<Box<dyn Stream<Item = Event> + Send>>,
}

impl Service {
    pub fn new(subs_manager: Arc<EventsManager>) -> Self {
        Self { subs_manager, simple_broker: Box::pin(SimpleBroker::<Event>::subscribe()) }
    }

    async fn publish_updates(subs: Arc<EventsManager>, event: &Event) -> Result<(), Error> {
        let mut closed_stream = Vec::new();
        let keys = event
            .keys
            .trim_end_matches(FELT_DELIMITER)
            .split(FELT_DELIMITER)
            .map(FieldElement::from_str)
            .collect::<Result<Vec<_>, _>>()
            .map_err(|e| ParseError::from(e))?;
        let data = event
            .data
            .trim_end_matches(FELT_DELIMITER)
            .split(FELT_DELIMITER)
            .map(FieldElement::from_str)
            .collect::<Result<Vec<_>, _>>()
            .map_err(|e| ParseError::from(e))?;

        for (idx, sub) in subs.subscribers.read().await.iter() {
            // publish all updates if ids is empty or only ids that are subscribed to
            if sub.keys.is_empty() || keys.starts_with(&sub.keys) {
                let resp = proto::world::SubscribeEventsResponse {
                    event: Some(proto::types::Event {
                        keys: keys.iter().map(|k| k.to_bytes_be().to_vec()).collect(),
                        data: data.iter().map(|d| d.to_bytes_be().to_vec()).collect(),
                        transaction_hash: FieldElement::from_str(&event.transaction_hash)
                            .map_err(ParseError::from)?
                            .to_bytes_be()
                            .to_vec(),
                    }),
                };

                if sub.sender.send(Ok(resp)).await.is_err() {
                    closed_stream.push(*idx);
                }
            }
        }

        for id in closed_stream {
            trace!(target = LOG_TARGET, id = %id, "Closing entity stream.");
            subs.remove_subscriber(id).await
        }

        Ok(())
    }
}

impl Future for Service {
    type Output = ();

    fn poll(self: std::pin::Pin<&mut Self>, cx: &mut Context<'_>) -> std::task::Poll<Self::Output> {
        let pin = self.get_mut();

        while let Poll::Ready(Some(event)) = pin.simple_broker.poll_next_unpin(cx) {
            let subs = Arc::clone(&pin.subs_manager);
            tokio::spawn(async move {
                if let Err(e) = Service::publish_updates(subs, &event).await {
                    error!(target = LOG_TARGET, error = %e, "Publishing entity update.");
                }
            });
        }

        Poll::Pending
    }
}
