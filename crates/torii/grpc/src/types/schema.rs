use std::collections::HashMap;
use std::hash::Hash;

use crypto_bigint::{Encoding, U256};
use dojo_types::primitive::Primitive;
use dojo_types::schema::{Enum, ModelMetadata, Struct, Ty};
use serde::{Deserialize, Serialize};
use starknet::core::types::{Felt, FromStrError};

use crate::proto::{self};

#[derive(Debug, thiserror::Error)]
pub enum SchemaError {
    #[error("Missing expected data: {0}")]
    MissingExpectedData(String),
    #[error("Unsupported primitive type for {0}")]
    UnsupportedType(String),
    #[error("Invalid byte length: {0}. Expected: {1}")]
    InvalidByteLength(usize, usize),
    #[error(transparent)]
    ParseIntError(#[from] std::num::ParseIntError),
    #[error(transparent)]
    FromSlice(#[from] std::array::TryFromSliceError),
    #[error(transparent)]
    FromStr(#[from] FromStrError),
}

#[derive(Debug, Serialize, Deserialize, PartialEq, Hash, Eq, Clone)]
pub struct Entity {
    pub hashed_keys: Felt,
    pub models: Vec<Struct>,
}

impl proto::types::Entity {
    pub fn map(self, models: &HashMap<Felt, ModelMetadata>) -> Result<Entity, SchemaError> {
        let hashed_keys = Felt::from_bytes_be_slice(&self.hashed_keys);
        let models = self
            .models
            .iter()
            .map(|model| {
                let name = model.name.clone();
                let mut ty = models
                    .values()
                    .find(|m| m.schema.name() == name)
                    .map(|m| m.schema.clone())
                    .ok_or(SchemaError::MissingExpectedData(name))?;
                let value = proto::types::Ty {
                    ty_type: Some(proto::types::ty::TyType::Struct(proto::types::Array {
                        children: model.children.clone(),
                    })),
                };
                value.parse(&mut ty)?;
                Ok(ty.as_struct().unwrap().clone())
            })
            .collect::<Result<Vec<Struct>, SchemaError>>()?;

        Ok(Entity { hashed_keys, models })
    }
}

impl proto::types::Ty {
    pub fn parse(&self, ty: &mut Ty) -> Result<(), SchemaError> {
        let ty_type =
            self.ty_type.clone().ok_or(SchemaError::MissingExpectedData("type".to_string()))?;

        match ty_type {
            proto::types::ty::TyType::Primitive(primitive_value) => {
                if let Ty::Primitive(primitive) = ty {
                    *primitive = primitive_value.try_into()?;
                } else {
                    return Err(SchemaError::MissingExpectedData("primitive".to_string()));
                }
            }
            proto::types::ty::TyType::Enum(enum_value) => {
                if let Ty::Enum(r#enum) = ty {
                    r#enum.option = Some(enum_value.option as u8);
                    if let Some(ty) = enum_value.ty {
                        ty.parse(&mut r#enum.options[enum_value.option as usize].ty)?;
                    }
                } else {
                    return Err(SchemaError::MissingExpectedData("enum".to_string()));
                }
            }
            proto::types::ty::TyType::Struct(struct_value) => {
                if let Ty::Struct(r#struct) = ty {
                    for (ty, r#child) in
                        struct_value.children.iter().zip(r#struct.children.iter_mut())
                    {
                        ty.parse(&mut r#child.ty)?;
                    }
                } else {
                    return Err(SchemaError::MissingExpectedData("struct".to_string()));
                }
            }
            proto::types::ty::TyType::Tuple(tuple_value) => {
                if let Ty::Tuple(tuple) = ty {
                    for (ty, r#child) in tuple_value.children.iter().zip(tuple.iter_mut()) {
                        ty.parse(r#child)?;
                    }
                } else {
                    return Err(SchemaError::MissingExpectedData("tuple".to_string()));
                }
            }
            proto::types::ty::TyType::Array(array_value) => {
                if let Ty::Array(array) = ty {
                    let schema = array[0].clone();
                    array.clear();
                    for ty in array_value.children.iter() {
                        let mut element = schema.clone();
                        ty.parse(&mut element)?;
                        array.push(element);
                    }
                } else {
                    return Err(SchemaError::MissingExpectedData("array".to_string()));
                }
            }
            proto::types::ty::TyType::Bytearray(bytearray_value) => {
                if let Ty::ByteArray(bytearray) = ty {
                    *bytearray = bytearray_value;
                } else {
                    return Err(SchemaError::MissingExpectedData("bytearray".to_string()));
                }
            }
        }

        Ok(())
    }
}

impl From<Ty> for proto::types::Ty {
    fn from(ty: Ty) -> Self {
        let ty_type = match ty {
            Ty::Primitive(primitive) => proto::types::ty::TyType::Primitive(primitive.into()),
            Ty::Enum(r#enum) => proto::types::ty::TyType::Enum(Box::new(r#enum.into())),
            Ty::Struct(r#struct) => proto::types::ty::TyType::Struct(r#struct.into()),
            Ty::Tuple(tuple) => proto::types::ty::TyType::Tuple(tuple.into()),
            Ty::Array(array) => proto::types::ty::TyType::Array(array.into()),
            Ty::ByteArray(bytearray) => proto::types::ty::TyType::Bytearray(bytearray),
        };

        proto::types::Ty { ty_type: Some(ty_type) }
    }
}

impl From<Struct> for proto::types::Model {
    fn from(r#struct: Struct) -> Self {
        let children = r#struct.children.into_iter().map(|child| child.ty.into()).collect();
        proto::types::Model { name: r#struct.name, children }
    }
}

impl From<Struct> for proto::types::Array {
    fn from(r#struct: Struct) -> Self {
        let children = r#struct.children.into_iter().map(|child| child.ty.into()).collect();
        proto::types::Array { children }
    }
}

impl From<Enum> for proto::types::Enum {
    fn from(r#enum: Enum) -> Self {
        let option = r#enum.option.unwrap_or_default() as u32;
        let ty = r#enum.options[option as usize].ty.clone().into();
        proto::types::Enum { option, ty: Some(Box::new(ty)) }
    }
}

impl From<Vec<Ty>> for proto::types::Array {
    fn from(tuple: Vec<Ty>) -> Self {
        let children = tuple.into_iter().map(|child| child.into()).collect();
        proto::types::Array { children }
    }
}

impl TryFrom<proto::types::Primitive> for Primitive {
    type Error = SchemaError;
    fn try_from(primitive: proto::types::Primitive) -> Result<Self, Self::Error> {
        let value = primitive
            .primitive_type
            .ok_or(SchemaError::MissingExpectedData("primitive_type".to_string()))?;

        let primitive = match &value {
            proto::types::primitive::PrimitiveType::Bool(bool) => Primitive::Bool(Some(*bool)),
            proto::types::primitive::PrimitiveType::I8(int) => Primitive::I8(Some(*int as i8)),
            proto::types::primitive::PrimitiveType::I16(int) => Primitive::I16(Some(*int as i16)),
            proto::types::primitive::PrimitiveType::I32(int) => Primitive::I32(Some(*int as i32)),
            proto::types::primitive::PrimitiveType::I64(int) => Primitive::I64(Some(*int as i64)),
            proto::types::primitive::PrimitiveType::I128(bytes) => Primitive::I128(Some(
                i128::from_be_bytes(bytes.as_slice().try_into().map_err(SchemaError::FromSlice)?),
            )),
            proto::types::primitive::PrimitiveType::U8(int) => Primitive::U8(Some(*int as u8)),
            proto::types::primitive::PrimitiveType::U16(int) => Primitive::U16(Some(*int as u16)),
            proto::types::primitive::PrimitiveType::U32(int) => Primitive::U32(Some(*int as u32)),
            proto::types::primitive::PrimitiveType::U64(int) => Primitive::U64(Some(*int)),
            proto::types::primitive::PrimitiveType::U128(bytes) => Primitive::U128(Some(
                u128::from_be_bytes(bytes.as_slice().try_into().map_err(SchemaError::FromSlice)?),
            )),
            proto::types::primitive::PrimitiveType::Usize(int) => {
                Primitive::USize(Some(*int as u32))
            }
            proto::types::primitive::PrimitiveType::Felt252(felt) => {
                Primitive::Felt252(Some(Felt::from_bytes_be_slice(felt.as_slice())))
            }
            proto::types::primitive::PrimitiveType::ClassHash(felt) => {
                Primitive::ClassHash(Some(Felt::from_bytes_be_slice(felt.as_slice())))
            }
            proto::types::primitive::PrimitiveType::ContractAddress(felt) => {
                Primitive::ContractAddress(Some(Felt::from_bytes_be_slice(felt.as_slice())))
            }
            proto::types::primitive::PrimitiveType::U256(bytes) => Primitive::U256(Some(
                U256::from_be_bytes(bytes.as_slice().try_into().map_err(SchemaError::FromSlice)?),
            )),
        };

        Ok(primitive)
    }
}

impl From<Primitive> for proto::types::Primitive {
    fn from(primitive: Primitive) -> Self {
        let value = match primitive {
            Primitive::Bool(bool) => {
                proto::types::primitive::PrimitiveType::Bool(bool.unwrap_or_default())
            }
            Primitive::I8(i8) => {
                proto::types::primitive::PrimitiveType::I8(i8.unwrap_or_default() as i32)
            }
            Primitive::I16(i16) => {
                proto::types::primitive::PrimitiveType::I16(i16.unwrap_or_default() as i32)
            }
            Primitive::I32(i32) => {
                proto::types::primitive::PrimitiveType::I32(i32.unwrap_or_default())
            }
            Primitive::I64(i64) => {
                proto::types::primitive::PrimitiveType::I64(i64.unwrap_or_default())
            }
            Primitive::I128(i128) => proto::types::primitive::PrimitiveType::I128(
                i128.unwrap_or_default().to_be_bytes().to_vec(),
            ),
            Primitive::U8(u8) => {
                proto::types::primitive::PrimitiveType::U8(u8.unwrap_or_default() as u32)
            }
            Primitive::U16(u16) => {
                proto::types::primitive::PrimitiveType::U16(u16.unwrap_or_default() as u32)
            }
            Primitive::U32(u32) => {
                proto::types::primitive::PrimitiveType::U32(u32.unwrap_or_default())
            }
            Primitive::U64(u64) => {
                proto::types::primitive::PrimitiveType::U64(u64.unwrap_or_default())
            }
            Primitive::U128(u128) => proto::types::primitive::PrimitiveType::U128(
                u128.unwrap_or_default().to_be_bytes().to_vec(),
            ),
            Primitive::USize(usize) => {
                proto::types::primitive::PrimitiveType::Usize(usize.unwrap_or_default())
            }
            Primitive::Felt252(felt) => proto::types::primitive::PrimitiveType::Felt252(
                felt.unwrap_or_default().to_bytes_be().to_vec(),
            ),
            Primitive::ClassHash(felt) => proto::types::primitive::PrimitiveType::ClassHash(
                felt.unwrap_or_default().to_bytes_be().to_vec(),
            ),
            Primitive::ContractAddress(felt) => {
                proto::types::primitive::PrimitiveType::ContractAddress(
                    felt.unwrap_or_default().to_bytes_be().to_vec(),
                )
            }
            Primitive::U256(u256) => proto::types::primitive::PrimitiveType::U256(
                u256.unwrap_or_default().to_be_bytes().to_vec(),
            ),
        };

        proto::types::Primitive { primitive_type: Some(value) }
    }
}
