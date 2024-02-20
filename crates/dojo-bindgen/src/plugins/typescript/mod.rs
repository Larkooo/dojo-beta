use std::collections::HashMap;
use std::path::{Path, PathBuf};

use async_trait::async_trait;
use cainome::parser::tokens::{Composite, CompositeType, Function};
use convert_case::Casing;

use crate::error::BindgenResult;
use crate::plugins::BuiltinPlugin;
use crate::{DojoContract, DojoData, DojoModel};

pub struct TypescriptPlugin {}

impl TypescriptPlugin {
    pub fn new() -> Self {
        Self {}
    }

    // Maps cairo types to C#/Unity SDK defined types
    fn map_type(type_name: &str) -> String {
        match type_name {
            "bool" => "RecsType.Boolean".to_string(),
            "u8" => "RecsType.Number".to_string(),
            "u16" => "RecsType.Number".to_string(),
            "u32" => "RecsType.Number".to_string(),
            "u64" => "RecsType.Number".to_string(),
            "u128" => "RecsType.BigInt".to_string(),
            "u256" => "RecsType.BigInt".to_string(),
            "usize" => "RecsType.Number".to_string(),
            "felt252" => "RecsType.BigInt".to_string(),
            "ClassHash" => "RecsType.BigInt".to_string(),
            "ContractAddress" => "RecsType.BigInt".to_string(),

            _ => type_name.to_string(),
        }
    }

    fn is_custom_type(type_name: &str) -> bool {
        TypescriptPlugin::map_type(type_name) == type_name
    }

    fn generated_header() -> String {
        format!(
            "// Generated by dojo-bindgen on {}. Do not modify this file manually.\n",
            chrono::Utc::now().to_rfc2822()
        )
    }

    // Token should be a struct
    // This will be formatted into a C# struct
    // using C# and unity SDK types
    fn format_struct(token: &Composite) -> String {
        let fields = token
            .inners
            .iter()
            .map(|field| {
                format!(
                    "{}: {},",
                    field.name,
                    TypescriptPlugin::map_type(field.token.clone().type_name().as_str()),
                )
            })
            .collect::<Vec<String>>()
            .join("\n    ");

        format!(
            "
// Type definition for `{path}` struct
export const {name} = {{
    {fields}
}};
",
            path = token.type_path,
            name = token.type_name(),
            fields = fields
        )
    }

    // Token should be an enum
    // This will be formatted into a C# enum
    // Enum is mapped using index of cairo enum
    fn format_enum(token: &Composite) -> String {
        let fields = token
            .inners
            .iter()
            .map(|field| format!("{},", field.name,))
            .collect::<Vec<String>>()
            .join("\n    ");

        format!(
            "
// Type definition for `{}` enum
export enum {} {{
    {}
}}
",
            token.type_path,
            token.type_name(),
            fields
        )
    }

    // Token should be a model
    // This will be formatted into a C# class inheriting from ModelInstance
    // Fields are mapped using C# and unity SDK types
    fn format_model(model: &Composite) -> String {
        let mut custom_types = Vec::<String>::new();
        let mut types = Vec::<String>::new();
        let fields = model
            .inners
            .iter()
            .map(|field| {
                let mapped = TypescriptPlugin::map_type(field.token.type_name().as_str());
                if mapped == field.token.type_name() {
                    custom_types.push(format!("\"{}\"", field.token.type_name()));
                } else {
                    types.push(format!("\"{}\"", field.token.type_name()));
                }

                format!(
                    "{}: {},",
                    field.name,
                    TypescriptPlugin::map_type(field.token.type_name().as_str()),
                )
            })
            .collect::<Vec<String>>()
            .join("\n            ");

        format!(
            "
        // Model definition for `{path}` model
        {model}: (() => {{
            return defineComponent(
                world,
                {{
                    {fields}
                }},
                {{
                    metadata: {{
                        name: \"{model}\",
                        types: [{types}],
                        customTypes: [{custom_types}],
                    }},
                }}
            );
        }})(),
        ",
            path = model.type_path,
            model = model.type_name(),
            fields = fields,
            types = types.join(", "),
            custom_types = custom_types.join(", ")
        )
    }

    // Handles a model definition and its referenced tokens
    // Will map all structs and enums to TS types
    // Will format the models into a object
    fn handle_model(&self, models: &[&DojoModel], handled_tokens: &mut Vec<Composite>) -> String {
        let mut out = String::new();
        out += TypescriptPlugin::generated_header().as_str();
        out += "import { defineComponent, Type as RecsType, World } from \"@dojoengine/recs\";\n";
        out += "\n";
        out += "export type ContractComponents = Awaited<
            ReturnType<typeof defineContractComponents>
        >;\n";

        out += "\n\n";

        let mut models_structs = Vec::new();
        for model in models {
            let tokens = &model.tokens;
            for token in &tokens.structs {
                handled_tokens.push(token.to_composite().unwrap().to_owned());

                // first index is our model struct
                if token.type_name() == model.name {
                    models_structs.push(token.to_composite().unwrap());
                    continue;
                }

                out += TypescriptPlugin::format_struct(token.to_composite().unwrap()).as_str();
            }

            for token in &tokens.enums {
                handled_tokens.push(token.to_composite().unwrap().to_owned());
                out += TypescriptPlugin::format_enum(token.to_composite().unwrap()).as_str();
            }

            out += "\n";
        }

        out += "
export function defineContractComponents(world: World) {
    return {
";

        for model in models_structs {
            out += TypescriptPlugin::format_model(model)
                .as_str();
        }

        out += "    };
}\n";

        out
    }

    // Formats a system into a C# method used by the contract class
    // Handled tokens should be a list of all structs and enums used by the contract
    // Such as a set of referenced tokens from a model
    fn format_system(system: &Function, handled_tokens: &[Composite]) -> String {
        let args = system
            .inputs
            .iter()
            .map(|arg| format!("{} {}", TypescriptPlugin::map_type(&arg.1.type_name()), arg.0,))
            .collect::<Vec<String>>()
            .join(", ");

        let calldata = system
            .inputs
            .iter()
            .map(|arg| {
                let token = arg.1.to_composite().unwrap();
                // r#type doesnt seem to be working rn.
                // instead, we can take a look at our
                // handled tokens db
                let token =
                    handled_tokens.iter().find(|t| t.type_name() == token.type_name()).unwrap();

                match token.r#type {
                    CompositeType::Struct => token
                        .inners
                        .iter()
                        .map(|field| format!("new FieldElement({}.{}).Inner()", arg.0, field.name))
                        .collect::<Vec<String>>()
                        .join(",\n                    "),
                    _ => {
                        format!("new FieldElement({}).Inner()", arg.0)
                    }
                }
            })
            .collect::<Vec<String>>()
            .join(",\n                ");

        format!(
            "
    // Call the `{system_name}` system with the specified Account and calldata
    const {pretty_system_name} = async ({{ account }}: {{ account: Account{arg_sep}{args} }}) => {{
        try {{
            return await provider.execute(
                account,
                contract_name,
                {system_name},
                [{calldata}]
            );
        }} catch (error) {{
            console.error(\"Error executing spawn:\", error);
            throw error;
        }}
    }};
            ",
            // selector for execute
            system_name = system.name,
            // pretty system name
            // snake case to camel case
            // move_to -> moveTo
            pretty_system_name = system.name.to_case(convert_case::Case::Camel),
            // add comma if we have args
            arg_sep = if !args.is_empty() { ", " } else { "" },
            // formatted args to use our mapped types
            args = args,
            // calldata for execute
            calldata = calldata
        )
    }

    // Formats a contract file path into a pretty contract name
    // eg. dojo_examples::actions::actions.json -> Actions
    fn formatted_contract_name(contract_file_name: &str) -> String {
        let contract_name =
            contract_file_name.split("::").last().unwrap().trim_end_matches(".json");
        contract_name.to_string()
    }

    // Handles a contract definition and its underlying systems
    // Will format the contract into a C# class and
    // all systems into C# methods
    // Handled tokens should be a list of all structs and enums used by the contract
    fn handle_contracts(
        &self,
        contracts: &[&DojoContract],
        handled_tokens: &[Composite],
    ) -> String {
        let mut out = String::new();
        out += TypescriptPlugin::generated_header().as_str();
        out += "import { Account } from \"starknet\";\n";
        out += "import { DojoProvider } from \"@dojoengine/core\";\n";
        out += "\n";
        out += "export type IWorld = Awaited<ReturnType<typeof setupWorld>>;";

        out += "\n\n";

        out += "export async function setupWorld(provider: DojoProvider) {";

        for contract in contracts {
            let systems = contract
                .systems
                .iter()
                .map(|system| {
                    TypescriptPlugin::format_system(system.to_function().unwrap(), handled_tokens)
                })
                .collect::<Vec<String>>()
                .join("\n\n    ");

            out += &format!(
                "
// System definitions for `{}` contract
function {}() {{
    const contract_name = \"{}\";

    {}
}}
        ",
                contract.contract_file_name,
                // capitalize contract name
                TypescriptPlugin::formatted_contract_name(&contract.contract_file_name),
                TypescriptPlugin::formatted_contract_name(&contract.contract_file_name),
                systems
            );
        }

        out
    }
}

#[async_trait]
impl BuiltinPlugin for TypescriptPlugin {
    async fn generate_code(&self, data: &DojoData) -> BindgenResult<HashMap<PathBuf, Vec<u8>>> {
        let mut out: HashMap<PathBuf, Vec<u8>> = HashMap::new();
        let mut handled_tokens = Vec::<Composite>::new();

        // Handle codegen for models
        let models_path = Path::new("models.gen.ts").to_owned();
        let models = data.models.values().collect::<Vec<_>>();
        let code = self.handle_model(models.as_slice(), &mut handled_tokens);

        out.insert(models_path, code.as_bytes().to_vec());

        // Handle codegen for contracts & systems
        let contracts_path = Path::new("contracts.gen.ts").to_owned();
        let contracts = data.contracts.values().collect::<Vec<_>>();
        let code = self.handle_contracts(contracts.as_slice(), &handled_tokens);

        out.insert(contracts_path, code.as_bytes().to_vec());

        Ok(out)
    }
}
