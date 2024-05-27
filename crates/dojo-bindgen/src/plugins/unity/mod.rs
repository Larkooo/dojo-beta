use std::collections::HashMap;
use std::path::{Path, PathBuf};

use async_trait::async_trait;
use cainome::parser::tokens::{Composite, CompositeType, Function, Token};

use crate::error::BindgenResult;
use crate::plugins::BuiltinPlugin;
use crate::{DojoContract, DojoData, DojoModel};

pub struct UnityPlugin {}

impl UnityPlugin {
    pub fn new() -> Self {
        Self {}
    }

    // Maps cairo types to C#/Unity SDK defined types
    fn map_type(token: &Token) -> String {
        match token.type_name().as_str() {
            "u8" => "byte".to_string(),
            "u16" => "ushort".to_string(),
            "u32" => "uint".to_string(),
            "u64" => "ulong".to_string(),
            "u128" => "BigInteger".to_string(),
            "u256" => "BigInteger".to_string(),
            "usize" => "uint".to_string(),
            "felt252" => "FieldElement".to_string(),
            "bytes31" => "string".to_string(),
            "ClassHash" => "FieldElement".to_string(),
            "ContractAddress" => "FieldElement".to_string(),
            "ByteArray" => "string".to_string(),
            "array" => {
                if let Token::Array(array) = token {
                    format!("{}[]", UnityPlugin::map_type(&array.inner))
                } else {
                    panic!("Invalid array token: {:?}", token);
                }
            }
            "tuple" => {
                if let Token::Tuple(tuple) = token {
                    let inners = tuple
                        .inners
                        .iter()
                        .map(UnityPlugin::map_type)
                        .collect::<Vec<String>>()
                        .join(", ");
                    format!("({})", inners)
                } else {
                    panic!("Invalid tuple token: {:?}", token);
                }
            }
            "generic_arg" => {
                if let Token::GenericArg(g) = &token {
                    g.clone()
                } else {
                    panic!("Invalid generic arg token: {:?}", token);
                }
            }

            _ => {
                let mut type_name = token.type_name().to_string();

                if let Token::Composite(composite) = token {
                    if composite.generic_args.len() > 0 {
                        type_name += &format!(
                            "<{}>",
                            composite
                                .generic_args
                                .iter()
                                .map(|(_, t)| UnityPlugin::map_type(t))
                                .collect::<Vec<_>>()
                                .join(", ")
                        )
                    }
                }

                type_name
            }
        }
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
            .map(|field| format!("public {} {};", UnityPlugin::map_type(&field.token), field.name))
            .collect::<Vec<String>>()
            .join("\n    ");

        format!(
            "
// Type definition for `{}` struct
[Serializable]
public struct {} {{
    {}
}}
",
            token.type_path,
            token.type_name(),
            fields
        )
    }

    // Token should be an enum
    // This will be formatted into a C# enum
    // Enum is mapped using index of cairo enum
    fn format_enum(token: &Composite) -> String {
        let mut name_with_generics = token.type_name();
        if token.generic_args.len() > 0 {
            name_with_generics += &format!(
                "<{}>",
                token.generic_args.iter().map(|(n, _)| n.clone()).collect::<Vec<_>>().join(", ")
            );
        }

        let mut result = format!(
            "
// Type definition for `{}` enum
public abstract record {}() {{",
            token.type_path, name_with_generics
        );

        for field in &token.inners {
            let type_name = UnityPlugin::map_type(&field.token).replace("(", "").replace(")", "");

            result += format!(
                "\n    public record {}({}) : {name_with_generics};",
                field.name,
                if type_name.is_empty() { type_name } else { format!("{} value", type_name) }
            )
            .as_str();
        }

        result += "\n}\n";

        result
    }

    // Token should be a model
    // This will be formatted into a C# class inheriting from ModelInstance
    // Fields are mapped using C# and unity SDK types
    fn format_model(model: &Composite) -> String {
        let fields = model
            .inners
            .iter()
            .map(|field| {
                format!(
                    "[ModelField(\"{}\")]\n    public {} {};",
                    field.name,
                    UnityPlugin::map_type(&field.token),
                    field.name,
                )
            })
            .collect::<Vec<String>>()
            .join("\n\n    ");

        format!(
            "
// Model definition for `{}` model
public class {} : ModelInstance {{
    {}

    // Start is called before the first frame update
    void Start() {{
    }}

    // Update is called once per frame
    void Update() {{
    }}
}}
        ",
            model.type_path,
            model.type_name(),
            fields
        )
    }

    // Handles a model definition and its referenced tokens
    // Will map all structs and enums to C# types
    // Will format the model into a C# class
    fn handle_model(&self, model: &DojoModel, handled_tokens: &mut Vec<Composite>) -> String {
        let mut out = String::new();
        out += UnityPlugin::generated_header().as_str();
        out += "using System;\n";
        out += "using Dojo;\n";
        out += "using Dojo.Starknet;\n";

        let mut model_struct: Option<&Composite> = None;
        let tokens = &model.tokens;
        for token in &tokens.structs {
            if handled_tokens.iter().any(|t| t.type_name() == token.type_name()) {
                continue;
            }

            handled_tokens.push(token.to_composite().unwrap().to_owned());

            // first index is our model struct
            if token.type_name() == model.name {
                model_struct = Some(token.to_composite().unwrap());
                continue;
            }

            out += UnityPlugin::format_struct(token.to_composite().unwrap()).as_str();
        }

        for token in &tokens.enums {
            if handled_tokens.iter().any(|t| t.type_name() == token.type_name()) {
                continue;
            }

            handled_tokens.push(token.to_composite().unwrap().to_owned());
            out += UnityPlugin::format_enum(token.to_composite().unwrap()).as_str();
        }

        out += "\n";

        out += UnityPlugin::format_model(model_struct.expect("model struct not found")).as_str();

        out
    }

    // Formats a system into a C# method used by the contract class
    // Handled tokens should be a list of all structs and enums used by the contract
    // Such as a set of referenced tokens from a model
    fn format_system(system: &Function, handled_tokens: &[Composite]) -> String {
        let args = system
            .inputs
            .iter()
            .map(|arg| format!("{} {}", UnityPlugin::map_type(&arg.1), &arg.0))
            .collect::<Vec<String>>()
            .join(", ");

        let calldata = system
            .inputs
            .iter()
            .map(|arg| {
                let token = &arg.1;
                let type_name = &arg.0;

                match handled_tokens.iter().find(|t| t.type_name() == token.type_name()) {
                    Some(t) => {
                        // Need to flatten the struct members.
                        match t.r#type {
                            CompositeType::Struct => t
                                .inners
                                .iter()
                                .map(|field| {
                                    format!(
                                        "new FieldElement({}.{}).Inner()",
                                        type_name, field.name
                                    )
                                })
                                .collect::<Vec<String>>()
                                .join(",\n                    "),
                            _ => {
                                format!("new FieldElement({}).Inner()", type_name)
                            }
                        }
                    }
                    None => match UnityPlugin::map_type(token).as_str() {
                        "FieldElement" => format!("{}.Inner()", type_name),
                        _ => format!("new FieldElement({}).Inner()", type_name),
                    },
                }
            })
            .collect::<Vec<String>>()
            .join(",\n                ");

        format!(
            "
    // Call the `{system_name}` system with the specified Account and calldata
    // Returns the transaction hash. Use `WaitForTransaction` to wait for the transaction to be \
             confirmed.
    public async Task<FieldElement> {system_name}(Account account{arg_sep}{args}) {{
        return await account.ExecuteRaw(new dojo.Call[] {{
            new dojo.Call{{
                to = contractAddress,
                selector = \"{system_name}\",
                calldata = new dojo.FieldElement[] {{
                    {calldata}
                }}
            }}
        }});
    }}
            ",
            // selector for execute
            system_name = system.name,
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
        // capitalize contract name
        contract_name.chars().next().unwrap().to_uppercase().to_string() + &contract_name[1..]
    }

    // Handles a contract definition and its underlying systems
    // Will format the contract into a C# class and
    // all systems into C# methods
    // Handled tokens should be a list of all structs and enums used by the contract
    fn handle_contract(&self, contract: &DojoContract, handled_tokens: &[Composite]) -> String {
        let mut out = String::new();
        out += UnityPlugin::generated_header().as_str();
        out += "using System;\n";
        out += "using System.Threading.Tasks;\n";
        out += "using Dojo;\n";
        out += "using Dojo.Starknet;\n";
        out += "using UnityEngine;\n";
        out += "using dojo_bindings;\n";

        let systems = contract
            .systems
            .iter()
            .map(|system| UnityPlugin::format_system(system.to_function().unwrap(), handled_tokens))
            .collect::<Vec<String>>()
            .join("\n\n    ");

        out += &format!(
            "
// System definitions for `{}` contract
public class {} : MonoBehaviour {{
    // The address of this contract
    public string contractAddress;

    {}
}}
        ",
            contract.qualified_path,
            // capitalize contract name
            UnityPlugin::formatted_contract_name(&contract.qualified_path),
            systems
        );

        out
    }
}

#[async_trait]
impl BuiltinPlugin for UnityPlugin {
    async fn generate_code(&self, data: &DojoData) -> BindgenResult<HashMap<PathBuf, Vec<u8>>> {
        let mut out: HashMap<PathBuf, Vec<u8>> = HashMap::new();
        let mut handled_tokens = Vec::<Composite>::new();

        // Handle codegen for models
        for (name, model) in &data.models {
            let models_path = Path::new(&format!("Models/{}.gen.cs", name)).to_owned();

            println!("Generating model: {}", name);
            let code = self.handle_model(model, &mut handled_tokens);

            out.insert(models_path, code.as_bytes().to_vec());
        }

        // Handle codegen for systems
        for (name, contract) in &data.contracts {
            let contracts_path = Path::new(&format!("Contracts/{}.gen.cs", name)).to_owned();

            println!("Generating contract: {}", name);
            let code = self.handle_contract(contract, &handled_tokens);

            out.insert(contracts_path, code.as_bytes().to_vec());
        }

        Ok(out)
    }
}
