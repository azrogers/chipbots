use proc_macro2::TokenStream;
use quote::quote;
use syn::{
    braced, bracketed,
    parse::Parse,
    parse_macro_input,
    token::{self, Comma},
    Expr, ExprBlock, Ident, LitByte, LitInt, LitStr,
};

struct InstructionDefinition {
    byte: LitInt,
    name: LitStr,
    params: Vec<Expr>,
    handler: ExprBlock,
}

impl Parse for InstructionDefinition {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let byte = input.parse::<LitInt>()?;
        input.parse::<Comma>()?;
        let name = input.parse::<LitStr>()?;
        input.parse::<Comma>()?;
        let param_content;
        bracketed!(param_content in input);
        let params: Vec<Expr> = param_content
            .parse_terminated(|input| input.parse::<Expr>(), token::Comma)?
            .into_iter()
            .collect();
        input.parse::<Comma>()?;
        let handler = input.parse::<ExprBlock>()?;
        Ok(InstructionDefinition {
            byte,
            name,
            params,
            handler,
        })
    }
}

struct InstructionSetDefinition {
    host: Ident,
    info: Ident,
    info_constant: Ident,
    result_type: Ident,
    missing_opcode_error: Expr,
    instructions: Vec<InstructionDefinition>,
}

impl Parse for InstructionSetDefinition {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let lookahead = input.lookahead1();
        if lookahead.peek(Ident) {
            let host = input.parse::<Ident>()?;
            input.parse::<token::Comma>()?;
            let info = input.parse::<Ident>()?;
            input.parse::<token::Comma>()?;
            let info_constant = input.parse::<Ident>()?;
            input.parse::<token::Comma>()?;
            let result_type = input.parse::<Ident>()?;
            input.parse::<token::Comma>()?;
            let missing_opcode_error = input.parse::<Expr>()?;
            input.parse::<token::Comma>()?;
            let instructions: Vec<InstructionDefinition> = input
                .parse_terminated(
                    |input| {
                        let content;
                        braced!(content in input);
                        let result = content.parse::<InstructionDefinition>()?;
                        Ok(result)
                    },
                    token::Comma,
                )?
                .into_iter()
                .collect();
            Ok(InstructionSetDefinition {
                host,
                info,
                info_constant,
                result_type,
                missing_opcode_error,
                instructions,
            })
        } else {
            Err(lookahead.error())
        }
    }
}

#[proc_macro]
pub fn instruction_set(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as InstructionSetDefinition);
    let host = input.host;
    let info = input.info;
    let info_constant = input.info_constant;
    let result_type = input.result_type;
    let missing_opcode_error = input.missing_opcode_error;
    let mut arms: Vec<TokenStream> = Vec::new();
    let mut infos: Vec<TokenStream> = Vec::new();
    for def in input.instructions {
        let byte = def.byte;
        let name = def.name;
        let args = def.params;
        let handler = def.handler;

        arms.push(quote! {
            #byte => #handler
        });

        infos.push(quote! {
            #info { byte: #byte, name: #name, args: &[#(#args),*] }
        });
    }
    quote! {
        static #info_constant: &'static [#info] = &[#(#infos),*];

        impl<const N: usize> #host<N> {
            fn step_internal(self: &mut #host<N>, opcode: u8) -> anyhow::Result<#result_type> {
                match opcode {
                    #(#arms),*
                    _ => #missing_opcode_error
                }
            }
        }
    }
    .into()
}
