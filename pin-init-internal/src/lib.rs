//! Internal implementation details of crate `pin_init`, **do not use**.

use proc_macro::TokenStream;
use syn::Error;

mod pin_init;

#[proc_macro_attribute]
pub fn pin_init(attr: TokenStream, input: TokenStream) -> TokenStream {
    pin_init::pin_init_attr(attr.into(), input.into())
        .unwrap_or_else(Error::into_compile_error)
        .into()
}

#[doc(hidden)]
#[proc_macro_derive(PinInit, attributes(pin))]
pub fn pin_init_derive(input: TokenStream) -> TokenStream {
    pin_init::pin_init_derive(input.into())
        .unwrap_or_else(Error::into_compile_error)
        .into()
}
