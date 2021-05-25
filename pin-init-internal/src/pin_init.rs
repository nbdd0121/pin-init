use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote, quote_spanned, ToTokens};
use syn::{
    punctuated::Punctuated, Data, DeriveInput, Error, Fields, GenericParam, Generics, ItemStruct,
    LifetimeDef, Member, Result, TraitBound, TraitBoundModifier, TypeParamBound,
};

pub fn pin_init_attr(_attr: TokenStream, input: TokenStream) -> Result<TokenStream> {
    let mut input: ItemStruct = syn::parse2(input)?;
    let attrs = std::mem::take(&mut input.attrs);
    Ok(quote! {
        #(#attrs)*
        #[derive(::pin_init::__private::PinInit)]
        #input
    })
}

pub fn pin_init_derive(input: TokenStream) -> Result<TokenStream> {
    let DeriveInput {
        vis,
        ident,
        generics,
        data,
        ..
    } = syn::parse2(input)?;

    // Check this is a struct, and extract inner.
    let data = match data {
        Data::Struct(v) => v,
        Data::Enum(v) => {
            return Err(Error::new(
                v.enum_token.span,
                "#[pin_init] cannot be applied to enum",
            ))
        }
        Data::Union(v) => {
            return Err(Error::new(
                v.union_token.span,
                "#[pin_init] cannot be applied to union",
            ))
        }
    };

    let (mut fields, named) = match data.fields {
        Fields::Named(v) => (v.named, true),
        Fields::Unnamed(v) => (v.unnamed, false),
        Fields::Unit => (Punctuated::new(), true),
    };

    // Remove #[pin] attribute and record if we've seen one.
    let has_pin: Vec<_> = fields
        .iter_mut()
        .map(|field| {
            let mut has_pin = false;
            field.attrs.retain(|a| {
                if a.path.is_ident("pin") {
                    has_pin = true;
                    false
                } else {
                    true
                }
            });
            has_pin
        })
        .collect();

    let field_name: Vec<_> = fields
        .iter()
        .enumerate()
        .map(|(i, field)| match &field.ident {
            Some(v) => Member::Named(v.clone()),
            None => Member::Unnamed(i.into()),
        })
        .collect();

    // Extract generics and where clauses
    let Generics {
        params: generics,
        where_clause,
        ..
    } = generics;
    let generics: Vec<_> = generics
        .into_iter()
        .map(|mut x| {
            match &mut x {
                GenericParam::Lifetime(_) => (),
                GenericParam::Type(t) => {
                    t.default = None;

                    // Need to remove ?Sized bound.
                    let bounds = std::mem::replace(&mut t.bounds, Punctuated::new());
                    t.bounds = bounds
                        .into_iter()
                        .filter(|b| {
                            !matches!(
                                b,
                                TypeParamBound::Trait(TraitBound {
                                    modifier: TraitBoundModifier::Maybe(_),
                                    ..
                                })
                            )
                        })
                        .collect();
                }
                GenericParam::Const(c) => c.default = None,
            }
            x
        })
        .collect();
    let ty_generics: Vec<_> = generics
        .iter()
        .map(|x| -> &dyn ToTokens {
            match x {
                GenericParam::Lifetime(l) => &l.lifetime,
                GenericParam::Type(t) => &t.ident,
                GenericParam::Const(c) => &c.ident,
            }
        })
        .collect();

    // Create identifier names that are unlikely to be used.
    let typestate_name: Vec<_> = field_name
        .iter()
        .enumerate()
        .map(|(f, _)| format_ident!("__C{}", f))
        .collect();

    let this_lifetime: LifetimeDef = syn::parse_str("'__this").unwrap();
    let error_ident = format_ident!("__E");
    let fn_ident = format_ident!("__F");
    let builder_ident = format_ident!("{}Builder", ident);

    // Hygiene for local variables.
    let mixed_site = Span::mixed_site();

    let mut builder = Vec::new();
    {
        let (typestate_impl, typestate_ty, drop_impl) = if named {
            (
                quote_spanned! {mixed_site => #(, const #typestate_name: bool)*},
                quote_spanned! {mixed_site => #(,#typestate_name)* },
                quote_spanned! {mixed_site=>
                    #(
                        if #typestate_name {
                            // SAFETY: Typestate ensures that we are only dropping
                            //         initiailized value.
                            unsafe {
                                let ptr = ::core::ptr::addr_of_mut!((*base).#field_name);
                                ptr.drop_in_place();
                            }
                        }
                    )*
                },
            )
        } else {
            (
                quote_spanned! {mixed_site => , const __C: usize },
                quote_spanned! {mixed_site => , __C },
                quote_spanned! {mixed_site=>
                    #(
                        if __C > #field_name {
                            // SAFETY: Typestate ensures that we are only dropping
                            //         initiailized value.
                            unsafe {
                                let ptr = ::core::ptr::addr_of_mut!((*base).#field_name);
                                ptr.drop_in_place();
                            }
                        }
                    )*
                },
            )
        };

        builder.push(quote_spanned! {mixed_site=>
            #[doc(hidden)]
            #[repr(transparent)]
            #[allow(nonstandard_style)]
            #vis struct #builder_ident<
                #this_lifetime
                #(,#generics)*
                #typestate_impl
            > #where_clause {
                ptr: ::pin_init::PinInit<#this_lifetime, #ident<#(#ty_generics),*>>,
            }

            #[allow(nonstandard_style)]
            impl<
                #this_lifetime
                #(,#generics)*
                #typestate_impl
            > #builder_ident <
                #this_lifetime
                #(,#ty_generics)*
                #typestate_ty
            > #where_clause {
                #[inline]
                fn __init_err<#error_ident>(mut self, err: #error_ident) -> ::pin_init::PinInitErr<#this_lifetime, #error_ident> {
                    let base = self.ptr.get_mut().as_mut_ptr();
                    #drop_impl
                    self.ptr.init_err(err)
                }
            }
        });
    }

    for i in 0..field_name.len() {
        let field_name_current = &field_name[i];
        let ty = &fields[i].ty;
        let field_vis = &fields[i].vis;

        let (typestate_impl, typestate_ty_pre, typestate_ty_post, fn_name) = if named {
            let typestate_name_before = &typestate_name[0..i];
            let typestate_name_after = &typestate_name[i + 1..];

            (
                quote_spanned! {mixed_site =>
                    #(, const #typestate_name_before: bool)*
                    #(, const #typestate_name_after: bool)*
                },
                quote_spanned! {mixed_site =>
                    #(,#typestate_name_before)*
                    , false
                    #(,#typestate_name_after)*
                },
                quote_spanned! {mixed_site =>
                    #(,#typestate_name_before)*
                    , true
                    #(,#typestate_name_after)*
                },
                quote_spanned! {mixed_site=> #field_name_current },
            )
        } else {
            let next = i + 1;
            (
                quote_spanned! {mixed_site => },
                quote_spanned! {mixed_site => , #i },
                quote_spanned! {mixed_site => , #next },
                quote_spanned! {mixed_site=> __next },
            )
        };

        let fn_item = if has_pin[i] {
            quote_spanned! {mixed_site=>
                #field_vis fn #fn_name<#error_ident, #fn_ident>(mut self, f: #fn_ident) -> ::core::result::Result<#builder_ident<
                    #this_lifetime
                    #(,#ty_generics)*
                    #typestate_ty_post
                >, ::pin_init::PinInitErr<#this_lifetime, #error_ident>>
                    where #fn_ident: for<'__a> ::core::ops::FnOnce(::pin_init::PinInit<'__a, #ty>) -> ::pin_init::PinInitResult<'__a, #ty, #error_ident>
                {
                    let base = self.ptr.get_mut().as_mut_ptr();
                    // SAFETY: No actual dereference
                    let ptr = unsafe { ::core::ptr::addr_of_mut!((*base).#field_name_current) };
                    // SAFETY: We will act according to the return value of `f`.
                    let pin = unsafe { ::pin_init::PinInit::new(&mut *(ptr as *mut ::core::mem::MaybeUninit<_>)) };
                    match f(pin) {
                        Ok(_) => (),
                        Err(err) => return Err(self.__init_err(err.into_inner())),
                    }
                    Ok(#builder_ident { ptr: self.ptr })
                }
            }
        } else {
            quote_spanned! {mixed_site=>
                #field_vis fn #fn_name<#error_ident>(mut self, f: #ty) -> ::core::result::Result<#builder_ident<
                    #this_lifetime
                    #(,#ty_generics)*
                    #typestate_ty_post
                >, ::pin_init::PinInitErr<#this_lifetime, #error_ident>>
                {
                    let base = self.ptr.get_mut().as_mut_ptr();
                    unsafe {
                        let ptr = ::core::ptr::addr_of_mut!((*base).#field_name_current);
                        ptr.write(f);
                    }
                    Ok(#builder_ident { ptr: self.ptr })
                }
            }
        };
        builder.push(quote_spanned! {mixed_site=>
            #[allow(nonstandard_style)]
            impl<
                #this_lifetime
                #(,#generics)*
                #typestate_impl
            > #builder_ident <
                #this_lifetime
                #(,#ty_generics)*
                #typestate_ty_pre
            > #where_clause {
                #[inline]
                #fn_item
            }
        });
    }

    {
        let (typestate_ty_pre, typestate_ty_post) = if named {
            let all_true: Vec<_> = field_name.iter().map(|_| quote!(true)).collect();
            let all_false: Vec<_> = field_name.iter().map(|_| quote!(false)).collect();

            (
                quote_spanned! {mixed_site => #(,#all_false)* },
                quote_spanned! {mixed_site => #(,#all_true)* },
            )
        } else {
            let len = field_name.len();
            (
                quote_spanned! {mixed_site => , 0 },
                quote_spanned! {mixed_site => , #len },
            )
        };

        builder.push(quote_spanned! {mixed_site=>
            #[allow(nonstandard_style)]
            impl<
                #this_lifetime
                #(,#generics)*
            > #builder_ident <
                #this_lifetime
                #(,#ty_generics)*
                #typestate_ty_post
            > #where_clause {
                #[inline]
                pub fn __init_ok(mut self) -> ::pin_init::PinInitOk<#this_lifetime, #ident<#(#ty_generics),*>>{
                    unsafe { self.ptr.init_ok() }
                }
            }

            #[allow(nonstandard_style)]
            impl<
                #this_lifetime
                #(,#generics)*
            > ::pin_init::PinInitable<#this_lifetime> for #ident<#(#ty_generics),*> #where_clause {
                #[doc(hidden)]
                type __PinInitBuilder = #builder_ident <
                    #this_lifetime
                    #(,#ty_generics)*
                    #typestate_ty_pre
                >;

                #[doc(hidden)]
                #[inline]
                fn __pin_init_builder(
                    this: ::pin_init::PinInit<#this_lifetime, Self>,
                ) -> Self::__PinInitBuilder {
                    #builder_ident { ptr: this }
                }
            }
        });
    }

    let gen = quote!(#(#builder)*);
    Ok(gen)
}
