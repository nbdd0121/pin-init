#![deny(warnings)]

use pin_init::*;

use std::marker::PhantomData;

// Ensure that proper warning suppression is in place.

#[pin_init]
#[allow(nonstandard_style)]
#[allow(dead_code)]
struct Test<'WRONG_LIFETIME_NAME, wrong_type_name, const wrong_const_name: bool> {
    WrongVariableName: PhantomData<&'WRONG_LIFETIME_NAME wrong_type_name>,
}
