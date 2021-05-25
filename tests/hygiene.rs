#![allow(non_camel_case_types)]
#![allow(dead_code)]

use std::marker::PhantomData;

use pin_init::*;

// Ensure that the variables we use in proc_macro does not use wrong hygiene.

#[pin_init]
struct LocalHygiene {
    base: usize,
    ptr: usize,
    pin: usize,
}

#[pin_init]
struct LocalHygienePin {
    #[pin]
    base: usize,
    #[pin]
    ptr: usize,
    #[pin]
    pin: usize,
}

#[pin_init]
struct GenericHygiene<base, ptr, pin> {
    base: PhantomData<base>,
    ptr: PhantomData<ptr>,
    pin: PhantomData<pin>,
}

#[pin_init]
struct GenericHygienePin<base, ptr, pin> {
    #[pin]
    base: PhantomData<base>,
    #[pin]
    ptr: PhantomData<ptr>,
    #[pin]
    pin: PhantomData<pin>,
}
