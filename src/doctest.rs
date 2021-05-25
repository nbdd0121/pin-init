// Helpers for documentation tests.

use std::convert::Infallible;
use std::marker::PhantomPinned;
use std::pin::Pin;
use pin_init::*;

pub struct NeedPin {
    address: *const NeedPin,
    _pinned: PhantomPinned,
}

impl NeedPin {
    pub fn verify(&self) {
        assert!(core::ptr::eq(self, self.address), "invariant not held");
    }
}

impl NeedPin {
    pub fn new(mut this: PinInit<'_, Self>) -> PinInitResult<'_, Infallible> {
        let v = this.get_mut().as_mut_ptr();
        unsafe { *core::ptr::addr_of_mut!((*v).address) = v };
        Ok(unsafe { this.init_ok() })
    }
}
