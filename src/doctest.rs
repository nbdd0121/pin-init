/// Helpers for documentation tests.

pub struct NeedPin {
    address: *const NeedPin,
    _pinned: core::marker::PhantomPinned,
}

impl NeedPin {
    pub fn verify(&self) {
        assert!(core::ptr::eq(self, self.address), "invariant not held");
    }
}
