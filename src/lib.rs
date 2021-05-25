#![no_std]
#![cfg_attr(doc_cfg, feature(doc_cfg))]
#![warn(unsafe_op_in_unsafe_fn)]

//! Safe Safe pinned-initialization in Rust.
//!
//! # The problem
//! Rust's `Pin` provides sufficient guarantee for C interop and self-referential
//! structs -- their address are stable once they're pinned and the destructor is
//! guaranteed to be called before the memory region can be deallocated.
//!
//! The problem here is "once pinned". `Pin` expects the type can be created without
//! pinning, and can be pinned later before any operations. This is okay for
//! `Generator`s, which are created without any self references, and self references
//! can only be created when polling the generator. For other types, e.g.
//! `pthread_mutex_t`, it is expected to be pinned from the start.
//!
//! For demonstration purpose, we will use this type `NeedPin`:
//! ```no_run
//! # use std::marker::PhantomPinned;
//! # use std::ptr;
//! struct NeedPin {
//! 	// Must points to itself
//!     address: *const NeedPin,
//!     _pinned: PhantomPinned,
//! }
//!
//! impl NeedPin {
//!     fn verify(&self) {
//!         assert!(ptr::eq(self, self.address), "invariant not held");
//!     }
//! }
//!
//! impl Drop for NeedPin {
//!     fn drop(&mut self) {
//!         /* Must be called */
//!     }
//! }
//! ```
//!
//! One could separate creating and initialization (Infallible is used as a
//! placeholder here but in reality it can fail):
//! ```no_run
//! # include!("doctest.rs");
//! # fn main() {}
//! impl NeedPin {
//!     unsafe fn uninit() -> Self {
//!         Self {
//!             address: ptr::null(),
//!             _pinned: PhantomPinned,
//!         }
//!     }
//!
//!     unsafe fn init(self: Pin<&mut Self>) -> Result<(), Infallible> {
//!         let this = unsafe { self.get_unchecked_mut() };
//!         this.address = this;
//!         Ok(())
//!     }
//! }
//! ```
//! but this requires unsafe and is very difficult to use.
//!
//! The ultimate goal is:
//! 1. Safety. We should be able to create and use such pinned type without unsafe.
//!    (Obviously the pinned type themselves are still unsafe to implement).
//! 2. Ergonomics. The syntax shouldn't be too different from anormal Rust.
//! 3. Aggregatable. A struct containing multiple pinned types can be safely
//!    created and initialized together.
//! 4. No Implicit Allocation. Allocation should not be required during initialization.
//!    User should be able to dictate whether it's initialized in a box or on the stack.
//! 5. Fallible. No assumption is made about success of initialization.
//!
//! # The solution: `pin_init`
//!
//! This crate provides type [`PinInit`] and [`PinInitResult`] as the primitives
//! for safe pinned-initialization. Details about these types can be found in
//! their respective documentation, but in a nutshell, instead of having a (fallible)
//! constructor of type `FnOnce() -> Result<T, Err>` like a normal unpinned type,
//! `pin_init` expect you to present a constructor of type
//! `for<'a> FnOnce(PinInit<'a, T>) -> PinInitResult<'a, Err>`.
//!
//! `NeedPin::new` could be define like this:
//! ```no_run
//! # use pin_init::*;
//! # use std::convert::Infallible;
//! # use std::ptr;
//! # struct NeedPin {
//! #     address: *const NeedPin,
//! #     _pinned: std::marker::PhantomPinned,
//! # }
//! impl NeedPin {
//!     pub fn new(mut this: PinInit<'_, Self>) -> PinInitResult<'_, Infallible> {
//!         let v = this.get_mut().as_mut_ptr();
//!         unsafe { *ptr::addr_of_mut!((*v).address) = v };
//!         Ok(unsafe { this.init_ok() })
//!     }
//! }
//! ```
//!
//! With Rust's affine type system and borrow checker, the `PinInitResult` is
//! essentially a certificate about whether the type is initialized or not.
//! `NeedPin` can now be easily initialized:
//! ```
//! # include!("doctest.rs");
//! # fn main() {
//! // In a box
//! let p: Pin<Box<NeedPin>> = pin_init::new_box(NeedPin::new).unwrap();
//! // On the stack
//! init_stack!(p = NeedPin::new);
//! let p: Pin<&mut NeedPin> = p.unwrap();
//! # }
//! ```
//!
//! For structs, if [`#[pin_init]`](pin_init) when defining the struct, then
//! [`init_pin!`] can create it very similar to the struct expression. Nested
//! structures are also supported.
//!
//! ```
//! # include!("doctest.rs");
//! # fn main() {
//! #[pin_init]
//! struct ManyPin {
//!     #[pin]
//!     a: NeedPin,
//!     b: usize,
//! }
//!
//! #[pin_init]
//! struct TooManyPin {
//!     #[pin]
//!     a: NeedPin,
//!     #[pin]
//!     b: ManyPin,
//! }
//! let p = new_box(init_pin!(TooManyPin {
//!     a:? NeedPin::new,
//!     b: init_pin!(ManyPin {
//!         a: NeedPin::new,
//!         b: 0,
//!     }),
//! }));
//! # }
//! ```
//!
//! This crate also provides a [`UniqueRc`] and [`UniqueArc`], inspired from servo_arc.
//! They can be used to mutably initialize `Rc` and `Arc` before they are being shared.
//! [`new_rc`] and [`new_arc`] are provided which create [`UniqueRc`] and [`UniqueArc`]
//! internally, pin-initialize it with given constructor, and convert them to the shareable form.

#[cfg(feature = "alloc")]
extern crate alloc;

#[cfg(feature = "alloc")]
mod unique;

/// Mark a type as being [`init_pin!`]-able.
///
/// Can only be applied to structs. Each field can be tagged with `#[pin]`
/// or not. Tagged fields are pin-initialized, and untaged fields are initialized
/// by value like they do in normal struct expression.
///
/// ```no_run
/// # include!("doctest.rs");
/// #[pin_init]
/// struct ManyPin {
///     #[pin]
///     a: NeedPin,
///     b: usize,
/// }
/// # fn main() {}
/// ```
///
/// Also works for tuple-structs:
/// ```no_run
/// # include!("doctest.rs");
/// #[pin_init]
/// struct ManyPin(#[pin] NeedPin, usize);
/// # fn main() {}
/// ```
///
/// You could apply it to unit-structs (but probably not very useful):
/// ```no_run
/// # include!("doctest.rs");
/// #[pin_init]
/// struct NoPin;
/// # fn main() {}
/// ```
pub use pin_init_internal::pin_init;
#[cfg(feature = "alloc")]
pub use unique::{UniqueArc, UniqueRc};

use core::marker::PhantomData;
use core::mem;
use core::mem::MaybeUninit;

#[cfg(feature = "alloc")]
use alloc::{boxed::Box, rc::Rc, sync::Arc};
#[cfg(feature = "alloc")]
use core::{mem::ManuallyDrop, pin::Pin};

/// A pinned, uninitialized pointer.
///
/// This can be considered as a [`Pin<&mut MaybeUninit<T>>`].
///
/// Creating this pointer ensures:
/// * The pointee has a stable location in memory. It cannot be moved elsewhere.
/// * The pointee is not yet initialized.
/// * The [`PinInitResult`] returned by a pinning constructor is respected.
///
/// To ensure safety, the creator of `PinInit` has to:
/// * Ensure [`PinInit<'a, T>`] is never used with `'a` equal to `'static`.
/// * Verify that a [`PinInitResult<'a, E>`] is received for each [`PinInit<'a, T>`]
///   produced. To ensure that the `PinInitResult` is indeed created from a given
///   `PinInit`, the use of `PinInit` should be "closed", i.e. in the form of
///   invoking a closure of type `for<'a> FnOnce(PinInit<'a, T>) -> PinInitResult<'a, E>`.
///   The HRTB ensures that the `PinInitResult` must either be created from the
///   supplied `PinInit` (or from another `PinInit<'static, T>`, which isn't possible).
/// * If the [`PinInitResult<'a, E>`] is `Ok`, then the creator must treat the
///   pointer as [`Pin<&mut T>`]. This means that the
///   drop gurantee kick in; the memory cannot be deallocated until `T` is dropped.
///   If the result is `Err`, then the creator must not treat the pointer as
///   uninitialized and should not try to drop `T`.
///   If the call panicked, then we are not certain about initialization state.
///   We therefore must respect the drop guarantee but also not drop the value.
///   The only solution is to leak memory. If that's not possible, then the
///   caller must abort.
///
/// [`PinInit<'a, T>`]: PinInit
/// [`PinInitResult<'a, E>`]: PinInitResult
/// [Pin]: core::pin::Pin
pub struct PinInit<'a, T> {
    ptr: *mut MaybeUninit<T>,
    // Make sure the lifetime `'a` isn't tied to `MaybeUninit<T>`, to avoid
    // implying `T: 'a`. Note that `PinInit::new` still takes `&'a mut MaybeUninit<T>`,
    // so only well-formed `PinInit` can be constructed.
    _marker: PhantomData<&'a mut ()>,
}

impl<'a, T> PinInit<'a, T> {
    /// Creates a new [`PinInit`] with a given [`MaybeUninit<T>`].
    ///
    /// # Safety
    /// The caller must satisfy the safety requirement listed above.
    #[inline]
    pub unsafe fn new(ptr: &'a mut MaybeUninit<T>) -> Self {
        PinInit {
            ptr: ptr,
            _marker: PhantomData,
        }
    }

    /// Gets a mutable reference to `MaybeUninit` inside of this `PinInit`.
    ///
    /// This is safe because the `MaybeUninit` we point to is not yet initialized,
    /// and `MaybeUninit` does not have `Drop` implementation.
    #[inline]
    pub fn get_mut(&mut self) -> &mut MaybeUninit<T> {
        unsafe { &mut *self.ptr }
    }

    /// Asserts that the initialize is indeed completed.
    ///
    /// # Safety
    /// This function is unsafe as this is equivalent to [`MaybeUninit::assume_init`].
    #[inline]
    pub unsafe fn init_ok(self) -> PinInitOk<'a> {
        PinInitOk {
            marker: PhantomData,
        }
    }

    /// Generates a `PinInitResult` signaling that the initialization is failed.
    ///
    /// Note that the caller should make sure nothing is partially pinned-initialized.
    /// This isn't the contract of this function, but is the contract for
    /// creating `PinInit` for pinned-initializing sub-fields.
    #[inline]
    pub fn init_err<E>(self, err: E) -> PinInitErr<'a, E> {
        PinInitErr {
            inner: err,
            marker: PhantomData,
        }
    }

    /// Completes the initialization by moving the given value.
    ///
    /// Useful if the the type `T` can be initialized unpinned.
    #[inline]
    pub fn init_with_value(mut self, value: T) -> PinInitOk<'a> {
        // SAFFTY: writing to `MaybeUninit` is safe.
        unsafe { self.get_mut().as_mut_ptr().write(value) };
        // SAFETY: we have just performed initialization.
        unsafe { self.init_ok() }
    }
}

/// Proof that the value is pin-initialization.
///
/// See documentation of [`PinInit`] for details.
pub struct PinInitOk<'a> {
    marker: PhantomData<&'a mut ()>,
}

/// Proof that the value is not pin-initialized.
///
/// See documentation of [`PinInit`] for details.
pub struct PinInitErr<'a, E> {
    inner: E,
    marker: PhantomData<&'a mut ()>,
}

impl<'a, E> PinInitErr<'a, E> {
    /// Retrieve the result of whether the initialization has been completed.
    ///
    /// The returned value must be inspected in order to comply with the
    /// safety guarantee of `PinInit`.
    #[inline]
    pub fn into_inner(self) -> E {
        self.inner
    }

    #[inline]
    pub fn map<T, F>(self, f: F) -> PinInitErr<'a, T>
    where
        F: FnOnce(E) -> T,
    {
        PinInitErr {
            inner: f(self.inner),
            marker: PhantomData,
        }
    }
}

/// Result of pin-initialization.
///
/// See documentation of [`PinInit`] for details.
pub type PinInitResult<'a, E> = Result<PinInitOk<'a>, PinInitErr<'a, E>>;

/// Pin-initialize a box.
#[cfg(feature = "alloc")]
#[cfg_attr(doc_cfg, doc(cfg(feature = "alloc")))]
#[inline]
pub fn init_box<T, E, F>(x: Pin<Box<MaybeUninit<T>>>, f: F) -> Result<Pin<Box<T>>, E>
where
    F: for<'a> FnOnce(PinInit<'a, T>) -> PinInitResult<'a, E>,
{
    // SAFETY: We don't move value out.
    // If `f` below panics, we might be in a partially initialized state. We
    // cannot drop nor assume_init, so we can only leak.
    let mut ptr = ManuallyDrop::new(unsafe { Pin::into_inner_unchecked(x) });
    // SAFETY: pinning is guaranteed by `storage`'s pin guarantee.
    //         We will check the return value, and act accordingly.
    match f(unsafe { PinInit::new(&mut ptr) }) {
        Ok(_) => {
            // SAFETY: We know it's initialized, and both `ManuallyDrop` and `Pin`
            //         are `#[repr(transparent)]` so this is safe.
            Ok(unsafe { mem::transmute(ptr) })
        }
        Err(err) => {
            let err = err.into_inner();
            // SAFETY: We know it's not initialized.
            drop(ManuallyDrop::into_inner(ptr));
            Err(err)
        }
    }
}

/// Pin-initialize a `UniqueRc`.
#[cfg(feature = "alloc")]
#[cfg_attr(doc_cfg, doc(cfg(feature = "alloc")))]
#[inline]
pub fn init_unique_rc<T, E, F>(
    x: Pin<UniqueRc<MaybeUninit<T>>>,
    f: F,
) -> Result<Pin<UniqueRc<T>>, E>
where
    F: for<'a> FnOnce(PinInit<'a, T>) -> PinInitResult<'a, E>,
{
    // SAFETY: See `init_box`.
    let mut ptr = ManuallyDrop::new(unsafe { Pin::into_inner_unchecked(x) });
    match f(unsafe { PinInit::new(&mut ptr) }) {
        Ok(_) => Ok(unsafe { mem::transmute(ptr) }),
        Err(err) => {
            let err = err.into_inner();
            drop(ManuallyDrop::into_inner(ptr));
            Err(err)
        }
    }
}

/// Pin-initialize a `UniqueArc`.
#[cfg(feature = "alloc")]
#[cfg_attr(doc_cfg, doc(cfg(feature = "alloc")))]
#[inline]
pub fn init_unique_arc<T, E, F>(
    x: Pin<UniqueArc<MaybeUninit<T>>>,
    f: F,
) -> Result<Pin<UniqueArc<T>>, E>
where
    F: for<'a> FnOnce(PinInit<'a, T>) -> PinInitResult<'a, E>,
{
    // SAFETY: See `init_box`.
    let mut ptr = ManuallyDrop::new(unsafe { Pin::into_inner_unchecked(x) });
    match f(unsafe { PinInit::new(&mut ptr) }) {
        Ok(_) => Ok(unsafe { mem::transmute(ptr) }),
        Err(err) => {
            let err = err.into_inner();
            drop(ManuallyDrop::into_inner(ptr));
            Err(err)
        }
    }
}

/// Create a new `Box` and pin-initialize it.
#[cfg(feature = "alloc")]
#[cfg_attr(doc_cfg, doc(cfg(feature = "alloc")))]
#[inline]
pub fn new_box<T, E, F>(f: F) -> Result<Pin<Box<T>>, E>
where
    F: for<'a> FnOnce(PinInit<'a, T>) -> PinInitResult<'a, E>,
{
    init_box(Box::pin(MaybeUninit::uninit()), f)
}

/// Create a new `UniqueRc` and pin-initialize it.
#[cfg(feature = "alloc")]
#[cfg_attr(doc_cfg, doc(cfg(feature = "alloc")))]
#[inline]
pub fn new_unique_rc<T, E, F>(f: F) -> Result<Pin<UniqueRc<T>>, E>
where
    F: for<'a> FnOnce(PinInit<'a, T>) -> PinInitResult<'a, E>,
{
    init_unique_rc(UniqueRc::new_uninit().into(), f)
}

/// Create a new `UniqueArc` and pin-initialize it.
#[cfg(feature = "alloc")]
#[cfg_attr(doc_cfg, doc(cfg(feature = "alloc")))]
#[inline]
pub fn new_unique_arc<T, E, F>(f: F) -> Result<Pin<UniqueArc<T>>, E>
where
    F: for<'a> FnOnce(PinInit<'a, T>) -> PinInitResult<'a, E>,
{
    init_unique_arc(UniqueArc::new_uninit().into(), f)
}

/// Create a new `Rc` and pin-initialize it.
#[cfg(feature = "alloc")]
#[cfg_attr(doc_cfg, doc(cfg(feature = "alloc")))]
#[inline]
pub fn new_rc<T, E, F>(f: F) -> Result<Pin<Rc<T>>, E>
where
    F: for<'a> FnOnce(PinInit<'a, T>) -> PinInitResult<'a, E>,
{
    Ok(UniqueRc::shareable_pin(new_unique_rc(f)?))
}

/// Create a new `Arc` and pin-initialize it.
#[cfg(feature = "alloc")]
#[cfg_attr(doc_cfg, doc(cfg(feature = "alloc")))]
#[inline]
pub fn new_arc<T, E, F>(f: F) -> Result<Pin<Arc<T>>, E>
where
    F: for<'a> FnOnce(PinInit<'a, T>) -> PinInitResult<'a, E>,
{
    Ok(UniqueArc::shareable_pin(new_unique_arc(f)?))
}

#[doc(hidden)]
pub mod __private {
    use super::*;
    pub use pin_init_internal::PinInit;

    #[inline]
    pub fn stack_init<'a, T, E, F>(x: PinInit<'a, T>, f: F) -> PinInitResult<'a, E>
    where
        F: for<'b> FnOnce(PinInit<'b, T>) -> PinInitResult<'b, E>,
    {
        struct PanicGuard;
        impl Drop for PanicGuard {
            fn drop(&mut self) {
                panic!("panicked while pin-initing variable on stack");
            }
        }

        // If `f` below panics, we might be in a partially initialized state. We
        // cannot drop nor assume_init, and we cannot leak memory on stack. So
        // the only sensible action would be to abort (with double-panic).
        let g = PanicGuard;
        let res = f(x);
        mem::forget(g);
        res
    }

    #[inline]
    pub unsafe fn assume_init_mut<T>(v: &mut MaybeUninit<T>) -> &mut T {
        // SAFETY: caller makes the guarantee.
        unsafe { &mut *v.as_mut_ptr() }
    }

    // Helps to find `init_pin` macro to find the builder.
    pub trait PinInitBuildable<'this>: Sized {
        type Builder;

        fn __builder(init: PinInit<'this, Self>) -> Self::Builder;
    }
}

/// Create and pin-initialize a new variable on the stack.
///
/// ```
/// # include!("doctest.rs");
/// # fn main() {
/// init_stack!(p = NeedPin::new);
/// // Now `p` is a `Result<Pin<&mut NeedPin>, Infallible>`.
/// # }
/// ```
///
/// Can be used together with [`init_pin!`]:
/// ```
/// # include!("doctest.rs");
/// # fn main() {
/// #[pin_init]
/// struct ManyPin {
///     #[pin]
///     a: NeedPin,
///     b: usize,
/// }
/// init_stack!(p = init_pin!(ManyPin {
///     a: NeedPin::new,
///     b: 0,
/// }));
/// # }
/// ```
///
/// The initializers should not panic, and should use `Err` to report failures.
/// If the initializer fails, because we cannot tell whether the value is
/// initialized or not (or even just partially initialized), drop guarantee cannot
/// be kept, this macro will abort the process.
#[macro_export]
macro_rules! init_stack {
    ($var:ident = $init:expr) => {
        let mut storage = ::core::mem::MaybeUninit::uninit();
        let $var = match $crate::__private::stack_init(
            unsafe { $crate::PinInit::new(&mut storage) },
            $init,
        ) {
            Ok(_) => Ok(unsafe {
                ::core::pin::Pin::new_unchecked($crate::__private::assume_init_mut(&mut storage))
            }),
            Err(err) => Err(err.into_inner()),
        };
    };
}

/// Create and pin-initialize a struct.
///
/// The type to create need to be marked with [`#[pin_init]`](pin_init).
///
/// ```
/// # include!("doctest.rs");
/// # fn main() {
/// #[pin_init]
/// struct ManyPin {
///     #[pin]
///     a: NeedPin,
///     b: usize,
/// }
/// let p = new_box(init_pin!(ManyPin {
///     a: NeedPin::new,
///     b: 0,
/// }));
/// # }
/// ```
///
/// Also works for tuple-structs:
/// ```
/// # include!("doctest.rs");
/// # fn main() {
/// #[pin_init]
/// struct ManyPin(#[pin] NeedPin, usize);
/// let p = new_box(init_pin!(ManyPin(
///     NeedPin::new,
///     0,
/// )));
/// # }
/// ```
///
/// You could apply it to unit-structs (but probably not very useful):
/// ```
/// # include!("doctest.rs");
/// # fn main() {
/// #[pin_init]
/// struct NoPin;
/// let p: Result<_, Infallible> = new_box(init_pin!(NoPin));
/// # }
/// ```
///
/// By default, no conversions are made for errors, as otherwise type inference
/// may fail (like using the ? operator in a closure). If you need error conversion,
/// you need to add a `?` before expression. You can add `try Error =>` to specify
/// the error to avoid type inference failure.
/// ```
/// # include!("doctest.rs");
/// # fn main() {
/// #[pin_init]
/// # struct ManyPin {
/// #     #[pin]
/// #     a: NeedPin,
/// #     b: usize,
/// # }
/// let p = new_box(init_pin!(try Infallible => ManyPin {
///     a:? NeedPin::new,
///     b: 0,
/// }));
/// # }
/// ```
///
/// `init_pin!` can be used for nested initialization as well:
/// ```
/// # include!("doctest.rs");
/// # fn main() {
/// #[pin_init]
/// # struct ManyPin {
/// #     #[pin]
/// #     a: NeedPin,
/// #     b: usize,
/// # }
/// #[pin_init]
/// struct TooManyPin {
///     #[pin]
///     a: NeedPin,
///     #[pin]
///     b: ManyPin,
/// }
/// let p = new_box(init_pin!(TooManyPin {
///     a:? NeedPin::new,
///     b: init_pin!(ManyPin {
///         a: NeedPin::new,
///         b: 0,
///     }),
/// }));
/// # }
/// ```
///
/// If you want to define a cosntructor, you can write like this:
/// ```
/// # include!("doctest.rs");
/// # fn main() {
/// # #[pin_init]
/// # struct ManyPin {
/// #     #[pin]
/// #     a: NeedPin,
/// #     b: usize,
/// # }
/// impl ManyPin {
///     pub fn new(this: PinInit<'_, Self>) -> PinInitResult<'_, Infallible> {
///         init_pin!(ManyPin {
///             a: NeedPin::new,
///             b: 1,
///         })(this)
///     }
/// }
/// # }
///
/// ```
#[macro_export]
macro_rules! init_pin {
    // try Error => Struct {}
    (try $err:ty => $ty:ident { $($tt:tt)* }) => {{
        |this| -> $crate::PinInitResult<'_, $err> {
            use $crate::__private::PinInitBuildable;
            let builder = $ty::__builder(this);
            $crate::__init_pin_internal!(@named builder => $($tt)*,);
            Ok(builder.__init_ok())
        }
    }};
    // try Error => Struct()
    (try $err:ty => $ty:ident ( $($tt:tt)* )) => {{
        |this| -> $crate::PinInitResult<'_, $err> {
            use $crate::__private::PinInitBuildable;
            let builder = $ty::__builder(this);
            $crate::__init_pin_internal!(@unnamed builder => $($tt)*,);
            Ok(builder.__init_ok())
        }
    }};
    // try Error => Struct
    (try $err:ty => $ty:ident) => {{
        |this| -> $crate::PinInitResult<'_, $err> {
            use $crate::__private::PinInitBuildable;
            let builder = $ty::__builder(this);
            Ok(builder.__init_ok())
        }
    }};

    // Struct {}
    ($ty:ident { $($tt:tt)* }) => {{
        |this| {
            use $crate::__private::PinInitBuildable;
            let builder = $ty::__builder(this);
            $crate::__init_pin_internal!(@named builder => $($tt)*,);
            Ok(builder.__init_ok())
        }
    }};
    // Struct()
    ($ty:ident ( $($tt:tt)* )) => {{
        |this| {
            use $crate::__private::PinInitBuildable;
            let builder = $ty::__builder(this);
            $crate::__init_pin_internal!(@unnamed builder => $($tt)*,);
            Ok(builder.__init_ok())
        }
    }};
    // Struct
    ($ty:ident) => {{
        |this| {
            use $crate::__private::PinInitBuildable;
            let builder = $ty::__builder(this);
            Ok(builder.__init_ok())
        }
    }};
}

#[doc(hidden)]
#[macro_export]
macro_rules! __init_pin_internal {
    (@named $builder:ident => $(,)?) => {};
    (@named $builder:ident => $ident:ident : ? $expr:expr, $($tt:tt)*) => {
        let $builder = match $builder.$ident($expr) {
            Ok(v) => v,
            Err(err) => return Err(err.map(From::from)),
        };
        __init_pin_internal!(@named $builder => $($tt)*);
    };
    (@named $builder:ident => $ident:ident : $expr:expr, $($tt:tt)*) => {
        let $builder = match $builder.$ident($expr) {
            Ok(v) => v,
            Err(err) => return Err(err),
        };
        __init_pin_internal!(@named $builder => $($tt)*);
    };
    (@unnamed $builder:ident => $(,)?) => {};
    (@unnamed $builder:ident => ? $expr:expr, $($tt:tt)*) => {
        let $builder = match $builder.__next($expr) {
            Ok(v) => v,
            Err(err) => return Err(err.map(From::from)),
        };
        __init_pin_internal!(@unnamed $builder => $($tt)*);
    };
    (@unnamed $builder:ident => $expr:expr, $($tt:tt)*) => {
        let $builder = match $builder.__next($expr) {
            Ok(v) => v,
            Err(err) => return Err(err),
        };
        __init_pin_internal!(@unnamed $builder => $($tt)*);
    };
}
