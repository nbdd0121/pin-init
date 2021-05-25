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
//!     // Must points to itself
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
//! `for<'a> FnOnce(PinInit<'a, T>) -> PinInitResult<'a, T, Err>`.
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
//!     pub fn new(mut this: PinInit<'_, Self>) -> PinInitResult<'_, Self, Infallible> {
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
//!
//! [`UniqueRc`]: struct.UniqueRc.html
//! [`UniqueArc`]: struct.UniqueArc.html
//! [`new_rc`]: fn.new_rc.html
//! [`new_arc`]: fn.new_arc.html

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
use core::pin::Pin;

#[cfg(feature = "alloc")]
use alloc::{boxed::Box, rc::Rc, sync::Arc};
#[cfg(feature = "alloc")]
use core::mem::ManuallyDrop;

/// A pinned, uninitialized pointer.
///
/// This can be considered as [`Pin<&mut MaybeUninit<T>>`]:
/// * The pointee has a stable location in memory. It cannot be moved elsewhere.
/// * The pointee is not yet initialized, therefore the drop guarantee is not
///   existent.
///
/// However, `PinInit` provides the additional guarantee that once a method
/// that successfully initialze the data is called (e.g. [`init_ok`](#method.init_ok)), the
/// pointee will be considered as [`Pin<&mut T>`], therefore the drop guarantee
/// kicks in, and `T`'s destructor is guaranteed to be called before the storage
/// is deallocated.
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
    /// The caller must ensure `ptr` has a stable location in memory.
    ///
    /// The caller must obtain a [`PinInitResult`] that is tied to the lifetime of the returned
    /// `PinInit`, and need to respect its value:
    /// * If [`PinInitOk`] is obtained, the caller must treat the `ptr` as [`Pin<&mut T>`].
    ///   This means that the drop guarantee kick in; the memory cannot be deallocated until `T`
    ///   is dropped.
    /// * If [`PinInitErr`] is obtained, `ptr` is uninitialized and the caller must not
    ///   try to drop `T`.
    /// * If panic happens while trying to get the result, then we are not certain about
    ///   initialization state. This means that the caller must respect the drop guarantee,
    ///   but also not drop the value. The only solution is to leak memory. If that's not possible,
    ///   then the caller must abort the process.
    ///
    /// The lifetime associated with this function should be "closed". It should be a local,
    /// temporary lifetime, shorter than any of the lifetime the caller have access to (including
    /// `'static`, and should not escape the calling function.
    /// This is to guarantee that the only way to get a [`PinInitResult<'a, T, E>`]
    /// is to use of the methods of this particular `PinInit` returned.
    /// In order to satisfy the requirement, the caller typically takes a constructor with type
    /// `for<'a> FnOnce(PinInit<'a, T>) -> PinInitResult<'a, T, E>`.
    ///
    /// [`PinInit<'a, T>`]: PinInit
    /// [`PinInitResult<'a, T, E>`]: PinInitResult
    #[inline]
    pub unsafe fn new(ptr: &'a mut MaybeUninit<T>) -> Self {
        PinInit {
            ptr,
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

    /// Asserts that the initialize is indeed completed. Doing so initiates the
    /// drop guarantee of `T`.
    ///
    /// # Safety
    /// This function is unsafe as this is equivalent to [`MaybeUninit::assume_init`].
    #[inline]
    pub unsafe fn init_ok(self) -> PinInitOk<'a, T> {
        PinInitOk {
            ptr: self.ptr as *mut T,
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

    /// Completes the initialization with a callback.
    ///
    /// Useful e.g. if the callback is produced by `init_pin!`.
    #[inline]
    pub fn init<E, F>(self, value: F) -> PinInitResult<'a, T, E>
    where
        F: FnOnce(Self) -> PinInitResult<'a, T, E>,
    {
        value(self)
    }

    /// Completes the initialization by moving the given value.
    ///
    /// Useful if the the type `T` can be initialized unpinned.
    #[inline]
    pub fn init_with_value(mut self, value: T) -> PinInitOk<'a, T> {
        // SAFFTY: writing to `MaybeUninit` is safe.
        unsafe { self.get_mut().as_mut_ptr().write(value) };
        // SAFETY: we have just performed initialization.
        unsafe { self.init_ok() }
    }
}

/// Proof that the value is pin-initialization.
///
/// See documentation of [`PinInit`] for details.
pub struct PinInitOk<'a, T> {
    // We don't want a T: 'a bound, so don't we cannot put `Pin<&'a mut T>` here.
    // This is safe as, `PinInitOk` can only come from `PinInit::new` which
    // guarantees the well-formedness.
    ptr: *mut T,
    marker: PhantomData<&'a mut ()>,
}

impl<'a, T> PinInitOk<'a, T> {
    /// Get the `Pin<&T>` view of the pinned and initialized `T`.
    #[inline]
    pub fn as_ref(&self) -> Pin<&T> {
        unsafe { Pin::new_unchecked(&*self.ptr) }
    }

    /// Get the `Pin<&mut T>` view of the pinned and initialized `T`.
    #[inline]
    pub fn as_mut(&mut self) -> Pin<&mut T> {
        unsafe { Pin::new_unchecked(&mut *self.ptr) }
    }

    /// Get the pinned and initialized `T`.
    #[inline]
    pub fn into_inner(self) -> Pin<&'a mut T> {
        unsafe { Pin::new_unchecked(&mut *self.ptr) }
    }
}

/// Proof that the value is not pin-initialized.
///
/// See documentation of [`PinInit`] for details.
pub struct PinInitErr<'a, E> {
    inner: E,
    marker: PhantomData<&'a mut ()>,
}

impl<'a, E> PinInitErr<'a, E> {
    /// Get a reference to the inner error.
    #[inline]
    pub fn as_ref(&self) -> &E {
        &self.inner
    }

    /// Get a mutable reference to the inner error.
    #[inline]
    pub fn as_mut(&mut self) -> &mut E {
        &mut self.inner
    }

    /// Get the inner error.
    #[inline]
    pub fn into_inner(self) -> E {
        self.inner
    }

    /// Map the inner error with the given function.
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
pub type PinInitResult<'a, T, E> = Result<PinInitOk<'a, T>, PinInitErr<'a, E>>;

/// Pin-initialize a box.
#[cfg(feature = "alloc")]
#[cfg_attr(doc_cfg, doc(cfg(feature = "alloc")))]
#[inline]
pub fn init_box<T, E, F>(x: Pin<Box<MaybeUninit<T>>>, f: F) -> Result<Pin<Box<T>>, E>
where
    F: for<'a> FnOnce(PinInit<'a, T>) -> PinInitResult<'a, T, E>,
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
    F: for<'a> FnOnce(PinInit<'a, T>) -> PinInitResult<'a, T, E>,
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
    F: for<'a> FnOnce(PinInit<'a, T>) -> PinInitResult<'a, T, E>,
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
    F: for<'a> FnOnce(PinInit<'a, T>) -> PinInitResult<'a, T, E>,
{
    init_box(Box::pin(MaybeUninit::uninit()), f)
}

/// Create a new `UniqueRc` and pin-initialize it.
#[cfg(feature = "alloc")]
#[cfg_attr(doc_cfg, doc(cfg(feature = "alloc")))]
#[inline]
pub fn new_unique_rc<T, E, F>(f: F) -> Result<Pin<UniqueRc<T>>, E>
where
    F: for<'a> FnOnce(PinInit<'a, T>) -> PinInitResult<'a, T, E>,
{
    init_unique_rc(UniqueRc::new_uninit().into(), f)
}

/// Create a new `UniqueArc` and pin-initialize it.
#[cfg(feature = "alloc")]
#[cfg_attr(doc_cfg, doc(cfg(feature = "alloc")))]
#[inline]
pub fn new_unique_arc<T, E, F>(f: F) -> Result<Pin<UniqueArc<T>>, E>
where
    F: for<'a> FnOnce(PinInit<'a, T>) -> PinInitResult<'a, T, E>,
{
    init_unique_arc(UniqueArc::new_uninit().into(), f)
}

/// Create a new `Rc` and pin-initialize it.
#[cfg(feature = "alloc")]
#[cfg_attr(doc_cfg, doc(cfg(feature = "alloc")))]
#[inline]
pub fn new_rc<T, E, F>(f: F) -> Result<Pin<Rc<T>>, E>
where
    F: for<'a> FnOnce(PinInit<'a, T>) -> PinInitResult<'a, T, E>,
{
    Ok(UniqueRc::shareable_pin(new_unique_rc(f)?))
}

/// Create a new `Arc` and pin-initialize it.
#[cfg(feature = "alloc")]
#[cfg_attr(doc_cfg, doc(cfg(feature = "alloc")))]
#[inline]
pub fn new_arc<T, E, F>(f: F) -> Result<Pin<Arc<T>>, E>
where
    F: for<'a> FnOnce(PinInit<'a, T>) -> PinInitResult<'a, T, E>,
{
    Ok(UniqueArc::shareable_pin(new_unique_arc(f)?))
}

/// Types that can be constructed using `init_pin`.
///
/// This trait is not meant for manual implementation and consumption.
/// You should use [`#[pin_init]`](pin_init) attribute to implement this trait, and
/// [`init_pin!`] macro to use.
///
/// This trait is implemented on some std types so they can also be constructed
/// using `init_pin!`.
pub trait PinInitable<'this>: Sized {
    #[doc(hidden)]
    type __PinInitBuilder;

    #[doc(hidden)]
    fn __pin_init_builder(init: PinInit<'this, Self>) -> Self::__PinInitBuilder;
}

#[doc(hidden)]
pub mod __private {
    use super::*;
    pub use pin_init_internal::PinInit;

    #[inline]
    pub fn stack_init<'a, T, E, F>(x: PinInit<'a, T>, f: F) -> Result<Pin<&'a mut T>, E>
    where
        F: for<'b> FnOnce(PinInit<'b, T>) -> PinInitResult<'b, T, E>,
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

        match res {
            Ok(ok) => Ok(ok.into_inner()),
            Err(err) => Err(err.into_inner()),
        }
    }

    pub struct ValueBuilder<'this, T>(PinInitOk<'this, T>);

    impl<'this, T> ValueBuilder<'this, T> {
        #[inline]
        pub fn __init_ok(self) -> PinInitOk<'this, T> {
            self.0
        }
    }

    // pin-project users may want a #[pin] PhantomPinned
    impl<'this> PinInitable<'this> for core::marker::PhantomPinned {
        #[doc(hidden)]
        type __PinInitBuilder = ValueBuilder<'this, Self>;

        #[doc(hidden)]
        #[inline]
        fn __pin_init_builder(init: PinInit<'this, Self>) -> Self::__PinInitBuilder {
            ValueBuilder(init.init_with_value(Self))
        }
    }

    pub struct TransparentBuilder<'this, T, W>(PinInit<'this, W>, PhantomData<PinInit<'this, T>>);

    impl<'this, T> PinInitable<'this> for core::cell::UnsafeCell<T> {
        #[doc(hidden)]
        type __PinInitBuilder = TransparentBuilder<'this, T, core::cell::UnsafeCell<T>>;

        #[doc(hidden)]
        #[inline]
        fn __pin_init_builder(init: PinInit<'this, Self>) -> Self::__PinInitBuilder {
            TransparentBuilder(init, PhantomData)
        }
    }

    impl<'this, T> PinInitable<'this> for core::cell::Cell<T> {
        #[doc(hidden)]
        type __PinInitBuilder = TransparentBuilder<'this, T, core::cell::Cell<T>>;

        #[doc(hidden)]
        #[inline]
        fn __pin_init_builder(init: PinInit<'this, Self>) -> Self::__PinInitBuilder {
            TransparentBuilder(init, PhantomData)
        }
    }

    impl<'this, T, W> TransparentBuilder<'this, T, W> {
        #[inline]
        pub fn __next<E, F>(mut self, f: F) -> Result<ValueBuilder<'this, W>, PinInitErr<'this, E>>
        where
            F: for<'a> FnOnce(PinInit<'a, T>) -> PinInitResult<'a, T, E>,
        {
            // This is okay because we only deal with #[repr(transparent)] structs here.
            let ptr = self.0.get_mut().as_mut_ptr() as *mut MaybeUninit<T>;
            match f(unsafe { PinInit::new(&mut *ptr) }) {
                Ok(_) => Ok(ValueBuilder(unsafe { self.0.init_ok() })),
                Err(err) => Err(self.0.init_err(err.into_inner())),
            }
        }
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
        let $var =
            $crate::__private::stack_init(unsafe { $crate::PinInit::new(&mut storage) }, $init);
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
/// If you want to define a constructor, you can write like this:
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
///     pub fn new(this: PinInit<'_, Self>) -> PinInitResult<'_, Self, Infallible> {
///         this.init(init_pin!(ManyPin {
///             a: NeedPin::new,
///             b: 1,
///         }))
///     }
/// }
/// # }
/// ```
///
/// `init_pin!` can also initialize some std types:
/// ```
/// # include!("doctest.rs");
/// # fn main() {
/// use core::cell::UnsafeCell;
/// use core::cell::Cell;
/// init_pin!(try Infallible => PhantomPinned);
/// init_pin!(UnsafeCell(NeedPin::new));
/// init_pin!(Cell(NeedPin::new));
/// # }
/// ```
#[macro_export]
macro_rules! init_pin {
    // try Error => Struct {}
    (try $err:ty => $ty:ident { $($tt:tt)* }) => {{
        |this| -> $crate::PinInitResult<'_, _, $err> {
            use $crate::PinInitable;
            let builder = $ty::__pin_init_builder(this);
            $crate::__init_pin_internal!(@named builder => $($tt)*,);
            Ok(builder.__init_ok())
        }
    }};
    // try Error => Struct()
    (try $err:ty => $ty:ident ( $($tt:tt)* )) => {{
        |this| -> $crate::PinInitResult<'_, _, $err> {
            use $crate::PinInitable;
            let builder = $ty::__pin_init_builder(this);
            $crate::__init_pin_internal!(@unnamed builder => $($tt)*,);
            Ok(builder.__init_ok())
        }
    }};
    // try Error => Struct
    (try $err:ty => $ty:ident) => {{
        |this| -> $crate::PinInitResult<'_, _, $err> {
            use $crate::PinInitable;
            let builder = $ty::__pin_init_builder(this);
            Ok(builder.__init_ok())
        }
    }};

    // Struct {}
    ($ty:ident { $($tt:tt)* }) => {{
        |this| {
            use $crate::PinInitable;
            let builder = $ty::__pin_init_builder(this);
            $crate::__init_pin_internal!(@named builder => $($tt)*,);
            Ok(builder.__init_ok())
        }
    }};
    // Struct()
    ($ty:ident ( $($tt:tt)* )) => {{
        |this| {
            use $crate::PinInitable;
            let builder = $ty::__pin_init_builder(this);
            $crate::__init_pin_internal!(@unnamed builder => $($tt)*,);
            Ok(builder.__init_ok())
        }
    }};
    // Struct
    ($ty:ident) => {{
        |this| {
            use $crate::PinInitable;
            let builder = $ty::__pin_init_builder(this);
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
