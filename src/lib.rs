#![no_std]
#![cfg_attr(doc_cfg, feature(doc_cfg))]
#![warn(unsafe_op_in_unsafe_fn)]

//! Safe pinned-initialization in Rust.
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
//! constructor that returns `Result<T, Err>`, `pin_init` expect you to present a constructor
//! that returns `impl PinInitializer<T, Err>`, where [`PinInitializer`] can be created from
//! a closure of type `for<'a> FnOnce(PinInit<'a, T>) -> PinInitResult<'a, T, Err>`
//! using [`init_from_closure`].
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
//!     pub fn new() -> impl PinInitializer<Self, Infallible> {
//!         init_from_closure(|mut this: PinInit<'_, Self>| -> PinInitResult<'_, Self, Infallible> {
//!             let v = this.get_mut().as_mut_ptr();
//!             unsafe { *ptr::addr_of_mut!((*v).address) = v };
//!             Ok(unsafe { this.init_ok() })
//!         })
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
//! let p: Pin<Box<NeedPin>> = pin_init::new_box(NeedPin::new()).unwrap();
//! // On the stack
//! init_stack!(p = NeedPin::new());
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
//!     a: NeedPin::new(),
//!     b: init_pin!(ManyPin {
//!         a: NeedPin::new(),
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
//! This crate allows safe initialization of pinned data structure.
//! [`pin-project`](https://docs.rs/pin-project) can be used to safely access these structs. You can
//! use both `#[pin_init]` and `#[pin_project]` together with your struct, they even share the same
//! `#[pin]` field attribute!
//!
//! See [examples](https://github.com/nbdd0121/pin-init/tree/trunk/examples) for some non-artifical examples.
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
///     a: NeedPin::new(),
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
///     NeedPin::new(),
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
/// you can use [`PinInitializer::map_err`].
/// You may need type annotation or [`specify_err`] to avoid type inference failure.
/// ```
/// # include!("doctest.rs");
/// # fn main() {
/// #[pin_init]
/// # struct ManyPin {
/// #     #[pin]
/// #     a: NeedPin,
/// #     b: usize,
/// # }
/// let p: Result<Pin<Box<_>>, Infallible> = new_box(init_pin!(ManyPin {
///     a: NeedPin::new().map_err(Into::into),
///     b: 0,
/// }));
/// # }
/// ```
///
/// `init_pin!` can be used for nested initialization as well:
/// ```
/// # include!("doctest.rs");
/// # fn main() {
/// # #[pin_init]
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
///     a: NeedPin::new(),
///     // Nested by default. To opt out write `b: #[unpin] NeedPin {`.
///     b: ManyPin {
///         a: NeedPin::new(),
///         b: 0,
///     },
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
///     pub fn new() -> impl PinInitializer<Self, Infallible> {
///         init_pin!(ManyPin {
///             a: NeedPin::new(),
///             b: 1,
///         })
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
/// specify_err::<_, Infallible, _>(init_pin!(PhantomPinned));
/// init_pin!(UnsafeCell(NeedPin::new()));
/// init_pin!(Cell(NeedPin::new()));
/// # }
/// ```
pub use pin_init_internal::init_pin;

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
    /// `PinInitializer<T, E>`, which can be seen as `for<'a> FnOnce(PinInit<'a, T>) -> PinInitResult<'a, T, E>`.
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
        F: PinInitializer<T, E>,
    {
        value.init(self)
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

/// Proof that the value is pin-initialized.
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

/// Initializer that can be used to safely pin-initialize `T`.
///
/// A blanket implementation `impl<T, E> PinInitializer<T, E> for T` is provided for all types, so
/// a non-pinned value can be used directly for pin-initialization.
pub trait PinInitializer<T, E>: Sized {
    /// Pin-iInitialize `this`.
    fn init<'a>(self, this: PinInit<'a, T>) -> PinInitResult<'a, T, E>;

    /// Maps the error from `E` to `E2`.
    fn map_err<E2, F>(self, f: F) -> MapErr<T, E, E2, Self, F>
    where
        F: FnOnce(E) -> E2,
    {
        MapErr {
            init: self,
            map: f,
            marker: PhantomData,
        }
    }
}

impl<T, E> PinInitializer<T, E> for T {
    fn init<'a>(self, this: PinInit<'a, T>) -> PinInitResult<'a, T, E> {
        Ok(this.init_with_value(self))
    }
}

#[doc(hidden)]
pub struct MapErr<T, E, E2, I, F> {
    init: I,
    map: F,
    marker: PhantomData<(fn(T) -> E, fn(E) -> E2)>,
}

impl<T, E, E2, I, F> PinInitializer<T, E2> for MapErr<T, E, E2, I, F>
where
    I: PinInitializer<T, E>,
    F: FnOnce(E) -> E2,
{
    fn init<'a>(self, this: PinInit<'a, T>) -> PinInitResult<'a, T, E2> {
        match self.init.init(this) {
            Ok(v) => Ok(v),
            Err(v) => Err(v.map(self.map)),
        }
    }
}

/// Specify an Error type if type inference cannot infer it.
pub fn specify_err<T, E, I>(init: I) -> impl PinInitializer<T, E>
where
    I: PinInitializer<T, E>,
{
    init
}

/// Construct a [`PinInitializer<T, E>`] with a closure.
pub fn init_from_closure<T, E, F>(f: F) -> impl PinInitializer<T, E>
where
    F: for<'a> FnOnce(PinInit<'a, T>) -> PinInitResult<'a, T, E>,
{
    struct ClosureInit<T, E, F>(F, PhantomData<fn(T) -> E>)
    where
        F: for<'a> FnOnce(PinInit<'a, T>) -> PinInitResult<'a, T, E>;

    impl<T, E, F> PinInitializer<T, E> for ClosureInit<T, E, F>
    where
        F: for<'a> FnOnce(PinInit<'a, T>) -> PinInitResult<'a, T, E>,
    {
        fn init<'a>(self, this: PinInit<'a, T>) -> PinInitResult<'a, T, E> {
            (self.0)(this)
        }
    }

    ClosureInit(f, PhantomData)
}

/// Pin-initialize a box.
#[cfg(feature = "alloc")]
#[cfg_attr(doc_cfg, doc(cfg(feature = "alloc")))]
#[inline]
pub fn init_box<T, E, F>(x: Pin<Box<MaybeUninit<T>>>, f: F) -> Result<Pin<Box<T>>, E>
where
    F: PinInitializer<T, E>,
{
    // SAFETY: We don't move value out.
    // If `f` below panics, we might be in a partially initialized state. We
    // cannot drop nor assume_init, so we can only leak.
    let mut ptr = ManuallyDrop::new(unsafe { Pin::into_inner_unchecked(x) });
    // SAFETY: pinning is guaranteed by `storage`'s pin guarantee.
    //         We will check the return value, and act accordingly.
    match f.init(unsafe { PinInit::new(&mut ptr) }) {
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
    F: PinInitializer<T, E>,
{
    // SAFETY: See `init_box`.
    let mut ptr = ManuallyDrop::new(unsafe { Pin::into_inner_unchecked(x) });
    match f.init(unsafe { PinInit::new(&mut ptr) }) {
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
    F: PinInitializer<T, E>,
{
    // SAFETY: See `init_box`.
    let mut ptr = ManuallyDrop::new(unsafe { Pin::into_inner_unchecked(x) });
    match f.init(unsafe { PinInit::new(&mut ptr) }) {
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
    F: PinInitializer<T, E>,
{
    init_box(Box::pin(MaybeUninit::uninit()), f)
}

/// Create a new `UniqueRc` and pin-initialize it.
#[cfg(feature = "alloc")]
#[cfg_attr(doc_cfg, doc(cfg(feature = "alloc")))]
#[inline]
pub fn new_unique_rc<T, E, F>(f: F) -> Result<Pin<UniqueRc<T>>, E>
where
    F: PinInitializer<T, E>,
{
    init_unique_rc(UniqueRc::new_uninit().into(), f)
}

/// Create a new `UniqueArc` and pin-initialize it.
#[cfg(feature = "alloc")]
#[cfg_attr(doc_cfg, doc(cfg(feature = "alloc")))]
#[inline]
pub fn new_unique_arc<T, E, F>(f: F) -> Result<Pin<UniqueArc<T>>, E>
where
    F: PinInitializer<T, E>,
{
    init_unique_arc(UniqueArc::new_uninit().into(), f)
}

/// Create a new `Rc` and pin-initialize it.
#[cfg(feature = "alloc")]
#[cfg_attr(doc_cfg, doc(cfg(feature = "alloc")))]
#[inline]
pub fn new_rc<T, E, F>(f: F) -> Result<Pin<Rc<T>>, E>
where
    F: PinInitializer<T, E>,
{
    Ok(UniqueRc::shareable_pin(new_unique_rc(f)?))
}

/// Create a new `Arc` and pin-initialize it.
#[cfg(feature = "alloc")]
#[cfg_attr(doc_cfg, doc(cfg(feature = "alloc")))]
#[inline]
pub fn new_arc<T, E, F>(f: F) -> Result<Pin<Arc<T>>, E>
where
    F: PinInitializer<T, E>,
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

    pub struct StackWrapper<T>(MaybeUninit<T>, bool);

    impl<T> StackWrapper<T> {
        #[inline]
        pub fn new() -> Self {
            StackWrapper(MaybeUninit::uninit(), false)
        }

        #[inline]
        pub fn init<F, E>(self: Pin<&mut Self>, f: F) -> Result<Pin<&mut T>, E>
        where
            F: PinInitializer<T, E>,
        {
            struct PanicGuard;
            impl Drop for PanicGuard {
                #[inline]
                fn drop(&mut self) {
                    panic!("panicked while pin-initing variable on stack");
                }
            }

            assert!(!self.1);

            let this = unsafe { self.get_unchecked_mut() };

            // If `f` below panics, we might be in a partially initialized state. We
            // cannot drop nor assume_init, and we cannot leak memory on stack. So
            // the only sensible action would be to abort (with double-panic).
            let g = PanicGuard;
            let res = f.init(unsafe { PinInit::new(&mut this.0) });
            mem::forget(g);

            match res {
                Ok(ok) => {
                    this.1 = true;
                    Ok(ok.into_inner())
                }
                Err(err) => Err(err.into_inner()),
            }
        }
    }

    impl<T> Drop for StackWrapper<T> {
        #[inline]
        fn drop(&mut self) {
            if self.1 {
                unsafe {
                    self.0.as_mut_ptr().drop_in_place();
                }
            }
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
            F: PinInitializer<T, E>,
        {
            // This is okay because we only deal with #[repr(transparent)] structs here.
            let ptr = self.0.get_mut().as_mut_ptr() as *mut MaybeUninit<T>;
            match f.init(unsafe { PinInit::new(&mut *ptr) }) {
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
/// init_stack!(p = NeedPin::new());
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
///     a: NeedPin::new(),
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
        let mut storage = $crate::__private::StackWrapper::new();
        let $var = unsafe { Pin::new_unchecked(&mut storage) }.init($crate::init_pin!($init));
    };
}
