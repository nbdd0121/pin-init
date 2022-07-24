use super::*;
#[cfg(feature = "alloc_try_pin_with")]
use core::alloc::AllocError;
use core::ops::{Deref, DerefMut};

/// An uniquely owned `Rc`.
///
/// Useful for constructing `Rc`, since we are certain that when `Rc` is
/// initially created, there is an unique reference. Once initially mutation
/// is done, it can be convert to `Rc` with `shareable()`.
#[cfg_attr(doc_cfg, doc(cfg(feature = "alloc")))]
#[repr(transparent)]
pub struct UniqueRc<T: ?Sized>(Rc<T>);

impl<T> UniqueRc<T> {
    /// Constructs a new `UniqueRc`.
    #[cfg(feature = "alloc_pin_with")]
    #[cfg_attr(doc_cfg, doc(cfg(feature = "alloc_pin_with")))]
    #[inline]
    pub fn new(data: T) -> Self {
        UniqueRc(Rc::new(data))
    }

    /// Try to constructs a new `UniqueRc`.
    #[cfg(feature = "alloc_try_pin_with")]
    #[cfg_attr(doc_cfg, doc(cfg(feature = "alloc_try_pin_with")))]
    #[inline]
    pub fn try_new(data: T) -> Result<Self, AllocError> {
        Ok(UniqueRc(Rc::try_new(data)?))
    }

    /// Convert to a shareable [`Rc<T>`].
    #[inline]
    pub fn shareable(x: Self) -> Rc<T> {
        x.0
    }

    /// Convert to a shareable [`Pin<Rc<T>>`].
    #[inline]
    pub fn shareable_pin(x: Pin<Self>) -> Pin<Rc<T>> {
        unsafe { Pin::new_unchecked(Pin::into_inner_unchecked(x).0) }
    }

    /// Constructs a new `UniqueRc` with uninitialized contents.
    #[inline]
    pub fn new_uninit() -> UniqueRc<MaybeUninit<T>> {
        UniqueRc::new(MaybeUninit::uninit())
    }
}

impl<T> UniqueRc<MaybeUninit<T>> {
    /// Convert to an initialized Rc.
    ///
    /// # Safety
    ///
    /// This function is unsafe as this is equivalent to [`MaybeUninit::assume_init`].
    #[inline]
    pub unsafe fn assume_init(self) -> UniqueRc<T> {
        unsafe { core::mem::transmute(self) }
    }
}

impl<T> Deref for UniqueRc<T> {
    type Target = T;
    #[inline]
    fn deref(&self) -> &T {
        &*self.0
    }
}

impl<T> DerefMut for UniqueRc<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut T {
        let ptr = Rc::as_ptr(&self.0) as *mut T;
        // SAFETY: We know this is unqiuely owned.
        unsafe { &mut *ptr }
    }
}

impl<T> From<UniqueRc<T>> for Pin<UniqueRc<T>> {
    fn from(x: UniqueRc<T>) -> Pin<UniqueRc<T>> {
        // SAFETY: stable address
        unsafe { Pin::new_unchecked(x) }
    }
}

// SAFETY: We know this is uniquely owned, so there is no possibility of data races
// over the Rc's non-atomic reference counts.
unsafe impl<T: Send> Send for UniqueRc<T> {}

// SAFETY: The underlying `Rc` cannot be cloned or dropped while the `UniqueRc` exists, so
// there is no possibility of data races over its non-atomic reference counts.
unsafe impl<T: Sync> Sync for UniqueRc<T> {}

/// An uniquely owned `Arc`.
///
/// Useful for constructing `Arc`, since we are certain that when `Arc` is
/// initially created, there is an unique reference. Once initially mutation
/// is done, it can be convert to `Arc` with `shareable()`.
#[cfg_attr(doc_cfg, doc(cfg(feature = "alloc")))]
#[repr(transparent)]
pub struct UniqueArc<T: ?Sized>(Arc<T>);

impl<T> UniqueArc<T> {
    /// Constructs a new `UniqueArc`.
    #[cfg(feature = "alloc_pin_with")]
    #[cfg_attr(doc_cfg, doc(cfg(feature = "alloc_pin_with")))]
    #[inline]
    pub fn new(data: T) -> Self {
        UniqueArc(Arc::new(data))
    }

    /// Try to constructs a new `UniqueArc`.
    #[cfg(feature = "alloc_try_pin_with")]
    #[cfg_attr(doc_cfg, doc(cfg(feature = "alloc_try_pin_with")))]
    #[inline]
    pub fn try_new(data: T) -> Result<Self, AllocError> {
        Ok(UniqueArc(Arc::try_new(data)?))
    }

    /// Convert to a shareable [`Arc<T>`].
    #[inline]
    pub fn shareable(x: Self) -> Arc<T> {
        x.0
    }

    /// Convert to a shareable [`Pin<Arc<T>>`].
    #[inline]
    pub fn shareable_pin(x: Pin<Self>) -> Pin<Arc<T>> {
        unsafe { Pin::new_unchecked(Pin::into_inner_unchecked(x).0) }
    }

    /// Constructs a new `UniqueArc` with uninitialized contents.
    #[inline]
    pub fn new_uninit() -> UniqueArc<MaybeUninit<T>> {
        UniqueArc::new(MaybeUninit::uninit())
    }
}

impl<T> UniqueArc<MaybeUninit<T>> {
    /// Convert to an initialized Arc.
    ///
    /// # Safety
    ///
    /// This function is unsafe as this is equivalent to [`MaybeUninit::assume_init`].
    #[inline]
    pub unsafe fn assume_init(self) -> UniqueArc<T> {
        unsafe { core::mem::transmute(self) }
    }
}

impl<T> Deref for UniqueArc<T> {
    type Target = T;
    #[inline]
    fn deref(&self) -> &T {
        &*self.0
    }
}

impl<T> DerefMut for UniqueArc<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut T {
        let ptr = Arc::as_ptr(&self.0) as *mut T;
        // SAFETY: We know this is unqiuely owned.
        unsafe { &mut *ptr }
    }
}

impl<T> From<UniqueArc<T>> for Pin<UniqueArc<T>> {
    fn from(x: UniqueArc<T>) -> Pin<UniqueArc<T>> {
        // SAFETY: stable address
        unsafe { Pin::new_unchecked(x) }
    }
}
