use pin_init::*;

use std::io::Error;
use std::mem::MaybeUninit;
use std::pin::Pin;
use std::{
    cell::UnsafeCell,
    ops::{Deref, DerefMut},
};

#[repr(transparent)]
struct RawMutex {
    pthread: UnsafeCell<libc::pthread_mutex_t>,
}

unsafe impl Send for RawMutex {}
unsafe impl Sync for RawMutex {}

struct RawMutexGuard<'a>(&'a RawMutex);

impl Drop for RawMutex {
    fn drop(&mut self) {
        // Thanks to pin_init, we are certain that self is initialized already.
        unsafe {
            libc::pthread_mutex_destroy(self.pthread.get());
        }
    }
}

impl RawMutex {
    // Use pin_init's abstraction to provide a safe initializaiton.
    pub fn new(mut init: PinInit<'_, Self>) -> PinInitResult<'_, Error> {
        let ptr = init.get_mut().as_mut_ptr() as *mut libc::pthread_mutex_t;
        unsafe {
            ptr.write(libc::PTHREAD_MUTEX_INITIALIZER);

            let mut attr = MaybeUninit::<libc::pthread_mutexattr_t>::uninit();
            let ret = libc::pthread_mutexattr_init(attr.as_mut_ptr());
            if ret != 0 {
                return Err(init.init_err(Error::from_raw_os_error(ret)));
            }

            let ret =
                libc::pthread_mutexattr_settype(attr.as_mut_ptr(), libc::PTHREAD_MUTEX_NORMAL);
            if ret != 0 {
                libc::pthread_mutexattr_destroy(attr.as_mut_ptr());
                return Err(init.init_err(Error::from_raw_os_error(ret)));
            }

            let ret = libc::pthread_mutex_init(ptr, attr.as_ptr());
            libc::pthread_mutexattr_destroy(attr.as_mut_ptr());
            if ret != 0 {
                return Err(init.init_err(Error::from_raw_os_error(ret)));
            }

            Ok(init.init_ok())
        }
    }

    pub fn lock(&self) -> RawMutexGuard<'_> {
        unsafe {
            libc::pthread_mutex_lock(self.pthread.get());
            RawMutexGuard(self)
        }
    }
}

impl Drop for RawMutexGuard<'_> {
    fn drop(&mut self) {
        unsafe {
            libc::pthread_mutex_unlock(self.0.pthread.get());
        }
    }
}

// Now we can use pin_init to define a Mutex that wraps the RawMutex
#[pin_init]
struct Mutex<T> {
    #[pin]
    mutex: RawMutex,
    #[pin]
    data: UnsafeCell<T>,
}

struct MutexGuard<'a, T>(RawMutexGuard<'a>, &'a mut T);

impl<'a, T> Deref for MutexGuard<'a, T> {
    type Target = T;
    fn deref(&self) -> &T {
        self.1
    }
}

impl<'a, T> DerefMut for MutexGuard<'a, T> {
    fn deref_mut(&mut self) -> &mut T {
        self.1
    }
}

impl<T> Mutex<T> {
    pub fn new<F>(init: PinInit<'_, Self>, value: F) -> PinInitResult<'_, Error>
    where
        F: for<'a> FnOnce(PinInit<'_, T>) -> PinInitResult<'_, Error>,
    {
        init_pin!(Mutex {
            mutex: RawMutex::new,
            data: |mut data| {
                let ptr = data.get_mut().as_mut_ptr() as *mut MaybeUninit<T>;
                match unsafe { value(PinInit::new(&mut *ptr)) } {
                    Ok(_) => Ok(unsafe { data.init_ok() }),
                    Err(err) => Err(data.init_err(err.into_inner())),
                }
            }
        })(init)
    }

    pub fn new_with_value(init: PinInit<'_, Self>, value: T) -> PinInitResult<'_, Error> {
        Self::new(init, |s| Ok(s.init_with_value(value)))
    }

    pub fn lock(&self) -> Pin<MutexGuard<'_, T>> {
        let g = self.mutex.lock();
        unsafe { Pin::new_unchecked(MutexGuard(g, &mut *self.data.get())) }
    }

    pub fn get_inner(self: Pin<&mut Self>) -> Pin<&mut T> {
        unsafe { Pin::new_unchecked(&mut *self.data.get()) }
    }
}

fn main() {
    {
        let m = new_box(|s| Mutex::new_with_value(s, 1)).unwrap();
        println!("{}", *m.lock());
        *m.lock() = 2;
        println!("{}", *m.lock());
        *m.lock() = 3;
        println!("{}", *m.lock());
    }

    {
        // Even complete, nested pinned data structure can be safely
        // created and initialized on the stack.
        init_stack!(m = |s| Mutex::new(s, |s| Mutex::new_with_value(s, 1)));
        let m = m.unwrap();
        println!("{}", *m.lock().as_mut().get_inner());
        *m.lock().lock() = 2;
        println!("{}", *m.lock().lock());
        *m.lock().as_mut().get_inner() = 3;
        println!("{}", *m.lock().as_mut().get_inner());
    }
}
