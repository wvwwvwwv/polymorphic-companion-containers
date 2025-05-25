//! Companion stack.

use std::mem::{MaybeUninit, align_of, forget, transmute};
use std::ops::{Deref, DerefMut};
use std::ptr::{drop_in_place, write};

use crate::exit_guard::ExitGuard;

const DEFAULT_STACK_SIZE: usize = 16384;

/// A dynamically sized stack.
#[derive(Debug)]
pub struct CompanionStack<const SIZE: usize = DEFAULT_STACK_SIZE> {
    buffer: MaybeUninit<[u8; SIZE]>,
    cursor: usize,
}

/// Errors.
#[derive(Debug)]
pub enum Error<E> {
    /// Failed to construct a value.
    ConstructionFailed(E),
    /// Stack is full.
    Full,
}

impl<const SIZE: usize> CompanionStack<SIZE> {
    /// Creates a new dynamically sized stack.
    #[must_use]
    pub fn new() -> Self {
        Self {
            buffer: MaybeUninit::uninit(),
            cursor: 0,
        }
    }

    /// Allocates a new value on the stack.
    ///
    /// # Errors
    ///
    /// Returns an error if the stack is full or if the alignment of the type is not supported.
    pub fn push_one<E, T: Sized, C: FnOnce() -> Result<T, E>>(
        &mut self,
        constructor: C,
    ) -> Result<Handle<T, SIZE>, Error<E>> {
        let alignment = align_of::<T>();
        let size = size_of::<T>();
        let buffer_start = unsafe { self.buffer.as_ptr().cast::<u8>().add(self.cursor) };
        let aligned_offset = buffer_start.align_offset(alignment);
        if aligned_offset == usize::MAX
            || self
                .cursor
                .checked_add(aligned_offset)
                .and_then(|start| start.checked_add(size))
                .filter(|end| *end <= SIZE)
                .is_none()
        {
            return Err(Error::Full);
        }
        let ptr = unsafe {
            self.buffer
                .as_mut_ptr()
                .cast::<u8>()
                .add(self.cursor + aligned_offset)
                .cast::<T>()
        };
        unsafe { ptr.write(constructor().map_err(|e| Error::ConstructionFailed(e))?) };

        let old_cursor = self.cursor;
        self.cursor = self.cursor + aligned_offset + size;
        let destructor = if std::mem::needs_drop::<T>() {
            drop_in_place::<T> as usize
        } else {
            0
        };
        Ok(Handle {
            inst: unsafe { &mut *ptr },
            old_cursor,
            stack: self,
            destructor,
        })
    }

    /// Pushes a slice onto the stack.
    ///
    /// # Errors
    ///
    /// Returns an error if the stack is full.
    pub fn push_many<E, T: Sized, C: FnMut(usize) -> Result<T, E>>(
        &mut self,
        mut constructor: C,
        len: usize,
    ) -> Result<Handle<[T], SIZE>, Error<E>> {
        let alignment = align_of::<T>();
        let size = size_of::<T>().checked_mul(len).ok_or(Error::Full)?;
        let buffer_start = unsafe { self.buffer.as_ptr().cast::<u8>().add(self.cursor) };
        let aligned_offset = buffer_start.align_offset(alignment);
        if aligned_offset == usize::MAX
            || self
                .cursor
                .checked_add(aligned_offset)
                .and_then(|start| start.checked_add(size))
                .filter(|end| *end <= SIZE)
                .is_none()
        {
            return Err(Error::Full);
        }
        let ptr = unsafe {
            self.buffer
                .as_mut_ptr()
                .cast::<u8>()
                .add(self.cursor + aligned_offset)
                .cast::<T>()
        };
        for i in 0..len {
            let mut exit_guard = ExitGuard::new(true, |failed| {
                if failed {
                    for j in 0..i {
                        unsafe {
                            drop_in_place(ptr.add(j));
                        }
                    }
                }
            });
            unsafe {
                write(
                    ptr.add(i),
                    constructor(i).map_err(|e| Error::ConstructionFailed(e))?,
                );
            }
            *exit_guard = false;
        }

        let old_cursor = self.cursor;
        self.cursor = self.cursor + aligned_offset + size;
        let destructor = if std::mem::needs_drop::<T>() {
            Self::slice_destructor::<T> as usize
        } else {
            0
        };
        Ok(Handle {
            inst: unsafe { &mut *std::ptr::slice_from_raw_parts_mut(ptr, len) },
            old_cursor,
            stack: self,
            destructor,
        })
    }

    /// Pushes a slice onto the stack.
    ///
    /// # Errors
    ///
    /// Returns an error if the stack is full.
    pub fn push_slice<T: Sized>(&mut self, slice: &[T]) -> Option<Handle<[T], SIZE>> {
        let alignment = align_of::<T>();
        let size = size_of::<T>().checked_mul(slice.len())?;
        let buffer_start = unsafe { self.buffer.as_ptr().cast::<u8>().add(self.cursor) };
        let aligned_offset = buffer_start.align_offset(alignment);
        if aligned_offset == usize::MAX
            || self
                .cursor
                .checked_add(aligned_offset)
                .and_then(|start| start.checked_add(size))
                .filter(|end| *end <= SIZE)
                .is_none()
        {
            return None;
        }
        let ptr = unsafe {
            self.buffer
                .as_mut_ptr()
                .cast::<u8>()
                .add(self.cursor + aligned_offset)
                .cast::<T>()
        };
        unsafe { std::ptr::copy_nonoverlapping(slice.as_ptr(), ptr, slice.len()) };

        let old_cursor = self.cursor;
        self.cursor = self.cursor + aligned_offset + size;
        let destructor = if std::mem::needs_drop::<T>() {
            Self::slice_destructor::<T> as usize
        } else {
            0
        };
        Some(Handle {
            inst: unsafe { &mut *std::ptr::slice_from_raw_parts_mut(ptr, slice.len()) },
            old_cursor,
            stack: self,
            destructor,
        })
    }

    /// Allocates a new value on the stack.
    #[must_use]
    pub fn buffer_addr(&self) -> usize {
        self.buffer.as_ptr() as usize
    }

    fn slice_destructor<T: Sized>(addr: usize, len: usize) {
        let ptr = addr as *mut T;
        for i in 0..len {
            unsafe { std::ptr::drop_in_place::<T>(ptr.add(i)) };
        }
    }
}

impl<const SIZE: usize> Default for CompanionStack<SIZE> {
    fn default() -> Self {
        Self::new()
    }
}

/// A dynamically sized stack handle.
pub struct Handle<'s, T: ?Sized, const SIZE: usize = DEFAULT_STACK_SIZE> {
    inst: &'s mut T,
    old_cursor: usize,
    stack: &'s mut CompanionStack<SIZE>,
    destructor: usize,
}

impl<'s, T: ?Sized, const SIZE: usize> Handle<'s, T, SIZE> {
    /// Borrows itself as a mutable reference and the stack.
    pub fn split(&mut self) -> (&mut T, &mut CompanionStack<SIZE>) {
        (self.inst, self.stack)
    }

    /// Converts the handle to a different type.
    #[must_use]
    pub fn into_deref_target<U>(self) -> Handle<'s, U, SIZE>
    where
        T: DerefMut<Target = U>,
        U: ?Sized,
    {
        let converted: Handle<U, SIZE> = Handle {
            inst: self.inst,
            old_cursor: self.old_cursor,
            stack: self.stack,
            destructor: self.destructor,
        };
        let transmuted: Handle<'s, U, SIZE> = unsafe { transmute(converted) };
        forget(self);
        transmuted
    }
}

impl<T: ?Sized, const SIZE: usize> Deref for Handle<'_, T, SIZE> {
    type Target = T;
    fn deref(&self) -> &T {
        self.inst
    }
}

impl<T: ?Sized, const SIZE: usize> DerefMut for Handle<'_, T, SIZE> {
    fn deref_mut(&mut self) -> &mut T {
        self.inst
    }
}

impl<T: ?Sized, const SIZE: usize> Drop for Handle<'_, T, SIZE> {
    fn drop(&mut self) {
        self.stack.cursor = self.old_cursor;
        if self.destructor != 0 {
            let destructor: fn(usize, usize) = unsafe { transmute(self.destructor) };
            #[allow(clippy::ref_as_ptr)]
            let addr = (self.inst as *mut T).cast::<()>() as usize;
            let len = if size_of::<&T>() == size_of::<*mut ()>() {
                1
            } else {
                let ptr = std::ptr::addr_of!(self.inst).cast::<usize>();
                unsafe { *ptr.add(1) }
            };
            destructor(addr, len);
        }
    }
}

impl<'s, T, U, const SIZE: usize> From<Handle<'s, T, SIZE>>
    for Handle<'s, dyn DerefMut<Target = U>, SIZE>
where
    T: DerefMut<Target = U>,
    U: ?Sized,
{
    fn from(value: Handle<'s, T, SIZE>) -> Self {
        let converted: Handle<dyn DerefMut<Target = U>, SIZE> = Handle {
            inst: value.inst,
            old_cursor: value.old_cursor,
            stack: value.stack,
            destructor: value.destructor,
        };
        let transmuted: Self = unsafe { transmute(converted) };
        forget(value);
        transmuted
    }
}

impl<'s, U, const SIZE: usize> From<Handle<'s, dyn DerefMut<Target = U>, SIZE>>
    for Handle<'s, U, SIZE>
where
    U: ?Sized,
{
    fn from(value: Handle<'s, dyn DerefMut<Target = U>, SIZE>) -> Self {
        value.into_deref_target()
    }
}

impl<'s, T, U, const SIZE: usize> From<Handle<'s, T, SIZE>>
    for Handle<'s, dyn Future<Output = U>, SIZE>
where
    T: Future<Output = U>,
    U: ?Sized,
{
    fn from(value: Handle<'s, T, SIZE>) -> Self {
        let converted: Handle<dyn Future<Output = U>, SIZE> = Handle {
            inst: value.inst,
            old_cursor: value.old_cursor,
            stack: value.stack,
            destructor: value.destructor,
        };
        let transmuted: Self = unsafe { transmute(converted) };
        forget(value);
        transmuted
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_push_one() {
        static mut NUM_DROPPED: usize = 0;

        #[derive(Debug)]
        struct Data<const SIZE: usize>(MaybeUninit<[u8; SIZE]>);

        impl<const SIZE: usize> Drop for Data<SIZE> {
            fn drop(&mut self) {
                unsafe { NUM_DROPPED += 1 };
            }
        }

        let mut ds = CompanionStack::<1024>::new();
        let mut handle1 = ds
            .push_one(|| Ok::<_, ()>(Data::<512>(MaybeUninit::uninit())))
            .unwrap();
        let (_, ds1) = handle1.split();
        let mut handle2 = ds1
            .push_one(|| Ok::<_, ()>(Data::<400>(MaybeUninit::uninit())))
            .unwrap();
        let (_, ds2) = handle2.split();
        assert!(
            ds2.push_one(|| Ok::<_, ()>(Data::<400>(MaybeUninit::uninit())))
                .is_err()
        );
        drop(handle2);
        drop(handle1);
        assert_eq!(unsafe { NUM_DROPPED }, 2);
        assert_eq!(ds.cursor, 0);
    }

    #[test]
    fn test_push_many() {
        static mut NUM_DROPPED: usize = 0;

        #[derive(Debug)]
        struct Data(usize);

        impl Drop for Data {
            fn drop(&mut self) {
                assert_ne!(self.0, usize::MAX);
                self.0 = usize::MAX;
                unsafe { NUM_DROPPED += 1 };
            }
        }

        let mut ds = CompanionStack::<1024>::new();
        let handle = ds.push_many(|i| Ok::<_, ()>(Data(i)), 7).unwrap();
        assert_eq!(handle.len(), 7);
        assert!(!handle.iter().enumerate().any(|(i, data)| i != data.0));
        drop(handle);
        assert_eq!(unsafe { NUM_DROPPED }, 7);
        assert_eq!(ds.cursor, 0);
    }

    #[test]
    fn test_async() {
        static mut NUM_DROPPED: usize = 0;

        #[derive(Debug)]
        struct Data<const SIZE: usize>(MaybeUninit<[u8; SIZE]>);

        impl<const SIZE: usize> Drop for Data<SIZE> {
            fn drop(&mut self) {
                unsafe { NUM_DROPPED += 1 };
            }
        }

        let mut ds = CompanionStack::new();
        let data = Data::<400>(MaybeUninit::uninit());
        let handle: Handle<dyn Future<Output = ()>> = if ds.buffer_addr() % 2 == 0 {
            ds.push_one(|| {
                Ok::<_, ()>(async move {
                    let data_moved = data;
                    println!("HI {:?}", &data_moved);
                })
            })
            .unwrap()
            .into()
        } else {
            ds.push_one(|| {
                Ok::<_, ()>(async {
                    println!("HO");
                })
            })
            .unwrap()
            .into()
        };
        drop(handle);
        assert_eq!(unsafe { NUM_DROPPED }, 1);
    }

    #[test]
    fn test_deref() {
        static mut NUM_DROPPED: usize = 0;

        trait A {
            fn a(&self) -> usize;
        }

        #[derive(Debug)]
        struct Data1(usize);

        impl Deref for Data1 {
            type Target = dyn A;
            fn deref(&self) -> &Self::Target {
                self
            }
        }

        impl A for Data1 {
            fn a(&self) -> usize {
                self.0
            }
        }

        impl DerefMut for Data1 {
            fn deref_mut(&mut self) -> &mut Self::Target {
                self
            }
        }

        impl Drop for Data1 {
            fn drop(&mut self) {
                unsafe { NUM_DROPPED += 1 };
            }
        }

        #[derive(Debug)]
        struct Data2(String);

        impl A for Data2 {
            fn a(&self) -> usize {
                self.0.len()
            }
        }

        impl Deref for Data2 {
            type Target = dyn A;
            fn deref(&self) -> &Self::Target {
                self
            }
        }

        impl DerefMut for Data2 {
            fn deref_mut(&mut self) -> &mut Self::Target {
                self
            }
        }

        let mut ds = CompanionStack::<1024>::new();
        let mut handle_deref_mut: Handle<dyn DerefMut<Target = dyn A>, 1024> =
            if ds.buffer_addr() % 2 == 1 {
                ds.push_one(|| Ok::<_, ()>(Data1(11))).unwrap().into()
            } else {
                ds.push_one(|| Ok::<_, ()>(Data2("HELLO".to_owned())))
                    .unwrap()
                    .into()
            };
        assert_eq!(handle_deref_mut.a(), 5);

        let (_, ds) = handle_deref_mut.split();

        let handle_dyn: Handle<dyn A, 1024> = if ds.buffer_addr() % 2 == 0 {
            ds.push_one(|| Ok::<_, ()>(Data1(11)))
                .unwrap()
                .into_deref_target()
        } else {
            ds.push_one(|| Ok::<_, ()>(Data2("HELLO".to_owned())))
                .unwrap()
                .into_deref_target()
        };
        assert_eq!(handle_dyn.a(), 11);

        drop(handle_dyn);
        drop(handle_deref_mut);

        assert_eq!(unsafe { NUM_DROPPED }, 1);
    }

    #[test]
    fn test_slice() {
        static mut NUM_DROPPED: usize = 0;

        #[derive(Debug, Default)]
        struct Data(usize);

        impl Drop for Data {
            fn drop(&mut self) {
                assert_ne!(self.0, usize::MAX);
                self.0 = usize::MAX;
                unsafe { NUM_DROPPED += 1 };
            }
        }

        let mut ds = CompanionStack::<1024>::new();
        let mut handle_slice: Handle<[Data], 1024> = if ds.buffer_addr() % 2 == 0 {
            ds.push_slice(&[Data(10), Data(11)]).unwrap()
        } else {
            ds.push_slice(&[Data(12), Data(13), Data(14)]).unwrap()
        };
        handle_slice[0].0 = 15;
        assert_eq!(handle_slice.len(), 2);
        assert_eq!(handle_slice[0].0, 15);
        assert_eq!(handle_slice[1].0, 11);

        drop(handle_slice);

        assert_eq!(unsafe { NUM_DROPPED }, 4);
    }
}
