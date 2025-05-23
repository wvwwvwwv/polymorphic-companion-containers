// #![deny(missing_docs, warnings, clippy::all, clippy::pedantic)]
#![doc = include_str!("../README.md")]

use std::mem::{MaybeUninit, align_of};
use std::ptr::drop_in_place;

const DEFAULT_STACK_SIZE: usize = 16384;

pub struct DS<const SIZE: usize = DEFAULT_STACK_SIZE> {
    buffer: MaybeUninit<[u8; SIZE]>,
    cursor: usize,
}

impl<const SIZE: usize> DS<SIZE> {
    pub fn new() -> Self {
        Self {
            buffer: MaybeUninit::uninit(),
            cursor: 0,
        }
    }
    pub fn alloc_sized<'s, T: Sized, C: FnOnce() -> T>(
        &'s mut self,
        constructor: C,
    ) -> Result<Handle<'s, T, SIZE>, ()> {
        let alignment = align_of::<T>();
        let size = size_of::<T>();
        let buffer_start = unsafe { self.buffer.as_ptr().cast::<u8>().add(self.cursor) };
        let aligned_offset = buffer_start.align_offset(alignment);
        if aligned_offset == usize::MAX {
            return Err(());
        } else if self
            .cursor
            .checked_add(aligned_offset)
            .and_then(|start| start.checked_add(size))
            .filter(|end| *end <= SIZE)
            .is_none()
        {
            return Err(());
        }
        let ptr = unsafe {
            self.buffer
                .as_mut_ptr()
                .cast::<u8>()
                .add(self.cursor + aligned_offset)
                .cast::<T>()
        };
        unsafe { ptr.write(constructor()) };

        let old_cursor = self.cursor;
        self.cursor = self.cursor + aligned_offset + size;
        let destructor = if std::mem::needs_drop::<T>() {
            drop_in_place::<T> as usize
        } else {
            0
        };
        Ok(Handle {
            inst: unsafe { &mut *ptr },
            addr: ptr as usize,
            old_cursor,
            stack: self,
            destructor,
        })
    }

    pub fn buffer_addr(&self) -> usize {
        self.buffer.as_ptr() as usize
    }
}

pub struct Handle<'s, T: ?Sized, const SIZE: usize> {
    inst: &'s mut T,
    addr: usize,
    old_cursor: usize,
    stack: &'s mut DS<SIZE>,
    destructor: usize,
}

impl<'s, T: ?Sized, const SIZE: usize> Handle<'s, T, SIZE> {
    pub fn split(&mut self) -> (&mut T, &mut DS<SIZE>) {
        (self.inst, self.stack)
    }
}

impl<'s, T: ?Sized, const SIZE: usize> Drop for Handle<'s, T, SIZE> {
    fn drop(&mut self) {
        self.stack.cursor = self.old_cursor;
        let destructor: fn(usize) = unsafe { std::mem::transmute::<usize, _>(self.destructor) };
        destructor(self.addr);
    }
}

mod tests {
    use super::*;

    #[test]
    fn test_handle_drop() {
        static mut NUM_DROPPED: usize = 0;

        #[derive(Debug)]
        struct Data<const SIZE: usize> {
            value: MaybeUninit<[u8; SIZE]>,
        }

        impl<const SIZE: usize> Drop for Data<SIZE> {
            fn drop(&mut self) {
                unsafe { NUM_DROPPED += 1 };
            }
        }

        let mut ds = DS::<1024>::new();
        let mut handle1 = ds
            .alloc_sized(|| Data::<512> {
                value: MaybeUninit::uninit(),
            })
            .unwrap();
        let (data1, ds1) = handle1.split();
        let mut handle2 = ds1
            .alloc_sized(|| Data::<400> {
                value: MaybeUninit::uninit(),
            })
            .unwrap();
        let (data2, ds2) = handle2.split();
        assert!(
            ds2.alloc_sized(|| Data::<400> {
                value: MaybeUninit::uninit(),
            })
            .is_err()
        );
        drop(handle2);
        drop(handle1);
        assert_eq!(unsafe { NUM_DROPPED }, 2);
        assert_eq!(ds.cursor, 0);
    }
}
