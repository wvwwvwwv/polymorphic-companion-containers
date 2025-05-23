#![deny(missing_docs, warnings, clippy::all, clippy::pedantic)]
#![doc = include_str!("../README.md")]

use std::mem::{align_of, MaybeUninit};

const DEFAULT_STACK_SIZE: usize = 16384;

pub struct DS<const SIZE: usize = DEFAULT_STACK_SIZE> {
    buffer: MaybeUninit<[u8; SIZE]>,
}

impl<const SIZE: usize> DS<SIZE> {
    pub fn new() -> Self {
        Self { buffer: MaybeUninit::uninit() }
    }
    pub fn alloc_unsized<T: !Sized, C: FnOnce() -> T>(&mut self, constructor: C) -> Result<DynHandle<'_, T>, ()> {
        Box::new(constructor());
        let align = align_of::<T>();
        if self.buffer.as_ptr().is_null() {
            Err(())
        } else {
            Ok(DynHandle::new(self.buffer.as_mut_ptr() as *mut T))
        }
    }
}

pub struct DynHandle<'s, T: !Sized, const SIZE: usize> {}

impl<'s, T: !Sized> DynHandle<'s, T> {
    pub fn new(value: &'s T) -> Self {
        Self {}
    }

    pub fn use(&mut self) -> (&mut T, &mut DS<SIZE>) {
        None
    }
}

pub struct Handle<'s, T: Sized, const SIZE: usize> {}

impl<'s, T: Sized> Handle<'s, T> {
    pub fn new(value: T) -> Self {
        Self {}
    }
}
