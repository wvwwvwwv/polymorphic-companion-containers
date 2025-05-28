//! [`CompanionStack`] is a last-in-first-out data structure that provides a safe and efficient way
//! to allocate and deallocate values on the stack at runtime.

use super::exit_guard::ExitGuard;
use core::borrow::{Borrow, BorrowMut};
use core::mem::{MaybeUninit, align_of, forget, needs_drop, transmute};
use core::ops::{Deref, DerefMut};
use core::ptr::{copy_nonoverlapping, drop_in_place, slice_from_raw_parts_mut, write};

/// [`CompanionStack`] is used to allocate and deallocate values on the stack when the sizes of the
/// values are not necessarily known at compile time.
#[derive(Debug)]
pub struct CompanionStack<const SIZE: usize = DEFAULT_STACK_SIZE> {
    /// The fixed size buffer.
    buffer: MaybeUninit<[u8; SIZE]>,
    /// The current position on the buffer.
    cursor: usize,
}

/// The default size of [`CompanionStack`].
pub const DEFAULT_STACK_SIZE: usize = size_of::<usize>() * 4095;

/// [`RefMut`] mutably borrows both the allocated value and the stack on which the value is located.
///
/// The lifetime of any newer values pushed into the stack is guaranteed to be shorter than the
/// lifetime of the [`RefMut`] by mutably borrowing the stack.
#[derive(Debug)]
pub struct RefMut<'s, T: ?Sized, const SIZE: usize = DEFAULT_STACK_SIZE> {
    /// The mutable reference to the allocated value.
    value_mut: &'s mut T,
    /// The mutable reference to the stack on which the value is located.
    stack_mut: &'s mut CompanionStack<SIZE>,
    /// The old cursor position before the value was allocated.
    old_cursor: usize,
}

/// [`CompanionStack`] raises an [`Error`] if the stack is full or fails to construct a value.
#[derive(Debug)]
pub enum Error<E> {
    /// Failed to construct a value.
    ConstructionFailed(E),
    /// The stack is full.
    Full,
}

/// [`AlignedSize`] is the align offset and size of a value on the stack.
///
/// [`AlignedSize::align_offset`] plus [`AlignedSize::size`] is the total size of memory in bytes
/// needed to store the value on the stack.
#[derive(Clone, Copy, Debug, Default)]
pub struct AlignedSize {
    /// The align offset is the number of bytes to skip before the value is aligned on the stack.
    pub align_offset: usize,
    /// The size of the value in bytes.
    pub size: usize,
}

/// [`Allocation`] represents an allocated memory chunk for a value on the stack.
#[derive(Debug)]
struct Allocation<T: Sized> {
    /// The start address of the allocated value.
    ptr: *mut T,
    /// The upper bound of the allocated memory chunk.
    upper_bound: usize,
}

impl<const SIZE: usize> CompanionStack<SIZE> {
    /// Creates a new [`CompanionStack`].
    ///
    /// # Examples
    ///
    /// ```
    /// use pcc::CompanionStack;
    ///
    /// let mut dyn_stack = CompanionStack::<65536>::new();
    /// ```
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self {
            buffer: MaybeUninit::uninit(),
            cursor: 0,
        }
    }

    /// Returns `true` if the [`CompanionStack`] is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # if cfg!(miri) {
    /// #     return;
    /// # }
    /// use pcc::CompanionStack;
    ///
    /// let mut dyn_stack = CompanionStack::<64>::new();
    /// assert!(dyn_stack.is_empty());
    ///
    /// let mut three = dyn_stack.push_one(|| Ok::<_, ()>(3)).unwrap();
    /// let (three, dyn_stack) = three.retrieve_stack();
    /// assert_eq!(*three, 3);
    /// assert!(!dyn_stack.is_empty());
    /// ```
    #[inline]
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.cursor == 0
    }

    /// Returns the current position of the cursor.
    ///
    /// Each [`CompanionStack`] has a cursor that points to the next available byte on the buffer,
    /// and the method returns the current position of the cursor. `SIZE - pos` is the remaining
    /// bytes available for use.
    ///
    /// # Examples
    ///
    /// ```
    /// # if cfg!(miri) {
    /// #     return;
    /// # }
    /// use pcc::CompanionStack;
    ///
    /// #[repr(align(64))]
    /// struct A(u8);
    ///
    /// let mut dyn_stack = CompanionStack::<256>::new();
    /// assert_eq!(dyn_stack.pos(), 0);
    ///
    /// let mut three = dyn_stack.push_one(|| Ok::<_, ()>(A(3))).unwrap();
    /// let (three, dyn_stack) = three.retrieve_stack();
    /// assert_eq!(three.0, 3);
    /// let alignment_offset = if dyn_stack.buffer_addr() % 64 == 0 {
    ///     0
    /// }  else {
    ///     64 - dyn_stack.buffer_addr() % 64
    /// };
    /// assert_eq!(dyn_stack.pos(), alignment_offset + 64);
    /// ```
    #[inline]
    #[must_use]
    pub const fn pos(&self) -> usize {
        self.cursor
    }

    /// Calculates the aligned size in bytes required for `len` number of values of the given type
    /// on the stack.
    ///
    /// Returns `None` if the requested size is too large to fit on the stack, otherwise returns
    /// an [`AlignedSize`] representing the aligned size.
    ///
    /// # Examples
    ///
    /// ```
    /// use pcc::CompanionStack;
    ///
    /// let dyn_stack = CompanionStack::<64>::new();
    ///
    /// let aligned_size_i32 = dyn_stack.aligned_size::<i32>(3).unwrap();
    /// assert!(aligned_size_i32.align_offset < 4);
    /// assert_eq!(aligned_size_i32.size, 12);
    ///
    /// assert!(dyn_stack.aligned_size::<[u64; 32]>(4).is_none());
    /// ```
    #[inline]
    #[must_use]
    pub fn aligned_size<T: Sized>(&self, len: usize) -> Option<AlignedSize> {
        let requested_size = size_of::<T>().checked_mul(len)?;
        let buffer_start = unsafe { self.buffer.as_ptr().cast::<u8>().add(self.cursor) };
        let align_offset = buffer_start.align_offset(align_of::<T>());
        if align_offset == usize::MAX {
            return None;
        }
        self.cursor
            .checked_add(align_offset)
            .and_then(|start| start.checked_add(requested_size))
            .filter(|end| *end <= SIZE)
            .map(|_| AlignedSize {
                align_offset,
                size: requested_size,
            })
    }

    /// Pushes a single value.
    ///
    /// # Errors
    ///
    /// Returns [`Error::Full`] if the stack is full, or an [`Error::ConstructionFailed`] if the
    /// constructor fails.
    ///
    /// # Examples
    ///
    /// ```
    /// # if cfg!(miri) {
    /// #     return;
    /// # }
    /// use pcc::CompanionStack;
    /// use pcc::companion_stack::Error;
    ///
    /// let mut dyn_stack = CompanionStack::<16>::new();
    /// let mut thirty_seven = dyn_stack.push_one(|| Ok::<_, ()>(37_usize)).unwrap();
    /// assert_eq!(*thirty_seven, 37);
    ///
    /// let (_, dyn_stack) = thirty_seven.retrieve_stack();
    ///
    /// let error = dyn_stack.push_one(|| Err::<(), String>("ERROR".to_string())).unwrap_err();
    /// match error {
    ///     Error::Full => panic!("Stack should not be full"),
    ///     Error::ConstructionFailed(e) => assert_eq!(e, "ERROR"),
    /// }
    ///
    /// let error = dyn_stack.push_one(|| Ok::<_, ()>([0; 16])).unwrap_err();
    /// match error {
    ///     Error::Full => assert_eq!(dyn_stack.pos(), size_of::<usize>()),
    ///     Error::ConstructionFailed(_) => panic!("Construction should not fail"),
    /// }
    /// ```
    #[inline]
    pub fn push_one<E, T: Sized, C: FnOnce() -> Result<T, E>>(
        &mut self,
        constructor: C,
    ) -> Result<RefMut<T, SIZE>, Error<E>> {
        let allocated = self.allocate::<T>(1).ok_or(Error::Full)?;
        let val = constructor().map_err(|e| Error::ConstructionFailed(e))?;

        let value_mut = unsafe {
            allocated.ptr.write(val);
            &mut *allocated.ptr
        };

        let old_cursor = self.cursor;
        self.cursor = allocated.upper_bound;

        Ok(RefMut {
            value_mut,
            stack_mut: self,
            old_cursor,
        })
    }

    /// Pushes multiple values.
    ///
    /// # Errors
    ///
    /// Returns [`Error::Full`] if the [`CompanionStack`] is full.
    ///
    /// # Examples
    ///
    /// ```
    /// # if cfg!(miri) {
    /// #     return;
    /// # }
    /// use pcc::CompanionStack;
    /// use pcc::companion_stack::Error;
    ///
    /// let mut dyn_stack = CompanionStack::<256>::new();
    /// let number = "37";
    /// let mut thirty_seven_plus = if number == "37" {
    ///     dyn_stack.push_many(|i| Ok::<_, ()>(37_u64 + i as u64), 17).unwrap()
    /// } else {
    ///     dyn_stack.push_many(|i| Ok::<_, ()>(47_u64 + i as u64), 67).unwrap()
    /// };
    /// assert_eq!(thirty_seven_plus.len(), 17);
    /// assert!(!thirty_seven_plus.iter().enumerate().any(|(i, n)| *n != 37_u64 + i as u64));
    ///
    /// let (_, dyn_stack) = thirty_seven_plus.retrieve_stack();
    ///
    /// let error = dyn_stack.push_many(|_| Err::<(), String>("ERROR".to_string()), 2).unwrap_err();
    /// match error {
    ///     Error::Full => panic!("Stack should not be full"),
    ///     Error::ConstructionFailed(e) => assert_eq!(e, "ERROR"),
    /// }
    /// ```
    #[inline]
    pub fn push_many<E, T: Sized, C: FnMut(usize) -> Result<T, E>>(
        &mut self,
        mut constructor: C,
        len: usize,
    ) -> Result<RefMut<[T], SIZE>, Error<E>> {
        let allocated = self.allocate::<T>(len).ok_or(Error::Full)?;
        for i in 0..len {
            let mut exit_guard = ExitGuard::new(needs_drop::<T>(), |failed| {
                // Drop all previously constructed elements if construction fails.
                if failed {
                    for j in 0..i {
                        unsafe { drop_in_place::<T>(allocated.ptr.add(j)) };
                    }
                }
            });
            let val = constructor(i).map_err(|e| Error::ConstructionFailed(e))?;
            unsafe {
                write(allocated.ptr.add(i), val);
            }
            *exit_guard = false;
        }

        let old_cursor = self.cursor;
        self.cursor = allocated.upper_bound;

        Ok(RefMut {
            value_mut: unsafe { &mut *slice_from_raw_parts_mut(allocated.ptr, len) },
            stack_mut: self,
            old_cursor,
        })
    }

    /// Pushes a slice.
    ///
    /// The supplied slice is copied onto the stack, and a [`RefMut`] to the copy is returned.
    /// Returns `None` if the [`CompanionStack`] is full.
    ///
    /// # Examples
    ///
    /// ```
    /// # if cfg!(miri) {
    /// #     return;
    /// # }
    /// use pcc::CompanionStack;
    ///
    /// let mut dyn_stack = CompanionStack::<64>::new();
    /// let mut seven_plus = dyn_stack.push_slice(&[0_u64; 7]).unwrap();
    /// assert_eq!(seven_plus.len(), 7);
    ///
    /// seven_plus.iter_mut().enumerate().for_each(|(i, n)| *n += 37 + i as u64);
    /// assert!(!seven_plus.iter().enumerate().any(|(i, n)| *n != 37 + i as u64));
    ///
    /// let (_, dyn_stack) = seven_plus.retrieve_stack();
    ///
    /// assert!(dyn_stack.push_slice(&[0_u64; 17]).is_none());
    /// ```
    #[inline]
    pub fn push_slice<T: Sized>(&mut self, slice: &[T]) -> Option<RefMut<[T], SIZE>> {
        let allocated = self.allocate::<T>(slice.len())?;
        let value_mut = unsafe {
            copy_nonoverlapping(slice.as_ptr(), allocated.ptr, slice.len());
            &mut *slice_from_raw_parts_mut(allocated.ptr, slice.len())
        };

        let old_cursor = self.cursor;
        self.cursor = allocated.upper_bound;

        Some(RefMut {
            value_mut,
            stack_mut: self,
            old_cursor,
        })
    }

    /// Returns the start address of the buffer.
    ///
    /// Relying on [`Self::pos`] is insufficient to determine whether the buffer can accommodate
    /// desired data, because the start address of the available buffer may not be aligned to the
    /// required alignment.
    ///
    /// # Examples
    ///
    /// ```
    /// # if cfg!(miri) {
    /// #     return;
    /// # }
    /// use pcc::CompanionStack;
    ///
    /// let mut dyn_stack = CompanionStack::default();
    /// assert_ne!(dyn_stack.buffer_addr(), 0);
    /// ```
    #[inline]
    #[must_use]
    pub fn buffer_addr(&self) -> usize {
        self.buffer.as_ptr() as usize
    }

    /// Allocates a chunk of memory for the given type.
    fn allocate<T: Sized>(&self, len: usize) -> Option<Allocation<T>> {
        let align_offset_and_size = self.aligned_size::<T>(len)?;
        let ptr = unsafe {
            self.buffer
                .as_ptr()
                .cast::<u8>()
                .add(self.cursor + align_offset_and_size.align_offset)
                .cast::<T>()
                .cast_mut()
        };
        let upper_bound =
            self.cursor + align_offset_and_size.align_offset + align_offset_and_size.size;
        Some(Allocation { ptr, upper_bound })
    }
}

impl Default for CompanionStack<DEFAULT_STACK_SIZE> {
    /// Creates a new [`CompanionStack`] of the default size.
    ///
    /// The default size is defined by [`DEFAULT_STACK_SIZE`].
    ///
    /// # Examples
    ///
    /// ```
    /// use pcc::CompanionStack;
    ///
    /// let mut dyn_stack = CompanionStack::default();
    /// ```
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<'s, T: ?Sized, const SIZE: usize> RefMut<'s, T, SIZE> {
    /// Retrieves the mutable [`CompanionStack`] reference from the [`RefMut`] along with the
    /// mutable reference to the value.
    ///
    /// The lifetime of the [`CompanionStack`] reference is shorter then `self`, forcing any newly
    /// pushed values to be dropped before `self` is dropped.
    ///
    /// # Examples
    ///
    /// ```
    /// # if cfg!(miri) {
    /// #     return;
    /// # }
    /// use pcc::CompanionStack;
    ///
    /// let mut dyn_stack = CompanionStack::<16>::new();
    /// let mut seven = dyn_stack.push_one(|| Ok::<_, ()>(7_usize)).unwrap();
    /// assert_eq!(*seven, 7);
    ///
    /// let (seven, dyn_stack) = seven.retrieve_stack();
    /// assert_eq!(*seven, 7);
    ///
    /// let eleven = dyn_stack.push_one(|| Ok::<_, ()>(11_u16)).unwrap();
    /// assert_eq!(*eleven, 11);
    /// ```
    #[inline]
    pub fn retrieve_stack(&mut self) -> (&mut T, &mut CompanionStack<SIZE>) {
        (self.value_mut, self.stack_mut)
    }

    /// Converts the [`RefMut`] into a [`RefMut`] of its dereferencing target.
    ///
    /// # Examples
    ///
    /// ```
    /// # if cfg!(miri) {
    /// #     return;
    /// # }
    /// use pcc::CompanionStack;
    /// use pcc::companion_stack::RefMut;
    /// use std::ops::{Deref, DerefMut};
    ///
    /// trait A {
    ///     fn a(&self) -> usize;
    /// }
    ///
    /// struct B(usize);
    /// impl A for B {
    ///     fn a(&self) -> usize {
    ///         self.0
    ///     }
    /// }
    /// impl Deref for B {
    ///     type Target = dyn A;
    ///     fn deref(&self) -> &Self::Target {
    ///         self
    ///     }
    /// }
    /// impl DerefMut for B {
    ///     fn deref_mut(&mut self) -> &mut Self::Target {
    ///         self
    ///     }
    /// }
    ///
    /// struct C(String);
    /// impl A for C {
    ///     fn a(&self) -> usize {
    ///         self.0.len()
    ///     }
    /// }
    /// impl Deref for C {
    ///     type Target = dyn A;
    ///     fn deref(&self) -> &Self::Target {
    ///         self
    ///     }
    /// }
    /// impl DerefMut for C {
    ///     fn deref_mut(&mut self) -> &mut Self::Target {
    ///         self
    ///     }
    /// }
    ///
    /// let b_or_c = 'b';
    ///
    /// let mut dyn_stack = CompanionStack::default();
    /// let ref_mut_dyn: RefMut<dyn A> = if b_or_c == 'b' {
    ///     dyn_stack
    ///         .push_one(|| Ok::<_, ()>(B(11)))
    ///         .unwrap()
    ///         .into_deref_target()
    /// } else {
    ///     dyn_stack
    ///         .push_one(|| Ok::<_, ()>(C("HELLO".to_owned())))
    ///         .unwrap()
    ///         .into_deref_target()
    /// };
    /// assert_eq!(ref_mut_dyn.a(), 11);
    /// ```
    #[inline]
    #[must_use]
    pub fn into_deref_target<U>(self) -> RefMut<'s, U, SIZE>
    where
        T: DerefMut<Target = U>,
        U: ?Sized,
    {
        let converted: RefMut<U, SIZE> = RefMut {
            value_mut: self.value_mut,
            stack_mut: self.stack_mut,
            old_cursor: self.old_cursor,
        };
        let transmuted: RefMut<'s, U, SIZE> = unsafe { transmute(converted) };
        forget(self);
        transmuted
    }
}

impl<T: ?Sized, const SIZE: usize> Borrow<T> for RefMut<'_, T, SIZE> {
    #[inline]
    fn borrow(&self) -> &T {
        self.value_mut
    }
}

impl<T: ?Sized, const SIZE: usize> BorrowMut<T> for RefMut<'_, T, SIZE> {
    #[inline]
    fn borrow_mut(&mut self) -> &mut T {
        self.value_mut
    }
}

impl<T: ?Sized, const SIZE: usize> AsRef<T> for RefMut<'_, T, SIZE> {
    #[inline]
    fn as_ref(&self) -> &T {
        self.value_mut
    }
}

impl<T: ?Sized, const SIZE: usize> AsMut<T> for RefMut<'_, T, SIZE> {
    #[inline]
    fn as_mut(&mut self) -> &mut T {
        self.value_mut
    }
}

#[cfg(feature = "nightly")]
impl<'s, T: ?Sized + core::marker::Unsize<U>, U: ?Sized, const SIZE: usize>
    core::ops::CoerceUnsized<RefMut<'s, U, SIZE>> for RefMut<'s, T, SIZE>
{
}

impl<T: ?Sized, const SIZE: usize> Deref for RefMut<'_, T, SIZE> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &T {
        self.value_mut
    }
}

impl<T: ?Sized, const SIZE: usize> DerefMut for RefMut<'_, T, SIZE> {
    #[inline]
    fn deref_mut(&mut self) -> &mut T {
        self.value_mut
    }
}

impl<T: ?Sized, const SIZE: usize> Drop for RefMut<'_, T, SIZE> {
    #[inline]
    fn drop(&mut self) {
        self.stack_mut.cursor = self.old_cursor;
        unsafe {
            drop_in_place(self.value_mut);
        }
    }
}

impl<'s, T, U, const SIZE: usize> From<RefMut<'s, T, SIZE>>
    for RefMut<'s, dyn DerefMut<Target = U>, SIZE>
where
    T: DerefMut<Target = U>,
    U: ?Sized,
{
    #[inline]
    fn from(value: RefMut<'s, T, SIZE>) -> Self {
        let converted: RefMut<dyn DerefMut<Target = U>, SIZE> = RefMut {
            value_mut: value.value_mut,
            stack_mut: value.stack_mut,
            old_cursor: value.old_cursor,
        };
        let transmuted: Self = unsafe { transmute(converted) };
        forget(value);
        transmuted
    }
}

impl<'s, U, const SIZE: usize> From<RefMut<'s, dyn DerefMut<Target = U>, SIZE>>
    for RefMut<'s, U, SIZE>
where
    U: ?Sized,
{
    fn from(value: RefMut<'s, dyn DerefMut<Target = U>, SIZE>) -> Self {
        value.into_deref_target()
    }
}

impl<'s, T: Sized, const SIZE: usize, const LEN: usize> From<RefMut<'s, [T; LEN], SIZE>>
    for RefMut<'s, [T], SIZE>
{
    #[inline]
    fn from(value: RefMut<'s, [T; LEN], SIZE>) -> Self {
        let converted: RefMut<[T], SIZE> = RefMut {
            value_mut: value.value_mut,
            stack_mut: value.stack_mut,
            old_cursor: value.old_cursor,
        };
        let transmuted: Self = unsafe { transmute(converted) };
        forget(value);
        transmuted
    }
}

impl<'s, T, U, const SIZE: usize> From<RefMut<'s, T, SIZE>>
    for RefMut<'s, dyn Future<Output = U>, SIZE>
where
    T: Future<Output = U>,
    U: ?Sized,
{
    #[inline]
    fn from(value: RefMut<'s, T, SIZE>) -> Self {
        let converted: RefMut<dyn Future<Output = U>, SIZE> = RefMut {
            value_mut: value.value_mut,
            stack_mut: value.stack_mut,
            old_cursor: value.old_cursor,
        };
        let transmuted: Self = unsafe { transmute(converted) };
        forget(value);
        transmuted
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::ptr::addr_of;
    use core::sync::atomic::AtomicUsize;
    use core::sync::atomic::Ordering::Relaxed;

    #[cfg_attr(miri, ignore)]
    #[test]
    fn test_push_one() {
        static NUM_DROPPED: AtomicUsize = AtomicUsize::new(0);

        #[derive(Debug)]
        struct Data<const SIZE: usize>(MaybeUninit<[u8; SIZE]>);

        impl<const SIZE: usize> Drop for Data<SIZE> {
            fn drop(&mut self) {
                NUM_DROPPED.fetch_add(1, Relaxed);
            }
        }

        let mut dyn_stack = CompanionStack::<1024>::new();
        let mut ref_mut_1 = dyn_stack
            .push_one(|| Ok::<_, ()>(Data::<512>(MaybeUninit::uninit())))
            .unwrap();
        let (_, dyn_stack1) = ref_mut_1.retrieve_stack();
        let mut ref_mut_2 = dyn_stack1
            .push_one(|| Ok::<_, ()>(Data::<400>(MaybeUninit::uninit())))
            .unwrap();
        let (_, dyn_stack2) = ref_mut_2.retrieve_stack();
        assert!(
            dyn_stack2
                .push_one(|| Ok::<_, ()>(Data::<400>(MaybeUninit::uninit())))
                .is_err()
        );
        drop(ref_mut_2);
        drop(ref_mut_1);
        assert_eq!(NUM_DROPPED.load(Relaxed), 2);
        assert_eq!(dyn_stack.cursor, 0);
    }

    #[cfg_attr(miri, ignore)]
    #[test]
    fn test_push_many() {
        static NUM_DROPPED: AtomicUsize = AtomicUsize::new(0);

        #[derive(Debug)]
        struct Data(usize);

        impl Drop for Data {
            fn drop(&mut self) {
                assert_ne!(self.0, usize::MAX);
                self.0 = usize::MAX;
                NUM_DROPPED.fetch_add(1, Relaxed);
            }
        }

        let mut dyn_stack = CompanionStack::<1024>::new();
        let mut ref_mut_1 = dyn_stack.push_many(|i| Ok::<_, ()>(Data(i)), 7).unwrap();
        let (array1, dyn_stack) = ref_mut_1.retrieve_stack();
        let ref_mut_2 = dyn_stack
            .push_one(|| Ok::<_, ()>([Data(0), Data(1), Data(2)]))
            .unwrap();
        assert_eq!(array1.len(), 7);
        assert_eq!(ref_mut_2.len(), 3);
        assert!(!array1.iter().enumerate().any(|(i, data)| i != data.0));

        let ref_mut_3: RefMut<[Data], 1024> = ref_mut_2.into();
        assert!(!ref_mut_3.iter().enumerate().any(|(i, data)| i != data.0));
        drop(ref_mut_3);
        assert_eq!(NUM_DROPPED.load(Relaxed), 3);

        drop(ref_mut_1);
        assert_eq!(NUM_DROPPED.load(Relaxed), 10);
    }

    #[cfg_attr(miri, ignore)]
    #[test]
    fn test_async() {
        static NUM_DROPPED: AtomicUsize = AtomicUsize::new(0);

        #[derive(Debug)]
        struct Data<const SIZE: usize>(MaybeUninit<[u8; SIZE]>);

        impl<const SIZE: usize> Drop for Data<SIZE> {
            fn drop(&mut self) {
                NUM_DROPPED.fetch_add(1, Relaxed);
            }
        }

        let mut dyn_stack = CompanionStack::new();
        let data = Data::<400>(MaybeUninit::uninit());
        let ref_mut: RefMut<dyn Future<Output = usize>> = if dyn_stack.buffer_addr() % 2 == 0 {
            dyn_stack
                .push_one(|| {
                    Ok::<_, ()>(async move {
                        let data_moved = data;
                        let result = addr_of!(data_moved) as usize;
                        drop(data_moved);
                        result
                    })
                })
                .unwrap()
                .into()
        } else {
            dyn_stack
                .push_one(|| Ok::<_, ()>(async { addr_of!(data) as usize }))
                .unwrap()
                .into()
        };
        drop(ref_mut);
        assert_eq!(NUM_DROPPED.load(Relaxed), 1);
    }

    #[cfg_attr(miri, ignore)]
    #[test]
    fn test_deref() {
        static NUM_DROPPED: AtomicUsize = AtomicUsize::new(0);

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
                NUM_DROPPED.fetch_add(1, Relaxed);
            }
        }

        #[derive(Debug)]
        struct Data2([u8; 4]);

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

        let mut dyn_stack = CompanionStack::<1024>::new();
        let mut ref_mut_deref_mut: RefMut<dyn DerefMut<Target = dyn A>, 1024> =
            if dyn_stack.buffer_addr() % 2 == 1 {
                dyn_stack
                    .push_one(|| Ok::<_, ()>(Data1(11)))
                    .unwrap()
                    .into()
            } else {
                dyn_stack
                    .push_one(|| Ok::<_, ()>(Data2([1, 2, 3, 4])))
                    .unwrap()
                    .into()
            };
        assert_eq!(ref_mut_deref_mut.a(), 4);

        let (_, dyn_stack) = ref_mut_deref_mut.retrieve_stack();

        let ref_mut_dyn: RefMut<dyn A, 1024> = if dyn_stack.buffer_addr() % 2 == 0 {
            dyn_stack
                .push_one(|| Ok::<_, ()>(Data1(11)))
                .unwrap()
                .into_deref_target()
        } else {
            dyn_stack
                .push_one(|| Ok::<_, ()>(Data2([1, 2, 3, 4])))
                .unwrap()
                .into_deref_target()
        };
        assert_eq!(ref_mut_dyn.a(), 11);

        drop(ref_mut_dyn);
        drop(ref_mut_deref_mut);

        assert_eq!(NUM_DROPPED.load(Relaxed), 1);
    }

    #[cfg_attr(miri, ignore)]
    #[test]
    fn test_slice() {
        static NUM_DROPPED: AtomicUsize = AtomicUsize::new(0);

        #[derive(Debug, Default)]
        struct Data(usize);

        impl Drop for Data {
            fn drop(&mut self) {
                assert_ne!(self.0, usize::MAX);
                self.0 = usize::MAX;
                NUM_DROPPED.fetch_add(1, Relaxed);
            }
        }

        let mut dyn_stack = CompanionStack::<1024>::new();
        let mut ref_mut_slice: RefMut<[Data], 1024> = if dyn_stack.buffer_addr() % 2 == 0 {
            dyn_stack.push_slice(&[Data(10), Data(11)]).unwrap()
        } else {
            dyn_stack
                .push_slice(&[Data(12), Data(13), Data(14)])
                .unwrap()
        };
        ref_mut_slice[0].0 = 15;
        assert_eq!(ref_mut_slice.len(), 2);
        assert_eq!(ref_mut_slice[0].0, 15);
        assert_eq!(ref_mut_slice[1].0, 11);

        drop(ref_mut_slice);

        assert_eq!(NUM_DROPPED.load(Relaxed), 4);
    }

    #[cfg(feature = "nightly")]
    #[cfg_attr(miri, ignore)]
    #[test]
    fn test_fn_mut_nightly() {
        static NUM_INVOKED: AtomicUsize = AtomicUsize::new(0);

        let mut dyn_stack = CompanionStack::default();
        let mut ref_mut_fn_mut: RefMut<dyn FnMut(usize) -> usize> = dyn_stack
            .push_one(|| Ok::<_, ()>(|x| x + NUM_INVOKED.fetch_add(1, Relaxed) + 1))
            .unwrap();
        assert_eq!(ref_mut_fn_mut(10), 11);
        assert_eq!(ref_mut_fn_mut(2), 4);
    }

    #[cfg(feature = "nightly")]
    #[cfg_attr(miri, ignore)]
    #[test]
    fn test_deref_nightly() {
        static NUM_DROPPED: AtomicUsize = AtomicUsize::new(0);

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

        impl Drop for Data1 {
            fn drop(&mut self) {
                NUM_DROPPED.fetch_add(1, Relaxed);
            }
        }

        #[derive(Debug)]
        struct Data2([u8; 4]);

        impl A for Data2 {
            fn a(&self) -> usize {
                self.0.len()
            }
        }

        impl Drop for Data2 {
            fn drop(&mut self) {
                NUM_DROPPED.fetch_add(1, Relaxed);
            }
        }

        let mut dyn_stack = CompanionStack::<1024>::new();
        let ref_mut: RefMut<dyn A, 1024> = if dyn_stack.buffer_addr() % 2 == 1 {
            dyn_stack.push_one(|| Ok::<_, ()>(Data1(11))).unwrap()
        } else {
            dyn_stack
                .push_one(|| Ok::<_, ()>(Data2([1, 2, 3, 4])))
                .unwrap()
        };
        assert_eq!(ref_mut.a(), 4);
        drop(ref_mut);

        assert_eq!(NUM_DROPPED.load(Relaxed), 1);
    }

    #[cfg(feature = "nightly")]
    #[cfg_attr(miri, ignore)]
    #[test]
    fn test_slice_nightly() {
        static NUM_DROPPED: AtomicUsize = AtomicUsize::new(0);

        #[derive(Debug, Default)]
        struct Data(usize);

        impl Drop for Data {
            fn drop(&mut self) {
                assert_ne!(self.0, usize::MAX);
                self.0 = usize::MAX;
                NUM_DROPPED.fetch_add(1, Relaxed);
            }
        }

        let mut dyn_stack = CompanionStack::<1024>::new();
        let mut ref_mut_slice: RefMut<[Data], 1024> = if dyn_stack.buffer_addr() % 2 == 0 {
            dyn_stack
                .push_one(|| Ok::<_, ()>([Data(10), Data(11)]))
                .unwrap()
        } else {
            dyn_stack
                .push_one(|| Ok::<_, ()>([Data(12), Data(13), Data(14)]))
                .unwrap()
        };
        ref_mut_slice[0].0 = 15;
        assert_eq!(ref_mut_slice.len(), 2);
        assert_eq!(ref_mut_slice[0].0, 15);
        assert_eq!(ref_mut_slice[1].0, 11);

        drop(ref_mut_slice);

        assert_eq!(NUM_DROPPED.load(Relaxed), 2);
    }
}
