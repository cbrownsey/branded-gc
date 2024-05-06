use core::{
    marker::PhantomData,
    ops::{Deref, DerefMut},
    ptr::Pointee,
};

use crate::{
    collect::Collect,
    context::Mutation,
    gc_box::{Erased, GcBox},
    metasized::MetaSized,
    slicetail::SliceTailed,
    write::{Barrier, Unlock},
    PhantomInvariant,
};

/// A cheaply copiable, garbage collected pointer.
///
/// The contained pointer has a minimum alignment of 8.
#[repr(transparent)]
pub struct Gc<'gc, T: ?Sized>(GcBox<T>, PhantomInvariant<'gc>);

// Safety: `Gc` has special requirements around the `Collect` trait.
unsafe impl<'gc, T: ?Sized + MetaSized + Collect + 'gc> Collect for Gc<'gc, T> {
    const NEEDS_TRACE: bool = true;

    fn trace(&self, cc: &crate::context::Collector) {
        cc.to_context().trace(self.erased_box());
    }
}

impl<'gc, T: ?Sized> Gc<'gc, T> {
    pub fn as_ptr(self) -> *mut () {
        self.0.as_ptr()
    }

    /// # Safety
    /// The given pointer must have been previously returned by the `as_ptr` function of an
    /// identically typed `Gc`.
    pub unsafe fn from_ptr(ptr: *mut ()) -> Self {
        Self::from_gc_box(GcBox::from_ptr(ptr))
    }

    unsafe fn from_gc_box(gc: GcBox<T>) -> Self {
        Gc(gc, PhantomData)
    }
}

impl<'gc, T: ?Sized + MetaSized + 'gc> Gc<'gc, T> {
    fn erased_box(&self) -> GcBox<Erased> {
        self.0.erase()
    }

    /// Converts a `Gc` pointer of one type to a `Gc` pointer of another type.
    ///
    /// # Safety
    /// The transmuted to type must have a size less than or equal to the original types size. The
    /// same is true for alignment.
    ///
    /// This does not alter the vtable, or how the pointer is stored in the context. It will still
    /// be collected and dropped as a value of the original type. This is essentially only valid
    /// for a transmutation to a `repr(transparent)` type.
    pub(crate) unsafe fn transmute<Dst>(self) -> Gc<'gc, Dst>
    where
        Dst: ?Sized + MetaSized,
        Dst: Pointee<Metadata = T::Metadata>,
    {
        let Gc(gc, _) = self;
        let meta = gc.metadata();
        debug_assert_eq!(T::layout(meta), T::layout(meta));
        Gc(GcBox::from_ptr(gc.as_ptr()), PhantomData)
    }

    /// Returns a reference to the contained value which lasts for the entire length of the
    /// closure, as opposed to the length of the `Gc`'s reference.
    ///
    /// # Examples
    /// ```
    /// use branded_gc::{rootless_arena, Gc};
    ///
    /// rootless_arena(|mt| {
    ///     let x: &u64 = {
    ///         let gc = Gc::new(12u64, mt);
    ///         Gc::long_ref(gc)
    ///     };
    ///
    ///     assert_eq!(*x, 12u64);
    /// });
    /// ```
    pub fn long_ref(this: Self) -> &'gc T {
        // Safety: A `GcBox` contained by a `Gc` must contain initialized data. And `Gc` pointers
        // must always contain initialized data, and a `Gc` is always valid for the entire length
        // of the closure.
        unsafe { &*this.0.data_ptr() }
    }

    /// Marks a garbage collected pointer as needing to be traced again, and returns a reference to
    /// the pointed to data, wrapped in a write [`Barrier`].
    ///
    /// # Examples
    /// ```
    /// use std::cell::Cell;
    /// use branded_gc::{rootless_arena, Gc, write::Barrier, locked_cell::LockedCell};
    ///
    /// rootless_arena(|mt| {
    ///     let gc = Gc::new(LockedCell::new(0i32), mt);
    ///     let cell: &Cell<_> = Gc::write_barrier(gc, mt).unlock();
    ///     cell.set(2i32);
    ///     assert_eq!(gc.get(), 2);
    /// });
    /// ```
    pub fn write_barrier(this: Self, mt: &Mutation<'gc>) -> &'gc Barrier<T> {
        mt.as_context().make_gray(this.erased_box());
        // Safety: `Gc` is turned gray above.
        unsafe { Barrier::new_unchecked(Self::long_ref(this)) }
    }

    /// Marks a garbage collected pointer as needing to be traced again, and returns a reference to
    /// the unlocked version of the pointed to data. Equivalent to
    /// `Gc::write_barrier(this, mt).unlock()`.
    ///
    /// # Examples
    /// ```
    /// use branded_gc::{rootless_arena, Gc, locked_cell::LockedCell};
    ///
    /// rootless_arena(|mt| {
    ///     let gc = Gc::new(LockedCell::new(12i32), mt);
    ///     let cell = Gc::unlock(gc, mt);
    ///     cell.set(5);
    ///     assert_eq!(gc.get(), 5);
    /// });
    /// ```
    pub fn unlock(this: Self, mt: &Mutation<'gc>) -> &'gc T::Unlocked
    where
        T: Unlock,
    {
        Gc::write_barrier(this, mt).unlock()
    }
}

impl<'gc, T: Collect + 'gc> Gc<'gc, T> {
    /// Allocates garbage collected memory to store the given value.
    ///
    /// This will cause an allocation, even if `T` is zero-sized.
    ///
    /// # Examples
    /// ```
    /// use branded_gc::{rootless_arena, Gc};
    ///
    /// rootless_arena(|mt| {
    ///     let gc = Gc::new([12u32; 4], mt);
    ///
    ///     assert_eq!(*gc, [12u32; 4]);
    /// });
    /// ```
    pub fn new(data: T, mt: &Mutation<'gc>) -> Self {
        let gc_box: GcBox<T> = GcBox::initialize_box(());
        gc_box.write_data(data);
        mt.adopt_box(gc_box.erase());
        // Safety: Data has been written to the `GcBox`.
        unsafe { Gc::from_gc_box(gc_box) }
    }
}

impl<'gc, T: Collect + 'gc> Gc<'gc, [T]> {
    /// Creates a new garbage collected slice of the given length by repeatedly calling the given
    /// function with the current index until the slice is full.
    ///
    /// # Examples
    /// ```
    /// use branded_gc::{rootless_arena, Gc};
    ///
    /// rootless_arena(|mt| {
    ///     let gc = Gc::new_slice(|idx| idx * 2, 5, mt);
    ///
    ///     assert_eq!(&*gc, &[0, 2, 4, 6, 8]);
    /// });
    /// ```
    pub fn new_slice(mut f: impl FnMut(usize) -> T, len: usize, mt: &Mutation<'gc>) -> Self {
        Self::try_new_slice::<core::convert::Infallible>(|idx| Ok(f(idx)), len, mt).unwrap()
    }

    pub fn try_new_slice<E>(
        mut f: impl FnMut(usize) -> Result<T, E>,
        len: usize,
        mt: &Mutation<'gc>,
    ) -> Result<Self, E> {
        let gc_box: GcBox<[T]> = GcBox::initialize_box(len);

        struct DropGuard<T: Collect>(GcBox<[T]>, usize);

        impl<T: Collect> Drop for DropGuard<T> {
            fn drop(&mut self) {
                for i in 0..self.1 {
                    // Safety: Drop guard may not be created with length longer than the allocated
                    // length.
                    let ptr = unsafe { self.0.data_ptr().cast::<T>().add(i) };
                    // Safety:
                    unsafe { core::ptr::drop_in_place(ptr) };
                }

                // Safety: This is only called if the given closure panics, in which case this and
                // the local defined at the top of `new_slice` are the only owners of this box.
                unsafe { self.0.deallocate() };
            }
        }

        for i in 0..len {
            let guard = DropGuard(gc_box, i);
            // Safety: The `GcBox` has allocated enough room for `len` instances of `T`.
            let ptr = unsafe { gc_box.data_ptr().cast::<T>().add(i) };
            // Safety: As above.
            unsafe { ptr.write(f(i)?) };
            core::mem::forget(guard);
        }

        mt.adopt_box(gc_box.erase());

        // Safety: Data has been written to the `GcBox`.
        Ok(unsafe { Gc::from_gc_box(gc_box) })
    }

    /// Creates a new garbage collected slice, copying each element from the given slice.
    ///
    /// If the given slice does not contain elements that implement copy, use
    /// `[Gc::cloned_from_slice]` instead.
    ///
    /// # Examples
    /// ```
    /// use branded_gc::{rootless_arena, Gc};
    ///
    /// rootless_arena(|mt| {
    ///     let gc = Gc::copy_from_slice(&[1i32, 2, 3, 4, 5], mt);
    ///
    ///     assert_eq!(&*gc, &[1i32, 2, 3, 4, 5]);
    /// });
    /// ```
    ///
    /// ```compile_fail
    /// use branded_gc::{rootless_arena, Gc};
    ///
    /// rootless_arena(|mt| {
    ///     Gc::copy_from_slice(&[String::from("Hello, "), String::from("World!")], mt);
    /// });
    /// ```
    pub fn copy_from_slice(source: &[T], mt: &Mutation<'gc>) -> Self
    where
        T: Copy,
    {
        let gc_box: GcBox<[T]> = GcBox::initialize_box(source.len());

        let ptr = gc_box.data_ptr().cast::<T>();
        // Safety: The `allocate_box` function has allocated exactly `source.len()` bytes at the
        // correct alignment. `T` is also `Copy` and so a bytewise copy is sound.
        unsafe { core::ptr::copy_nonoverlapping(source.as_ptr(), ptr, source.len()) };
        mt.adopt_box(gc_box.erase());

        // Safety: `gc_box` has an initialized data field.
        unsafe { Gc::from_gc_box(gc_box) }
    }

    /// Creates a new garbage collected slice, cloning each element from the given slice.
    ///
    /// If you want to guarantee that the given slice contains bitwise copiable elements, use
    /// `[Gc::copy_from_slice]` instead.
    ///
    /// # Examples
    /// ```
    /// use branded_gc::{rootless_arena, Gc};
    ///
    /// rootless_arena(|mt| {
    ///     let gc = Gc::clone_from_slice(&[1i32, 2, 3, 4, 5], mt);
    ///
    ///     assert_eq!(&*gc, &[1i32, 2, 3, 4, 5]);
    /// });
    /// ```
    pub fn clone_from_slice(source: &[T], mt: &Mutation<'gc>) -> Self
    where
        T: Clone,
    {
        Self::new_slice(
            // Safety: The given closure will be called once for each index up to `source.len()`,
            // which means `idx` is always in range.
            |idx| unsafe { source.get_unchecked(idx).clone() },
            source.len(),
            mt,
        )
    }

    /// Creates a new garbage collected slice from a `[Vec]`, taking ownership of each element in
    /// said `[Vec]`.
    ///
    /// # Examples
    /// ```
    /// use branded_gc::{rootless_arena, Gc};
    ///
    /// rootless_arena(|mt| {
    ///     let v = vec![Box::new(1u64), Box::new(2), Box::new(3)];
    ///     let gc = Gc::from_vec(v, mt);
    ///
    ///     assert_eq!(&*gc, &[Box::new(1u64), Box::new(2), Box::new(3)]);
    /// });
    /// ```
    pub fn from_vec(source: alloc::vec::Vec<T>, mt: &Mutation<'gc>) -> Self {
        let len = source.len();
        let mut source = source.into_iter();

        // Safety: The given closure will be called once for each index up to `source.len()`,
        // which is exactly how many elements this iterator has.
        Self::new_slice(|_| unsafe { source.next().unwrap_unchecked() }, len, mt)
    }
}

impl<'gc, T: Collect + 'gc, S: Collect + 'gc> Gc<'gc, SliceTailed<T, S>> {
    /// Creates a new garbage collected slice tailing `head`, of the given length by
    /// repeatedly calling the given function with the current index until the slice is full.
    ///
    /// # Examples
    /// ```
    /// use branded_gc::{rootless_arena, Gc};
    ///
    /// rootless_arena(|mt| {
    ///     let gc = Gc::new_tailed(12u32, |idx| idx * 2, 5, mt);
    ///
    ///     assert_eq!(gc.head, 12u32);
    ///     assert_eq!(&gc.tail, &[0, 2, 4, 6, 8]);
    /// });
    /// ```
    pub fn new_tailed(
        head: T,
        mut f: impl FnMut(usize) -> S,
        len: usize,
        mt: &Mutation<'gc>,
    ) -> Self {
        Self::try_new_tailed::<core::convert::Infallible>(head, |idx| Ok(f(idx)), len, mt).unwrap()
    }

    pub fn try_new_tailed<E>(
        head: T,
        mut f: impl FnMut(usize) -> Result<S, E>,
        len: usize,
        mt: &Mutation<'gc>,
    ) -> Result<Self, E> {
        let gc_box: GcBox<SliceTailed<T, S>> = GcBox::initialize_box(len);

        // Safety: The `initialize_box` function allocates enough space for the contained object.
        unsafe { gc_box.data_ptr().cast::<T>().write(head) };
        struct DropGuard<T: Collect, S: Collect>(GcBox<SliceTailed<T, S>>, usize);

        impl<T: Collect, S: Collect> Drop for DropGuard<T, S> {
            fn drop(&mut self) {
                for i in 0..self.1 {
                    // Safety: Drop guard may not be created with length longer than the allocated
                    // length.
                    #[expect(clippy::multiple_unsafe_ops_per_block)]
                    let ptr = unsafe {
                        self.0
                            .data_ptr()
                            .cast::<S>()
                            .byte_add(<SliceTailed<T, S>>::tail_offset())
                            .add(i)
                    };
                    // Safety: Elements up to the `self.1`-th element have been initialised, and
                    // no others.
                    unsafe { core::ptr::drop_in_place(ptr) };
                }

                // Safety: The `T` field of the contained `SliceTailed` is initialised before the
                // drop guard is constructed.
                unsafe { core::ptr::drop_in_place(self.0.data_ptr().cast::<T>()) }
                // Safety: This is only called if the given closure panics, in which case this and
                // the local defined at the top of `new_slice` are the only owners of this box.
                unsafe { self.0.deallocate() };
            }
        }

        for i in 0..len {
            let guard = DropGuard(gc_box, i);
            // Safety: The `GcBox` has allocated enough room for `len` instances of `S` succeeding
            // an instance of `T`.
            #[expect(clippy::multiple_unsafe_ops_per_block)]
            let ptr = unsafe {
                gc_box
                    .data_ptr()
                    .cast::<S>()
                    .byte_add(<SliceTailed<T, S>>::tail_offset())
                    .add(i)
            };
            // Safety: As above.
            unsafe { ptr.write(f(i)?) };
            core::mem::forget(guard);
        }

        mt.adopt_box(gc_box.erase());

        // Safety: Data has been written to the `GcBox`.
        Ok(unsafe { Gc::from_gc_box(gc_box) })
    }

    /// Creates a new garbage collected slice tailing `head`, copying each element
    /// from the given slice.
    ///
    /// If the given slice does not contain elements that implement copy, use
    /// `[Gc::cloned_from_slice]` instead.
    ///
    /// # Examples
    /// ```
    /// use branded_gc::{rootless_arena, Gc};
    ///
    /// rootless_arena(|mt| {
    ///     let gc = Gc::tail_copied_from(42u32, &[1i32, 2, 3, 4, 5], mt);
    ///
    ///     assert_eq!(gc.head, 42u32);
    ///     assert_eq!(&gc.tail, &[1i32, 2, 3, 4, 5]);
    /// });
    /// ```
    ///
    /// ```compile_fail
    /// use branded_gc::{rootless_arena, Gc};
    ///
    /// rootless_arena(|mt| {
    ///     Gc::tail_copied_from(42u32, &[String::from("Hello, "), String::from("World!")], mt);
    /// });
    /// ```
    pub fn tail_copied_from(head: T, source: &[S], mt: &Mutation<'gc>) -> Self
    where
        S: Copy,
    {
        Self::new_tailed(
            head,
            |idx| {
                // Safety: The given closure will be called once for each index up to `source.len()`,
                // which means `idx` is always in range.
                unsafe { *source.get_unchecked(idx) }
            },
            source.len(),
            mt,
        )
    }

    /// Creates a new garbage collected slice following `head`, cloning each element from the
    /// given slice.
    ///
    /// If you want to guarantee that the given slice contains bitwise copiable elements, use
    /// `[Gc::copy_from_slice]` instead.
    ///
    /// # Examples
    /// ```
    /// use branded_gc::{rootless_arena, Gc};
    ///
    /// rootless_arena(|mt| {
    ///     let gc = Gc::clone_from_slice(&[1i32, 2, 3, 4, 5], mt);
    ///
    ///     assert_eq!(&*gc, &[1i32, 2, 3, 4, 5]);
    /// });
    /// ```
    pub fn tail_cloned_from(head: T, source: &[S], mt: &Mutation<'gc>) -> Self
    where
        S: Clone,
    {
        Self::new_tailed(
            head,
            // Safety: The given closure will be called once for each index up to `source.len()`,
            // which means `idx` is always in range.
            |idx| unsafe { source.get_unchecked(idx).clone() },
            source.len(),
            mt,
        )
    }

    /// Creates a new garbage collected slice from a `[Vec]`, taking ownership of each element in
    /// said `[Vec]`.
    ///
    /// # Examples
    /// ```
    /// use branded_gc::{rootless_arena, Gc};
    ///
    /// rootless_arena(|mt| {
    ///     let v = vec![Box::new(1u64), Box::new(2), Box::new(3)];
    ///     let gc = Gc::from_vec(v, mt);
    ///
    ///     assert_eq!(&*gc, &[Box::new(1u64), Box::new(2), Box::new(3)]);
    /// });
    /// ```
    pub fn tail_from_vec(head: T, source: alloc::vec::Vec<S>, mt: &Mutation<'gc>) -> Self {
        let len = source.len();
        let mut source = source.into_iter();

        Self::new_tailed(
            head,
            |_| {
                // Safety: The given closure will be called once for each index up to `source.len()`,
                // which is exactly how many elements this iterator has.
                unsafe { source.next().unwrap_unchecked() }
            },
            len,
            mt,
        )
    }
}

impl<'gc> Gc<'gc, [u8]> {
    pub fn as_string(self) -> Result<Gc<'gc, str>, core::str::Utf8Error> {
        core::str::from_utf8(&self)?;
        // Safety: UTF-8 validity checked above.
        Ok(unsafe { self.as_string_unchecked() })
    }

    /// # Safety
    /// The contained slice must be a valid UTF-8 string.
    pub unsafe fn as_string_unchecked(self) -> Gc<'gc, str> {
        // Safety: `[u8]` to `str` has no differences in abi, drop, collect, or trace
        // implementations.
        unsafe { self.transmute() }
    }
}

impl<'gc> Gc<'gc, str> {
    /// Creates a new garbage collected string, copied from the given `&str`.
    ///
    /// # Examples
    /// ```
    /// use branded_gc::{rootless_arena, Gc};
    ///
    /// rootless_arena(|mt| {
    ///     let gc = Gc::from_str("Hello, World!", mt);
    ///
    ///     assert_eq!(&*gc, "Hello, World!");
    /// });
    /// ```
    pub fn from_str(s: &str, mt: &Mutation<'gc>) -> Self {
        let gc_box: GcBox<str> = GcBox::initialize_box(s.len());

        let start = gc_box.data_ptr().cast::<u8>();
        // Safety:
        // - The `gc_box` is initialized with a length equal to the given string.
        // - `str` has an alignment of one.
        // - The destination is freshly allocated and so cannot overlap with the source string.
        unsafe { core::ptr::copy_nonoverlapping(s.as_ptr(), start, s.len()) }

        mt.adopt_box(gc_box.erase());
        // Safety: The contained data has been initialized.
        unsafe { Gc::from_gc_box(gc_box) }
    }

    /// Creates a `Gc<str>` from multiple strings concatenated together. This causes only one
    /// allocation, sized to fit every string, and copies them all in together.
    ///
    /// # Examples
    /// ```
    /// use branded_gc::{rootless_arena, Gc};
    ///
    /// rootless_arena(|mt| {
    ///     let gc = Gc::from_many_str(&["Hel", "lo, ", "Wor", "ld", "!"], mt);
    ///     assert_eq!(&*gc, "Hello, World!");
    /// });
    /// ```
    pub fn from_many_str(s: &[&str], mt: &Mutation<'gc>) -> Self {
        let len: usize = s.iter().map(|s| s.len()).sum();
        let mut iter = s.iter().flat_map(|s| s.bytes());

        // Safety: The given function is guaranteed to only be called exactly `len` times.
        let gc = unsafe { Gc::new_slice(|_| iter.next().unwrap_unchecked(), len, mt) };
        // Safety: str has the same memory representation as [u8].
        unsafe { gc.transmute() }
    }
}

impl<'gc, T: ?Sized + MetaSized> Gc<'gc, T> {
    #[must_use]
    pub fn ptr_eq(this: Self, other: Self) -> bool {
        core::ptr::eq(this.0.as_ptr(), other.0.as_ptr())
    }
}

impl<T: core::fmt::Debug + ?Sized + MetaSized> core::fmt::Debug for Gc<'_, T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        core::fmt::Debug::fmt(&**self, f)
    }
}

impl<T: core::fmt::Display + ?Sized + MetaSized> core::fmt::Display for Gc<'_, T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        core::fmt::Display::fmt(&**self, f)
    }
}

impl<T: ?Sized> Clone for Gc<'_, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: ?Sized> Copy for Gc<'_, T> {}

impl<T: PartialEq + ?Sized + MetaSized> PartialEq for Gc<'_, T> {
    fn eq(&self, other: &Self) -> bool {
        **self == **other
    }
}

impl<T: Eq + ?Sized + MetaSized> Eq for Gc<'_, T> {}

impl<T: PartialOrd + ?Sized + MetaSized> PartialOrd for Gc<'_, T> {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        (**self).partial_cmp(&**other)
    }
}

impl<T: Ord + ?Sized + MetaSized> Ord for Gc<'_, T> {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        (**self).cmp(&**other)
    }
}

impl<T: core::hash::Hash + ?Sized + MetaSized> core::hash::Hash for Gc<'_, T> {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        (**self).hash(state);
    }
}

impl<T: ?Sized + MetaSized> Deref for Gc<'_, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        // Safety: The data field of the contained `GcBox` being initialized is an invariant of the
        // `Gc` struct.
        unsafe { self.0.data() }
    }
}

/// The write mechanism for garbage collected pointers is provided by the `Gc::write` method.
impl<T: ?Sized> !DerefMut for Gc<'_, T> {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rootless_arena;

    #[test]
    fn gc_sized_new() {
        rootless_arena(|mt| {
            let gc1 = Gc::new(12i32, mt);
            let gc2 = Gc::new(48i128, mt);
            let gc3 = Gc::new(alloc::string::String::from("Hello, World!"), mt);

            assert_eq!(*gc1, 12i32);
            assert_eq!(*gc2, 48i128);
            assert_eq!(&*gc3, "Hello, World!");
        });
    }

    #[test]
    fn gc_collect_new() {
        rootless_arena(|mt| {
            let gc: Gc<Option<Gc<()>>> = Gc::new(None, mt);

            assert_eq!(*gc, None);
        })
    }

    #[test]
    fn gc_slice_new() {
        use alloc::boxed::Box;
        rootless_arena(|mt| {
            let gc1 = Gc::new_slice(|_| 0u8, 0, mt);
            let gc2 = Gc::new_slice(|idx| idx, 8, mt);
            let gc3 = Gc::copy_from_slice(&[5i32, 4, 3, 2, 1, 0], mt);
            let gc4 = Gc::clone_from_slice(
                &[
                    Box::new(5i32),
                    Box::new(4),
                    Box::new(3),
                    Box::new(2),
                    Box::new(1),
                    Box::new(0),
                ],
                mt,
            );
            let gc5 = Gc::from_vec(alloc::vec::Vec::from([1, 2, 3, 4, 5]), mt);
            let gc6 = Gc::copy_from_slice(&[1256u64, 65132u64], mt);

            assert_eq!(&*gc1, &[]);
            assert_eq!(&*gc2, &[0, 1, 2, 3, 4, 5, 6, 7]);
            assert_eq!(&*gc3, &[5, 4, 3, 2, 1, 0]);
            assert_eq!(
                &*gc4,
                &[
                    Box::new(5),
                    Box::new(4),
                    Box::new(3),
                    Box::new(2),
                    Box::new(1),
                    Box::new(0)
                ]
            );
            assert_eq!(&*gc5, &[1, 2, 3, 4, 5]);
            assert_eq!(&*gc6, &[1256u64, 65132u64]);
        });
    }

    #[test]
    fn gc_str_new() {
        rootless_arena(|mt| {
            let gc1 = Gc::from_str("", mt);
            let gc2 = Gc::from_str("Hello, World!", mt);
            assert_eq!(&*gc1, "");
            assert_eq!(&*gc2, "Hello, World!");
        })
    }

    #[test]
    #[should_panic]
    fn panic_in_slice_creation() {
        #[allow(clippy::unwrap_used)]
        rootless_arena(|mt| {
            Gc::new_slice(
                |idx| {
                    assert!(idx != 5);
                    alloc::string::String::new()
                },
                12,
                mt,
            );
        })
    }
}
