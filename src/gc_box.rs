use core::{
    alloc::{Layout, LayoutError},
    cell::Cell,
    hint::unreachable_unchecked,
    marker::PhantomData,
    ptr::{NonNull, Pointee},
};

use crate::{
    collect::Collect,
    context::{Collector, ObjectColour},
    metasized::MetaSized,
};

/// An internal, highly unsafe garbage collected pointer.
///
/// # Safety
/// The invariants held by the `GcBox` is that the header and metadata fields are always
/// initialized, however the data contained within may be in any arbitrary state.
#[repr(transparent)]
pub(crate) struct GcBox<T: ?Sized>(NonNull<()>, PhantomData<T>);

impl<T: ?Sized> core::fmt::Debug for GcBox<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "GcBox({:?})", &self.0)
    }
}

impl<T: ?Sized, U: ?Sized> PartialEq<GcBox<U>> for GcBox<T> {
    fn eq(&self, other: &GcBox<U>) -> bool {
        // N.B The needs trace flag of an erased pointer should be removed to allow
        // `GcBox<T> == GcBox<Erased>`.
        (self.0.addr().get() & !1) == (other.0.addr().get() & !1)
    }
}

impl<T: ?Sized> Eq for GcBox<T> {}

impl<T: ?Sized> Clone for GcBox<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: ?Sized> Copy for GcBox<T> {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum Erased {}

impl GcBox<Erased> {
    pub unsafe fn restore_type<T: ?Sized + MetaSized + Collect>(self) -> GcBox<T> {
        use core::num::NonZeroUsize;
        let GcBox(ptr, _) = self;
        GcBox(
            ptr.map_addr(|a| NonZeroUsize::new(a.get() & !1)
                .expect("this operation only removes the lowest bit, and since the contained type has an alignment of 8, the address can never be 1")),
            PhantomData,
        )
    }

    pub fn ptr_needs_trace(&self) -> bool {
        self.0.addr().get() & 1 != 0
    }
}

impl<T> GcBox<T> {
    pub fn write_data(&self, data: T) {
        // Safety: An invariant of the `GcBox` is that there must be enough space for a properly
        // sized instance of T.
        unsafe { self.data_ptr().write(data) }
    }
}

impl<T: ?Sized + MetaSized> GcBox<T> {
    /// Creates a new `GcBox` when given the of the to be contained data, and a callback, which
    /// allocates space for it.
    pub fn initialize_box(meta: T::Metadata) -> GcBox<T>
    where
        T: Collect,
    {
        let (layout, offset) = Self::inner_layout(meta)
            .expect("a layout failure is rare enough to assume it never happens");

        // Safety: Layout has to be non zero, as it includes the header.
        let ptr = unsafe { alloc::alloc::alloc(layout) };
        // Safety: The offset returned by `inner_layout` is the number of bytes taken by the
        // metadata, padding and header, which at worst places the pointer one past the end of the
        // allocation, if the data is zero sized.
        let ptr = unsafe { ptr.cast::<()>().byte_add(offset) };
        debug_assert!(ptr.is_aligned_to(8));

        // Safety: The pointer is appropriately offset and sized as above.
        let gc: Self = unsafe { GcBox::from_ptr(ptr) };

        // Safety: The allocation is sized to fit the metadata alongside all other values.
        unsafe {
            gc.metadata_ptr().write(meta);
        };
        // Safety: The allocation is sized to fit the header alongside all other values.
        unsafe {
            gc.header_ptr().write(GcBoxHeader {
                vtable_ptr: VTablePtr::new::<T>(),
                context_index: Cell::new(0),
            });
        };

        gc
    }

    /// Returns a Layout for memory capable of storing the contents of a `GcBox`, meaning the
    /// metadata, the `GcHeader`, and the data itself. Also returns the offset in bytes between the
    /// beginning of the metadata and the data, and the beginning of the header and the data
    /// respectively.
    pub fn inner_layout(meta: T::Metadata) -> Result<(Layout, usize), LayoutError> {
        let metadata = Layout::new::<T::Metadata>();
        let header = Layout::new::<GcBoxHeader>();
        let data = T::layout(meta)?;

        let (layout, _) = metadata.extend(header)?;
        let (layout, data_offset) = layout.extend(data)?;

        Ok((layout, data_offset))
    }
}

impl<T: ?Sized + Pointee> GcBox<T> {
    /// Creates a `GcBox` from the given pointer.
    ///
    /// # Safety
    /// The given pointer must point to the data field of a valid `GcBox` inner in memory.
    pub unsafe fn from_ptr(ptr: *mut ()) -> Self {
        GcBox(NonNull::new_unchecked(ptr), PhantomData)
    }

    // pub fn ptr_eq(this: Self, other: Self) -> bool {
    //     core::ptr::eq(this.as_ptr(), other.as_ptr())
    // }

    pub fn as_ptr(&self) -> *mut () {
        let GcBox(ptr, PhantomData) = self;
        ptr.as_ptr()
    }

    /// Returns a pointer to the contained data. The pointed to data may or may not be initalized.
    pub fn data_ptr(&self) -> *mut T {
        core::ptr::from_raw_parts_mut(self.0.as_ptr(), self.metadata())
    }

    /// Returns a reference to the contained data.
    ///
    /// # Safety
    /// Since `GcBox` maintains no invariants about the state of the contained data, this function
    /// is only safe to be called if the contained data is initalized and in a valid state.
    ///
    /// It is also unsound to call this function on a `GcBox<Erased>`, as that would return a
    /// reference to an uninhabited enum.
    pub unsafe fn data(&self) -> &T {
        // Safety: Upheld by caller.
        unsafe { &*self.data_ptr() }
    }

    fn header_ptr(&self) -> *mut GcBoxHeader {
        // Safety: `GcBox` is guaranteed to have an initialized `GcHeader` at the first available
        // spot behind where the data is allocated.
        unsafe { rewind_ptr_mut(self.as_ptr()) }
    }

    fn metadata_ptr(&self) -> *mut T::Metadata {
        // Safety: `GcBox` is guaranteed to have an initialized metadata value at the first
        // available spot behind where the `GcHeader` is allocated.
        unsafe { rewind_ptr_mut(self.header_ptr()) }
    }

    /// Returns a copy of this box's metadata.
    pub(crate) fn metadata(&self) -> T::Metadata {
        // Safety: Having an initialized metadata value is an invariant of the `GcBox`.
        unsafe { *self.metadata_ptr() }
    }

    /// Returns a reference to this box's header.
    fn header(&self) -> &GcBoxHeader {
        // Safety: Having an initialized `GcBoxHeader` value is an invariant of the `GcBox`.
        unsafe { &*self.header_ptr() }
    }

    /// Returns a referece to this box's vtable.
    fn vtable(&self) -> &'static GcVTable {
        self.header().vtable_ptr.as_ref()
    }

    pub(crate) fn set_colour(&self, colour: ObjectColour) {
        self.header().vtable_ptr.set_colour(colour)
    }

    #[must_use]
    pub(crate) fn colour(&self) -> ObjectColour {
        self.header().vtable_ptr.get_colour()
    }

    #[must_use]
    pub(crate) fn needs_trace(&self) -> bool {
        self.header().vtable_ptr.get_needs_trace()
    }

    pub fn layout(&self) -> (Layout, usize) {
        // Safety: An invariant of `GcBox` is that the vtable was created with the same type as the
        // contained value.
        unsafe { (self.vtable().layout)(self.erase()) }
    }

    pub unsafe fn drop(&self) {
        // Safety: An invariant of `GcBox` is that the vtable was created with the same type as the
        // contained value.
        unsafe { (self.vtable().drop)(self.erase()) }
    }

    pub unsafe fn collect(&self, cc: &Collector) {
        // Safety: An invariant of `GcBox` is that the vtable was created with the same type as the
        // contained value.
        unsafe { (self.vtable().collect)(self.erase(), cc) }
    }

    pub fn erase(self) -> GcBox<Erased> {
        let GcBox(ptr, _) = self;
        let ptr = ptr.map_addr(|a| a | (self.needs_trace() as usize));
        GcBox(ptr, PhantomData)
    }

    /// Deallocate the memory backing this `GcBox`. All subsequent reads and writes to and from
    /// this box are unsound.
    pub unsafe fn deallocate(self) {
        let (layout, offset) = self.layout();
        // Safety: The `GcBox::layout` function is guaranteed to give an accurate offset from the
        // start of the allocation to the beginning of the data.
        let ptr = unsafe { self.as_ptr().byte_sub(offset) };

        // Safety: The LSB is masked off in case this box is erased.
        unsafe { alloc::alloc::dealloc(ptr.cast::<u8>().map_addr(|p| p & !1), layout) };
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Default)]
struct GcBoxHeader {
    /// Contains the pointer to this objects vtable, as well as the flag for if this type needs to
    /// be traced at all and the objects current colour.
    vtable_ptr: VTablePtr,
    context_index: Cell<usize>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct VTablePtr(Cell<*const GcVTable>);

impl Default for VTablePtr {
    fn default() -> Self {
        Self(Cell::new(<&'static GcVTable>::default()))
    }
}

impl VTablePtr {
    #[must_use]
    pub fn new<T>() -> Self
    where
        T: ?Sized + MetaSized + Collect,
    {
        let s = Self(Cell::new(GcVTable::new::<T>()));
        s.set_needs_trace(T::NEEDS_TRACE);
        s
    }

    fn update_addr<F>(&self, f: F)
    where
        F: FnOnce(usize) -> usize,
    {
        let ptr = self.0.get();
        self.0.set(ptr.map_addr(f));
    }

    #[must_use]
    pub fn as_ref(&self) -> &'static GcVTable {
        let ptr = self.0.get();
        // Safety: `GcVTable` has an alignment of 8 (1 << 4) and so the last four bits must always
        // be zero. Since the colour tag is only two bits wide, and the 'is live' flag only uses
        // the third bit, they never touch any required bits.
        unsafe { &*ptr.map_addr(|addr| addr & !0b111) }
    }

    #[must_use]
    pub fn get_colour(&self) -> ObjectColour {
        ObjectColour::from_tag(self.0.get().addr() & 0b11)
    }

    pub fn set_colour(&self, colour: ObjectColour) {
        self.update_addr(|a| (a & !0b11) | colour.to_tag());
    }

    #[must_use]
    pub fn get_needs_trace(&self) -> bool {
        self.0.get().addr() & 0b100 != 0
    }

    pub fn set_needs_trace(&self, needs_trace: bool) {
        let needs_trace = needs_trace as usize;
        self.update_addr(|a| (a & !0b100) | (needs_trace << 2))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct GcVTable {
    /// Returns the layout of the total allocation, and the offset from the start of the allocation
    /// and the data pointer.
    ///
    /// # Safety
    /// To call this function soundly, this `GcVTable` must have been created by a call to
    /// `GcVTable::new()`, where `T` is the same type as the type that the given erased `GcBox` was
    /// instantiated with.
    layout: unsafe fn(GcBox<Erased>) -> (Layout, usize),
    /// # Safety
    /// To call this function soundly, this `GcVTable` must have been created by a call to
    /// `GcVTable::new()`, where `T` is the same type as the type that the given erased `GcBox` was
    /// instantiated with.
    ///
    /// Additionally, the given erased box must contain initialized data.
    collect: unsafe fn(GcBox<Erased>, cc: &Collector),
    /// Drops the data contained within the given box, leaving the data field uninitalized.
    ///
    /// # Safety
    /// To call this function soundly, this `GcVTable` must have been created by a call to
    /// `GcVTable::new()`, where `T` is the same type as the type that the given erased `GcBox` was
    /// instantiated with.
    ///
    /// Additionally, the given erased box must contain initalized data.
    drop: unsafe fn(GcBox<Erased>),
}

impl Default for &'static GcVTable {
    fn default() -> Self {
        // Since this was not created by a call to `GcVTable::new`, all fields are meaningless, and
        // all function pointers are unsound to call.
        const {
            &GcVTable {
                layout: |_| {
                    // Safety: Calling this function is inherently unsound.
                    unsafe { unreachable_unchecked() }
                },
                collect: |_, _| {
                    // Safety: Calling this function is inherently unsound.
                    unsafe { unreachable_unchecked() }
                },
                drop: |_| {
                    // Safety: Calling this function is inherently unsound.
                    unsafe { unreachable_unchecked() }
                },
            }
        }
    }
}

impl GcVTable {
    /// Retrieve a static pointer to a constant `GcVTable` for a given type.
    ///
    /// This makes use of constant promotion to generate the `GcVTable` at compile time instead of
    /// at runtime, and so we can get a static reference from it.
    pub(crate) const fn new<T>() -> &'static GcVTable
    where
        T: ?Sized + MetaSized + Collect,
    {
        const {
            &GcVTable {
                layout: |gc: GcBox<Erased>| {
                    // Safety: The caller of this function is in charge of ensuring that this function
                    // is only called with an erased version of a `GcBox<T>`.
                    let gc: GcBox<T> = unsafe { gc.restore_type() };

                    // Safety: `inner_layout` is the function used to layout the `GcBox` with the
                    // metadata stored inside, that means this function has succeeded in the past.
                    unsafe { GcBox::<T>::inner_layout(gc.metadata()).unwrap_unchecked() }
                },
                collect: |gc: GcBox<Erased>, cc: &Collector| {
                    // Safety: The caller of this function is in charge of ensuring that this function
                    // is only called with an erased version of a `GcBox<T>`.
                    let gc: GcBox<T> = unsafe { gc.restore_type() };

                    // Safety: The caller is responsible for ensuring that this function is only called
                    // when the `GcBox` contains initialized data.
                    unsafe { gc.data().trace(cc) };
                },
                drop: |gc: GcBox<Erased>| {
                    // Safety: The caller of this function is in charge of ensuring that this function
                    // is only called with an erased version of a `GcBox<T>`.
                    let gc: GcBox<T> = unsafe { gc.restore_type() };

                    // Safety: The caller is responsible for ensuring that this function is only called
                    // when the `GcBox` contains initialized data.
                    unsafe { core::ptr::drop_in_place(gc.data_ptr()) };
                },
            }
        }
    }
}

unsafe fn rewind_ptr_mut<From, To>(ptr: *mut From) -> *mut To {
    use core::mem::{align_of, size_of};
    let offset = size_of::<To>() + (ptr.addr() % align_of::<To>());
    // Safety: The caller must uphold that there is an instance of `To` in the first available
    // aligned memory location behind `ptr`.
    let ptr = unsafe { ptr.cast::<To>().byte_sub(offset) };
    if ptr.is_aligned() {
        ptr
    } else {
        ptr.with_addr(ptr.addr().next_multiple_of(align_of::<To>()))
    }
}

#[cfg(test)]
#[allow(
    clippy::undocumented_unsafe_blocks,
    clippy::multiple_unsafe_ops_per_block
)]
mod test {
    #[cfg(not(feature = "std"))]
    use alloc::{string::String, vec::Vec};

    use crate::Gc;

    use super::*;

    #[test]
    fn basic_allocation_and_deallocation() {
        let gc = GcBox::<u32>::initialize_box(());
        unsafe { gc.deallocate() };

        let gc = GcBox::<[u8]>::initialize_box(12);
        unsafe { gc.deallocate() };

        let gc = GcBox::<()>::initialize_box(());
        unsafe { gc.deallocate() };

        let gc = GcBox::<String>::initialize_box(());
        unsafe { gc.deallocate() };
    }

    #[test]
    fn basic_data_storage() {
        let gc = GcBox::<u32>::initialize_box(());
        unsafe { gc.data_ptr().write(1234567890) }

        assert_eq!(*unsafe { gc.data() }, 1234567890);
        gc.metadata();

        unsafe { gc.deallocate() };

        let gc = GcBox::<[u8]>::initialize_box(12);
        for i in 0..12 {
            unsafe { gc.data_ptr().cast::<u8>().add(i).write(i as u8) };
        }

        assert_eq!(
            unsafe { gc.data() },
            &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
        );
        assert_eq!(gc.metadata(), 12);

        unsafe { gc.deallocate() };

        let gc = GcBox::<String>::initialize_box(());
        unsafe { gc.data_ptr().write(String::from("Hello, world!")) };

        assert_eq!(&**unsafe { gc.data() }, "Hello, world!");

        unsafe { gc.drop() };
        unsafe { gc.deallocate() };
    }

    #[test]
    fn vtable_tags() {
        let gc = GcBox::<String>::initialize_box(());
        unsafe { gc.data_ptr().write(String::from("Hello, World!")) };

        gc.set_colour(ObjectColour::White);
        assert_eq!(gc.colour(), ObjectColour::White);
        gc.set_colour(ObjectColour::Gray);
        assert_eq!(gc.colour(), ObjectColour::Gray);
        gc.set_colour(ObjectColour::Black);
        assert_eq!(gc.colour(), ObjectColour::Black);

        assert!(!gc.needs_trace());

        unsafe { gc.drop() };
        unsafe { gc.deallocate() };
    }

    #[test]
    fn vtable_functions() {
        let table = GcVTable::new::<i32>();
        let ptr = VTablePtr::new::<i32>();

        assert!(core::ptr::eq(table, ptr.as_ref()));

        let x = [
            ObjectColour::White,
            ObjectColour::Gray,
            ObjectColour::Black,
            ObjectColour::WeakGray,
        ]
        .into_iter()
        .cycle()
        .take(8);
        let y = core::iter::repeat(true)
            .take(4)
            .chain(core::iter::repeat(false).take(4));

        for (colour, needs_trace) in x.zip(y) {
            ptr.set_colour(colour);
            assert_eq!(ptr.get_colour(), colour);
            ptr.set_needs_trace(needs_trace);
            assert_eq!(ptr.get_needs_trace(), needs_trace);

            assert!(core::ptr::eq(table, ptr.as_ref()));
        }
    }

    #[test]
    fn erased_needs_trace() {
        let no_trace1: GcBox<String> = GcBox::initialize_box(());
        let no_trace2: GcBox<Vec<u8>> = GcBox::initialize_box(());
        let no_trace3: GcBox<usize> = GcBox::initialize_box(());
        let no_trace4: GcBox<()> = GcBox::initialize_box(());
        let no_trace5: GcBox<[u32]> = GcBox::initialize_box(12);

        let needs_trace1: GcBox<Vec<Gc<'_, ()>>> = GcBox::initialize_box(());
        let needs_trace2: GcBox<[Gc<'_, u8>]> = GcBox::initialize_box(12);

        assert!(!no_trace1.erase().ptr_needs_trace());
        assert!(!no_trace2.erase().ptr_needs_trace());
        assert!(!no_trace3.erase().ptr_needs_trace());
        assert!(!no_trace4.erase().ptr_needs_trace());
        assert!(!no_trace5.erase().ptr_needs_trace());

        assert!(needs_trace1.erase().ptr_needs_trace());
        assert!(needs_trace2.erase().ptr_needs_trace());

        unsafe { no_trace1.deallocate() };
        unsafe { no_trace2.deallocate() };
        unsafe { no_trace3.deallocate() };
        unsafe { no_trace4.deallocate() };
        unsafe { no_trace5.deallocate() };

        unsafe { needs_trace1.deallocate() };
        unsafe { needs_trace2.deallocate() };
    }
}
