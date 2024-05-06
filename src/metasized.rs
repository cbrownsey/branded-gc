use core::{
    alloc::{Layout, LayoutError},
    ptr::Pointee,
};

/// A shim trait for types whose size and alignment are known fully from the metadata associated
/// with them, that is the length being the metadata for a slice, and the unit type being the
/// metadata for any `Sized` type.
///
/// # Safety
/// The returned layout *must* be valid for any and all instances of that type whose metadata is
/// the same as the metadata passed into this function.
pub unsafe trait MetaSized: Pointee {
    fn layout(meta: Self::Metadata) -> Result<Layout, LayoutError>;
}

// Safety: Sized types have a layout given by `Layout::new`.
unsafe impl<T> MetaSized for T {
    fn layout(_meta: Self::Metadata) -> Result<Layout, LayoutError> {
        Ok(Layout::new::<T>())
    }
}

// Safety: Slices have a layout given by `Layout::array`.
unsafe impl<T> MetaSized for [T] {
    fn layout(meta: usize) -> Result<Layout, LayoutError> {
        Layout::array::<T>(meta)
    }
}

// Safety: The `str` type has the same layout as `[u8]`.
unsafe impl MetaSized for str {
    fn layout(meta: usize) -> Result<Layout, LayoutError> {
        Layout::array::<u8>(meta)
    }
}
