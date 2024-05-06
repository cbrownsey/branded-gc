use core::alloc::Layout;

use crate::{metasized::MetaSized, Collect};

/// A good-enough-for-now type to emulate dynamically sized types, specifically ones that have a
/// slice as their last field.
#[repr(C)]
pub struct SliceTailed<T, S> {
    pub head: T,
    pub tail: [S],
}

// Safety: SliceTailed is repr(C)
unsafe impl<T, S> MetaSized for SliceTailed<T, S> {
    fn layout(meta: Self::Metadata) -> Result<core::alloc::Layout, core::alloc::LayoutError> {
        Ok(Layout::new::<T>().extend(Layout::array::<S>(meta)?)?.0)
    }
}

// Safety: Trivial.
unsafe impl<T: Collect, S: Collect> Collect for SliceTailed<T, S> {
    const NEEDS_TRACE: bool = T::NEEDS_TRACE || S::NEEDS_TRACE;

    fn trace(&self, cc: &crate::Collector) {
        self.head.trace(cc);
        for elem in &self.tail {
            elem.trace(cc);
        }
    }
}

impl<T, S> SliceTailed<T, S> {
    pub(crate) fn tail_offset() -> usize {
        Layout::new::<T>()
            .extend(Layout::new::<S>())
            .expect("two sized types should never overflow")
            .1
    }
}
