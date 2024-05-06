#![allow(clippy::undocumented_unsafe_blocks)]
use crate::context::Collector;

/// This trait allows for values stored in a garbage collected environment to be safely and
/// precisely traced.
///
/// # Safety
/// To implement this trait on any object these invariants *must* be upheld.
/// - `NEEDS_TRACE` *must* be true if the type can contain a garbage collected pointer. It *may*
/// be true if the type does not contain a garbage collected pointer. For optimization purposes
/// it *should* be false if the type cannot contain a garbage collected pointer.
/// - `trace` *must* call itself on any type it contains which is or contains a garbage collected
/// pointer.
/// - The implementing type *must not* dereference a garbage collected pointer during the calling
/// of the `drop` function, as that pointer may have already been dropped.
pub unsafe trait Collect {
    const NEEDS_TRACE: bool;

    fn trace(&self, _cc: &Collector) {}
}

unsafe impl<T: Collect + 'static> Collect for &'static T {
    const NEEDS_TRACE: bool = false;
}

unsafe impl<T: Collect> Collect for [T] {
    const NEEDS_TRACE: bool = T::NEEDS_TRACE;

    fn trace(&self, cc: &Collector) {
        for el in self {
            el.trace(cc);
        }
    }
}

unsafe impl<T: Collect, const N: usize> Collect for [T; N] {
    const NEEDS_TRACE: bool = T::NEEDS_TRACE;

    fn trace(&self, cc: &Collector) {
        for ele in self {
            ele.trace(cc);
        }
    }
}

macro_rules! impl_collect_static {
    ($($t:ty),+) => {
        $(
            // Safety: `'static` types never need to be traced.
            unsafe impl Collect for $t
            where
                Self: 'static,
            {
                const NEEDS_TRACE: bool = false;
            }
        )+
    };
}

impl_collect_static!(u8, u16, u32, u64, u128, usize);
impl_collect_static!(i8, i16, i32, i64, i128, isize);
impl_collect_static!(());
impl_collect_static!(str, alloc::string::String);
impl_collect_static!(core::ffi::CStr, alloc::ffi::CString);
impl_collect_static!(core::any::TypeId);
#[cfg(feature = "std")]
impl_collect_static!(std::ffi::OsStr, std::ffi::OsString);
#[cfg(feature = "std")]
impl_collect_static!(std::path::Path, std::path::PathBuf);

unsafe impl<T: Collect> Collect for alloc::boxed::Box<T> {
    const NEEDS_TRACE: bool = T::NEEDS_TRACE;

    fn trace(&self, cc: &Collector) {
        (**self).trace(cc)
    }
}

unsafe impl<T: Collect> Collect for alloc::vec::Vec<T> {
    const NEEDS_TRACE: bool = T::NEEDS_TRACE;

    fn trace(&self, cc: &Collector) {
        for e in self {
            e.trace(cc);
        }
    }
}

unsafe impl<T: Collect> Collect for Option<T> {
    const NEEDS_TRACE: bool = T::NEEDS_TRACE;

    fn trace(&self, cc: &Collector) {
        match self {
            Some(val) => val.trace(cc),
            None => {}
        }
    }
}

unsafe impl<T: Collect> Collect for (T,) {
    const NEEDS_TRACE: bool = T::NEEDS_TRACE;

    fn trace(&self, cc: &Collector) {
        self.0.trace(cc)
    }
}

macro_rules! tuple_impl_collect {
    ($($t:ident),+) => {
        unsafe impl<$($t),+> Collect for ($($t),+)
        where $($t: Collect),+ {
            const NEEDS_TRACE: bool = $($t::NEEDS_TRACE)|+;

            fn trace(&self, cc: &Collector) {
                #[allow(non_snake_case)]
                let ($($t),+) = self;
                $($t.trace(cc);)+
            }
        }
    }
}

tuple_impl_collect!(A, B);
tuple_impl_collect!(A, B, C);
tuple_impl_collect!(A, B, C, D);
tuple_impl_collect!(A, B, C, D, E);
tuple_impl_collect!(A, B, C, D, E, F);
tuple_impl_collect!(A, B, C, D, E, F, G);
tuple_impl_collect!(A, B, C, D, E, F, G, H);
tuple_impl_collect!(A, B, C, D, E, F, G, H, I);
tuple_impl_collect!(A, B, C, D, E, F, G, H, I, J);
tuple_impl_collect!(A, B, C, D, E, F, G, H, I, J, K);
tuple_impl_collect!(A, B, C, D, E, F, G, H, I, J, K, L);
