#![cfg_attr(not(feature = "std"), no_std)]
#![feature(
    ptr_metadata,
    pointer_is_aligned_to,
    lint_reasons,
    strict_provenance,
    negative_impls
)]
#![allow(unstable_name_collisions)]
#![warn(
    clippy::panic,
    clippy::unwrap_used,
    clippy::undocumented_unsafe_blocks,
    clippy::multiple_unsafe_ops_per_block,
    fuzzy_provenance_casts
)]

extern crate alloc;

mod arena;
mod collect;
mod context;
mod gc;
mod gc_box;
pub mod locked_cell;
pub mod metasized;
mod slicetail;
pub mod write;

pub use arena::{rootless_arena, Arena, Rootable};
pub use collect::Collect;
pub use context::{Collector, Mutation, Pacing};
pub use gc::Gc;

pub type PhantomInvariant<'gc> = core::marker::PhantomData<fn(&'gc mut ()) -> &'gc mut ()>;

pub(crate) trait CellUpdatePolyfill<T> {
    fn update<F>(&self, f: F) -> T
    where
        F: FnOnce(T) -> T,
        T: Copy;
}

impl<T> CellUpdatePolyfill<T> for core::cell::Cell<T> {
    fn update<F>(&self, f: F) -> T
    where
        F: FnOnce(T) -> T,
        T: Copy,
    {
        let val = f(self.get());
        self.set(val);
        val
    }
}
