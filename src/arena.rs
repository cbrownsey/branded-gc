#[cfg(not(feature = "std"))]
use alloc::boxed::Box;

use crate::{
    collect::Collect,
    context::{Context, Mutation, Pacing},
};

pub trait Rootable: 'static {
    type Root<'brand>: Collect;
}

pub struct Arena<T: Rootable> {
    root: T::Root<'static>,
    context: Box<Context>,
}

/// Arena is `Send`, as all garbage collected pointers are owned solely by a single arena, and
/// modifications can *only* happen during a closure call.
// Safety: As above
unsafe impl<T: Rootable> Send for Arena<T> {}

/// Arena provides no atomic synchronization, and no guarantees are made that pointers wouldn't be
/// deallocated during another thread's running.
impl<T: Rootable> !Sync for Arena<T> {}

impl<T: Rootable> Arena<T> {
    pub fn new<F>(f: F) -> Self
    where
        F: for<'gc> FnOnce(&Mutation<'gc>) -> T::Root<'gc>,
    {
        let context = Box::new(Context::new());
        context.set_trace_root();

        Arena {
            root: f(Mutation::from_context(&context)),
            context,
        }
    }

    pub fn root<F, R>(&self, f: F) -> R
    where
        F: for<'gc> FnOnce(&T::Root<'gc>, &Mutation<'gc>) -> R,
    {
        let ret = f(&self.root, Mutation::from_context(&self.context));
        ret
    }

    pub fn root_mut<F, R>(&mut self, f: F) -> R
    where
        F: for<'gc> FnOnce(&mut T::Root<'gc>, &Mutation<'gc>) -> R,
    {
        self.context.set_trace_root();
        let ret = f(&mut self.root, Mutation::from_context(&self.context));
        ret
    }

    pub fn step_collect(&self) {
        self.context.do_collection(&self.root);
    }

    pub fn collect_all(&self) {
        let pacing = self.context.pacing();
        self.context.set_pacing(Pacing::MAX);
        self.context.do_collection(&self.root);
        self.context.set_pacing(pacing);
    }
}

struct NullRoot;

impl Rootable for NullRoot {
    type Root<'brand> = NullRoot;
}

// Safety: `NullRoot` contains no pointers.
unsafe impl Collect for NullRoot {
    const NEEDS_TRACE: bool = false;
}

pub fn rootless_arena<F, T>(f: F) -> T
where
    F: for<'gc> FnOnce(&Mutation<'gc>) -> T,
{
    let arena: Arena<NullRoot> = Arena::new(|_| NullRoot);
    arena.root(|_, mt| f(mt))
}
