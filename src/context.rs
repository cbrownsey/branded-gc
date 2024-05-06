use crate::CellUpdatePolyfill;

use core::{
    cell::{Cell, RefCell},
    ptr,
};

#[allow(unused_imports)]
use alloc::{collections::VecDeque, vec::Vec};

use crate::{
    collect::Collect,
    gc_box::{Erased, GcBox},
    metasized::MetaSized,
    PhantomInvariant,
};

#[repr(transparent)]
pub struct Mutation<'gc>(Context, PhantomInvariant<'gc>);

impl<'gc> Mutation<'gc> {
    pub(crate) fn from_context(ctx: &Context) -> &Mutation<'gc> {
        // Safety: `Mutation` is a transparent wrapper around a `Context`.
        unsafe { &*ptr::from_ref(ctx).cast::<Self>() }
    }

    pub(crate) fn as_context(&self) -> &Context {
        &self.0
    }

    pub(crate) fn adopt_box(&self, gc: GcBox<Erased>) {
        self.as_context().adopt_box(gc);
    }
}

#[repr(transparent)]
pub struct Collector(Context);

impl Collector {
    pub(crate) fn from_context(ctx: &Context) -> &Collector {
        // Safety: `Collector` is a transparent wrapper around a `Context`.
        unsafe { &*ptr::from_ref(ctx).cast::<Self>() }
    }

    pub(crate) fn to_context(&self) -> &Context {
        &self.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub enum ObjectColour {
    #[default]
    White,
    WeakGray,
    Gray,
    Black,
}

impl ObjectColour {
    const WHITE_TAG: usize = 0b00;
    const DEAD_TAG: usize = 0b01;
    const GRAY_TAG: usize = 0b10;
    const BLACK_TAG: usize = 0b11;

    pub fn to_tag(self) -> usize {
        match self {
            ObjectColour::White => Self::WHITE_TAG,
            ObjectColour::WeakGray => Self::DEAD_TAG,
            ObjectColour::Gray => Self::GRAY_TAG,
            ObjectColour::Black => Self::BLACK_TAG,
        }
    }

    pub fn from_tag(val: usize) -> Self {
        match val & 0b11 {
            Self::WHITE_TAG => Self::White,
            Self::GRAY_TAG => Self::Gray,
            Self::BLACK_TAG => Self::Black,
            Self::DEAD_TAG => Self::WeakGray,
            _ => unreachable!(),
        }
    }
}

/// A structure containing the parameters for how often, and how quickly to move through the
/// collection phases of a given [`Arena`].
///
/// The parameters contained are
/// - `trigger_multiplier`: If the [`Arena`] is currently in the sleep phase, then it will exit
/// the sleep phase when the equation `allocated > max_heap * (trigger_multiplier / 100 + 1)`,
/// where `allocated` is the number of bytes currently allocated, and `max_heap` is the largest
/// number of allocated bytes at the end of a previous sweep phase.
/// - `mark_stride`: If the [`Arena`] is in the mark phase, then it will mark up to `mark_stride`
/// number of objects.
/// - `sweep_stride`: If the [`Arena`] is in the sweep phase, then it will drop and deallocate up
/// to `sweep_stride` number of objects.
///
/// [`Arena`]: crate::Arena
#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
pub struct Pacing {
    /// Exit sleep phase when `allocated > max_active_heap * (trigger_multiplier / 100 + 1)`.
    trigger_multiplier: usize,
    // The number of objects to mark per collect call, skipping objects that don't need marking.
    mark_stride: usize,
    // The number of objects to deallocate per collect call.
    sweep_stride: usize,
}

impl Pacing {
    pub const MAX: Self = Self {
        trigger_multiplier: 0,
        mark_stride: usize::MAX,
        sweep_stride: usize::MAX,
    };

    pub const fn new(trigger_multiplier: usize, mark_stride: usize, sweep_stride: usize) -> Self {
        assert!(trigger_multiplier > 0);
        assert!(mark_stride > 0);
        assert!(sweep_stride > 0);
        Self {
            trigger_multiplier,
            mark_stride,
            sweep_stride,
        }
    }

    pub const fn multiplier(&self) -> usize {
        self.trigger_multiplier
    }

    pub const fn mark_stride(&self) -> usize {
        self.mark_stride
    }

    pub const fn sweep_stride(&self) -> usize {
        self.sweep_stride
    }
}

/// Creates a pacing with default parameters of a trigger multiplier of 175%, a mark stride of 32
/// objects, and a sweep stride of 8 objects.
impl Default for Pacing {
    fn default() -> Self {
        Self::new(75, 32, 8)
    }
}

#[derive(Debug, Clone, Default)]
pub struct Context {
    /// A list of all `GcBox` allocated with this context in no particular order.
    objects: RefCell<Vec<GcBox<Erased>>>,
    /// A list of all `GcBox` that have been marked gray during the current `Mark` phase.
    trace_queue: RefCell<VecDeque<GcBox<Erased>>>,
    trace_root: Cell<bool>,
    /// A list of all `GcBox` that were allocated during the `Sweep` phase.
    fresh_objects: RefCell<Vec<GcBox<Erased>>>,

    phase: Cell<Phase>,
    sweep_position: Cell<usize>,

    /// The largest sum of all allocations that have been marked and not swept at the end of each
    /// collection cycle.
    lifetime_max_heap: Cell<usize>,
    allocated: Cell<usize>,

    pacing: Cell<Pacing>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Phase {
    #[default]
    Sleep,
    Mark,
    Sweep,
}

impl Context {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn phase(&self) -> Phase {
        self.phase.get()
    }

    pub fn pacing(&self) -> Pacing {
        self.pacing.get()
    }

    pub fn set_pacing(&self, pacing: Pacing) {
        self.pacing.set(pacing);
    }

    pub fn set_trace_root(&self) {
        self.trace_root.set(true);
    }

    pub(crate) fn trace(&self, gc_box: GcBox<Erased>) {
        match gc_box.colour() {
            ObjectColour::Gray | ObjectColour::Black => {}
            ObjectColour::White => {
                self.trace_queue.borrow_mut().push_back(gc_box);
                gc_box.set_colour(ObjectColour::Gray);
            }
            ObjectColour::WeakGray => todo!(),
        }
    }

    pub(crate) fn make_gray(&self, gc_box: GcBox<Erased>) {
        match self.phase() {
            Phase::Sleep => {}
            Phase::Mark => self.trace_queue.borrow_mut().push_back(gc_box),
            Phase::Sweep => {}
        }
    }

    /// Determines if this context should proceed from the `Sleep` phase.
    fn should_proceed(&self) -> bool {
        let threshold = self
            .lifetime_max_heap
            .get()
            .saturating_mul(self.pacing.get().trigger_multiplier.saturating_add(100))
            / 100;

        self.allocated.get() > threshold
    }

    pub fn do_collection<R: Collect>(&self, root: &R) {
        loop {
            match self.phase() {
                Phase::Sleep => {
                    if self.should_proceed() {
                        self.phase.set(Phase::Mark);
                        continue;
                    } else {
                        return;
                    }
                }
                Phase::Mark => {
                    let cc = Collector::from_context(self);
                    let stride = self.pacing().mark_stride;
                    let mut queue = self.trace_queue.borrow_mut();
                    let mut marked = 0;

                    if self.trace_root.get() {
                        let queue_len = queue.len();
                        root.trace(cc);
                        marked += queue.len() - queue_len;

                        if marked >= stride {
                            return;
                        }
                    }

                    while let Some(obj) = queue.pop_front() {
                        let queue_len = queue.len();

                        if obj.ptr_needs_trace() {
                            // Safety: Objects allocated in a context must be initialized.
                            unsafe { obj.collect(cc) };
                            obj.set_colour(ObjectColour::Black);

                            marked += queue.len() - queue_len;

                            if marked >= stride {
                                return;
                            }
                        }
                    }

                    debug_assert!(queue.is_empty());
                    debug_assert!(self
                        .objects
                        .borrow()
                        .iter()
                        .all(|o| matches!(o.colour(), ObjectColour::Black | ObjectColour::White)));
                    self.sweep_position.set(0);
                    self.phase.set(Phase::Sweep);
                    continue;
                }
                Phase::Sweep => {
                    let stride = self.pacing().sweep_stride;
                    let mut objects = self.objects.borrow_mut();
                    let mut swept = 0;

                    let mut idx = self.sweep_position.get();
                    loop {
                        if idx >= objects.len() {
                            break;
                        }

                        let obj = objects[idx];
                        if obj.colour() == ObjectColour::White {
                            // Safety:
                            // - All objects stored in a context must be initialized.
                            // - This object has been marked as white, meaning it is not being held
                            // by user code.
                            unsafe { objects[idx].drop() };
                            // Safety: As above.
                            unsafe { self.deallocate_box(objects[idx]) };
                            swept += 1;

                            objects.swap_remove(idx);
                        } else {
                            // N.B when an object is removed from the list, that index needs to be
                            // checked again
                            idx += 1;
                        }

                        if swept >= stride {
                            return;
                        }
                    }

                    self.phase.set(Phase::Sleep);
                    continue;
                }
            }
        }
    }

    pub fn track_allocation(&self, bytes: usize) {
        self.allocated.update(|n| n + bytes);
    }

    pub fn untrack_allocation(&self, bytes: usize) {
        self.allocated.update(|n| n - bytes);
    }

    pub(crate) fn adopt_box(&self, gc: GcBox<Erased>) {
        self.track_allocation(gc.layout().0.size());
        // Fresh allocations are coloured white, and so if they are made during the sweep phase,
        // they were never marked and so should be held until the next collection cycle.
        match self.phase() {
            Phase::Sleep | Phase::Mark => self.objects.borrow_mut().push(gc),
            Phase::Sweep => self.fresh_objects.borrow_mut().push(gc),
        }
    }

    pub(crate) unsafe fn deallocate_box<T: ?Sized + MetaSized>(&self, gc: GcBox<T>) {
        self.untrack_allocation(gc.layout().0.size());
        // Safety: The closure deallocated with the global allocator, which is the same allocator
        // that allocated.
        unsafe { gc.deallocate() }
    }
}

impl Drop for Context {
    fn drop(&mut self) {
        for obj in core::mem::take(&mut self.objects).into_inner().into_iter() {
            // Safety: All erased boxes saved in a context are initialized.
            unsafe { obj.drop() };
            // Safety: All erased boxes saved in a context are allocated.
            unsafe { self.deallocate_box(obj) };
        }
    }
}
