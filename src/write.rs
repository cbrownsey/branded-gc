/// A wrapper around a reference, the existence of which guarantees that the closest paret `Gc`
/// pointer has had a write barrier triggered upon it.
#[repr(transparent)]
pub struct Barrier<T: ?Sized>(T);

impl<T: ?Sized> Barrier<T> {
    /// Create a barrier around the given reference.
    ///
    /// # Safety
    /// Creating this write barrier cannot allow any interior mutability to adopt a garbage
    /// collected pointer without marking the closest parent pointer as gray.   
    pub unsafe fn new_unchecked(val: &T) -> &Barrier<T> {
        // Safety: This cast is valid as `Barrier` is `repr(transparent)`.
        unsafe { &*(val as *const T as *const Barrier<T>) }
    }

    /// Creates a barrier around the given reference. This is sound because any type `T` where
    /// `T: 'static` cannot ever hold or adopt a garbage collected pointer.
    pub fn from_static(val: &T) -> &Barrier<T>
    where
        T: 'static,
    {
        // Safety: A static value cannot possibly contain a garbage collected pointer.
        unsafe { Barrier::new_unchecked(val) }
    }

    /// Removes the barrier from around some data.
    pub fn remove_barrier(&self) -> &T {
        &self.0
    }

    /// Unlocks the contained locked mutability primitive
    pub fn unlock(&self) -> &T::Unlocked
    where
        T: Unlock,
    {
        // Safety: The purpose of `Barrier` is to statically guarantee that the containing `Gc` has
        // been marked as gray.
        unsafe { self.remove_barrier().unlock_unchecked() }
    }

    /// Project a barrier around an object into a barrier around some data contained within that
    /// object.
    ///
    /// # Safety
    /// The only condition for this function to be safe is that the field pointer must be valid,
    /// point to initialized data, and be contained entirely within the `&self` object.
    pub unsafe fn project_into_unchecked<U>(&self, field: *const U) -> &Barrier<U> {
        // Safety: The containing object already had a write barrier, and since the caller
        // guarantees that this pointer is within the same allocation, it must have the same
        // parent gc, which was marked as gray already.
        unsafe { &*(field as *const Barrier<U>) }
    }
}

impl<T: ?Sized> core::ops::Deref for Barrier<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T: ?Sized> core::ops::DerefMut for Barrier<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

/// Projects a `Barrier` reference into one of its fields, and returns a
/// reference to that field wrapped in a barrier.
#[macro_export]
macro_rules! project_barrier {
    ($e:expr, $field:tt) => {{
        let barrier: &$crate::write::Barrier<_> = $e;
        let val = barrier.remove_barrier();
        unsafe { barrier.unsafe_project(::core::ptr::addr_of!(val.$field)) }
    }};
}

/// A trait to provide interior mutability primitives with a mechanism for safely editing the
/// contents of a garbage collected pointer, ensuring that a write barrier is triggered.
pub trait Unlock {
    type Unlocked;

    /// # Safety
    /// The containing `Gc` must have a write barrier triggered on it.
    unsafe fn unlock_unchecked(&self) -> &Self::Unlocked;
}
