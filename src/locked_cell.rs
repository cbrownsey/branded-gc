use core::cell::{Cell, OnceCell, RefCell};

use crate::{collect::Collect, write::Unlock};

#[repr(transparent)]
pub struct LockedCell<T: ?Sized>(Cell<T>);

// Safety: `LockedCell` only provicdes interior mutability through a write barrier.
unsafe impl<T: Collect + Copy> Collect for LockedCell<T> {
    const NEEDS_TRACE: bool = T::NEEDS_TRACE;

    fn trace(&self, cc: &crate::context::Collector) {
        self.0.get().trace(cc);
    }
}

impl<T> Unlock for LockedCell<T> {
    type Unlocked = Cell<T>;

    unsafe fn unlock_unchecked(&self) -> &Self::Unlocked {
        &self.0
    }
}

impl<T> LockedCell<T> {
    /// Creates a new `LockedCell` containing the given value.
    ///
    /// # Examples
    /// ```
    /// use branded_gc::locked_cell::LockedCell;
    ///
    /// let c = LockedCell::new(5);
    /// ```
    pub fn new(val: T) -> Self {
        Self(Cell::new(val))
    }

    /// Unwraps the value, consuming the locked cell.
    ///
    /// # Examples
    /// ```
    /// use branded_gc::locked_cell::LockedCell;
    ///
    /// let c = LockedCell::new(5);
    /// let five = c.into_inner();
    ///
    /// assert_eq!(five, 5);
    /// ```
    pub fn into_inner(self) -> T {
        self.0.into_inner()
    }
}

impl<T> LockedCell<T>
where
    T: Copy,
{
    /// Returns a copy of the contained value.
    ///
    /// # Examples
    /// ```
    /// use branded_gc::locked_cell::LockedCell;
    ///
    /// let c = LockedCell::new(5);
    ///
    /// let five = c.get();
    /// # assert_eq!(five, 5);
    /// ```
    pub fn get(&self) -> T {
        self.0.get()
    }
}

impl<T> LockedCell<T>
where
    T: ?Sized,
{
    /// Returns a raw pointer to the underlying data in this cell. Modifying this pointer is
    /// subject to all rules regarding adopting garbage collected pointers.
    ///
    /// # Examples
    /// ```
    /// use branded_gc::locked_cell::LockedCell;
    ///
    /// let c = LockedCell::new(5);
    ///
    /// let ptr = c.as_ptr();
    /// ```
    pub fn as_ptr(&self) -> *mut T {
        self.0.as_ptr()
    }

    /// Returns a mutable reference to the underlying data.
    ///
    /// This call borrows `LockedCell` mutably (at compile time) which guarantees that this is the
    /// only reference, and that the parent garbage collected pointer (if any) has had a write
    /// barrier triggered.
    ///
    /// # Examples
    /// ```
    /// use branded_gc::locked_cell::LockedCell;
    /// let mut c = LockedCell::new(5);
    /// *c.get_mut() += 1;
    ///
    /// assert_eq!(c.get(), 6);
    /// ```
    pub fn get_mut(&mut self) -> &mut T {
        self.0.get_mut()
    }
}

impl<T: core::fmt::Debug + Copy> core::fmt::Debug for LockedCell<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_tuple("LockedCell").field(&self.0.get()).finish()
    }
}

impl<T: Copy> Clone for LockedCell<T> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<T: Default> Default for LockedCell<T> {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl<T: PartialEq + Copy> PartialEq for LockedCell<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<T: Eq + Copy> Eq for LockedCell<T> {}

impl<T: PartialOrd + Copy> PartialOrd for LockedCell<T> {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        self.0.partial_cmp(&other.0)
    }
}

impl<T: Ord + Copy> Ord for LockedCell<T> {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.0.cmp(&other.0)
    }
}

impl<T> From<T> for LockedCell<T> {
    fn from(value: T) -> Self {
        LockedCell::new(value)
    }
}

#[repr(transparent)]
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct LockedRefCell<T: ?Sized>(RefCell<T>);

// Safety: `LockedRefCell` only provicdes interior mutability through a write barrier.
unsafe impl<T: Collect> Collect for LockedRefCell<T> {
    const NEEDS_TRACE: bool = T::NEEDS_TRACE;

    fn trace(&self, cc: &crate::context::Collector) {
        self.0.borrow().trace(cc)
    }
}

impl<T> Unlock for LockedRefCell<T> {
    type Unlocked = RefCell<T>;

    unsafe fn unlock_unchecked(&self) -> &Self::Unlocked {
        &self.0
    }
}

impl<T> LockedRefCell<T> {
    /// Creates a new `LockedRefCell` containing `value`.
    ///
    /// # Examples
    /// ```
    /// use branded_gc::locked_cell::LockedRefCell;
    ///
    /// let c = LockedRefCell::new(5);
    /// ```
    pub fn new(value: T) -> Self {
        Self(RefCell::new(value))
    }

    /// Consumes the `LockedRefCell`, returning the wrapped value.
    ///
    /// # Examples
    /// ```
    /// use branded_gc::locked_cell::LockedRefCell;
    ///
    /// let c = LockedRefCell::new(5);
    ///
    /// let five = c.into_inner();
    /// # assert_eq!(five, 5);
    /// ```
    pub fn into_inner(self) -> T {
        self.0.into_inner()
    }
}

impl<T> LockedRefCell<T>
where
    T: ?Sized,
{
    /// Immutably borrows the contained value.
    ///
    /// This borrow lasts until the returned `Ref` exits scope. Multiple immutable borrows can be
    /// taken out at the same time.
    ///
    /// # Panics
    /// Panics if the value is currently mutably borrowed. For a non-panicking variant, use
    /// [`try_borrow`].
    ///
    /// # Examples
    /// ```
    /// use branded_gc::locked_cell::LockedRefCell;
    ///
    /// let c = LockedRefCell::new(5);
    ///
    /// let borrowed_five = c.borrow();
    /// let borrowed_five2 = c.borrow();
    /// # assert_eq!(*borrowed_five, 5);
    /// # assert!(core::ptr::eq(&*borrowed_five, &*borrowed_five2));
    /// ```
    pub fn borrow(&self) -> core::cell::Ref<'_, T> {
        self.0.borrow()
    }

    /// Immutably borrows the wrapped value, returning an error if the value is currently mutably borrowed.
    ///
    /// The borrow lasts until the returned Ref exits scope. Multiple immutable borrows can be taken out at the same time.
    ///
    /// This is the non-panicking variant of borrow.
    ///
    /// # Examples
    /// ```
    /// use branded_gc::{write::Barrier, locked_cell::LockedRefCell};
    ///
    /// let c = LockedRefCell::new(5);
    /// let b = Barrier::from_static(&c);
    ///
    /// {
    ///     let m = b.unlock().borrow_mut();
    ///     assert!(b.try_borrow().is_err());
    /// }
    ///
    /// {
    ///     let m = b.borrow();
    ///     assert!(b.try_borrow().is_ok());
    /// }
    /// ```
    pub fn try_borrow(&self) -> Result<core::cell::Ref<'_, T>, core::cell::BorrowError> {
        self.0.try_borrow()
    }

    /// Returns a raw pointer to the underlying data in this cell. Modifying this pointer is
    /// subject to all rules regarding adopting garbage collected pointers.
    ///
    /// # Examples
    /// ```
    /// use branded_gc::locked_cell::LockedCell;
    ///
    /// let c = LockedCell::new(5);
    ///
    /// let ptr = c.as_ptr();
    /// ```
    pub fn as_ptr(&self) -> *mut T {
        self.0.as_ptr()
    }

    pub fn get_mut(&mut self) -> &mut T {
        self.0.get_mut()
    }
}

#[repr(transparent)]
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct LockedOnceCell<T>(OnceCell<T>);

// Safety: `LockedOnceCell` only provicdes interior mutability through a write barrier.
unsafe impl<T: Collect> Collect for LockedOnceCell<T> {
    const NEEDS_TRACE: bool = T::NEEDS_TRACE;

    fn trace(&self, cc: &crate::context::Collector) {
        if let Some(val) = self.0.get() {
            val.trace(cc);
        }
    }
}

impl<T> Unlock for LockedOnceCell<T> {
    type Unlocked = OnceCell<T>;

    unsafe fn unlock_unchecked(&self) -> &Self::Unlocked {
        &self.0
    }
}

impl<T> LockedOnceCell<T> {
    pub fn new() -> Self {
        Self(OnceCell::new())
    }
}

impl<T> From<T> for LockedOnceCell<T> {
    fn from(value: T) -> Self {
        LockedOnceCell(OnceCell::from(value))
    }
}
