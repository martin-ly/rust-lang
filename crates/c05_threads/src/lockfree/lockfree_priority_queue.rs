// Stub module for lock-free priority queue; implementation to be added.
use std::marker::PhantomData;

pub struct LockFreePriorityQueue<T> {
    _marker: PhantomData<T>,
}

impl<T> LockFreePriorityQueue<T> {
    pub fn new() -> Self {
        Self {
            _marker: PhantomData,
        }
    }
}
