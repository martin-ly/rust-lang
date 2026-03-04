//! Smart Pointers Examples
//!
//! Demonstrates Box, Rc, RefCell, and custom smart pointers.

use std::ops::Deref;

/// Example 1: Box<T>
/// 
/// Box allocates data on the heap.
/// ```
/// use rust_ownership_decidability::smart_pointers::box_demo;
/// box_demo();
/// ```
pub fn box_demo() {
    let b = Box::new(5);
    println!("b = {}", b);
    assert_eq!(*b, 5);
}

/// Example 2: Custom Smart Pointer
/// 
/// Implementing a simple Box-like type.
pub struct MyBox<T> {
    data: T,
}

impl<T> MyBox<T> {
    pub fn new(x: T) -> MyBox<T> {
        MyBox { data: x }
    }
}

impl<T> Deref for MyBox<T> {
    type Target = T;
    
    fn deref(&self) -> &T {
        &self.data
    }
}

impl<T> Drop for MyBox<T> {
    fn drop(&mut self) {
        println!("Dropping MyBox!");
    }
}

/// Example 3: Reference Counting (Rc)
/// 
/// Rc enables multiple ownership of immutable data.
/// ```
/// use rust_ownership_decidability::smart_pointers::rc_demo;
/// rc_demo();
/// ```
pub fn rc_demo() {
    use std::rc::Rc;
    
    let data = Rc::new(String::from("shared"));
    println!("Reference count: {}", Rc::strong_count(&data));
    
    let data2 = Rc::clone(&data);
    println!("Reference count: {}", Rc::strong_count(&data));
    
    drop(data2);
    println!("Reference count after drop: {}", Rc::strong_count(&data));
}

/// Example 4: Interior Mutability with RefCell
/// 
/// RefCell enforces borrowing rules at runtime.
/// ```
/// use rust_ownership_decidability::smart_pointers::refcell_demo;
/// refcell_demo();
/// ```
pub fn refcell_demo() {
    use std::cell::RefCell;
    
    let cell = RefCell::new(5);
    
    {
        let mut borrow = cell.borrow_mut();
        *borrow += 1;
    } // mutable borrow ends here
    
    println!("Value: {}", cell.borrow());
}

/// Example 5: Mock with RefCell
/// 
/// Using RefCell to track mutations for testing.
pub struct MockMessenger {
    sent_messages: RefCell<Vec<String>>,
}

impl MockMessenger {
    pub fn new() -> MockMessenger {
        MockMessenger {
            sent_messages: RefCell::new(vec![]),
        }
    }
    
    pub fn send(&self, message: &str) {
        self.sent_messages.borrow_mut().push(message.to_string());
    }
    
    pub fn message_count(&self) -> usize {
        self.sent_messages.borrow().len()
    }
}

use std::cell::RefCell;

/// Example 6: Circular Reference Prevention
/// 
/// Using Weak references to prevent memory leaks.
pub fn weak_reference_demo() {
    use std::rc::{Rc, Weak};
    
    let data = Rc::new(5);
    let weak: Weak<i32> = Rc::downgrade(&data);
    
    if let Some(shared) = weak.upgrade() {
        println!("Value: {}", shared);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_box() {
        let b = Box::new(5);
        assert_eq!(*b, 5);
    }

    #[test]
    fn test_mybox() {
        let b = MyBox::new(5);
        assert_eq!(*b, 5);
    }

    #[test]
    fn test_mock_messenger() {
        let mock = MockMessenger::new();
        mock.send("Hello");
        mock.send("World");
        assert_eq!(mock.message_count(), 2);
    }

    #[test]
    fn test_refcell() {
        let cell = RefCell::new(5);
        *cell.borrow_mut() += 1;
        assert_eq!(*cell.borrow(), 6);
    }
}
