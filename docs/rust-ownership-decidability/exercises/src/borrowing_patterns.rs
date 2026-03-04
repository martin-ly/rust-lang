//! Borrowing Patterns Examples
//!
//! Demonstrates immutable borrowing, mutable borrowing, and reborrowing.

/// Example 1: Immutable Borrowing
/// 
/// Multiple immutable borrows are allowed.
/// ```
/// use rust_ownership_decidability::borrowing_patterns::immutable_borrow_demo;
/// immutable_borrow_demo();
/// ```
pub fn immutable_borrow_demo() {
    let s = String::from("hello");
    
    let r1 = &s;
    let r2 = &s;
    
    println!("{} and {}", r1, r2); // Both valid
}

/// Example 2: Mutable Borrowing
/// 
/// Only one mutable borrow is allowed at a time.
/// ```
/// use rust_ownership_decidability::borrowing_patterns::mutable_borrow_demo;
/// mutable_borrow_demo();
/// ```
pub fn mutable_borrow_demo() {
    let mut s = String::from("hello");
    
    let r = &mut s;
    r.push_str(", world");
    
    println!("{}", r);
}

/// Example 3: Non-Lexical Lifetimes (NLL)
/// 
/// Borrow scopes end at last use, not at end of block.
/// ```
/// use rust_ownership_decidability::borrowing_patterns::nll_demo;
/// nll_demo();
/// ```
pub fn nll_demo() {
    let mut s = String::from("hello");
    
    let r1 = &s;
    println!("{}", r1); // r1's last use
    
    // r1 is no longer used, so we can borrow mutably
    let r2 = &mut s;
    r2.push_str("!");
    println!("{}", r2);
}

/// Example 4: Reborrowing
/// 
/// A mutable reference can be temporarily reborrowed.
pub fn reborrow_demo() {
    let mut s = String::from("hello");
    let r1 = &mut s;
    
    // Reborrow r1
    let r2 = &mut *r1;
    r2.push_str(" world");
    
    // r2 ends here, r1 is valid again
    println!("{}", r1);
}

/// Example 5: Slice Borrowing
/// 
/// Borrowing a slice of a vector.
pub fn slice_borrow_demo() {
    let v = vec![1, 2, 3, 4, 5];
    let slice = &v[1..4];
    
    assert_eq!(slice, &[2, 3, 4]);
}

/// Example 6: The Borrow Checker at Work
/// 
/// This demonstrates why the borrow checker prevents data races.
pub fn borrow_checker_prevents_race() {
    let mut data = vec![1, 2, 3];
    
    // Immutable borrow
    let first = &data[0];
    
    // Cannot mutate while immutable borrow is active
    // data.push(4); // Error!
    
    println!("First: {}", first);
    
    // Now we can mutate
    data.push(4);
    println!("Data: {:?}", data);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_immutable_borrow() {
        let s = String::from("test");
        let r1 = &s;
        let r2 = &s;
        assert_eq!(*r1, "test");
        assert_eq!(*r2, "test");
    }

    #[test]
    fn test_mutable_borrow() {
        let mut s = String::from("hello");
        let r = &mut s;
        r.push_str(" world");
        assert_eq!(*r, "hello world");
    }

    #[test]
    fn test_nll() {
        let mut s = String::from("hello");
        let r1 = &s;
        println!("{}", r1); // Last use of r1
        
        let r2 = &mut s;
        r2.push_str("!");
        assert_eq!(*r2, "hello!");
    }

    #[test]
    fn test_slice_borrow() {
        let v = vec![1, 2, 3, 4, 5];
        let slice = &v[1..4];
        assert_eq!(slice, &[2, 3, 4]);
    }
}
