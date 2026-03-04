//! Ownership Basics Examples
//!
//! Demonstrates core ownership concepts: move, copy, clone, and drop.

/// Example 1: Ownership Move
/// 
/// String does not implement Copy, so assignment moves ownership.
/// ```
/// use rust_ownership_decidability::ownership_basics::demonstrate_move;
/// demonstrate_move();
/// ```
pub fn demonstrate_move() {
    let s1 = String::from("hello");
    let s2 = s1; // Ownership moved to s2
    
    // println!("{}", s1); // Error: value borrowed after move
    println!("{}", s2); // OK
}

/// Example 2: Copy Trait
/// 
/// Primitive types implement Copy, so assignment copies the value.
/// ```
/// use rust_ownership_decidability::ownership_basics::demonstrate_copy;
/// demonstrate_copy();
/// ```
pub fn demonstrate_copy() {
    let x = 5;
    let y = x; // x is copied to y
    
    println!("x = {}, y = {}", x, y); // Both valid
}

/// Example 3: Clone Trait
/// 
/// Explicit deep copy for heap-allocated types.
/// ```
/// use rust_ownership_decidability::ownership_basics::demonstrate_clone;
/// demonstrate_clone();
/// ```
pub fn demonstrate_clone() {
    let s1 = String::from("hello");
    let s2 = s1.clone(); // Deep copy
    
    println!("s1 = {}, s2 = {}", s1, s2); // Both valid
}

/// Example 4: Ownership in Functions
/// 
/// Passing a value to a function moves ownership.
pub fn take_ownership(s: String) {
    println!("Taken: {}", s);
} // s dropped here

/// Example 5: Return Value Transfer
/// 
/// Ownership can be returned from functions.
pub fn give_ownership() -> String {
    String::from("given")
}

/// Example 6: Tuple Transfer
/// 
/// Multiple values can be transferred via tuples.
pub fn calculate_and_stringify(x: i32, y: i32) -> (i32, String) {
    let sum = x + y;
    let s = format!("Sum is {}", sum);
    (sum, s)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_copy_behavior() {
        let x = 5;
        let y = x;
        assert_eq!(x, 5); // x still valid
        assert_eq!(y, 5);
    }

    #[test]
    fn test_clone_behavior() {
        let s1 = String::from("test");
        let s2 = s1.clone();
        assert_eq!(s1, "test");
        assert_eq!(s2, "test");
    }

    #[test]
    fn test_function_transfer() {
        let s = String::from("hello");
        take_ownership(s);
        // s is no longer valid here
    }

    #[test]
    fn test_return_transfer() {
        let s = give_ownership();
        assert_eq!(s, "given");
    }

    #[test]
    fn test_tuple_transfer() {
        let (sum, s) = calculate_and_stringify(3, 4);
        assert_eq!(sum, 7);
        assert_eq!(s, "Sum is 7");
    }
}
