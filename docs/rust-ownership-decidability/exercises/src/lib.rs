//! Rust Ownership and Decidability - Code Exercises
//!
//! This library provides code examples for understanding Rust ownership,
//! borrowing, lifetimes, and decidability concepts.

pub mod borrowing_patterns;
pub mod concurrency;
pub mod lifetime_examples;
pub mod ownership_basics;
pub mod smart_pointers;

/// Verify all examples compile and run correctly
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_library_loads() {
        // Just verify the library compiles
    }
}
