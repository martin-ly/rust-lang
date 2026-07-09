//! Shared crate D with additive, non-exclusive features.
//!
//! Each feature gates a single greeting function. Features are designed to be
//! additive so that Cargo's feature unification can safely enable their union.

/// Greeting available when the `std` feature is enabled.
#[cfg(feature = "std")]
pub fn std_greeting() -> String {
    "Hello from crate-d / std feature".to_string()
}

/// Greeting available when the `alloc` feature is enabled.
#[cfg(feature = "alloc")]
pub fn alloc_greeting() -> String {
    "Hello from crate-d / alloc feature".to_string()
}

/// Greeting available when the `serde` feature is enabled.
#[cfg(feature = "serde")]
pub fn serde_greeting() -> String {
    "Hello from crate-d / serde feature".to_string()
}
