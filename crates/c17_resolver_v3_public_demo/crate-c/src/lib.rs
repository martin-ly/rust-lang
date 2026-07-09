//! Crate C: publicly depends on crate-d with the `alloc` feature enabled.

/// Returns a greeting produced by crate-d's `alloc` feature.
pub fn greet() -> String {
    crate_d::alloc_greeting()
}
