//! Crate B: publicly depends on crate-d with the `std` feature enabled.

/// Returns a greeting produced by crate-d's `std` feature.
pub fn greet() -> String {
    crate_d::std_greeting()
}
