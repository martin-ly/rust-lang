//! Crate A: depends on B and C, and directly on D with the serde feature.
//!
//! This binary exercises the feature-unification path through a public
//! dependency chain under Cargo resolver v3.

fn main() {
    println!("B: {}", crate_b::greet());
    println!("C: {}", crate_c::greet());
    println!("D (serde): {}", crate_d::serde_greeting());
}
