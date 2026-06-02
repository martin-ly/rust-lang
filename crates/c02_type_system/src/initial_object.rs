//! Initial Object — Category Theory Concept
//!
//! In category theory, an initial object is an object from which there exists
//! a unique morphism to every other object. It is the "sender" that can map
//! to any other object via a unique morphism.
//!
//! # Rust Analogy
//!
//! `Option<T>::None` can be viewed as an initial object because for any type `T`,
//! `None` represents a missing value — a morphism from the initial object to `T`.

/// Convert any value to `None`, demonstrating the initial object concept.
///
/// In category-theoretic terms, this is the unique morphism from the
/// initial object to `Option<T>`.
#[allow(dead_code)]
pub fn to_option<T>(_: T) -> Option<T> {
    None
}
