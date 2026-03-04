//! Integration Tests for Rust Ownership and Decidability
//!
//! These tests verify all examples compile and behave correctly.

use rust_ownership_decidability::*;
use std::sync::{Arc, Mutex};
use std::thread;

// ============================================================================
// Ownership Tests
// ============================================================================

#[test]
fn test_ownership_basics() {
    ownership_basics::demonstrate_move();
    ownership_basics::demonstrate_copy();
    ownership_basics::demonstrate_clone();
}

#[test]
fn test_ownership_transfer_in_functions() {
    let s = String::from("test");
    ownership_basics::take_ownership(s);
    // s is no longer valid
}

#[test]
fn test_ownership_return() {
    let s = ownership_basics::give_ownership();
    assert_eq!(s, "given");
}

#[test]
fn test_tuple_transfer() {
    let (sum, s) = ownership_basics::calculate_and_stringify(10, 20);
    assert_eq!(sum, 30);
    assert_eq!(s, "Sum is 30");
}

// ============================================================================
// Borrowing Tests
// ============================================================================

#[test]
fn test_immutable_borrow() {
    borrowing_patterns::immutable_borrow_demo();
}

#[test]
fn test_mutable_borrow() {
    borrowing_patterns::mutable_borrow_demo();
}

#[test]
fn test_nll() {
    borrowing_patterns::nll_demo();
}

#[test]
fn test_reborrow() {
    borrowing_patterns::reborrow_demo();
}

#[test]
fn test_slice_borrow() {
    borrowing_patterns::slice_borrow_demo();
}

#[test]
fn test_borrow_prevention() {
    borrowing_patterns::borrow_checker_prevents_race();
}

// ============================================================================
// Lifetime Tests
// ============================================================================

#[test]
fn test_longest_function() {
    let s1 = String::from("longer string here");
    let s2 = "short";
    let result = lifetime_examples::longest(&s1, s2);
    assert_eq!(result, "longer string here");
}

#[test]
fn test_lifetime_struct() {
    let text = String::from("hello world");
    let excerpt = lifetime_examples::ImportantExcerpt { part: &text[0..5] };
    assert_eq!(excerpt.part(), "hello");
}

#[test]
fn test_first_word() {
    let s = "hello world";
    assert_eq!(lifetime_examples::first_word_elided(s), "hello");
    
    let s = "nowords";
    assert_eq!(lifetime_examples::first_word_elided(s), "nowords");
}

#[test]
fn test_static_lifetime() {
    let s = lifetime_examples::get_static_string();
    assert_eq!(s, "I live forever!");
}

#[test]
fn test_multiple_lifetimes() {
    let s1 = String::from("first");
    let s2 = String::from("second");
    let result = lifetime_examples::mix_lifetimes(&s1, &s2);
    assert_eq!(result, "first");
}

#[test]
fn test_lifetime_wrapper() {
    let data = 42;
    let wrapper = lifetime_examples::Wrapper::new(&data);
    assert_eq!(*wrapper.get(), 42);
}

#[test]
fn test_parser_trait() {
    use lifetime_examples::Parser;
    let parser = lifetime_examples::WordParser;
    assert_eq!(parser.parse("hello world"), Some("hello"));
    assert_eq!(parser.parse(""), None);
}

// ============================================================================
// Smart Pointer Tests
// ============================================================================

#[test]
fn test_box() {
    smart_pointers::box_demo();
}

#[test]
fn test_mybox() {
    let b = smart_pointers::MyBox::new(42);
    assert_eq!(*b, 42);
}

#[test]
fn test_rc() {
    smart_pointers::rc_demo();
}

#[test]
fn test_refcell() {
    smart_pointers::refcell_demo();
}

#[test]
fn test_mock_messenger() {
    let mock = smart_pointers::MockMessenger::new();
    mock.send("Message 1");
    mock.send("Message 2");
    assert_eq!(mock.message_count(), 2);
}

#[test]
fn test_weak_reference() {
    smart_pointers::weak_reference_demo();
}

// ============================================================================
// Concurrency Tests
// ============================================================================

#[test]
fn test_spawn() {
    concurrency::spawn_demo();
}

#[test]
fn test_move_closure() {
    concurrency::move_closure_demo();
}

#[test]
fn test_arc() {
    concurrency::arc_demo();
}

#[test]
fn test_mutex() {
    concurrency::mutex_demo();
}

#[test]
fn test_scoped_threads() {
    concurrency::scoped_threads_demo();
}

#[test]
fn test_deadlock_prevention() {
    concurrency::deadlock_prevention();
}

// ============================================================================
// Combined Tests
// ============================================================================

#[test]
fn test_complex_ownership_scenario() {
    // Complex scenario involving multiple ownership concepts
    let data = Arc::new(Mutex::new(vec![]));
    let mut handles = vec![];
    
    for i in 0..5 {
        let data = Arc::clone(&data);
        let handle = thread::spawn(move || {
            let mut vec = data.lock().unwrap();
            vec.push(i);
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    let result = data.lock().unwrap();
    assert_eq!(result.len(), 5);
}

#[test]
fn test_lifetime_with_threads() {
    // Using scoped threads to borrow data
    let data = vec![1, 2, 3, 4, 5];
    
    thread::scope(|s| {
        s.spawn(|| {
            let sum: i32 = data.iter().sum();
            assert_eq!(sum, 15);
        });
    });
    
    // Original data still valid
    assert_eq!(data.len(), 5);
}
