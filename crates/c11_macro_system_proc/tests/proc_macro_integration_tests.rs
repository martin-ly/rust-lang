//! 过程宏集成测试 / Proc-Macro Integration Tests

use c11_macro_system_proc_macros::{AutoClone, Builder, conditional, debug_print, serializable, timed};

// ============================================================
// Builder 派生宏测试
// ============================================================

#[derive(Builder, Debug, PartialEq)]
struct TestConfig {
    name: String,
    count: u32,
}

#[test]
fn test_builder_all_fields_set() {
    let config = TestConfig::builder()
        .name("test".to_string())
        .count(42)
        .build()
        .expect("build should succeed");

    assert_eq!(config.name, "test");
    assert_eq!(config.count, 42);
}

#[test]
fn test_builder_missing_field_fails() {
    let result = TestConfig::builder().name("test".to_string()).build();
    assert!(result.is_err());
}

// ============================================================
// AutoClone 派生宏测试
// ============================================================

#[derive(AutoClone, Debug, PartialEq)]
struct Cloneable {
    data: String,
    value: i64,
}

#[test]
fn test_auto_clone_creates_equal_copy() {
    let original = Cloneable {
        data: "hello".to_string(),
        value: -7,
    };
    let cloned = original.clone();
    assert_eq!(original, cloned);
    // Verify deep copy (different allocation)
    assert_ne!(original.data.as_ptr(), cloned.data.as_ptr());
}

// ============================================================
// debug_print 属性宏测试
// ============================================================

#[debug_print]
fn add_with_debug(a: i32, b: i32) -> i32 {
    a + b
}

#[test]
fn test_debug_print_preserves_signature_and_result() {
    assert_eq!(add_with_debug(2, 3), 5);
}

// ============================================================
// timed 属性宏测试
// ============================================================

#[timed]
fn fibonacci(n: u32) -> u32 {
    match n {
        0 => 0,
        1 => 1,
        _ => fibonacci(n - 1) + fibonacci(n - 2),
    }
}

#[test]
fn test_timed_preserves_signature_and_result() {
    assert_eq!(fibonacci(10), 55);
}

// ============================================================
// serializable 函数宏测试
// ============================================================

serializable! {
    struct Record {
        id: u64,
        label: String,
        score: f64,
    }
}

#[test]
fn test_serializable_to_json_contains_fields() {
    let record = Record {
        id: 99,
        label: "alpha".to_string(),
        score: std::f64::consts::PI,
    };
    let json = record.to_json();
    assert!(json.contains("\"id\": 99"));
    assert!(json.contains("\"label\": \"alpha\""));
    assert!(json.contains("\"score\": 3.14"));
}

#[test]
fn test_serializable_debug_format() {
    let record = Record {
        id: 1,
        label: "x".to_string(),
        score: 0.0,
    };
    let debug = format!("{:?}", record);
    assert!(debug.starts_with("Record "));
}

// ============================================================
// conditional 函数宏测试
// ============================================================

#[test]
fn test_conditional_selects_debug_branch() {
    let msg = conditional! {
        #[cfg(debug_assertions)]
        "debug"

        #[cfg(not(debug_assertions))]
        "release"
    };

    assert_eq!(msg, "debug");
}
