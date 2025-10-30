//! # 基础功能测试
//!
//! 测试 lib.rs 中的基础示例代码

use c12_wasm::array_examples::*;
use c12_wasm::basic_examples::*;
use c12_wasm::complex_types::*;
use c12_wasm::string_examples::*;

// ============================================================================
// 基础示例测试
// ============================================================================

#[test]
fn test_add_function() {
    assert_eq!(add(2, 3), 5);
    assert_eq!(add(-1, 1), 0);
    assert_eq!(add(0, 0), 0);
    assert_eq!(add(100, -50), 50);
}

#[test]
fn test_greet_function() {
    assert_eq!(greet("World"), "Hello, World!");
    assert_eq!(greet("Rust"), "Hello, Rust!");
    assert_eq!(greet("WASM"), "Hello, WASM!");
}

#[test]
fn test_sum_array() {
    assert_eq!(sum_array(&[1, 2, 3, 4, 5]), 15);
    assert_eq!(sum_array(&[]), 0);
    assert_eq!(sum_array(&[-1, 1, -2, 2]), 0);
    assert_eq!(sum_array(&[10]), 10);
}

// ============================================================================
// 字符串操作测试
// ============================================================================

#[test]
fn test_reverse_string() {
    assert_eq!(reverse_string("hello"), "olleh");
    assert_eq!(reverse_string("rust"), "tsur");
    assert_eq!(reverse_string(""), "");
    assert_eq!(reverse_string("a"), "a");
}

#[test]
fn test_is_palindrome() {
    // 基础回文测试
    assert!(is_palindrome("racecar"));
    assert!(is_palindrome("level"));
    assert!(is_palindrome("noon"));

    // 带空格和标点的回文
    assert!(is_palindrome("A man a plan a canal Panama"));
    assert!(is_palindrome("Was it a car or a cat I saw"));

    // 非回文
    assert!(!is_palindrome("hello"));
    assert!(!is_palindrome("world"));

    // 边界情况
    assert!(is_palindrome("a"));
    assert!(is_palindrome(""));
}

#[test]
fn test_count_words() {
    assert_eq!(count_words("hello world"), 2);
    assert_eq!(count_words("rust wasm is awesome"), 4);
    assert_eq!(count_words(""), 0);
    assert_eq!(count_words("single"), 1);
    assert_eq!(count_words("  multiple   spaces   "), 2);
}

#[test]
fn test_to_uppercase() {
    assert_eq!(to_uppercase("hello"), "HELLO");
    assert_eq!(to_uppercase("Rust"), "RUST");
    assert_eq!(to_uppercase(""), "");
    assert_eq!(to_uppercase("Hello World"), "HELLO WORLD");
}

// ============================================================================
// 数组操作测试
// ============================================================================

#[test]
fn test_calculate_average() {
    assert_eq!(calculate_average(&[1.0, 2.0, 3.0, 4.0, 5.0]), 3.0);
    assert_eq!(calculate_average(&[10.0, 20.0]), 15.0);
    assert_eq!(calculate_average(&[]), 0.0);
    assert_eq!(calculate_average(&[5.0]), 5.0);
}

#[test]
fn test_find_max() {
    assert_eq!(find_max(&[1, 5, 3, 2, 4]), Some(5));
    assert_eq!(find_max(&[-1, -5, -3]), Some(-1));
    assert_eq!(find_max(&[42]), Some(42));
    assert_eq!(find_max(&[]), None);
}

#[test]
fn test_reverse_array() {
    assert_eq!(reverse_array(&[1, 2, 3, 4, 5]), vec![5, 4, 3, 2, 1]);
    assert_eq!(reverse_array(&[]), vec![]);
    assert_eq!(reverse_array(&[42]), vec![42]);
}

#[test]
fn test_filter_even() {
    assert_eq!(filter_even(&[1, 2, 3, 4, 5, 6]), vec![2, 4, 6]);
    assert_eq!(filter_even(&[1, 3, 5]), vec![]);
    assert_eq!(filter_even(&[2, 4, 6]), vec![2, 4, 6]);
    assert_eq!(filter_even(&[]), vec![]);
}

// ============================================================================
// 复杂类型测试
// ============================================================================

#[test]
fn test_counter_new() {
    let counter = Counter::new();
    assert_eq!(counter.value(), 0);
}

#[test]
fn test_counter_increment() {
    let mut counter = Counter::new();

    counter.increment();
    assert_eq!(counter.value(), 1);

    counter.increment();
    assert_eq!(counter.value(), 2);

    counter.increment();
    assert_eq!(counter.value(), 3);
}

#[test]
fn test_counter_decrement() {
    let mut counter = Counter::new();

    counter.increment();
    counter.increment();
    counter.increment();
    assert_eq!(counter.value(), 3);

    counter.decrement();
    assert_eq!(counter.value(), 2);

    counter.decrement();
    assert_eq!(counter.value(), 1);
}

#[test]
fn test_counter_reset() {
    let mut counter = Counter::new();

    counter.increment();
    counter.increment();
    counter.increment();
    assert_eq!(counter.value(), 3);

    counter.reset();
    assert_eq!(counter.value(), 0);
}

#[test]
fn test_person() {
    let person = Person::new("Alice".to_string(), 30);

    assert_eq!(person.name(), "Alice");
    assert_eq!(person.age(), 30);
    assert_eq!(person.to_str(), "Alice (30 years old)");
}

#[test]
fn test_person_set_age() {
    let mut person = Person::new("Bob".to_string(), 25);
    assert_eq!(person.age(), 25);

    person.set_age(26);
    assert_eq!(person.age(), 26);
}

// ============================================================================
// 性能优化测试
// ============================================================================

#[test]
fn test_process_bytes_optimized() {
    use c12_wasm::performance_examples::process_bytes_optimized;

    let input = vec![1, 2, 3, 4, 5];
    let output = process_bytes_optimized(&input);

    assert_eq!(output, vec![2, 4, 6, 8, 10]);
}

#[test]
fn test_create_preallocated_vector() {
    use c12_wasm::performance_examples::create_preallocated_vector;

    let vec = create_preallocated_vector(5);
    assert_eq!(vec.len(), 5);
    assert_eq!(vec, vec![0, 1, 2, 3, 4]);
}

// ============================================================================
// 错误处理测试
// ============================================================================

// Note: safe_divide test is skipped as it uses JsValue
// which requires WASM environment. See wasm-bindgen-test for WASM tests.

// Note: validate_string test is skipped as it uses JsValue
// which requires WASM environment. See wasm-bindgen-test for WASM tests.

// ============================================================================
// 集成测试
// ============================================================================

#[test]
fn test_complex_workflow() {
    // 创建计数器并操作
    let mut counter = Counter::new();
    counter.increment();
    counter.increment();

    // 使用计数器值进行计算
    let count = counter.value();
    let doubled = add(count, count);

    assert_eq!(doubled, 4);

    // 字符串处理
    let message = greet("WASM");
    assert_eq!(count_words(&message), 2);

    // 数组处理
    let numbers = vec![1, 2, 3, 4, 5];
    let sum = sum_array(&numbers);
    let max = find_max(&numbers);

    assert_eq!(sum, 15);
    assert_eq!(max, Some(5));
}
