//! # Rust 1.90 新特性测试 (历史版本)
//!
//! ⚠️ **历史版本文件** - 本文件仅作为历史参考保留
//!
//! **当前推荐版本**: Rust 1.92.0+ | 最新测试请参考 `rust_192_comprehensive_tests.rs`
//!
//! 测试 Rust 1.90 引入的新特性

use c12_wasm::ecosystem_examples::rust_190_features::*;

// ============================================================================
// let-else 模式测试
// ============================================================================

#[test]
fn test_let_else_with_some() {
    let data = Some("test data".to_string());
    let result = process_data_with_let_else(data);

    assert!(result.is_ok());
    assert_eq!(result.unwrap(), "TEST DATA");
}

#[test]
fn test_let_else_with_none() {
    let data = None;
    let result = process_data_with_let_else(data);

    assert!(result.is_err());
    assert_eq!(result.unwrap_err(), "No data provided");
}

// ============================================================================
// return-position impl Trait 测试
// ============================================================================

#[test]
fn test_impl_trait_return() {
    let numbers = vec![1, -2, 3, -4, 5, -6, 7];
    let filtered: Vec<&i32> = get_filtered_numbers(&numbers).collect();

    assert_eq!(filtered, vec![&1, &3, &5, &7]);
}

#[test]
fn test_impl_trait_return_empty() {
    let numbers = vec![-1, -2, -3];
    let filtered: Vec<&i32> = get_filtered_numbers(&numbers).collect();

    assert!(filtered.is_empty());
}

#[test]
fn test_impl_trait_return_all_positive() {
    let numbers = vec![1, 2, 3, 4, 5];
    let filtered: Vec<&i32> = get_filtered_numbers(&numbers).collect();

    assert_eq!(filtered, vec![&1, &2, &3, &4, &5]);
}

// ============================================================================
// 集成测试：结合多个新特性
// ============================================================================

#[test]
fn test_rust_190_features_integration() {
    // 1. 使用 let-else 处理数据
    let input = Some("hello world rust wasm".to_string());
    let processed = process_data_with_let_else(input);
    assert!(processed.is_ok());

    let upper_text = processed.unwrap();
    assert_eq!(upper_text, "HELLO WORLD RUST WASM");

    // 2. 使用 impl Trait 过滤数据
    let numbers = vec![1, -2, 3, -4, 5, -6, 7, -8, 9];
    let positive_numbers: Vec<i32> = get_filtered_numbers(&numbers).copied().collect();

    assert_eq!(positive_numbers, vec![1, 3, 5, 7, 9]);

    // 3. 组合使用
    let count = positive_numbers.len();
    assert_eq!(count, 5);
}

// ============================================================================
// 边界情况测试
// ============================================================================

#[test]
fn test_edge_cases() {
    // 空字符串
    let result = process_data_with_let_else(Some("".to_string()));
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), "");

    // 空数组
    let numbers: Vec<i32> = vec![];
    let filtered: Vec<&i32> = get_filtered_numbers(&numbers).collect();
    assert!(filtered.is_empty());

    // 包含零的数组
    let numbers = vec![0, -1, 1, 0];
    let filtered: Vec<&i32> = get_filtered_numbers(&numbers).collect();
    assert_eq!(filtered, vec![&1]);
}

// ============================================================================
// 性能相关测试
// ============================================================================

#[test]
fn test_performance_characteristics() {
    // 测试大数据集
    let large_data: Vec<i32> = (0..10000).map(|i| i - 5000).collect();

    // 使用 impl Trait 的迭代器是惰性的
    let filtered = get_filtered_numbers(&large_data);

    // 只取前 10 个，不会处理全部数据
    let first_10: Vec<&i32> = filtered.take(10).collect();
    assert_eq!(first_10.len(), 10);
    assert!(first_10.iter().all(|&&x| x > 0));
}

#[test]
fn test_iterator_chaining() {
    let numbers = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

    // 链式调用多个迭代器操作
    let result: i32 = get_filtered_numbers(&numbers)
        .filter(|&&x| x % 2 == 0)  // 只保留偶数
        .map(|&x| x * 2)            // 乘以2
        .sum(); // 求和

    // 原始正数: 1,2,3,4,5,6,7,8,9,10
    // 偶数: 2,4,6,8,10
    // 乘以2: 4,8,12,16,20
    // 求和: 60
    assert_eq!(result, 60);
}
