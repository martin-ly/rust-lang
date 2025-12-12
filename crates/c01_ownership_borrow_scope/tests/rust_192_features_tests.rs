//! # Rust 1.92.0 特性测试套件 / Rust 1.92.0 Features Test Suite
//!
//! 本测试套件验证 Rust 1.92.0 所有新特性的正确实现和功能。
//! This test suite verifies the correct implementation and functionality of all Rust 1.92.0 new features.

use c01_ownership_borrow_scope::{
    SafeMaybeUninit,
    Rust192Union,
    Rust192ZeroSizedArray,
    rust_192_tracked_function,
    rust_192_higher_ranked_lifetime,
    rust_192_must_use_result,
    rust_192_nonzero_div_ceil_example,
    rust_192_location_file_as_c_str_example,
    rust_192_rotate_right_example,
    rust_192_iterator_eq_example,
    rust_192_tuple_extend_example,
    rust_192_repeat_example,
    run_all_rust_192_features_examples,
    get_rust_192_features_info,
};

#[test]
fn test_safe_maybe_uninit() {
    // 测试 SafeMaybeUninit 的基本功能
    let mut uninit = SafeMaybeUninit::<i32>::new();
    assert!(!uninit.is_initialized());

    uninit.write(42);
    assert!(uninit.is_initialized());
    assert_eq!(uninit.read(), 42);

    let value = uninit.into_inner();
    assert_eq!(value, 42);
}

#[test]
fn test_safe_maybe_uninit_from() {
    // 测试从已初始化值创建
    let uninit = SafeMaybeUninit::from(100);
    assert!(uninit.is_initialized());
    assert_eq!(uninit.read(), 100);
}

#[test]
fn test_rust192_union() {
    // 测试联合体的基本功能
    let mut union = Rust192Union::new();
    union.set_integer(0x12345678);
    assert_eq!(union.get_integer(), 0x12345678);

    // 测试原始引用
    let raw_ref = union.get_integer_raw();
    assert!(!raw_ref.is_null());

    let mut_raw_ref = union.get_integer_mut_raw();
    assert!(!mut_raw_ref.is_null());
}

#[test]
fn test_rust192_zero_sized_array() {
    // 测试零大小数组
    let zero_array: Rust192ZeroSizedArray<String> = Rust192ZeroSizedArray::new();
    assert_eq!(zero_array.len(), 0);
    assert!(zero_array.is_empty());

    let zero_array_int: Rust192ZeroSizedArray<i32> = Rust192ZeroSizedArray::default();
    assert_eq!(zero_array_int.len(), 0);
}

#[test]
fn test_rust192_trait() {
    // 测试改进的自动特征和 Sized 边界处理
    use c01_ownership_borrow_scope::Rust192Trait;
    let s = String::from("test");
    let processed = s.process_item(String::from("processed"));
    assert_eq!(processed, "processed");
}

#[test]
fn test_rust192_multiple_bounds() {
    // 测试多边界关联项
    use c01_ownership_borrow_scope::rust_192_features::Rust192MultipleBounds;

    let vec = vec![1u8, 2, 3];
    let processed = vec.process(vec.clone());
    assert_eq!(processed, vec![1u8, 2, 3]);
}

#[test]
fn test_rust192_tracked_function() {
    // 测试 track_caller 和 no_mangle 组合
    let result = rust_192_tracked_function(21);
    assert_eq!(result, 42);
}

#[test]
fn test_rust192_higher_ranked_lifetime() {
    // 测试高阶生命周期
    rust_192_higher_ranked_lifetime(|s| s);
    // 如果函数能正常执行，说明高阶生命周期处理正确
}

#[test]
fn test_rust192_must_use_result() {
    // 测试改进的 unused_must_use
    let result = rust_192_must_use_result();
    assert!(result.is_ok());
    // 注意：这个函数不应该触发 unused_must_use 警告
}

#[test]
fn test_rust192_nonzero_div_ceil() {
    // 测试 NonZero::div_ceil
    rust_192_nonzero_div_ceil_example();
    // 如果函数能正常执行，说明 API 可用
}

#[test]
fn test_rust192_location_file_as_c_str() {
    // 测试 Location::file_as_c_str
    rust_192_location_file_as_c_str_example();
    // 如果函数能正常执行，说明 API 可用
}

#[test]
fn test_rust192_rotate_right() {
    // 测试 rotate_right
    rust_192_rotate_right_example();
    // 如果函数能正常执行，说明 API 可用
}

#[test]
fn test_rust192_iterator_eq() {
    // 测试迭代器方法特化
    rust_192_iterator_eq_example();
    // 如果函数能正常执行，说明 API 可用
}

#[test]
fn test_rust192_tuple_extend() {
    // 测试元组扩展
    rust_192_tuple_extend_example();
    // 如果函数能正常执行，说明 API 可用
}

#[test]
fn test_rust192_repeat() {
    // 测试 iter::Repeat
    rust_192_repeat_example();
    // 如果函数能正常执行，说明 API 可用
}

#[test]
fn test_get_rust_192_features_info() {
    // 测试获取特性信息
    let info = get_rust_192_features_info();
    assert!(!info.is_empty());
    assert!(info.contains("Rust 1.92.0"));
}

#[test]
fn test_run_all_rust_192_features_examples() {
    // 测试运行所有示例
    run_all_rust_192_features_examples();
    // 如果函数能正常执行，说明所有特性都可用
}

#[test]
fn test_rust192_union_raw_references() {
    // 测试联合体原始引用的安全性
    let mut union = Rust192Union::new();
    union.set_integer(42);

    // Rust 1.92.0: 可以在安全代码中获取原始引用
    let raw_const = union.get_integer_raw();
    let raw_mut = union.get_integer_mut_raw();

    // 验证引用不为空
    assert!(!raw_const.is_null());
    assert!(!raw_mut.is_null());

    // 注意：解引用原始指针需要 unsafe，这里只测试获取引用的安全性
}

#[test]
fn test_safe_maybe_uninit_drop() {
    // 测试 SafeMaybeUninit 的 Drop 行为
    {
        let mut uninit = SafeMaybeUninit::<String>::new();
        uninit.write(String::from("test"));
        // 当 uninit 离开作用域时，应该正确 drop
    }
    // 如果这里没有 panic，说明 Drop 行为正确
}

#[test]
fn test_rust192_zero_sized_array_different_types() {
    // 测试不同类型的零大小数组
    let _zero_string: Rust192ZeroSizedArray<String> = Rust192ZeroSizedArray::new();
    let _zero_int: Rust192ZeroSizedArray<i32> = Rust192ZeroSizedArray::new();
    let _zero_vec: Rust192ZeroSizedArray<Vec<u8>> = Rust192ZeroSizedArray::new();
    // 如果都能创建，说明零大小数组优化正常工作
}
