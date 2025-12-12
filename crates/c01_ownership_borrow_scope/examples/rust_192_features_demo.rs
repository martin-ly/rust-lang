//! # Rust 1.92.0 最新特性演示 / Rust 1.92.0 Latest Features Demo
//!
//! 本示例展示 Rust 1.92.0 版本的最新特性，包括：
//! This example demonstrates the latest features in Rust 1.92.0, including:
//!
//! - `MaybeUninit` 表示和有效性文档化 / Documented `MaybeUninit` Representation and Validity
//! - 联合体字段的原始引用安全访问 / Safe Access to Union Fields with Raw References
//! - 改进的自动特征和 `Sized` 边界处理 / Improved Auto-Trait and `Sized` Bounds Handling
//! - 零大小数组的优化处理 / Optimized Handling of Zero-Sized Arrays
//! - `#[track_caller]` 和 `#[no_mangle]` 的组合使用 / Combined Use of `#[track_caller]` and `#[no_mangle]`
//! - 更严格的 Never 类型 Lint / Stricter Never Type Lints
//! - 关联项的多个边界 / Multiple Bounds for Associated Items
//! - 增强的高阶生命周期区域处理 / Enhanced Higher-Ranked Region Handling
//! - 改进的 `unused_must_use` Lint 行为 / Refined `unused_must_use` Lint Behavior
//! - 标准库 API 稳定化 / Stabilized Standard Library APIs
//! - 迭代器方法特化 / Specialized Iterator Methods
//! - 简化的元组扩展 / Simplified Tuple Extension
//! - 增强的 `EncodeWide` Debug 信息 / Enhanced Debug Information for `EncodeWide`
//! - `iter::Repeat` 中的无限循环 panic / Panic on Infinite Loops in `iter::Repeat`

use c01_ownership_borrow_scope::{
    run_all_rust_192_features_examples,
    get_rust_192_features_info,
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
};

/// 主函数 / Main Function
fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== Rust 1.92.0 最新特性演示 / Rust 1.92.0 Latest Features Demo ===");

    // 显示模块信息 / Show module information
    println!("模块信息 / Module Info: {}", get_rust_192_features_info());

    // 运行所有最新特性示例 / Run all latest features examples
    run_all_rust_192_features_examples();

    // 演示 MaybeUninit 安全使用 / Demonstrate Safe MaybeUninit Usage
    demonstrate_maybe_uninit();

    // 演示联合体原始引用 / Demonstrate Union Raw References
    demonstrate_union_raw_references();

    // 演示零大小数组 / Demonstrate Zero-Sized Arrays
    demonstrate_zero_sized_arrays();

    // 演示 track_caller 和 no_mangle 组合 / Demonstrate Combined track_caller and no_mangle
    demonstrate_track_caller_no_mangle();

    // 演示多边界关联项 / Demonstrate Multiple Bounds for Associated Items
    demonstrate_multiple_bounds();

    // 演示高阶生命周期 / Demonstrate Higher-Ranked Lifetimes
    demonstrate_higher_ranked_lifetimes();

    // 演示标准库 API / Demonstrate Standard Library APIs
    demonstrate_standard_library_apis();

    // 演示迭代器方法 / Demonstrate Iterator Methods
    demonstrate_iterator_methods();

    println!("\n=== Rust 1.92.0 最新特性演示完成 / Rust 1.92.0 Latest Features Demo Completed ===");

    Ok(())
}

/// 演示 MaybeUninit 安全使用 / Demonstrate Safe MaybeUninit Usage
fn demonstrate_maybe_uninit() {
    println!("\n=== MaybeUninit 安全使用演示 / Safe MaybeUninit Usage Demo ===");

    // 创建未初始化的 MaybeUninit
    let mut uninit = SafeMaybeUninit::<i32>::new();
    println!("初始状态 / Initial state: initialized = {}", uninit.is_initialized());

    // 写入值
    uninit.write(42);
    println!("写入后 / After write: initialized = {}", uninit.is_initialized());
    println!("值 / Value: {}", uninit.read());

    // 提取值
    let value = uninit.into_inner();
    println!("提取的值 / Extracted value: {}", value);

    // 从已初始化的值创建
    let from_value = SafeMaybeUninit::from(100);
    println!("从值创建 / Created from value: {}", from_value.read());
}

/// 演示联合体原始引用 / Demonstrate Union Raw References
fn demonstrate_union_raw_references() {
    println!("\n=== 联合体原始引用演示 / Union Raw References Demo ===");

    let mut union = Rust192Union::new();
    union.set_integer(0x12345678);

    println!("整数值 / Integer value: 0x{:X}", union.get_integer());

    // Rust 1.92.0: 使用原始引用安全访问联合体字段
    let raw_ref = union.get_integer_raw();
    println!("原始引用地址 / Raw reference address: {:p}", raw_ref);

    // 使用可变原始引用
    let mut_raw_ref = union.get_integer_mut_raw();
    println!("可变原始引用地址 / Mutable raw reference address: {:p}", mut_raw_ref);
}

/// 演示零大小数组 / Demonstrate Zero-Sized Arrays
fn demonstrate_zero_sized_arrays() {
    println!("\n=== 零大小数组演示 / Zero-Sized Arrays Demo ===");

    // Rust 1.92.0: 优化的零大小数组处理
    let zero_array: Rust192ZeroSizedArray<String> = Rust192ZeroSizedArray::new();
    println!("数组长度 / Array length: {}", zero_array.len());
    println!("是否为空 / Is empty: {}", zero_array.is_empty());

    // 可以创建不同类型的零大小数组
    let zero_array_int: Rust192ZeroSizedArray<i32> = Rust192ZeroSizedArray::default();
    println!("整数零大小数组长度 / Integer zero-sized array length: {}", zero_array_int.len());
}

/// 演示 track_caller 和 no_mangle 组合 / Demonstrate Combined track_caller and no_mangle
fn demonstrate_track_caller_no_mangle() {
    println!("\n=== track_caller 和 no_mangle 组合演示 / Combined track_caller and no_mangle Demo ===");

    // Rust 1.92.0: 可以组合使用两个属性
    let result = rust_192_tracked_function(21);
    println!("函数结果 / Function result: {}", result);
}

/// 演示多边界关联项 / Demonstrate Multiple Bounds for Associated Items
fn demonstrate_multiple_bounds() {
    println!("\n=== 多边界关联项演示 / Multiple Bounds for Associated Items Demo ===");

    use c01_ownership_borrow_scope::rust_192_features::Rust192MultipleBounds;

    let vec = vec![1u8, 2, 3, 4, 5];
    let processed = vec.process(vec.clone());
    println!("处理后的向量 / Processed vector: {:?}", processed);
}

/// 演示高阶生命周期 / Demonstrate Higher-Ranked Lifetimes
fn demonstrate_higher_ranked_lifetimes() {
    println!("\n=== 高阶生命周期演示 / Higher-Ranked Lifetimes Demo ===");

    // Rust 1.92.0: 增强的高阶生命周期区域处理
    rust_192_higher_ranked_lifetime(|s| {
        println!("处理字符串 / Processing string: {}", s);
        s
    });
}

/// 演示标准库 API / Demonstrate Standard Library APIs
fn demonstrate_standard_library_apis() {
    println!("\n=== 标准库 API 演示 / Standard Library APIs Demo ===");

    // NonZero::div_ceil
    rust_192_nonzero_div_ceil_example();

    // Location::file_as_c_str
    rust_192_location_file_as_c_str_example();

    // rotate_right
    rust_192_rotate_right_example();
}

/// 演示迭代器方法 / Demonstrate Iterator Methods
fn demonstrate_iterator_methods() {
    println!("\n=== 迭代器方法演示 / Iterator Methods Demo ===");

    // Rust 1.92.0: 特化的迭代器比较方法
    rust_192_iterator_eq_example();

    // 元组扩展
    rust_192_tuple_extend_example();

    // iter::Repeat
    rust_192_repeat_example();
}

/// 演示改进的 unused_must_use / Demonstrate Refined unused_must_use
#[allow(dead_code)]
fn demonstrate_refined_unused_must_use() {
    println!("\n=== 改进的 unused_must_use 演示 / Refined unused_must_use Demo ===");

    // Rust 1.92.0: 不再对 Result<(), !> 发出警告
    let _ = rust_192_must_use_result();
    println!("Result<(), !> 不会触发 unused_must_use 警告 / Result<(), !> does not trigger unused_must_use warning");
}
