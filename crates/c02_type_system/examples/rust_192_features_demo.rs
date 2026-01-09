//! # Rust 1.92.0 新特性演示
//!
//! 本示例展示 Rust 1.92.0 版本的新特性和改进：
//! - 关联项的多个边界（Trait 系统核心）
//! - 增强的高阶生命周期区域处理
//! - 改进的自动特征和 `Sized` 边界处理
//! - `MaybeUninit` 在类型系统中的应用
//! - `NonZero::div_ceil` 在类型大小计算中的应用
//! - 迭代器方法特化在类型处理中的应用
//!
//! 运行：`cargo run --example rust_192_features_demo`

use c02_type_system::rust_192_features::*;
use std::num::NonZeroUsize;

fn main() {
    println!("🦀 Rust 1.92.0 类型系统特性演示\n");
    println!("{}", "=".repeat(60));

    // 1. 关联项的多个边界
    demonstrate_multiple_bounds();

    // 2. 增强的高阶生命周期区域处理
    demonstrate_higher_ranked_lifetimes();

    // 3. 改进的自动特征和 Sized 边界处理
    demonstrate_auto_traits();

    // 4. MaybeUninit 在类型系统中的应用
    demonstrate_maybe_uninit();

    // 5. NonZero::div_ceil 在类型大小计算中的应用
    demonstrate_nonzero_div_ceil();

    // 6. 迭代器方法特化
    demonstrate_iterator_specialization();

    // 7. 综合演示
    println!("\n{}", "=".repeat(60));
    println!("综合演示:");
    demonstrate_rust_192_type_system_features();
}

/// 1. 关联项的多个边界演示
fn demonstrate_multiple_bounds() {
    println!("\n【1. 关联项的多个边界】");
    println!("{}", "-".repeat(40));

    // 字符串转换器
    let converter = StringConverter;
    let input = String::from("hello world");
    let output = converter.convert(input.clone());
    println!("✓ 字符串转换器:");
    println!("  输入: \"{}\"", input);
    println!("  输出: \"{}\"", output);

    // 泛型类型转换器
    let generic_converter = GenericTypeConverter::<String, String>::new();
    let converted = generic_converter.convert(String::from("test"));
    println!("\n✓ 泛型类型转换器:");
    println!("  输入: \"test\"");
    println!("  输出: \"{}\"", converted);

    // 演示多边界约束
    println!("\n✓ 多边界约束说明:");
    println!("  - Input: Clone + Send + Sync + 'static");
    println!("  - Output: Clone + Send + 'static");
    println!("  - Rust 1.92.0 允许为关联类型指定多个边界");
}

/// 2. 增强的高阶生命周期区域处理演示
fn demonstrate_higher_ranked_lifetimes() {
    println!("\n【2. 增强的高阶生命周期区域处理】");
    println!("{}", "-".repeat(40));

    // 高阶生命周期函数
    let input_str = "test string for lifetime";
    let processed = process_strings(input_str, |s| {
        // 可以在这里进行字符串处理
        s
    });
    println!("✓ 高阶生命周期处理:");
    println!("  输入: \"{}\"", input_str);
    println!("  输出: \"{}\"", processed);

    // 使用 convert_with_lifetime
    let result = convert_with_lifetime("lifetime demo", |s| s);
    println!("\n✓ convert_with_lifetime:");
    println!("  结果: \"{}\"", result);

    // 字符串反转处理器
    let reverser = StringReverser;
    let reversed = reverser.process("hello");
    println!("\n✓ HigherRankedLifetimeProcessor:");
    println!("  处理结果: \"{}\"", reversed);

    println!("\n✓ 高阶生命周期说明:");
    println!("  - Rust 1.92.0 增强了 HRTB 一致性规则");
    println!("  - 提供更强的类型安全保障");
}

/// 3. 改进的自动特征和 Sized 边界处理演示
fn demonstrate_auto_traits() {
    println!("\n【3. 改进的自动特征和 Sized 边界处理】");
    println!("{}", "-".repeat(40));

    // AutoTraitExample
    let example = AutoTraitExample::new(42);
    println!("✓ AutoTraitExample:");
    println!("  值: {}", example.get());

    let string_example = AutoTraitExample::new(String::from("auto trait"));
    println!("  字符串值: {}", string_example.get());

    println!("\n✓ 自动特征说明:");
    println!("  - Rust 1.92.0 改进了自动特征的推断");
    println!("  - Send 和 Sync 会自动传播");
    println!("  - 更智能的边界推断");
}

/// 4. MaybeUninit 在类型系统中的应用演示
fn demonstrate_maybe_uninit() {
    println!("\n【4. MaybeUninit 在类型系统中的应用】");
    println!("{}", "-".repeat(40));

    // 创建未初始化管理器
    let mut manager = TypeSafeUninitManager::<String>::new();
    println!("✓ 创建未初始化管理器:");
    println!("  初始化状态: {}", manager.is_initialized());
    println!("  获取值: {:?}", manager.get());

    // 初始化
    manager.initialize(String::from("initialized value"));
    println!("\n✓ 初始化后:");
    println!("  初始化状态: {}", manager.is_initialized());
    if let Some(value) = manager.get() {
        println!("  值: \"{}\"", value);
    }

    // 修改值
    if let Some(value) = manager.get_mut() {
        *value = String::from("modified value");
        println!("\n✓ 修改后:");
        println!("  值: \"{}\"", value);
    }

    // 整数示例
    let mut int_manager = TypeSafeUninitManager::<i32>::new();
    int_manager.initialize(100);
    println!("\n✓ 整数管理器:");
    println!("  值: {:?}", int_manager.get());

    println!("\n✓ MaybeUninit 说明:");
    println!("  - Rust 1.92.0 文档化了 MaybeUninit 的表示和有效性");
    println!("  - 提供类型安全的未初始化内存管理");
}

/// 5. NonZero::div_ceil 在类型大小计算中的应用演示
fn demonstrate_nonzero_div_ceil() {
    println!("\n【5. NonZero::div_ceil 在类型大小计算中的应用】");
    println!("{}", "-".repeat(40));

    // 类型大小计算器
    let alignment = NonZeroUsize::new(8).unwrap();
    let calculator = TypeSizeCalculator::new(alignment);

    // 计算对齐大小
    let aligned_size = calculator.calculate_aligned::<u64>(10);
    println!("✓ 类型大小计算:");
    println!("  10 个 u64 对齐后大小: {} 字节", aligned_size);
    println!("  (u64 大小: {} 字节, 对齐: {} 字节)",
             std::mem::size_of::<u64>(), alignment.get());

    // 计算块数
    let blocks = calculator.calculate_blocks(100, NonZeroUsize::new(16).unwrap());
    println!("\n✓ 内存块计算:");
    println!("  100 字节需要 {} 个 16 字节块", blocks);

    // 不同对齐方式
    let alignments = vec![4, 8, 16, 32];
    println!("\n✓ 不同对齐方式的大小计算:");
    for &align in &alignments {
        let calc = TypeSizeCalculator::new(NonZeroUsize::new(align).unwrap());
        let size = calc.calculate_aligned::<u8>(100);
        println!("  对齐 {} 字节: {} 字节", align, size);
    }

    println!("\n✓ NonZero::div_ceil 说明:");
    println!("  - Rust 1.92.0 新稳定化的 API");
    println!("  - 安全地计算对齐后的类型大小");
    println!("  - 避免除零错误");
}

/// 6. 迭代器方法特化演示
fn demonstrate_iterator_specialization() {
    println!("\n【6. 迭代器方法特化】");
    println!("{}", "-".repeat(40));

    // 比较类型列表
    let list1 = vec![1, 2, 3, 4, 5];
    let list2 = vec![1, 2, 3, 4, 5];
    let list3 = vec![1, 2, 3, 4, 6];

    println!("✓ 类型列表比较:");
    println!("  list1: {:?}", list1);
    println!("  list2: {:?}", list2);
    println!("  list3: {:?}", list3);
    println!("  list1 == list2: {}", compare_type_lists(&list1, &list2));
    println!("  list1 == list3: {}", compare_type_lists(&list1, &list3));

    // 类型列表验证器
    let validator = TypeListValidator::new(vec![1, 2, 3]);
    println!("\n✓ 类型列表验证器:");
    println!("  验证 [1, 2, 3]: {}", validator.validate(&[1, 2, 3]));
    println!("  验证 [1, 2, 4]: {}", validator.validate(&[1, 2, 4]));
    println!("  验证 [1, 2, 3, 4]: {}", validator.validate(&[1, 2, 3, 4]));

    // 字符串列表比较
    let str_list1 = vec!["a", "b", "c"];
    let str_list2 = vec!["a", "b", "c"];
    let str_list3 = vec!["a", "b", "d"];
    println!("\n✓ 字符串列表比较:");
    println!("  str_list1 == str_list2: {}",
             compare_type_lists(&str_list1, &str_list2));
    println!("  str_list1 == str_list3: {}",
             compare_type_lists(&str_list1, &str_list3));

    println!("\n✓ 迭代器特化说明:");
    println!("  - Rust 1.92.0: Iterator::eq 为 TrustedLen 迭代器特化");
    println!("  - 性能更好的迭代器比较");
}
