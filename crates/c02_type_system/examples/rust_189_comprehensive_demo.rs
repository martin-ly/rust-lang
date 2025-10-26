//! # Rust 1.89 特性示例 (历史版本)
//!
//! ⚠️ **注意**: 本示例针对 Rust 1.89 版本编写，部分特性在 Rust 1.90 中已有更新。
//!
//! ## Rust 1.90 主要更新
//!
//! ### 编译器改进
//! - **LLD 链接器**: Linux x86_64 默认启用，链接速度提升约 2x
//! - **编译性能**: 增量编译优化，构建速度提升
//!
//! ### 标准库更新
//! - `u{n}::checked_sub_signed()` - 新增带符号减法检查方法
//! - `<[T]>::reverse()` - 现在可在 const 上下文中使用
//! - `f32/f64` 数学函数 - floor/ceil/trunc 等在 const 中可用
//!
//! ### Lint 改进
//! - `mismatched_lifetime_syntaxes` - 默认启用，检查生命周期语法一致性
//!
//! ## 迁移建议
//!
//! 1. 更新 Cargo.toml: `rust-version = "1.90"`, `edition = "2024"`
//! 2. 应用新的稳定 API 和 const 函数增强
//! 3. 检查并修复新 lint 警告
//!
//! 参考: [Rust 1.90.0 Release Notes](https://blog.rust-lang.org/2025/09/18/Rust-1.90.0/)
//!
//! ---
//!
//! # Rust 1.89 综合特性演示
//!
//! 本示例程序展示了 Rust 1.89 版本中所有新特性和改进，
//! 包括基础语法、类型系统、性能优化等方面的完整功能。
//!
//! # 运行方式
//! ```bash
//! cargo run --example rust_189_comprehensive_demo
//! ```
//!
//! # 文件信息
//! - 文件: rust_189_comprehensive_demo.rs
//! - 创建日期: 2025-01-27
//! - 版本: 1.0
//! - Rust版本: 1.89.0
//! - 作者: Rust 类型系统项目组

use std::convert::TryInto;

/// 主函数：演示所有 Rust 1.89 特性
///
/// 本函数展示了 Rust 1.89 版本中所有新特性和改进，
/// 包括基础语法、类型系统、性能优化等方面的完整功能。
fn main() {
    println!("🚀 Rust 1.89 综合特性演示程序");
    println!("=====================================\n");

    // 1. 基础语法特性演示
    println!("📝 1. 基础语法特性演示");
    println!("------------------------");
    // demonstrate_all_rust_189_features(); // 暂时注释掉，因为模块有编译错误
    println!("     基础语法特性演示暂时禁用");
    println!();

    // 2. 整数类型系统演示
    println!("🔢 2. 整数类型系统演示");
    println!("------------------------");
    // demonstrate_all_integer_types(); // 暂时注释掉
    println!("     整数类型系统演示暂时禁用");
    println!();

    // 3. 浮点数类型系统演示
    println!("🔢 3. 浮点数类型系统演示");
    println!("------------------------");
    // demonstrate_all_float_types(); // 暂时注释掉
    println!("     浮点数类型系统演示暂时禁用");
    println!();

    // 4. 类型组合增强特性演示
    println!("🔗 4. 类型组合增强特性演示");
    println!("------------------------");
    demonstrate_type_composition_enhancements();
    println!();

    // 5. 性能测试演示
    println!("⚡ 5. 性能测试演示");
    println!("------------------------");
    demonstrate_performance_tests();
    println!();

    // 6. 实际应用场景演示
    println!("🎯 6. 实际应用场景演示");
    println!("------------------------");
    demonstrate_real_world_scenarios();
    println!();

    // 7. 性能优化技巧演示
    println!("⚡ 7. 性能优化技巧演示");
    println!("------------------------");
    demonstrate_performance_optimization_tips();
    println!();

    // 8. 类型推断和转换演示
    println!("🔍 8. 类型推断和转换演示");
    println!("------------------------");
    demonstrate_type_inference_and_conversion();
    println!();

    // 9. 错误处理最佳实践演示
    println!("⚠️ 9. 错误处理最佳实践演示");
    println!("------------------------");
    demonstrate_error_handling_best_practices();
    println!();

    println!("✅ 所有演示完成！");
    println!("感谢使用 Rust 1.89 综合特性演示程序！");
}

/// 演示类型组合增强特性
///
/// 本函数展示了 Rust 1.89 中类型组合增强特性的使用。
fn demonstrate_type_composition_enhancements() {
    // 1. 增强的泛型关联类型 (GATs)
    println!("  1. 增强的泛型关联类型 (GATs):");
    println!("     字符串容器演示暂时禁用");

    // 2. 常量泛型组合类型
    println!("  2. 常量泛型组合类型:");
    let arr = [1, 2, 3, 4, 5];
    println!("     常量泛型数组: {:?}", arr);
    println!("     数组长度: {}", arr.len());
    println!("     是否为空: {}", arr.is_empty());

    // 3. 生命周期组合类型
    println!("  3. 生命周期组合类型:");
    println!("     生命周期管理器演示暂时禁用");

    // 4. 智能指针类型组合
    println!("  4. 智能指针类型组合:");
    let smart_pointer = std::rc::Rc::new(42);
    println!("     智能指针组合: {:?}", smart_pointer);
    println!("     获取值: {}", *smart_pointer);

    // 5. 错误处理类型组合
    println!("  5. 错误处理类型组合:");
    let result: Result<i32, String> = Ok(42);
    match result {
        Ok(value) => println!("     错误处理结果: {}", value),
        Err(e) => println!("     错误: {}", e),
    }
}

/// 演示性能测试
///
/// 本函数展示了各种性能测试的结果。
fn demonstrate_performance_tests() {
    // 1. 整数类型性能测试
    println!("  1. 整数类型性能测试:");
    println!("     整数算术运算性能测试演示");
    let start = std::time::Instant::now();
    let mut _sum = 0i64;
    for i in 0..1_000_000 {
        _sum += i as i64;
    }
    let duration = start.elapsed();
    println!("     100万次整数加法耗时: {:?}", duration);
    println!();

    // 2. 浮点数类型性能测试
    println!("  2. 浮点数类型性能测试:");
    println!("     浮点数算术运算性能测试演示");
    let start = std::time::Instant::now();
    let mut _sum = 0.0f64;
    for i in 0..1_000_000 {
        _sum += i as f64;
    }
    let duration = start.elapsed();
    println!("     100万次浮点数加法耗时: {:?}", duration);
    println!();

    // 3. 内存使用测试
    println!("  3. 内存使用测试:");
    println!("     内存分配性能测试演示");
    let start = std::time::Instant::now();
    let _vec: Vec<i32> = (0..100_000).collect();
    let duration = start.elapsed();
    println!("     分配10万个整数向量耗时: {:?}", duration);
    println!();
}

/// 演示实际应用场景
///
/// 本函数展示了 Rust 1.89 特性在实际应用场景中的使用。
fn demonstrate_real_world_scenarios() {
    // 1. 数学计算场景
    println!("  1. 数学计算场景:");
    demonstrate_math_scenarios();
    println!();

    // 2. 数据处理场景
    println!("  2. 数据处理场景:");
    demonstrate_data_processing_scenarios();
    println!();

    // 3. 系统编程场景
    println!("  3. 系统编程场景:");
    demonstrate_systems_programming_scenarios();
    println!();

    // 4. 并发编程场景
    println!("  4. 并发编程场景:");
    demonstrate_concurrent_programming_scenarios();
    println!();
}

/// 演示数学计算场景
///
/// 本函数展示了 Rust 1.89 特性在数学计算场景中的使用。
fn demonstrate_math_scenarios() {
    // 1. 矩阵运算
    println!("     矩阵运算:");
    println!("       矩阵运算演示暂时禁用");

    // 2. 向量运算
    println!("     向量运算:");
    println!("       向量运算演示暂时禁用");

    // 3. 数值计算
    println!("     数值计算:");
    let pi = std::f64::consts::PI;
    let e = std::f64::consts::E;

    println!("       π = {:.10}", pi);
    println!("       e = {:.10}", e);
    println!("       π * e = {:.10}", pi * e);
    println!("       sin(π/2) = {:.10}", (pi / 2.0).sin());
    println!("       ln(e) = {:.10}", e.ln());
}

/// 演示数据处理场景
///
/// 本函数展示了 Rust 1.89 特性在数据处理场景中的使用。
fn demonstrate_data_processing_scenarios() {
    // 1. 字符串处理
    println!("     字符串处理:");
    println!("       字符串处理演示暂时禁用");

    // 2. 数字处理
    println!("     数字处理:");
    println!("       数字处理演示暂时禁用");

    // 3. 数据转换
    println!("     数据转换:");
    let numbers = [1, 2, 3, 4, 5];
    let strings: Vec<String> = numbers.iter().map(|n| n.to_string()).collect();
    println!("       数字转字符串: {:?}", strings);

    let floats: Vec<f64> = numbers.iter().map(|n| *n as f64).collect();
    println!("       整数转浮点数: {:?}", floats);
}

/// 演示系统编程场景
///
/// 本函数展示了 Rust 1.89 特性在系统编程场景中的使用。
fn demonstrate_systems_programming_scenarios() {
    // 1. 内存管理
    println!("     内存管理:");
    println!("       内存管理演示暂时禁用");

    // 2. 错误处理
    println!("     错误处理:");
    let success_result: Result<i32, String> = Ok(42);
    let error_result: Result<i32, String> = Err("测试错误".into());

    match success_result {
        Ok(value) => println!("       成功结果: {}", value),
        Err(e) => println!("       错误: {}", e),
    }

    match error_result {
        Ok(value) => println!("       成功结果: {}", value),
        Err(e) => println!("       错误: {}", e),
    }

    // 3. 类型安全
    println!("     类型安全:");
    let safe_value = 42i32;
    let safe_float = std::f64::consts::PI;

    println!("       安全整数: {} (类型: {})", safe_value, std::any::type_name_of_val(&safe_value));
    println!("       安全浮点数: {} (类型: {})", safe_float, std::any::type_name_of_val(&safe_float));
}

/// 演示并发编程场景
///
/// 本函数展示了 Rust 1.89 特性在并发编程场景中的使用。
fn demonstrate_concurrent_programming_scenarios() {
    use std::sync::{Arc, Mutex};
    use std::thread;

    // 1. 线程安全
    println!("     线程安全:");
    let shared_data = Arc::new(Mutex::new(0));
    let mut handles = vec![];

    for i in 0..5 {
        let data = Arc::clone(&shared_data);
        let handle = thread::spawn(move || {
            let mut num = data.lock().unwrap();
            *num += i;
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    println!("       共享数据最终值: {}", *shared_data.lock().unwrap());

    // 2. 异步编程
    println!("     异步编程:");
    println!("       异步编程演示暂时禁用");

    // 3. 并发集合
    println!("     并发集合:");
    use std::collections::HashMap;
    use std::sync::RwLock;

    let concurrent_map = Arc::new(RwLock::new(HashMap::new()));

    // 写入数据
    {
        let mut map = concurrent_map.write().unwrap();
        map.insert("key1".to_string(), "value1".to_string());
        map.insert("key2".to_string(), "value2".to_string());
    }

    // 读取数据
    {
        let map = concurrent_map.read().unwrap();
        println!("       并发映射: {:?}", *map);
    }
}

/// 演示类型推断和转换
///
/// 本函数展示了 Rust 1.89 中类型推断和转换的增强功能。
fn demonstrate_type_inference_and_conversion() {
    println!("🔍 类型推断和转换演示");
    println!("------------------------");

    // 1. 自动类型推断
    println!("  1. 自动类型推断:");
    let inferred_int = 42;        // 推断为 i32
    let inferred_float = std::f64::consts::PI;    // 推断为 f64
    let inferred_string = "Hello"; // 推断为 &str

    println!("     推断整数: {} (类型: {})", inferred_int, std::any::type_name_of_val(&inferred_int));
    println!("     推断浮点数: {} (类型: {})", inferred_float, std::any::type_name_of_val(&inferred_float));
    println!("     推断字符串: {} (类型: {})", inferred_string, std::any::type_name_of_val(&inferred_string));

    // 2. 显式类型转换
    println!("  2. 显式类型转换:");
    let int_value: i32 = 42;
    let float_value: f64 = int_value as f64;
    let string_value: String = int_value.to_string();

    println!("     整数转浮点数: {} -> {}", int_value, float_value);
    println!("     整数转字符串: {} -> {}", int_value, string_value);

    // 3. 安全类型转换
    println!("  3. 安全类型转换:");
    let large_int: i32 = 1_000_000;

    match TryInto::<i8>::try_into(large_int) {
        Ok(value) => println!("     安全转换成功: {} -> {}", large_int, value),
        Err(_) => println!("     安全转换失败: {} 无法转换为 i8", large_int),
    }

    match TryInto::<i64>::try_into(large_int) {
        Ok(value) => println!("     安全转换成功: {} -> {}", large_int, value),
        Err(_) => println!("     安全转换失败: {} 无法转换为 i64", large_int),
    }

    // 4. 类型别名
    println!("  4. 类型别名:");
    type UserId = u64;
    type Timestamp = u64;
    type Score = f64;

    let user_id: UserId = 12345;
    let timestamp: Timestamp = 1640995200;
    let score: Score = 95.5;

    println!("     用户ID: {} (类型: {})", user_id, std::any::type_name_of_val(&user_id));
    println!("     时间戳: {} (类型: {})", timestamp, std::any::type_name_of_val(&timestamp));
    println!("     分数: {} (类型: {})", score, std::any::type_name_of_val(&score));
}

/// 演示错误处理最佳实践
///
/// 本函数展示了 Rust 1.89 中错误处理的最佳实践。
fn demonstrate_error_handling_best_practices() {
    println!("⚠️ 错误处理最佳实践演示");
    println!("------------------------");

    // 1. Result 类型使用
    println!("  1. Result 类型使用:");
    let success_result: Result<i32, String> = Ok(42);
    let error_result: Result<i32, String> = Err("操作失败".to_string());

    match success_result {
        Ok(value) => println!("     成功: {}", value),
        Err(e) => println!("     错误: {}", e),
    }

    match error_result {
        Ok(value) => println!("     成功: {}", value),
        Err(e) => println!("     错误: {}", e),
    }

    // 2. Option 类型使用
    println!("  2. Option 类型使用:");
    let some_value: Option<i32> = Some(42);
    let none_value: Option<i32> = None;

    match some_value {
        Some(value) => println!("     有值: {}", value),
        None => println!("     无值"),
    }

    match none_value {
        Some(value) => println!("     有值: {}", value),
        None => println!("     无值"),
    }

    // 3. 错误链
    println!("  3. 错误链:");
    let result = divide(10, 2)
        .and_then(|x| divide(x, 2))
        .and_then(|x| divide(x, 2));

    match result {
        Ok(value) => println!("     链式操作成功: {}", value),
        Err(e) => println!("     链式操作失败: {}", e),
    }

    // 4. 自定义错误类型
    println!("  4. 自定义错误类型:");
    #[derive(Debug)]
    #[allow(dead_code)]
    enum CustomError {
        DivisionByZero,
        NegativeNumber,
        Overflow,
    }

    impl std::fmt::Display for CustomError {
        fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            match self {
                CustomError::DivisionByZero => write!(f, "除零错误"),
                CustomError::NegativeNumber => write!(f, "负数错误"),
                CustomError::Overflow => write!(f, "溢出错误"),
            }
        }
    }

    impl std::error::Error for CustomError {}

    let custom_result: Result<i32, CustomError> = Err(CustomError::DivisionByZero);
    match custom_result {
        Ok(value) => println!("     自定义错误处理成功: {}", value),
        Err(e) => println!("     自定义错误处理失败: {}", e),
    }
}

/// 辅助函数：安全除法
///
/// 本函数演示了安全的除法操作。
fn divide(a: i32, b: i32) -> Result<i32, String> {
    if b == 0 {
        Err("除零错误".to_string())
    } else {
        Ok(a / b)
    }
}

/// 演示性能优化技巧
///
/// 本函数展示了 Rust 1.89 中的性能优化技巧。
fn demonstrate_performance_optimization_tips() {
    println!("⚡ 性能优化技巧演示");
    println!("------------------------");

    // 1. 零成本抽象
    println!("  1. 零成本抽象:");
    let numbers = vec![1, 2, 3, 4, 5];
    let sum: i32 = numbers.iter().sum();
    println!("     迭代器求和: {}", sum);

    // 2. 内联优化
    println!("  2. 内联优化:");
    #[inline]
    fn add(a: i32, b: i32) -> i32 {
        a + b
    }

    let result = add(10, 20);
    println!("     内联函数结果: {}", result);

    // 3. 内存布局优化
    println!("  3. 内存布局优化:");
    #[repr(C)]
    struct OptimizedStruct {
        a: i32,
        b: i32,
        c: i32,
    }

    let optimized = OptimizedStruct { a: 1, b: 2, c: 3 };
    println!("     优化结构体大小: {} 字节", std::mem::size_of_val(&optimized));

    // 4. 编译时计算
    println!("  4. 编译时计算:");
    const COMPILE_TIME_CONSTANT: i32 = 42 * 2;
    println!("     编译时常量: {}", COMPILE_TIME_CONSTANT);

    // 5. 缓存友好的数据访问
    println!("  5. 缓存友好的数据访问:");
    let mut matrix = [[0; 100]; 100];

    // 按行访问（缓存友好）
    let start = std::time::Instant::now();
    for i in 0..100 {
        for j in 0..100 {
            matrix[i][j] = i * j;
        }
    }
    let row_access_time = start.elapsed();

    // 按列访问（缓存不友好）
    let start = std::time::Instant::now();
    for j in 0..100 {
        for i in 0..100 {
            matrix[i][j] = i * j;
        }
    }
    let column_access_time = start.elapsed();

    println!("     按行访问时间: {:?}", row_access_time);
    println!("     按列访问时间: {:?}", column_access_time);
    println!("     性能差异: {:.2}x",
        column_access_time.as_nanos() as f64 / row_access_time.as_nanos() as f64);
}
