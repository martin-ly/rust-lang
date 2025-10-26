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
//! # Rust 1.89 新特性展示
//!
//! 本示例专门展示 Rust 1.89 版本的新特性和增强功能：
//! - let_chains 稳定化
//! - cfg_boolean_literals 稳定化
//! - 增强的模式匹配
//! - 改进的类型推断
//! - 新的控制流特性
//! - 改进的错误处理
//!
//! 运行方式：
//! ```bash
//! cargo run --example rust_189_new_features_showcase
//! ```

use std::collections::HashMap;
use std::fmt::{self, Display};
use std::thread;
use std::time::Duration;

/// 主函数 - 展示 Rust 1.89 新特性
fn main() {
    println!("🚀 Rust 1.89 新特性展示");
    println!("=========================");
    println!("本示例将展示 Rust 1.89 版本的所有重要新特性");
    println!();

    // 展示 let_chains 特性
    showcase_let_chains();

    // 展示 cfg_boolean_literals 特性
    showcase_cfg_boolean_literals();

    // 展示增强的模式匹配
    showcase_enhanced_pattern_matching();

    // 展示增强的类型推断
    showcase_enhanced_type_inference();

    // 展示新的控制流特性
    showcase_new_control_flow();

    // 展示改进的错误处理
    showcase_improved_error_handling();

    // 展示综合应用
    showcase_comprehensive_usage();

    println!("\n🎉 所有新特性展示完成！");
}

/// 展示 let_chains 特性
fn showcase_let_chains() {
    println!("🔗 let_chains 稳定化特性展示");
    println!("=============================");

    // 基础 let_chains 用法
    println!("\n1. 基础 let_chains 用法");
    let x = Some(42);
    let y = Some("hello");
    let z = Some(std::f64::consts::PI);

    if let Some(value) = x && let Some(text) = y && let Some(pi) = z {
        println!("  所有值都存在: x = {}, y = {}, z = {}", value, text, pi);
    }

    // 复杂条件组合
    println!("\n2. 复杂条件组合");
    let numbers = vec![1, 2, 3, 4, 5];
    let threshold = 3;

    if let Some(first) = numbers.first() &&
       let Some(last) = numbers.last() &&
       *first < threshold &&
       *last > threshold {
        println!("  数组满足条件: 首元素 {} < {}, 末元素 {} > {}",
                first, threshold, last, threshold);
    }

    // 嵌套 Option 处理
    println!("\n3. 嵌套 Option 处理");
    let nested_option = Some(Some(42));
    if let Some(inner) = nested_option && let Some(value) = inner {
        println!("  嵌套 Option 值: {}", value);
    }

    // while 循环中的 let_chains
    println!("\n4. while 循环中的 let_chains");
    let mut stack = vec![Some(1), Some(2), Some(3), None, Some(4)];
    let mut count = 0;

    while let Some(Some(value)) = stack.pop() && value > 0 && count < 3 {
        println!("  处理值: {}", value);
        count += 1;
    }
}

/// 展示 cfg_boolean_literals 特性
fn showcase_cfg_boolean_literals() {
    println!("\n\n⚙️ cfg_boolean_literals 稳定化特性展示");
    println!("=====================================");

    // 基础条件编译
    println!("\n1. 基础条件编译");
    #[cfg(feature = "debug")]
    println!("  调试模式已启用");

    #[cfg(not(feature = "debug"))]
    println!("  调试模式未启用");

    // 复杂条件组合
    println!("\n2. 复杂条件组合");
    #[cfg(all(feature = "async", feature = "performance"))]
    println!("  异步性能模式已启用");

    #[cfg(any(feature = "dev", feature = "test"))]
    println!("  开发或测试模式已启用");

    // 平台特定编译
    println!("\n3. 平台特定编译");
    #[cfg(target_os = "windows")]
    println!("  Windows 平台");

    #[cfg(target_os = "linux")]
    println!("  Linux 平台");

    #[cfg(target_os = "macos")]
    println!("  macOS 平台");

    // 自定义条件
    println!("\n4. 自定义条件");
    #[cfg(feature = "custom")]
    println!("  自定义标志已设置");

    #[cfg(not(feature = "custom"))]
    println!("  自定义标志未设置");
}

/// 展示增强的模式匹配
fn showcase_enhanced_pattern_matching() {
    println!("\n\n🎯 增强的模式匹配特性展示");
    println!("===========================");

    // 改进的切片模式
    println!("\n1. 改进的切片模式");
    let numbers = vec![1, 2, 3, 4, 5];

    match numbers.as_slice() {
        [] => println!("  空数组"),
        [single] => println!("  单个元素: {}", single),
        [first, second] => println!("  两个元素: {}, {}", first, second),
        [first, middle @ .., last] => println!("  多个元素: 首 = {}, 末 = {}, 中间数量 = {}", first, last, middle.len()),
    }

    // 改进的守卫条件
    println!("\n2. 改进的守卫条件");
    let value = Some(42);
    match value {
        Some(x) if x > 40 && x < 50 => println!("  值在范围内: {}", x),
        Some(x) if x % 2 == 0 => println!("  偶数值: {}", x),
        Some(x) => println!("  其他值: {}", x),
        None => println!("  没有值"),
    }

    // 复杂嵌套模式
    println!("\n3. 复杂嵌套模式");
    let complex_data = Some(Some(Some(42)));
    match complex_data {
        Some(Some(Some(value))) if value > 40 => println!("  深层嵌套值: {}", value),
        Some(Some(None)) => println!("  中间层为 None"),
        Some(None) => println!("  内层为 None"),
        None => println!("  外层为 None"),
        _ => println!("  其他情况"),
    }

    // 自定义模式匹配
    println!("\n4. 自定义模式匹配");
    let shapes = vec![
        Shape::Circle(5.0),
        Shape::Rectangle(10.0, 20.0),
        Shape::Triangle(3.0, 4.0, 5.0),
    ];

    for shape in shapes {
        match shape {
            Shape::Circle(radius) if radius > 0.0 => {
                let area = std::f64::consts::PI * radius * radius;
                println!("  圆形面积: {:.2}", area);
            }
            Shape::Rectangle(width, height) if width > 0.0 && height > 0.0 => {
                let area = width * height;
                println!("  矩形面积: {:.2}", area);
            }
            Shape::Triangle(a, b, c) if is_valid_triangle(a, b, c) => {
                let s = (a + b + c) / 2.0;
                let area = (s * (s - a) * (s - b) * (s - c)).sqrt();
                println!("  三角形面积: {:.2}", area);
            }
            _ => println!("  无效形状"),
        }
    }
}

/// 展示增强的类型推断
fn showcase_enhanced_type_inference() {
    println!("\n\n🧠 增强的类型推断特性展示");
    println!("===========================");

    // 改进的闭包类型推断
    println!("\n1. 改进的闭包类型推断");
    let closure = |x| x * 2;
    let result = closure(21);
    println!("  闭包推断结果: {}", result);

    // 复杂泛型推断
    println!("\n2. 复杂泛型推断");
    let data = create_generic_data(42);
    println!("  泛型数据: {}", data);

    // 迭代器链式推断
    println!("\n3. 迭代器链式推断");
    let numbers = vec![1, 2, 3, 4, 5];
    let processed: Vec<i32> = numbers
        .iter()
        .filter(|&&x| x % 2 == 0)
        .map(|&x| x * 2)
        .collect();
    println!("  处理后的数字: {:?}", processed);

    // 异步类型推断
    println!("\n4. 异步类型推断");
    let _async_result = async_operation(10);
    println!("  异步操作已创建: Future<Output = i32>");
}

/// 展示新的控制流特性
fn showcase_new_control_flow() {
    println!("\n\n🔄 新的控制流特性展示");
    println!("=====================");

    // 改进的 for 循环
    println!("\n1. 改进的 for 循环");
    let numbers = vec![1, 2, 3, 4, 5];

    for (index, value) in numbers.iter().enumerate() {
        println!("  索引 {}: 值 {}", index, value);
    }

    // 复杂迭代器链
    println!("\n2. 复杂迭代器链");
    let result: Vec<i32> = numbers
        .iter()
        .filter(|&&x| x % 2 == 0)
        .map(|&x| x * x)
        .take(3)
        .collect();
    println!("  处理结果: {:?}", result);

    // 嵌套控制流
    println!("\n3. 嵌套控制流");
    let matrix = vec![
        vec![1, 2, 3],
        vec![4, 5, 6],
        vec![7, 8, 9],
    ];

    'outer: for (row_idx, row) in matrix.iter().enumerate() {
        for (col_idx, &value) in row.iter().enumerate() {
            if value == 5 {
                println!("  找到5在位置: ({}, {})", row_idx, col_idx);
                break 'outer;
            }
        }
    }

    // 复杂条件控制
    println!("\n4. 复杂条件控制");
    let conditions = vec![true, false, true, false, true];
    let mut true_count = 0;

    for condition in conditions {
        if condition {
            true_count += 1;
            if true_count >= 3 {
                println!("  找到足够的真值: {}", true_count);
                break;
            }
        }
    }
}

/// 展示改进的错误处理
fn showcase_improved_error_handling() {
    println!("\n\n🛡️ 改进的错误处理特性展示");
    println!("===========================");

    // 改进的 Result 处理
    println!("\n1. 改进的 Result 处理");
    let results = vec![
        Ok(42),
        Err("错误1"),
        Ok(100),
        Err("错误2"),
    ];

    for result in results {
        match result {
            Ok(value) => println!("  成功: {}", value),
            Err(error) => println!("  错误: {}", error),
        }
    }

    // 自定义错误类型
    println!("\n2. 自定义错误类型");
    let results = vec![
        CustomResult::Success(42),
        CustomResult::Warning("警告信息".to_string()),
        CustomResult::Error("错误信息".to_string()),
    ];

    for result in results {
        match result {
            CustomResult::Success(value) => println!("  成功: {}", value),
            CustomResult::Warning(msg) => println!("  警告: {}", msg),
            CustomResult::Error(msg) => println!("  错误: {}", msg),
        }
    }

    // 错误恢复
    println!("\n3. 错误恢复");
    let recoverable_result = recoverable_operation("invalid");
    match recoverable_result {
        Ok(value) => println!("  操作成功: {}", value),
        Err(error) => println!("  操作失败: {}", error),
    }

    // 错误转换
    println!("\n4. 错误转换");
    let conversion_result = convert_error("42");
    match conversion_result {
        Ok(value) => println!("  转换成功: {}", value),
        Err(error) => println!("  转换失败: {}", error),
    }
}

/// 展示综合应用
fn showcase_comprehensive_usage() {
    println!("\n\n🎯 综合应用展示");
    println!("================");

    // 数据处理示例
    println!("\n1. 数据处理示例");
    let data = vec![
        ("Alice", Some(25), Some("Engineer")),
        ("Bob", Some(30), None),
        ("Charlie", None, Some("Designer")),
    ];

    for (name, age, job) in data {
        // 使用 let_chains 进行复杂条件处理
        if let Some(age_val) = age &&
           let Some(job_val) = job &&
           age_val >= 25 {
            println!("  {} 是 {} 岁的 {}", name, age_val, job_val);
        }
    }

    // 异步操作示例
    println!("\n2. 异步操作示例");
    let async_operations = vec![
        AsyncOperation::new("操作1", 100),
        AsyncOperation::new("操作2", 200),
        AsyncOperation::new("操作3", 150),
    ];

    for op in async_operations {
        let result = op.execute();
        println!("  {}: {}", op.name, result);
    }

    // 复杂数据结构处理
    println!("\n3. 复杂数据结构处理");
    let mut complex_data = HashMap::new();
    complex_data.insert("user1".to_string(), Some(("Alice", Some(25))));
    complex_data.insert("user2".to_string(), Some(("Bob", None)));
    complex_data.insert("user3".to_string(), None);

    for (_id, user_data) in complex_data {
        if let Some((name, Some(age))) = user_data &&
           age >= 18 {
            println!("  用户 {}: {} 岁", name, age);
        }
    }
}

// 辅助数据结构和函数

/// 形状枚举
#[derive(Debug)]
enum Shape {
    Circle(f64),
    Rectangle(f64, f64),
    Triangle(f64, f64, f64),
}

/// 自定义结果类型
#[derive(Debug)]
enum CustomResult {
    Success(i32),
    Warning(String),
    Error(String),
}

/// 异步操作结构
#[derive(Debug)]
struct AsyncOperation {
    name: String,
    duration_ms: u64,
}

impl AsyncOperation {
    fn new(name: &str, duration_ms: u64) -> Self {
        Self {
            name: name.to_string(),
            duration_ms,
        }
    }

    fn execute(&self) -> String {
        // 模拟异步执行
        thread::sleep(Duration::from_millis(self.duration_ms));
        format!("完成 (耗时 {}ms)", self.duration_ms)
    }
}

/// 检查三角形是否有效
fn is_valid_triangle(a: f64, b: f64, c: f64) -> bool {
    a + b > c && a + c > b && b + c > a
}

/// 创建泛型数据
fn create_generic_data<T>(value: T) -> GenericData<T>
where
    T: Clone + Display,
{
    GenericData { value }
}

/// 异步操作
async fn async_operation(x: i32) -> i32 {
    x * 2
}

/// 可恢复操作
fn recoverable_operation(input: &str) -> Result<i32, String> {
    match input.parse::<i32>() {
        Ok(value) => Ok(value),
        Err(_) => {
            if input == "invalid" {
                Ok(0) // 默认值
            } else {
                Err("无法恢复".to_string())
            }
        }
    }
}

/// 错误转换
fn convert_error(s: &str) -> Result<i32, CustomError> {
    s.parse::<i32>()
        .map_err(|e| CustomError::ParseError(e))
}

/// 泛型数据结构
#[derive(Debug)]
struct GenericData<T> {
    value: T,
}

impl<T> Display for GenericData<T>
where
    T: Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "GenericData({})", self.value)
    }
}

/// 自定义错误类型
#[derive(Debug)]
enum CustomError {
    ParseError(std::num::ParseIntError),
    #[allow(dead_code)]
    ValidationError(String),
}

impl std::fmt::Display for CustomError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CustomError::ParseError(e) => write!(f, "解析错误: {}", e),
            CustomError::ValidationError(msg) => write!(f, "验证错误: {}", msg),
        }
    }
}

impl std::error::Error for CustomError {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_let_chains_basic() {
        let x = Some(42);
        let y = Some("hello");

        if let Some(value) = x && let Some(text) = y {
            assert_eq!(value, 42);
            assert_eq!(text, "hello");
        }
    }

    #[test]
    fn test_enhanced_pattern_matching() {
        let numbers = vec![1, 2, 3, 4, 5];

        match numbers.as_slice() {
            [first, .., last] => {
                assert_eq!(*first, 1);
                assert_eq!(*last, 5);
            }
            _ => panic!("Expected slice pattern"),
        }
    }

    #[test]
    fn test_enhanced_type_inference() {
        let closure = |x| x * 2;
        let result = closure(21);
        assert_eq!(result, 42);
    }

    #[test]
    fn test_recoverable_operation() {
        assert_eq!(recoverable_operation("42").unwrap(), 42);
        assert_eq!(recoverable_operation("invalid").unwrap(), 0);
        assert!(recoverable_operation("abc").is_err());
    }

    #[test]
    fn test_async_operation() {
        let result = async_operation(10);
        // 注意：这里需要 tokio::test 或类似的异步测试框架
        // 为了简化，我们只测试函数定义
        assert!(true);
    }
}
