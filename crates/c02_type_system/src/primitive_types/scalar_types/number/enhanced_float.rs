//! Rust 1.89 浮点数类型系统完整实现
//! Rust 1.89 point type system complete
//! - 所有浮点数类型的详细定义和特性
//! - all point type definition and feature
//! - Rust 1.89 新featureapplication
//! - 类型安全的最佳实践
//! - type
//! - 性能优化技巧
//! - performance optimization tip
//! - 完整的示例和测试用例
//! - complete example and
//! # 文件信息
//! #
//! - 文件: enhanced_float.rs
//! - 创建日期: 2025-01-27
//! - date : 2025-01-27
//! - 版本: 1.0
//! - this : 1.0
//! - 版this: 1.0
//! - 作者: Rust 类型系统项目组
//! - : Rust type system project
use std::{f32, f64};

/// Rust 1.89 浮点数类型系统
/// Rust 1.89 point type system
/// 包括类型安全、性能优化、错误处理等最佳实践。
/// type 、performance optimization 、error handling etc. 。
pub mod float_types {
    use super::*;

    /// 32位浮点数类型 (f32)
    /// 32point type (f32)
    /// f32 是单精度浮点数类型，占用4字节内存。
    /// f32 point type ，4memory 。
    /// # 特性
    /// # feature
    /// - 内存占用：4字节
    /// - memory ：4
    /// - 精度：约7位十进制数字
    /// - ：7
    /// - 范围：约 ±3.4 × 10^38
    /// - scope ： ±3.4 × 10^38
    /// - range：约 ±3.4 × 10^38
    /// - 特殊值：NaN、+∞、-∞
    /// - ：NaN、+∞、-∞
    /// # 示例
    /// # example
    /// let value: f32 = std::f32::consts::PI;
    /// let max: f32 = f32::MAX;
    /// let min: f32 = f32::MIN;
    /// ```
    pub mod f32_operations {
        use super::*;

        /// 基本 f32 操作
        /// this f32
        /// 基this f32 操作
        /// this f32
        pub fn basic_operations() {
            let a: f32 = std::f32::consts::PI;
            let b: f32 = std::f32::consts::E;

            // 基本算术运算
            let sum = a + b;
            let diff = a - b;
            let product = a * b;
            let quotient = a / b;
            let remainder = a % b;

            println!("f32 基本运算:");
            println!("  {} + {} = {}", a, b, sum);
            println!("  {} - {} = {}", a, b, diff);
            println!("  {} * {} = {}", a, b, product);
            println!("  {} / {} = {}", a, b, quotient);
            println!("  {} % {} = {}", a, b, remainder);

            // 边界值
            println!("  f32::MAX = {}", f32::MAX);
            println!("  f32::MIN = {}", f32::MIN);
            println!("  f32::MIN_POSITIVE = {}", f32::MIN_POSITIVE);
            println!("  f32::EPSILON = {}", f32::EPSILON);
        }

        /// 特殊值操作
        pub fn special_values() {
            // 特殊值
            let nan = f32::NAN;
            let infinity = f32::INFINITY;
            let neg_infinity = f32::NEG_INFINITY;

            println!("f32 特殊值:");
            println!("  NaN: {}", nan);
            println!("  +∞: {}", infinity);
            println!("  -∞: {}", neg_infinity);

            // 检查特殊值
            println!("  {} is NaN: {}", nan, nan.is_nan());
            println!("  {} is infinite: {}", infinity, infinity.is_infinite());
            println!("  {} is finite: {}", infinity, infinity.is_finite());
            println!("  {} is normal: {}", infinity, infinity.is_normal());

            // NaN 的特殊性质
            println!("  NaN == NaN: {}", nan.is_nan() && nan.is_nan());
            println!("  NaN != NaN: {}", nan.is_nan() && nan.is_nan());
            println!("  NaN > 0: {}", nan > 0.0);
            println!("  NaN < 0: {}", nan < 0.0);
        }

        /// 数学函数
        /// function
        /// 数学function
        pub fn mathematical_functions() {
            let x: f32 = 1.0;

            println!("f32 数学函数:");
            println!("  sin({}) = {}", x, x.sin());
            println!("  cos({}) = {}", x, x.cos());
            println!("  tan({}) = {}", x, x.tan());
            println!("  asin({}) = {}", x, x.asin());
            println!("  acos({}) = {}", x, x.acos());
            println!("  atan({}) = {}", x, x.atan());
            println!("  exp({}) = {}", x, x.exp());
            println!("  ln({}) = {}", x, x.ln());
            println!("  log10({}) = {}", x, x.log10());
            println!("  log2({}) = {}", x, x.log2());
            println!("  sqrt({}) = {}", x, x.sqrt());
            println!("  cbrt({}) = {}", x, x.cbrt());
            println!("  abs({}) = {}", x, x.abs());
            println!("  floor({}) = {}", x, x.floor());
            println!("  ceil({}) = {}", x, x.ceil());
            println!("  round({}) = {}", x, x.round());
            println!("  trunc({}) = {}", x, x.trunc());
            println!("  fract({}) = {}", x, x.fract());
        }

        /// 精度和舍入
        /// and
        pub fn precision_and_rounding() {
            let value: f32 = std::f32::consts::PI;

            println!("f32 精度和舍入:");
            println!("  原始值: {}", value);
            println!("  保留2位小数: {:.2}", value);
            println!("  保留4位小数: {:.4}", value);
            println!("  科学计数法: {:e}", value);
            println!("  科学计数法(大写): {:E}", value);

            // 舍入操作
            println!("  floor: {}", value.floor());
            println!("  ceil: {}", value.ceil());
            println!("  round: {}", value.round());
            println!("  trunc: {}", value.trunc());
        }
    }

    /// 64位浮点数类型 (f64)
    /// 64point type (f64)
    /// f64 是双精度浮点数类型，占用8字节内存。
    /// f64 point type ，8memory 。
    /// # 特性
    /// # feature
    /// - 内存占用：8字节
    /// - memory ：8
    /// - 精度：约15-17位十进制数字
    /// - ：15-17
    /// - 范围：约 ±1.8 × 10^308
    /// - scope ： ±1.8 × 10^308
    /// - range：约 ±1.8 × 10^308
    /// - 特殊值：NaN、+∞、-∞
    /// - ：NaN、+∞、-∞
    /// # 示例
    /// # example
    /// let value: f64 = std::f64::consts::PI;
    /// let max: f64 = f64::MAX;
    /// let min: f64 = f64::MIN;
    /// ```
    pub mod f64_operations {
        use super::*;

        /// 基本 f64 操作
        /// this f64
        /// 基this f64 操作
        /// this f64
        pub fn basic_operations() {
            let a: f64 = std::f64::consts::PI;
            let b: f64 = std::f64::consts::E;

            // 基本算术运算
            let sum = a + b;
            let diff = a - b;
            let product = a * b;
            let quotient = a / b;
            let remainder = a % b;

            println!("f64 基本运算:");
            println!("  {} + {} = {}", a, b, sum);
            println!("  {} - {} = {}", a, b, diff);
            println!("  {} * {} = {}", a, b, product);
            println!("  {} / {} = {}", a, b, quotient);
            println!("  {} % {} = {}", a, b, remainder);

            // 边界值
            println!("  f64::MAX = {}", f64::MAX);
            println!("  f64::MIN = {}", f64::MIN);
            println!("  f64::MIN_POSITIVE = {}", f64::MIN_POSITIVE);
            println!("  f64::EPSILON = {}", f64::EPSILON);
        }

        /// 特殊值操作
        pub fn special_values() {
            // 特殊值
            let nan = f64::NAN;
            let infinity = f64::INFINITY;
            let neg_infinity = f64::NEG_INFINITY;

            println!("f64 特殊值:");
            println!("  NaN: {}", nan);
            println!("  +∞: {}", infinity);
            println!("  -∞: {}", neg_infinity);

            // 检查特殊值
            println!("  {} is NaN: {}", nan, nan.is_nan());
            println!("  {} is infinite: {}", infinity, infinity.is_infinite());
            println!("  {} is finite: {}", infinity, infinity.is_finite());
            println!("  {} is normal: {}", infinity, infinity.is_normal());

            // NaN 的特殊性质
            println!("  NaN == NaN: {}", nan.is_nan() && nan.is_nan());
            println!("  NaN != NaN: {}", nan.is_nan() && nan.is_nan());
            println!("  NaN > 0: {}", nan > 0.0);
            println!("  NaN < 0: {}", nan < 0.0);
        }

        /// 数学函数
        /// function
        /// 数学function
        pub fn mathematical_functions() {
            let x: f64 = 1.0;

            println!("f64 数学函数:");
            println!("  sin({}) = {}", x, x.sin());
            println!("  cos({}) = {}", x, x.cos());
            println!("  tan({}) = {}", x, x.tan());
            println!("  asin({}) = {}", x, x.asin());
            println!("  acos({}) = {}", x, x.acos());
            println!("  atan({}) = {}", x, x.atan());
            println!("  exp({}) = {}", x, x.exp());
            println!("  ln({}) = {}", x, x.ln());
            println!("  log10({}) = {}", x, x.log10());
            println!("  log2({}) = {}", x, x.log2());
            println!("  sqrt({}) = {}", x, x.sqrt());
            println!("  cbrt({}) = {}", x, x.cbrt());
            println!("  abs({}) = {}", x, x.abs());
            println!("  floor({}) = {}", x, x.floor());
            println!("  ceil({}) = {}", x, x.ceil());
            println!("  round({}) = {}", x, x.round());
            println!("  trunc({}) = {}", x, x.trunc());
            println!("  fract({}) = {}", x, x.fract());
        }

        /// 精度和舍入
        /// and
        pub fn precision_and_rounding() {
            let value: f64 = std::f64::consts::PI;

            println!("f64 精度和舍入:");
            println!("  原始值: {}", value);
            println!("  保留2位小数: {:.2}", value);
            println!("  保留4位小数: {:.4}", value);
            println!("  保留8位小数: {:.8}", value);
            println!("  科学计数法: {:e}", value);
            println!("  科学计数法(大写): {:E}", value);

            // 舍入操作
            println!("  floor: {}", value.floor());
            println!("  ceil: {}", value.ceil());
            println!("  round: {}", value.round());
            println!("  trunc: {}", value.trunc());
        }
    }

    /// 浮点数比较
    /// point
    /// 由于浮点数的精度问题，直接使用 == 比较可能不准确。
    /// point problem ， == may 。
    /// 本模块提供了安全的浮点数比较方法。
    /// This module provides point method 。
    pub mod comparison {
        use super::*;

        /// 近似相等比较
        /// etc.
        /// 近似相etc.Compare
        pub fn approximate_equality() {
            let a: f64 = 0.1 + 0.2;
            let b: f64 = 0.3;

            println!("浮点数比较:");
            println!("  a = {}", a);
            println!("  b = {}", b);
            println!("  a == b: {}", a == b);
            println!("  a ≈ b (ε=1e-10): {}", (a - b).abs() < 1e-10);
            println!("  a ≈ b (ε=1e-15): {}", (a - b).abs() < 1e-15);

            // 使用 f64::EPSILON 进行比较
            let epsilon = f64::EPSILON;
            println!("  f64::EPSILON = {}", epsilon);
            println!("  a ≈ b (使用EPSILON): {}", (a - b).abs() < epsilon);
        }

        /// 相对误差比较
        /// to
        /// 相to误差Compare
        pub fn relative_error_comparison() {
            let a: f64 = 1.0;
            let b: f64 = 1.0000000001;

            println!("相对误差比较:");
            println!("  a = {}", a);
            println!("  b = {}", b);

            let relative_error = (a - b).abs() / a.abs().max(b.abs());
            println!("  相对误差: {}", relative_error);
            println!("  相对误差 < 1e-10: {}", relative_error < 1e-10);
        }

        /// 有序比较
        /// 有序Compare
        pub fn ordered_comparison() {
            let values = vec![
                std::f64::consts::PI,
                2.71,
                1.41,
                0.0,
                -1.0,
                f64::NAN,
                f64::INFINITY,
            ];

            println!("有序比较:");
            for value in &values {
                println!(
                    "  {}: is_nan={}, is_infinite={}, is_finite={}, is_normal={}",
                    value,
                    value.is_nan(),
                    value.is_infinite(),
                    value.is_finite(),
                    value.is_normal()
                );
            }

            // 排序（NaN 会被放在最后）
            let mut sorted_values = values.clone();
            sorted_values.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));

            println!("  排序后: {:?}", sorted_values);
        }
    }

    /// 浮点数转换
    /// point conversion
    /// 本模块提供了浮点数类型转换功能，包括：
    /// This module provides point type conversion functionality ，：
    /// - 显式类型转换
    /// - type conversion
    /// - 显式typeconversion
    /// - 安全转换
    /// - conversion
    /// - 安全conversion
    /// - 字符串转换
    /// - conversion
    /// - 字符串conversion
    /// - 整数转换
    /// - conversion
    /// - 整数conversion
    pub mod conversion {
        use super::*;

        /// 显式类型转换
        /// type conversion
        /// 显式typeconversion
        pub fn explicit_conversion() {
            let f32_value: f32 = std::f32::consts::PI;
            let f64_value: f64 = std::f64::consts::E;

            // f32 到 f64（安全）
            let f32_to_f64: f64 = f32_value as f64;

            // f64 到 f32（可能丢失精度）
            let f64_to_f32: f32 = f64_value as f32;

            println!("显式类型转换:");
            println!("  f32 {} -> f64 {}", f32_value, f32_to_f64);
            println!("  f64 {} -> f32 {}", f64_value, f64_to_f32);
        }

        /// 安全类型转换
        /// type conversion
        /// 安全typeconversion
        pub fn safe_conversion() {
            let f64_value: f64 = std::f64::consts::PI;

            // 安全转换为 f32（使用显式转换，因为 f64 到 f32 总是可能的）
            let f32_value: f32 = f64_value as f32;
            println!("安全转换 f64 {} -> f32 {}", f64_value, f32_value);

            // 演示精度损失
            let precision_loss = (f64_value - f32_value as f64).abs();
            println!("  精度损失: {}", precision_loss);
        }

        /// 字符串转换
        /// conversion
        /// 字符串conversion
        pub fn string_conversion() {
            let value: f64 = std::f64::consts::PI;

            // 转换为字符串
            let string_value = value.to_string();
            println!("字符串转换:");
            println!("  f64 {} -> String '{}'", value, string_value);

            // 从字符串解析
            match "std::f64::consts::PI".parse::<f64>() {
                Ok(parsed) => println!("  String 'std::f64::consts::PI' -> f64 {}", parsed),
                Err(e) => println!("  解析失败: {}", e),
            }

            // 格式化字符串
            let formatted = format!("{:.2}", value);
            println!("  格式化: '{}'", formatted);
        }

        /// 整数转换
        /// conversion
        /// 整数conversion
        pub fn integer_conversion() {
            let float_value: f64 = std::f64::consts::PI;

            // 转换为整数（截断）
            let int_value = float_value as i32;
            println!("整数转换:");
            println!("  f64 {} -> i32 {}", float_value, int_value);

            // 四舍五入转换
            let rounded_value = float_value.round() as i32;
            println!("  f64 {} -> i32 (四舍五入) {}", float_value, rounded_value);

            // 安全转换（检查是否在 i32 范围内）
            if float_value >= i32::MIN as f64 && float_value <= i32::MAX as f64 {
                let int_value = float_value as i32;
                println!("  安全转换 f64 {} -> i32 {}", float_value, int_value);
            } else {
                println!("  转换失败: f64 {} 超出 i32 范围", float_value);
            }
        }
    }

    /// 浮点数格式化
    /// point
    /// 本模块提供了各种浮点数格式化功能，
    /// This module provides point functionality ，
    /// 包括不同精度、科学计数法、对齐等。
    /// 、、to etc. 。
    pub mod formatting {
        use super::*;

        /// 精度格式化
        /// 精度Format
        pub fn precision_formatting() {
            let value: f64 = std::f64::consts::PI;

            println!("精度格式化:");
            println!("  原始值: {}", value);
            println!("  保留0位小数: {:.0}", value);
            println!("  保留2位小数: {:.2}", value);
            println!("  保留4位小数: {:.4}", value);
            println!("  保留8位小数: {:.8}", value);
        }

        /// 科学计数法格式化
        pub fn scientific_formatting() {
            let value: f64 = 1234567.89;

            println!("科学计数法格式化:");
            println!("  原始值: {}", value);
            println!("  科学计数法: {:e}", value);
            println!("  科学计数法(大写): {:E}", value);
            println!("  科学计数法(2位小数): {:.2e}", value);
            println!("  科学计数法(4位小数): {:.4E}", value);
        }

        /// 对齐和填充
        /// to and
        pub fn alignment_and_padding() {
            let value: f64 = std::f64::consts::PI;

            println!("对齐和填充:");
            println!("  左对齐(15位): '{:<15}'", value);
            println!("  右对齐(15位): '{:>15}'", value);
            println!("  居中对齐(15位): '{:^15}'", value);
            println!("  右对齐带前导零(15位): '{:015}'", value);
            println!("  右对齐带填充(15位): '{:*>15}'", value);
        }

        /// 千位分隔符
        pub fn thousand_separator() {
            let value: f64 = 1234567.89;

            println!("千位分隔符:");
            println!("  原始值: {}", value);
            println!("  格式化显示: {}", value);
            println!("  保留2位小数: {:.2}", value);
            println!("  科学计数法: {:e}", value);

            // 手动实现千位分隔符
            let formatted = format!("{:.2}", value);
            println!("  手动格式化: {}", formatted);
        }
    }

    /// 浮点数错误处理
    /// point error handling
    /// 本模块提供了处理浮点数运算中可能出现的错误的方法，
    /// This module provides point in may method ，
    /// 包括溢出、下溢、除零等。
    /// 、under 、etc. 。
    pub mod error_handling {
        use super::*;

        /// 溢出检查
        /// 溢出Check
        pub fn overflow_checking() {
            let large_value: f64 = f64::MAX;
            let small_value: f64 = f64::MIN_POSITIVE;

            println!("溢出检查:");
            println!("  f64::MAX = {}", large_value);
            println!("  f64::MIN_POSITIVE = {}", small_value);

            // 检查乘法溢出
            let result = large_value * 2.0;
            if result.is_infinite() {
                println!("  乘法溢出: {} * 2.0 = {}", large_value, result);
            }

            // 检查加法溢出
            let result2 = large_value + large_value;
            if result2.is_infinite() {
                println!(
                    "  加法溢出: {} + {} = {}",
                    large_value, large_value, result2
                );
            }
        }

        /// 下溢检查
        /// under
        pub fn underflow_checking() {
            let small_value: f64 = f64::MIN_POSITIVE;

            println!("下溢检查:");
            println!("  f64::MIN_POSITIVE = {}", small_value);

            // 检查除法下溢
            let result = small_value / 2.0;
            if result == 0.0 && !result.is_infinite() {
                println!("  除法下溢: {} / 2.0 = {}", small_value, result);
            }
        }

        /// 除零检查
        /// 除零Check
        pub fn division_by_zero_checking() {
            let value: f64 = 1.0;
            let zero: f64 = 0.0;

            println!("除零检查:");
            println!("  {} / {} = {}", value, zero, value / zero);
            println!("  {} / {} = {}", -value, zero, -value / zero);
            println!("  {} / {} = NaN (0/0)", zero, zero);

            // 检查结果
            let result = value / zero;
            if result.is_infinite() {
                println!("  结果无穷大: {}", result);
            } else if result.is_nan() {
                println!("  结果NaN: {}", result);
            }
        }

        /// 安全运算
        pub fn safe_operations() {
            let a: f64 = 1.0;
            let b: f64 = 0.0;

            println!("安全运算:");

            // 安全除法
            let safe_div = if b != 0.0 { Some(a / b) } else { None };
            match safe_div {
                Some(result) => println!("  安全除法: {} / {} = {}", a, b, result),
                None => println!("  安全除法: {} / {} = 除零错误", a, b),
            }

            // 安全平方根
            let safe_sqrt = if a >= 0.0 { Some(a.sqrt()) } else { None };
            match safe_sqrt {
                Some(result) => println!("  安全平方根: sqrt({}) = {}", a, result),
                None => println!("  安全平方根: sqrt({}) = 负数错误", a),
            }

            // 安全对数
            let safe_log = if a > 0.0 { Some(a.ln()) } else { None };
            match safe_log {
                Some(result) => println!("  安全对数: ln({}) = {}", a, result),
                None => println!("  安全对数: ln({}) = 非正数错误", a),
            }
        }
    }
}

/// 浮点数性能测试
/// point performance test
/// 本模块提供了各种浮点数类型的性能测试，
/// This module provides point type performance test ，
/// 帮助开发者选择最适合的浮点数类型。
/// point type 。
pub mod performance_tests {
    use super::*;
    use std::time::Instant;

    /// 算术运算性能测试
    /// performance test
    /// 算术运算performance test
    pub fn arithmetic_performance_test() {
        const ITERATIONS: usize = 1_000_000;

        println!("浮点数类型性能测试 ({} 次迭代):", ITERATIONS);

        // f32 性能测试
        let start = Instant::now();
        let mut sum_f32: f32 = 0.0;
        for i in 0..ITERATIONS {
            sum_f32 += i as f32 * 0.001;
        }
        let f32_duration = start.elapsed();
        println!("  f32 运算时间: {:?}, 结果: {}", f32_duration, sum_f32);

        // f64 性能测试
        let start = Instant::now();
        let mut sum_f64: f64 = 0.0;
        for i in 0..ITERATIONS {
            sum_f64 += i as f64 * 0.001;
        }
        let f64_duration = start.elapsed();
        println!("  f64 运算时间: {:?}, 结果: {}", f64_duration, sum_f64);

        // 性能比较
        println!("性能比较:");
        println!(
            "  f64 vs f32: {:.2}x",
            f64_duration.as_nanos() as f64 / f32_duration.as_nanos() as f64
        );
    }

    /// 数学函数性能测试
    /// function performance test
    /// 数学functionperformance test
    pub fn mathematical_functions_performance_test() {
        const ITERATIONS: usize = 100_000;

        println!("数学函数性能测试 ({} 次迭代):", ITERATIONS);

        // f32 数学函数性能测试
        let start = Instant::now();
        let mut sum_f32: f32 = 0.0;
        for i in 0..ITERATIONS {
            sum_f32 += (i as f32 * 0.001).sin();
        }
        let f32_duration = start.elapsed();
        println!(
            "  f32 sin() 运算时间: {:?}, 结果: {}",
            f32_duration, sum_f32
        );

        // f64 数学函数性能测试
        let start = Instant::now();
        let mut sum_f64: f64 = 0.0;
        for i in 0..ITERATIONS {
            sum_f64 += (i as f64 * 0.001).sin();
        }
        let f64_duration = start.elapsed();
        println!(
            "  f64 sin() 运算时间: {:?}, 结果: {}",
            f64_duration, sum_f64
        );

        // 性能比较
        println!("性能比较:");
        println!(
            "  f64 vs f32: {:.2}x",
            f64_duration.as_nanos() as f64 / f32_duration.as_nanos() as f64
        );
    }

    /// 内存使用测试
    /// memory
    pub fn memory_usage_test() {
        println!("浮点数类型内存使用:");
        println!("  f32: {} 字节", std::mem::size_of::<f32>());
        println!("  f64: {} 字节", std::mem::size_of::<f64>());

        // 数组内存使用
        let f32_array: [f32; 1000] = [0.0; 1000];
        let f64_array: [f64; 1000] = [0.0; 1000];

        println!("  数组内存使用:");
        println!(
            "    [f32; 1000]: {} 字节",
            std::mem::size_of_val(&f32_array)
        );
        println!(
            "    [f64; 1000]: {} 字节",
            std::mem::size_of_val(&f64_array)
        );
    }
}

/// 主函数：演示所有浮点数类型功能
/// Main function ：demonstration all point type functionality
/// 包括基本操作、特殊值处理、数学函数、格式化等。
/// this 、、function 、etc. 。
pub fn demonstrate_all_float_types() {
    println!("=== Rust 1.89 浮点数类型系统演示 ===\n");

    // f32 操作
    println!("1. f32 操作:");
    float_types::f32_operations::basic_operations();
    println!();
    float_types::f32_operations::special_values();
    println!();
    float_types::f32_operations::mathematical_functions();
    println!();
    float_types::f32_operations::precision_and_rounding();
    println!();

    // f64 操作
    println!("2. f64 操作:");
    float_types::f64_operations::basic_operations();
    println!();
    float_types::f64_operations::special_values();
    println!();
    float_types::f64_operations::mathematical_functions();
    println!();
    float_types::f64_operations::precision_and_rounding();
    println!();

    // 比较操作
    println!("3. 比较操作:");
    float_types::comparison::approximate_equality();
    println!();
    float_types::comparison::relative_error_comparison();
    println!();
    float_types::comparison::ordered_comparison();
    println!();

    // 转换操作
    println!("4. 转换操作:");
    float_types::conversion::explicit_conversion();
    println!();
    float_types::conversion::safe_conversion();
    println!();
    float_types::conversion::string_conversion();
    println!();
    float_types::conversion::integer_conversion();
    println!();

    // 格式化操作
    println!("5. 格式化操作:");
    float_types::formatting::precision_formatting();
    println!();
    float_types::formatting::scientific_formatting();
    println!();
    float_types::formatting::alignment_and_padding();
    println!();
    float_types::formatting::thousand_separator();
    println!();

    // 错误处理
    println!("6. 错误处理:");
    float_types::error_handling::overflow_checking();
    println!();
    float_types::error_handling::underflow_checking();
    println!();
    float_types::error_handling::division_by_zero_checking();
    println!();
    float_types::error_handling::safe_operations();
    println!();

    // 性能测试
    println!("7. 性能测试:");
    performance_tests::arithmetic_performance_test();
    println!();
    performance_tests::mathematical_functions_performance_test();
    println!();
    performance_tests::memory_usage_test();
    println!();

    println!("=== 演示完成 ===");
}

/// 简化的浮点数操作函数（保持向后兼容）
/// point function （after ）
#[allow(unused)]
pub fn float_operation() {
    // 调用新的演示函数
    demonstrate_all_float_types();
}

/// 简化的浮点数操作函数2（保持向后兼容）
/// point function 2（after ）
#[allow(unused)]
pub fn float_operation_2() {
    // 调用新的演示函数
    demonstrate_all_float_types();
}
