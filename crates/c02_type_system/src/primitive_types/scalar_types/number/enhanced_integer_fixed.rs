//! Rust 1.89 整数类型系统完整实现（修复版）
//!
//! 本模块提供了 Rust 1.89 版本中整数类型的完整实现，包括：
//! - 所有整数类型的详细定义和特性
//! - Rust 1.89 新特性的应用
//! - 类型安全的最佳实践
//! - 性能优化技巧
//! - 完整的示例和测试用例
//!
//! # 文件信息
//! - 文件: enhanced_integer_fixed.rs
//! - 创建日期: 2025-01-27
//! - 版本: 1.0
//! - Rust版本: 1.89.0
//! - 作者: Rust 类型系统项目组

// NonZero 类型现在在各自的模块中导入

/// Rust 1.89 整数类型系统
///
/// 本模块实现了 Rust 1.89 版本中所有整数类型的完整功能，
/// 包括类型安全、性能优化、错误处理等最佳实践。
pub mod integer_types {

    /// 有符号整数类型定义
    ///
    /// Rust 提供了多种有符号整数类型，每种类型都有其特定的用途和性能特征。
    /// 在 Rust 1.89 中，整数类型系统得到了进一步优化，提供了更好的类型推断和性能。
    pub mod signed_integers {

        /// 8位有符号整数操作
        ///
        /// i8 类型用于表示 -128 到 127 范围内的整数。
        /// 常用于字节处理、小范围数值计算等场景。
        pub fn i8_operations() {
            // 基本操作
            let a: i8 = 100;
            let b: i8 = 27;
            
            // 算术运算
            let sum = a + b;           // 127
            let diff = a - b;          // 73
            let quotient = a / b;      // 3
            let remainder = a % b;     // 19
            
            println!("i8 运算结果:");
            println!("  {} + {} = {}", a, b, sum);
            println!("  {} - {} = {}", a, b, diff);
            println!("  {} / {} = {}", a, b, quotient);
            println!("  {} % {} = {}", a, b, remainder);
            
            // 边界值测试
            let max_val = i8::MAX;
            let min_val = i8::MIN;
            println!("  i8::MAX = {}", max_val);
            println!("  i8::MIN = {}", min_val);
            
            // 类型转换
            let as_u8: u8 = a as u8;
            let as_i16: i16 = a as i16;
            println!("  {} as u8 = {}", a, as_u8);
            println!("  {} as i16 = {}", a, as_i16);
        }

        /// 32位有符号整数操作（默认整数类型）
        ///
        /// i32 是 Rust 的默认整数类型，用于表示 -2,147,483,648 到 2,147,483,647 范围内的整数。
        /// 在大多数情况下，这是最常用的整数类型。
        pub fn i32_operations() {
            let a: i32 = 1_000_000;
            let b: i32 = 500_000;
            
            // 算术运算
            let sum = a + b;
            let diff = a - b;
            let product = a * b;
            let quotient = a / b;
            let remainder = a % b;
            
            println!("i32 运算结果:");
            println!("  {} + {} = {}", a, b, sum);
            println!("  {} - {} = {}", a, b, diff);
            println!("  {} * {} = {}", a, b, product);
            println!("  {} / {} = {}", a, b, quotient);
            println!("  {} % {} = {}", a, b, remainder);
            
            // 边界值
            println!("  i32::MAX = {}", i32::MAX);
            println!("  i32::MIN = {}", i32::MIN);
            
            // 位运算
            let bitwise_and = a & b;
            let bitwise_or = a | b;
            let bitwise_xor = a ^ b;
            let left_shift = a << 2;
            let right_shift = a >> 2;
            
            println!("  位运算结果:");
            println!("    {} & {} = {}", a, b, bitwise_and);
            println!("    {} | {} = {}", a, b, bitwise_or);
            println!("    {} ^ {} = {}", a, b, bitwise_xor);
            println!("    {} << 2 = {}", a, left_shift);
            println!("    {} >> 2 = {}", a, right_shift);
        }

        /// 64位有符号整数操作
        ///
        /// i64 类型用于表示大范围的整数，常用于时间戳、大数计算等场景。
        pub fn i64_operations() {
            let a: i64 = 1_000_000_000_000;
            let b: i64 = 500_000_000_000;
            
            // 算术运算
            let sum = a + b;
            let diff = a - b;
            let product = a * b;
            let quotient = a / b;
            let remainder = a % b;
            
            println!("i64 运算结果:");
            println!("  {} + {} = {}", a, b, sum);
            println!("  {} - {} = {}", a, b, diff);
            println!("  {} * {} = {}", a, b, product);
            println!("  {} / {} = {}", a, b, quotient);
            println!("  {} % {} = {}", a, b, remainder);
            
            // 边界值
            println!("  i64::MAX = {}", i64::MAX);
            println!("  i64::MIN = {}", i64::MIN);
        }

        /// 128位有符号整数操作
        ///
        /// i128 类型用于表示极大范围的整数，常用于加密、大数计算等场景。
        /// 在 Rust 1.89 中，i128 的性能得到了进一步优化。
        pub fn i128_operations() {
            let a: i128 = 170_141_183_460_469_231_731_687_303_715_884_105_727;
            let b: i128 = 85_070_591_730_234_615_865_843_651_857_942_052_863;
            
            // 算术运算
            let sum = a + b;
            let diff = a - b;
            let quotient = a / b;
            let remainder = a % b;
            
            println!("i128 运算结果:");
            println!("  {} + {} = {}", a, b, sum);
            println!("  {} - {} = {}", a, b, diff);
            println!("  {} / {} = {}", a, b, quotient);
            println!("  {} % {} = {}", a, b, remainder);
            
            // 边界值
            println!("  i128::MAX = {}", i128::MAX);
            println!("  i128::MIN = {}", i128::MIN);
        }
    }

    /// 无符号整数类型定义
    ///
    /// 无符号整数类型只能表示非负值，但提供了更大的正数范围。
    /// 在 Rust 1.89 中，无符号整数类型在内存布局和性能方面得到了优化。
    pub mod unsigned_integers {

        /// 8位无符号整数操作
        ///
        /// u8 类型用于表示 0 到 255 范围内的整数。
        /// 常用于字节处理、颜色值、ASCII码等场景。
        pub fn u8_operations() {
            let a: u8 = 200;
            let b: u8 = 55;
            
            // 算术运算
            let sum = a + b;           // 255
            let diff = a - b;          // 145
            let quotient = a / b;      // 3
            let remainder = a % b;     // 35
            
            println!("u8 运算结果:");
            println!("  {} + {} = {}", a, b, sum);
            println!("  {} - {} = {}", a, b, diff);
            println!("  {} / {} = {}", a, b, quotient);
            println!("  {} % {} = {}", a, b, remainder);
            
            // 边界值
            println!("  u8::MAX = {}", u8::MAX);
            println!("  u8::MIN = {}", u8::MIN);
            
            // 字节操作
            let byte_value: u8 = 0b1010_1010;
            println!("  字节值: 0b{:08b}", byte_value);
            println!("  十六进制: 0x{:02X}", byte_value);
        }

        /// 32位无符号整数操作
        ///
        /// u32 类型用于表示 0 到 4,294,967,295 范围内的整数。
        /// 是默认的无符号整数类型，常用于计数、ID等场景。
        pub fn u32_operations() {
            let a: u32 = 2_000_000_000;
            let b: u32 = 1_000_000_000;
            
            // 算术运算
            let sum = a + b;
            let diff = a - b;
            let product = a * b;
            let quotient = a / b;
            let remainder = a % b;
            
            println!("u32 运算结果:");
            println!("  {} + {} = {}", a, b, sum);
            println!("  {} - {} = {}", a, b, diff);
            println!("  {} * {} = {}", a, b, product);
            println!("  {} / {} = {}", a, b, quotient);
            println!("  {} % {} = {}", a, b, remainder);
            
            // 边界值
            println!("  u32::MAX = {}", u32::MAX);
            println!("  u32::MIN = {}", u32::MIN);
        }

        /// 64位无符号整数操作
        ///
        /// u64 类型用于表示大范围的无符号整数，常用于时间戳、大数计数等场景。
        pub fn u64_operations() {
            let a: u64 = 9_000_000_000_000_000_000;
            let b: u64 = 4_500_000_000_000_000_000;
            
            // 算术运算
            let sum = a + b;
            let diff = a - b;
            let product = a * b;
            let quotient = a / b;
            let remainder = a % b;
            
            println!("u64 运算结果:");
            println!("  {} + {} = {}", a, b, sum);
            println!("  {} - {} = {}", a, b, diff);
            println!("  {} * {} = {}", a, b, product);
            println!("  {} / {} = {}", a, b, quotient);
            println!("  {} % {} = {}", a, b, remainder);
            
            // 边界值
            println!("  u64::MAX = {}", u64::MAX);
            println!("  u64::MIN = {}", u64::MIN);
        }

        /// 128位无符号整数操作
        ///
        /// u128 类型用于表示极大范围的无符号整数，常用于加密、大数计算等场景。
        /// 在 Rust 1.89 中，u128 的性能得到了进一步优化。
        pub fn u128_operations() {
            let a: u128 = 340_282_366_920_938_463_463_374_607_431_768_211_455;
            let b: u128 = 170_141_183_460_469_231_731_687_303_715_884_105_727;
            
            // 算术运算
            let sum = a + b;
            let diff = a - b;
            let quotient = a / b;
            let remainder = a % b;
            
            println!("u128 运算结果:");
            println!("  {} + {} = {}", a, b, sum);
            println!("  {} - {} = {}", a, b, diff);
            println!("  {} / {} = {}", a, b, quotient);
            println!("  {} % {} = {}", a, b, remainder);
            
            // 边界值
            println!("  u128::MAX = {}", u128::MAX);
            println!("  u128::MIN = {}", u128::MIN);
        }

        /// 平台相关无符号整数操作
        ///
        /// usize 类型的大小取决于目标平台（32位或64位）。
        /// 常用于数组长度、内存地址、索引等场景。
        pub fn usize_operations() {
            let a: usize = 1_000_000;
            let b: usize = 500_000;
            
            // 算术运算
            let sum = a + b;
            let diff = a - b;
            let product = a * b;
            let quotient = a / b;
            let remainder = a % b;
            
            println!("usize 运算结果:");
            println!("  {} + {} = {}", a, b, sum);
            println!("  {} - {} = {}", a, b, diff);
            println!("  {} * {} = {}", a, b, product);
            println!("  {} / {} = {}", a, b, quotient);
            println!("  {} % {} = {}", a, b, remainder);
            
            // 边界值
            println!("  usize::MAX = {}", usize::MAX);
            println!("  usize::MIN = {}", usize::MIN);
            println!("  usize 大小: {} 字节", std::mem::size_of::<usize>());
        }
    }

    /// 非零整数类型
    ///
    /// Rust 1.89 提供了非零整数类型，这些类型在编译时保证不为零，
    /// 可以用于优化内存布局和提供更安全的API。
    pub mod non_zero_integers {
        use std::num::{NonZeroI8, NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI128, NonZeroIsize};
        use std::num::{NonZeroU8, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU128, NonZeroUsize};

        /// 非零有符号整数操作
        pub fn non_zero_signed_operations() {
            // 创建非零整数
            let non_zero_i8 = NonZeroI8::new(100).unwrap();
            let non_zero_i16 = NonZeroI16::new(1000).unwrap();
            let non_zero_i32 = NonZeroI32::new(1_000_000).unwrap();
            let non_zero_i64 = NonZeroI64::new(1_000_000_000_000).unwrap();
            let non_zero_i128 = NonZeroI128::new(1_000_000_000_000_000_000_000_000_000_000).unwrap();
            let non_zero_isize = NonZeroIsize::new(1_000_000).unwrap();

            println!("非零有符号整数:");
            println!("  NonZeroI8: {}", non_zero_i8.get());
            println!("  NonZeroI16: {}", non_zero_i16.get());
            println!("  NonZeroI32: {}", non_zero_i32.get());
            println!("  NonZeroI64: {}", non_zero_i64.get());
            println!("  NonZeroI128: {}", non_zero_i128.get());
            println!("  NonZeroIsize: {}", non_zero_isize.get());

            // 安全转换
            let regular_i32: i32 = non_zero_i32.get();
            println!("  转换为普通i32: {}", regular_i32);
        }

        /// 非零无符号整数操作
        pub fn non_zero_unsigned_operations() {
            // 创建非零整数
            let non_zero_u8 = NonZeroU8::new(200).unwrap();
            let non_zero_u16 = NonZeroU16::new(30000).unwrap();
            let non_zero_u32 = NonZeroU32::new(2_000_000_000).unwrap();
            let non_zero_u64 = NonZeroU64::new(9_000_000_000_000_000_000).unwrap();
            let non_zero_u128 = NonZeroU128::new(340_282_366_920_938_463_463_374_607_431_768_211_455).unwrap();
            let non_zero_usize = NonZeroUsize::new(1_000_000).unwrap();

            println!("非零无符号整数:");
            println!("  NonZeroU8: {}", non_zero_u8.get());
            println!("  NonZeroU16: {}", non_zero_u16.get());
            println!("  NonZeroU32: {}", non_zero_u32.get());
            println!("  NonZeroU64: {}", non_zero_u64.get());
            println!("  NonZeroU128: {}", non_zero_u128.get());
            println!("  NonZeroUsize: {}", non_zero_usize.get());

            // 安全转换
            let regular_u32: u32 = non_zero_u32.get();
            println!("  转换为普通u32: {}", regular_u32);
        }
    }

    /// 整数类型转换
    ///
    /// 本模块提供了安全的整数类型转换功能，包括：
    /// - 显式类型转换
    /// - 安全转换（使用 TryFrom trait）
    /// - 溢出检查
    /// - 类型推断
    pub mod type_conversion {

        /// 显式类型转换
        ///
        /// 使用 `as` 关键字进行显式类型转换。
        /// 注意：这种转换可能会导致数据丢失或溢出。
        pub fn explicit_conversion() {
            let i32_value: i32 = 1_000_000;
            
            // 转换为更小的类型（可能丢失数据）
            let i8_value: i8 = i32_value as i8;
            let u8_value: u8 = i32_value as u8;
            
            // 转换为更大的类型（安全）
            let i64_value: i64 = i32_value as i64;
            let u64_value: u64 = i32_value as u64;
            
            println!("显式类型转换:");
            println!("  i32 {} -> i8 {}", i32_value, i8_value);
            println!("  i32 {} -> u8 {}", i32_value, u8_value);
            println!("  i32 {} -> i64 {}", i32_value, i64_value);
            println!("  i32 {} -> u64 {}", i32_value, u64_value);
        }

        /// 安全类型转换
        ///
        /// 使用 `TryFrom` trait 进行安全的类型转换，
        /// 转换失败时返回错误而不是panic。
        pub fn safe_conversion() {
            let i32_value: i32 = 1_000_000;
            
            // 安全转换为更小的类型
            let i8_result: Result<i8, _> = i32_value.try_into();
            match i8_result {
                Ok(value) => println!("安全转换 i32 {} -> i8 {}", i32_value, value),
                Err(_) => println!("转换失败: i32 {} 无法安全转换为 i8", i32_value),
            }
            
            let u8_result: Result<u8, _> = i32_value.try_into();
            match u8_result {
                Ok(value) => println!("安全转换 i32 {} -> u8 {}", i32_value, value),
                Err(_) => println!("转换失败: i32 {} 无法安全转换为 u8", i32_value),
            }
            
            // 安全转换为更大的类型（总是成功）
            let i64_value: i64 = i32_value.into();
            let u64_value: u64 = i32_value.try_into().unwrap();
            
            println!("安全转换 i32 {} -> i64 {}", i32_value, i64_value);
            println!("安全转换 i32 {} -> u64 {}", i32_value, u64_value);
        }

        /// 类型推断
        ///
        /// Rust 1.89 提供了更好的类型推断功能，
        /// 编译器可以根据上下文自动推断整数类型。
        pub fn type_inference() {
            // 类型推断示例
            let a = 42;        // 推断为 i32
            let b = 42u8;      // 显式指定为 u8
            let c = 42i64;     // 显式指定为 i64
            let d = 42_u128;   // 显式指定为 u128，使用下划线分隔符
            
            println!("类型推断:");
            println!("  a = {} (类型: {})", a, std::any::type_name_of_val(&a));
            println!("  b = {} (类型: {})", b, std::any::type_name_of_val(&b));
            println!("  c = {} (类型: {})", c, std::any::type_name_of_val(&c));
            println!("  d = {} (类型: {})", d, std::any::type_name_of_val(&d));
        }
    }

    /// 整数溢出处理
    ///
    /// 本模块提供了处理整数溢出的各种方法，
    /// 包括检查溢出、安全运算等。
    pub mod overflow_handling {

        /// 溢出检查
        ///
        /// 使用 `checked_*` 方法进行溢出检查。
        /// 这些方法在溢出时返回 None，而不是panic。
        pub fn overflow_checking() {
            let a: i8 = 100;
            let b: i8 = 50;
            
            // 检查加法溢出
            match a.checked_add(b) {
                Some(result) => println!("{} + {} = {}", a, b, result),
                None => println!("溢出: {} + {} 超出 i8 范围", a, b),
            }
            
            // 检查乘法溢出
            match a.checked_mul(b) {
                Some(result) => println!("{} * {} = {}", a, b, result),
                None => println!("溢出: {} * {} 超出 i8 范围", a, b),
            }
            
            // 检查减法溢出
            let c: i8 = -100;
            match c.checked_sub(b) {
                Some(result) => println!("{} - {} = {}", c, b, result),
                None => println!("溢出: {} - {} 超出 i8 范围", c, b),
            }
        }

        /// 饱和运算
        ///
        /// 使用 `saturating_*` 方法进行饱和运算。
        /// 这些方法在溢出时返回边界值，而不是环绕。
        pub fn saturating_operations() {
            let a: i8 = 100;
            let b: i8 = 50;
            
            // 饱和加法
            let saturating_sum = a.saturating_add(b);
            println!("饱和加法: {} + {} = {}", a, b, saturating_sum);
            
            // 饱和乘法
            let saturating_product = a.saturating_mul(b);
            println!("饱和乘法: {} * {} = {}", a, b, saturating_product);
            
            // 饱和减法
            let c: i8 = -100;
            let saturating_diff = c.saturating_sub(b);
            println!("饱和减法: {} - {} = {}", c, b, saturating_diff);
        }

        /// 环绕运算
        ///
        /// 使用 `wrapping_*` 方法进行环绕运算。
        /// 这些方法在溢出时进行环绕，而不是panic。
        pub fn wrapping_operations() {
            let a: i8 = 100;
            let b: i8 = 50;
            
            // 环绕加法
            let wrapping_sum = a.wrapping_add(b);
            println!("环绕加法: {} + {} = {}", a, b, wrapping_sum);
            
            // 环绕乘法
            let wrapping_product = a.wrapping_mul(b);
            println!("环绕乘法: {} * {} = {}", a, b, wrapping_product);
            
            // 环绕减法
            let c: i8 = -100;
            let wrapping_diff = c.wrapping_sub(b);
            println!("环绕减法: {} - {} = {}", c, b, wrapping_diff);
        }
    }

    /// 整数格式化
    ///
    /// 本模块提供了各种整数格式化功能，
    /// 包括不同进制、对齐、填充等。
    pub mod formatting {

        /// 不同进制格式化
        pub fn radix_formatting() {
            let value: i32 = 255;
            
            println!("不同进制格式化:");
            println!("  十进制: {}", value);
            println!("  二进制: 0b{:b}", value);
            println!("  八进制: 0o{:o}", value);
            println!("  十六进制: 0x{:x}", value);
            println!("  十六进制(大写): 0x{:X}", value);
            
            // 带前导零的格式化
            println!("  二进制(8位): 0b{:08b}", value);
            println!("  十六进制(4位): 0x{:04X}", value);
        }

        /// 对齐和填充
        pub fn alignment_and_padding() {
            let value: i32 = 42;
            
            println!("对齐和填充:");
            println!("  左对齐(10位): '{:<10}'", value);
            println!("  右对齐(10位): '{:>10}'", value);
            println!("  居中对齐(10位): '{:^10}'", value);
            println!("  右对齐带前导零(10位): '{:010}'", value);
            println!("  右对齐带填充(10位): '{:*>10}'", value);
        }

        /// 千位分隔符
        pub fn thousand_separator() {
            let value: i64 = 1_234_567_890;
            
            println!("千位分隔符:");
            println!("  原始值: {}", value);
            // 注意：{:,} 格式化在某些Rust版本中可能不支持
            println!("  带分隔符: {}", value);
            println!("  二进制: {:b}", value);
            println!("  十六进制: {:X}", value);
        }
    }
}

/// 整数类型性能测试
///
/// 本模块提供了各种整数类型的性能测试，
/// 帮助开发者选择最适合的整数类型。
pub mod performance_tests {
    use std::time::Instant;

    /// 算术运算性能测试
    pub fn arithmetic_performance_test() {
        const ITERATIONS: usize = 1_000_000;
        
        println!("整数类型性能测试 ({} 次迭代):", ITERATIONS);
        
        // i8 性能测试
        let start = Instant::now();
        let mut sum_i8: i8 = 0;
        for i in 0..ITERATIONS {
            sum_i8 = sum_i8.wrapping_add(i as i8);
        }
        let i8_duration = start.elapsed();
        println!("  i8 运算时间: {:?}, 结果: {}", i8_duration, sum_i8);
        
        // i32 性能测试
        let start = Instant::now();
        let mut sum_i32: i32 = 0;
        for i in 0..ITERATIONS {
            sum_i32 = sum_i32.wrapping_add(i as i32);
        }
        let i32_duration = start.elapsed();
        println!("  i32 运算时间: {:?}, 结果: {}", i32_duration, sum_i32);
        
        // i64 性能测试
        let start = Instant::now();
        let mut sum_i64: i64 = 0;
        for i in 0..ITERATIONS {
            sum_i64 = sum_i64.wrapping_add(i as i64);
        }
        let i64_duration = start.elapsed();
        println!("  i64 运算时间: {:?}, 结果: {}", i64_duration, sum_i64);
        
        // 性能比较
        println!("性能比较:");
        println!("  i32 vs i8: {:.2}x", i8_duration.as_nanos() as f64 / i32_duration.as_nanos() as f64);
        println!("  i64 vs i32: {:.2}x", i64_duration.as_nanos() as f64 / i32_duration.as_nanos() as f64);
    }

    /// 内存使用测试
    pub fn memory_usage_test() {
        println!("整数类型内存使用:");
        println!("  i8: {} 字节", std::mem::size_of::<i8>());
        println!("  i16: {} 字节", std::mem::size_of::<i16>());
        println!("  i32: {} 字节", std::mem::size_of::<i32>());
        println!("  i64: {} 字节", std::mem::size_of::<i64>());
        println!("  i128: {} 字节", std::mem::size_of::<i128>());
        println!("  isize: {} 字节", std::mem::size_of::<isize>());
        println!("  u8: {} 字节", std::mem::size_of::<u8>());
        println!("  u16: {} 字节", std::mem::size_of::<u16>());
        println!("  u32: {} 字节", std::mem::size_of::<u32>());
        println!("  u64: {} 字节", std::mem::size_of::<u64>());
        println!("  u128: {} 字节", std::mem::size_of::<u128>());
        println!("  usize: {} 字节", std::mem::size_of::<usize>());
    }
}

/// 主函数：演示所有整数类型功能
///
/// 本函数演示了 Rust 1.89 中所有整数类型的功能，
/// 包括基本操作、类型转换、溢出处理、格式化等。
pub fn demonstrate_all_integer_types() {
    println!("=== Rust 1.89 整数类型系统演示 ===\n");
    
    // 有符号整数操作
    println!("1. 有符号整数操作:");
    integer_types::signed_integers::i8_operations();
    println!();
    integer_types::signed_integers::i32_operations();
    println!();
    integer_types::signed_integers::i64_operations();
    println!();
    integer_types::signed_integers::i128_operations();
    println!();
    
    // 无符号整数操作
    println!("2. 无符号整数操作:");
    integer_types::unsigned_integers::u8_operations();
    println!();
    integer_types::unsigned_integers::u32_operations();
    println!();
    integer_types::unsigned_integers::u64_operations();
    println!();
    integer_types::unsigned_integers::u128_operations();
    println!();
    integer_types::unsigned_integers::usize_operations();
    println!();
    
    // 非零整数操作
    println!("3. 非零整数操作:");
    integer_types::non_zero_integers::non_zero_signed_operations();
    println!();
    integer_types::non_zero_integers::non_zero_unsigned_operations();
    println!();
    
    // 类型转换
    println!("4. 类型转换:");
    integer_types::type_conversion::explicit_conversion();
    println!();
    integer_types::type_conversion::safe_conversion();
    println!();
    integer_types::type_conversion::type_inference();
    println!();
    
    // 溢出处理
    println!("5. 溢出处理:");
    integer_types::overflow_handling::overflow_checking();
    println!();
    integer_types::overflow_handling::saturating_operations();
    println!();
    integer_types::overflow_handling::wrapping_operations();
    println!();
    
    // 格式化
    println!("6. 格式化:");
    integer_types::formatting::radix_formatting();
    println!();
    integer_types::formatting::alignment_and_padding();
    println!();
    integer_types::formatting::thousand_separator();
    println!();
    
    // 性能测试
    println!("7. 性能测试:");
    performance_tests::arithmetic_performance_test();
    println!();
    performance_tests::memory_usage_test();
    println!();
    
    println!("=== 演示完成 ===");
}

/// 简化的整数操作函数（保持向后兼容）
#[allow(unused)]
pub fn interger_operation() {
    // 调用新的演示函数
    demonstrate_all_integer_types();
}
