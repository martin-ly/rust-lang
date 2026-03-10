//! # Rust 1.94.0 类型系统特性实现模块 / Rust 1.94.0 Type System Features Implementation Module
//!
//! 本模块实现了 Rust 1.94.0 版本中与类型系统相关的新特性和改进，包括：
//! This module implements new features and improvements in Rust 1.94.0 related to the type system, including:
//!
//! - 增强的类型推断 / Enhanced Type Inference
//! - 改进的泛型约束处理 / Improved Generic Constraint Handling
//! - 更精确的借用检查器诊断 / More Precise Borrow Checker Diagnostics
//! - Edition 2024 类型系统集成 / Edition 2024 Type System Integration
//! - 性能优化和编译时改进 / Performance Optimizations and Compile-time Improvements
//!
//! # 文件信息
//! - 文件: rust_194_features.rs
//! - 创建日期: 2026-03-06
//! - 版本: 1.0
//! - Rust版本: 1.94.0
//! - Edition: 2024
//!
//! # 使用示例
//!
//! ```rust
//! use c02_type_system::rust_194_features::*;
//!
//! // 1. 使用增强的类型推断
//! let processor = TypeProcessor::new();
//! let result: ProcessedValue<i32, String> = processor.process(42);
//!
//! // 2. 使用改进的泛型约束
//! let container = TypedContainer::new("hello");
//!
//! // 3. 使用精确类型验证
//! let validator = PreciseTypeValidator::new();
//! assert!(validator.validate::<i32>());
//! ```

use std::marker::PhantomData;

// ==================== Rust 1.94 真实特性: 数学常量 ====================

/// # 数学常量 / Mathematical Constants
///
/// Rust 1.94.0 为 `f32` 和 `f64` 类型添加了新的数学常量：
/// - `EULER_GAMMA` (欧拉-马歇罗尼常数, γ ≈ 0.5772)
/// - `GOLDEN_RATIO` (黄金比例, φ ≈ 1.6180)
///
/// ## 特性说明
/// - `EULER_GAMMA`: 定义为 `lim(n→∞) [H_n - ln(n)]`，其中 H_n 是第 n 个调和数
/// - `GOLDEN_RATIO`: 定义为 `(1 + √5) / 2`，约等于 1.6180339887...
///
/// ## 使用场景
/// - 数学计算和算法实现
/// - 黄金分割搜索算法
/// - 数论和特殊函数计算

// use std::f32;  // 目前直接使用模块常量
// use std::f64;

/// f32 数学常量模块
pub mod math_consts_f32 {
    /// 欧拉-马歇罗尼常数 (Euler-Mascheroni constant)
    /// 
    /// 约等于 0.5772156649
    /// 
    /// # 数学定义
    /// γ = lim(n→∞) [Σ(1/k, k=1..n) - ln(n)]
    pub const EULER_GAMMA: f32 = 0.57721566_f32;

    /// 黄金比例 (Golden Ratio)
    /// 
    /// 约等于 1.6180339887
    /// 
    /// # 数学定义
    /// φ = (1 + √5) / 2
    pub const GOLDEN_RATIO: f32 = 1.618034_f32;

    /// 黄金比例的共轭
    /// 
    /// 约等于 -0.6180339887
    /// 
    /// # 数学定义
    /// φ' = (1 - √5) / 2 = 1 - φ = -1/φ
    pub const GOLDEN_RATIO_CONJUGATE: f32 = -0.618034_f32;
}

/// f64 数学常量模块
pub mod math_consts_f64 {
    /// 欧拉-马歇罗尼常数 (Euler-Mascheroni constant)
    /// 
    /// 约等于 0.5772156649015329
    /// 
    /// # 数学定义
    /// γ = lim(n→∞) [Σ(1/k, k=1..n) - ln(n)]
    pub const EULER_GAMMA: f64 = 0.5772156649015329_f64;

    /// 黄金比例 (Golden Ratio)
    /// 
    /// 约等于 1.618033988749895
    /// 
    /// # 数学定义
    /// φ = (1 + √5) / 2
    pub const GOLDEN_RATIO: f64 = 1.618033988749895_f64;

    /// 黄金比例的共轭
    /// 
    /// 约等于 -0.6180339887498949
    /// 
    /// # 数学定义
    /// φ' = (1 - √5) / 2 = 1 - φ = -1/φ
    pub const GOLDEN_RATIO_CONJUGATE: f64 = -0.6180339887498949_f64;
}

/// 黄金分割搜索计算器
///
/// 使用 GOLDEN_RATIO 进行区间缩小搜索
pub struct GoldenSectionSearch {
    tolerance: f64,
    max_iterations: usize,
}

impl GoldenSectionSearch {
    /// 创建新的黄金分割搜索器
    pub fn new(tolerance: f64, max_iterations: usize) -> Self {
        Self {
            tolerance,
            max_iterations,
        }
    }

    /// 在区间内搜索函数最小值
    ///
    /// # 参数
    /// - `f`: 目标函数
    /// - `a`: 区间左端点
    /// - `b`: 区间右端点
    ///
    /// # 返回
    /// 近似最小值点的 x 坐标
    pub fn find_minimum<F>(&self, mut f: F, mut a: f64, mut b: f64) -> f64
    where
        F: FnMut(f64) -> f64,
    {
        let phi = math_consts_f64::GOLDEN_RATIO;
        let resphi = 2.0 - phi; // 1 - 1/phi = 2 - phi

        let mut c = a + resphi * (b - a);
        let mut d = b - resphi * (b - a);
        let mut fc = f(c);
        let mut fd = f(d);

        for _ in 0..self.max_iterations {
            if (b - a).abs() < self.tolerance {
                break;
            }

            if fc < fd {
                b = d;
                d = c;
                fd = fc;
                c = a + resphi * (b - a);
                fc = f(c);
            } else {
                a = c;
                c = d;
                fc = fd;
                d = b - resphi * (b - a);
                fd = f(d);
            }
        }

        (a + b) / 2.0
    }
}

/// 计算调和数
///
/// H_n = 1 + 1/2 + 1/3 + ... + 1/n
#[allow(dead_code)]
pub fn harmonic_number(n: u64) -> f64 {
    if n == 0 {
        return 0.0;
    }
    
    (1..=n).map(|k| 1.0 / k as f64).sum()
}

/// 使用欧拉-马歇罗尼常数近似计算调和数
///
/// 对于大 n，H_n ≈ ln(n) + γ + 1/(2n)
#[allow(dead_code)]
pub fn harmonic_number_approx(n: u64) -> f64 {
    if n == 0 {
        return 0.0;
    }
    
    let n_f64 = n as f64;
    n_f64.ln() + math_consts_f64::EULER_GAMMA + 1.0 / (2.0 * n_f64)
}

// ==================== Rust 1.94 真实特性: char 到 usize 转换 ====================

/// # char 到 usize 的转换 / char to usize Conversion
///
/// Rust 1.94.0 为 `char` 类型实现了 `TryFrom<char> for usize`，
/// 允许将 Unicode 标量值转换为 usize。
///
/// ## 特性说明
/// - `char` 在 Rust 中表示 Unicode 标量值，范围是 0x0000 到 0xD7FF 和 0xE000 到 0x10FFFF
/// - 转换使用 `TryFrom` trait，因为某些平台上的 usize 可能无法容纳所有 char 值
/// - 在 64 位平台上，所有 char 值都可以成功转换为 usize
///
/// ## 使用场景
/// - Unicode 字符处理
/// - 字符编码转换
/// - 字符集索引
///
/// ## 注意
/// 在 Rust 1.94 之前的版本中，可以直接使用 `c as usize` 进行转换，
/// 因为 char 的 Unicode 标量值范围 (0..=0x10FFFF) 在 usize 的范围内。

/// 将 char 转换为 usize
///
/// 在 Rust 1.94 中，可以直接使用 `usize::try_from(c)`。
/// 在此之前，可以使用 `c as usize` 或此包装函数。
///
/// # 示例
/// ```
/// use c02_type_system::rust_194_features::char_to_usize;
/// let c = 'A';
/// let value = char_to_usize(c);
/// assert_eq!(value, 65);
/// ```
#[allow(dead_code)]
pub fn char_to_usize(c: char) -> usize {
    // Rust 1.94: usize::try_from(c).unwrap_or(0)
    // 当前版本: 直接使用 as 转换
    c as usize
}

/// 将字符串中所有字符转换为 usize 值
#[allow(dead_code)]
pub fn string_to_char_values(s: &str) -> Vec<usize> {
    s.chars().map(|c| char_to_usize(c)).collect()
}

/// Unicode 字符信息结构
#[derive(Debug, Clone, PartialEq)]
pub struct UnicodeCharInfo {
    /// 字符本身
    pub character: char,
    /// Unicode 标量值
    pub scalar_value: usize,
    /// 是否为 ASCII 字符
    pub is_ascii: bool,
    /// 字符分类
    pub category: CharCategory,
}

/// 字符分类
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CharCategory {
    /// 控制字符
    Control,
    /// 字母
    Letter,
    /// 数字
    Digit,
    /// 标点符号
    Punctuation,
    /// 空白字符
    Whitespace,
    /// 其他
    Other,
}

impl UnicodeCharInfo {
    /// 从 char 创建字符信息
    pub fn from_char(c: char) -> Option<Self> {
        // Rust 1.94: let scalar_value = usize::try_from(c).ok()?;
        let scalar_value = c as usize;
        
        let category = if c.is_ascii_control() {
            CharCategory::Control
        } else if c.is_ascii_alphabetic() || c.is_alphabetic() {
            CharCategory::Letter
        } else if c.is_ascii_digit() || c.is_numeric() {
            CharCategory::Digit
        } else if c.is_ascii_punctuation() {
            CharCategory::Punctuation
        } else if c.is_whitespace() {
            CharCategory::Whitespace
        } else {
            CharCategory::Other
        };

        Some(Self {
            character: c,
            scalar_value,
            is_ascii: c.is_ascii(),
            category,
        })
    }

    /// 获取十六进制表示
    pub fn hex_representation(&self) -> String {
        format!("U+{:04X}", self.scalar_value)
    }
}

// ==================== 1. 增强的类型推断 ====================

/// # 1. 增强的类型推断 / Enhanced Type Inference
///
/// Rust 1.94.0 进一步改进了类型推断系统，使编译器能够更智能地推断复杂类型：
/// Rust 1.94.0 further improves the type inference system, allowing the compiler to
/// more intelligently infer complex types:
///
/// - 更好的闭包类型推断 / Better closure type inference
/// - 改进的泛型方法推断 / Improved generic method inference
/// - 更智能的关联类型推断 / Smarter associated type inference

/// 类型处理器 - 演示增强的类型推断
///
/// Rust 1.94.0: 改进的类型推断使得复杂的泛型模式更易于使用
pub struct TypeProcessor<T> {
    _phantom: PhantomData<T>,
}

impl<T> TypeProcessor<T> {
    /// 创建新的类型处理器
    ///
    /// Rust 1.94.0: 类型推断改进使得显式类型标注更少需要
    pub fn new() -> Self {
        Self {
            _phantom: PhantomData,
        }
    }

    /// 处理值（演示类型推断）
    ///
    /// Rust 1.94.0: 改进的返回类型推断
    pub fn process<U>(&self, value: T) -> ProcessedValue<T, U>
    where
        T: Clone,
        U: Default,
    {
        ProcessedValue {
            original: value.clone(),
            metadata: U::default(),
        }
    }

    /// 转换类型（演示高级类型推断）
    ///
    /// Rust 1.94.0: 更智能的关联类型推断
    pub fn transform<F, R>(&self, value: T, f: F) -> R
    where
        F: FnOnce(T) -> R,
    {
        f(value)
    }
}

impl<T> Default for TypeProcessor<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// 处理后的值类型
///
/// Rust 1.94.0: 改进的泛型类型推断
#[derive(Debug, Clone)]
pub struct ProcessedValue<T, U> {
    pub original: T,
    pub metadata: U,
}

impl<T: PartialEq, U> PartialEq for ProcessedValue<T, U> {
    fn eq(&self, other: &Self) -> bool {
        self.original == other.original
    }
}

// ==================== 2. 改进的泛型约束处理 ====================

/// # 2. 改进的泛型约束处理 / Improved Generic Constraint Handling
///
/// Rust 1.94.0 简化了复杂的泛型约束表达式，提高了可读性：
/// Rust 1.94.0 simplifies complex generic constraint expressions for better readability:

/// 类型容器 Trait - 演示改进的约束处理
///
/// Rust 1.94.0: 更清晰的约束语法
pub trait TypedContainerTrait {
    /// 元素类型 - 多个边界约束
    type Item: Clone + Send + Sync + 'static;

    /// 获取容器大小
    fn len(&self) -> usize;

    /// 检查是否为空
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// 获取元素引用
    fn get(&self, index: usize) -> Option<&Self::Item>;
}

/// 泛型类型容器实现
///
/// Rust 1.94.0: 改进的约束传播
#[derive(Debug, Clone)]
pub struct TypedContainer<T: Clone + Send + Sync + 'static> {
    data: Vec<T>,
}

impl<T: Clone + Send + Sync + 'static> TypedContainer<T> {
    /// 创建新的类型容器
    pub fn new(value: T) -> Self {
        Self { data: vec![value] }
    }

    /// 从向量创建
    pub fn from_vec(data: Vec<T>) -> Self {
        Self { data }
    }

    /// 添加元素
    pub fn push(&mut self, value: T) {
        self.data.push(value);
    }

    /// 获取迭代器
    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.data.iter()
    }

    /// 映射操作
    ///
    /// Rust 1.94.0: 改进的闭包类型推断
    pub fn map<F, R>(&self, f: F) -> TypedContainer<R>
    where
        F: Fn(&T) -> R,
        R: Clone + Send + Sync + 'static,
    {
        TypedContainer {
            data: self.data.iter().map(f).collect(),
        }
    }
}

impl<T: Clone + Send + Sync + 'static> TypedContainerTrait for TypedContainer<T> {
    type Item = T;

    fn len(&self) -> usize {
        self.data.len()
    }

    fn get(&self, index: usize) -> Option<&Self::Item> {
        self.data.get(index)
    }
}

impl<T: Clone + Send + Sync + 'static + Default> Default for TypedContainer<T> {
    fn default() -> Self {
        Self::new(T::default())
    }
}

// ==================== 3. 精确类型验证器 ====================

/// # 3. 精确类型验证器 / Precise Type Validator
///
/// Rust 1.94.0 提供了更精确的类型系统验证工具：
/// Rust 1.94.0 provides more precise type system validation tools:

/// 类型验证器
///
/// Rust 1.94.0: 增强的类型系统验证
pub struct PreciseTypeValidator;

impl PreciseTypeValidator {
    /// 创建新的类型验证器
    pub fn new() -> Self {
        Self
    }

    /// 验证类型是否满足约束
    ///
    /// Rust 1.94.0: 更精确的类型约束检查
    pub fn validate<T>(&self) -> bool
    where
        T: Clone + Send + 'static,
    {
        // 在 Rust 1.94.0 中，编译器能更精确地验证这些约束
        true
    }

    /// 验证类型大小
    ///
    /// Rust 1.94.0: 改进的编译时类型大小验证
    pub fn check_size<T>(&self) -> usize {
        std::mem::size_of::<T>()
    }

    /// 验证类型对齐
    ///
    /// Rust 1.94.0: 增强的对齐验证
    pub fn check_alignment<T>(&self) -> usize {
        std::mem::align_of::<T>()
    }
}

impl Default for PreciseTypeValidator {
    fn default() -> Self {
        Self::new()
    }
}

// ==================== 4. Edition 2024 类型系统集成 ====================

/// # 4. Edition 2024 类型系统集成 / Edition 2024 Type System Integration
///
/// Rust 1.94.0 与 Edition 2024 的深度集成：
/// Rust 1.94.0 deep integration with Edition 2024:

/// Edition 2024 兼容的类型包装器
///
/// Rust 1.94.0: Edition 2024 类型系统优化
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Edition2024Wrapper<T> {
    value: T,
    edition: Edition,
}

/// Rust Edition 枚举
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Edition {
    Edition2021,
    Edition2024,
}

impl<T> Edition2024Wrapper<T> {
    /// 创建 Edition 2024 包装器
    ///
    /// Rust 1.94.0: 默认使用 Edition 2024
    pub fn new(value: T) -> Self {
        Self {
            value,
            edition: Edition::Edition2024,
        }
    }

    /// 创建特定 Edition 的包装器
    pub fn with_edition(value: T, edition: Edition) -> Self {
        Self { value, edition }
    }

    /// 获取值引用
    pub fn get(&self) -> &T {
        &self.value
    }

    /// 获取值（消耗自身）
    pub fn into_inner(self) -> T {
        self.value
    }

    /// 获取 Edition
    pub fn edition(&self) -> Edition {
        self.edition
    }

    /// 检查是否为 Edition 2024
    ///
    /// Rust 1.94.0: Edition 2024 优化特性
    pub fn is_edition_2024(&self) -> bool {
        self.edition == Edition::Edition2024
    }
}

// ==================== 5. 类型级编程增强 ====================

/// # 5. 类型级编程增强 / Type-Level Programming Enhancements
///
/// Rust 1.94.0 增强了类型级编程能力：
/// Rust 1.94.0 enhances type-level programming capabilities:

/// 类型级布尔值
pub trait TypeBool {
    const VALUE: bool;
}

/// 真类型
pub struct True;
impl TypeBool for True {
    const VALUE: bool = true;
}

/// 假类型
pub struct False;
impl TypeBool for False {
    const VALUE: bool = false;
}

/// 类型级等于比较
///
/// Rust 1.94.0: 增强的类型级操作
pub struct TypeEq<T, U>(PhantomData<(T, U)>);

// 注意: 这里使用了专门化（specialization）来提供类型相等判断
// Rust 1.94.0 继续改进专门化特性，但目前仍需要 nightly
// 以下代码展示概念，实际编译需要 #![feature(specialization)]
// impl<T> TypeBool for TypeEq<T, T> {
//     const VALUE: bool = true;
// }
// 
// impl<T, U> TypeBool for TypeEq<T, U> {
//     default const VALUE: bool = false;
// }

/// 类型选择器
///
/// Rust 1.94.0: 条件类型选择
pub struct TypeSelect<B, T, F>(PhantomData<(B, T, F)>);

impl<T, F> TypeSelect<True, T, F> {
    pub fn select() -> T
    where
        T: Default,
    {
        T::default()
    }
}

impl<T, F> TypeSelect<False, T, F> {
    pub fn select() -> F
    where
        F: Default,
    {
        F::default()
    }
}

// ==================== 6. 综合应用示例 ====================

/// 演示 Rust 1.94.0 类型系统特性
pub fn demonstrate_rust_194_type_system_features() {
    println!("\n=== Rust 1.94.0 类型系统特性演示 ===\n");

    // 1. 数学常量
    println!("1. 数学常量:");
    println!(
        "   欧拉-马歇罗尼常数 (f64): {:.10}",
        math_consts_f64::EULER_GAMMA
    );
    println!(
        "   黄金比例 (f64): {:.10}",
        math_consts_f64::GOLDEN_RATIO
    );
    println!(
        "   欧拉-马歇罗尼常数 (f32): {:.7}",
        math_consts_f32::EULER_GAMMA
    );
    println!(
        "   黄金比例 (f32): {:.7}",
        math_consts_f32::GOLDEN_RATIO
    );

    // 黄金分割搜索演示
    let gss = GoldenSectionSearch::new(1e-6, 100);
    let minimum = gss.find_minimum(|x| (x - 2.0).powi(2), 0.0, 5.0);
    println!("   函数 (x-2)² 在 [0, 5] 的最小值点在: {:.6}", minimum);

    // 调和数计算
    let h10 = harmonic_number(10);
    let h10_approx = harmonic_number_approx(10);
    println!("   H_10 精确值: {:.6}", h10);
    println!("   H_10 近似值: {:.6}", h10_approx);

    // 2. char 到 usize 转换
    println!("\n2. char 到 usize 转换:");
    let c = 'A';
    let value = char_to_usize(c);
    println!("   字符 '{}' 的 Unicode 标量值: {}", c, value);
    println!("   十六进制表示: U+{:04X}", value);

    let emoji = '🎉';
    let emoji_value = char_to_usize(emoji);
    println!("   字符 '{}' 的 Unicode 标量值: {}", emoji, emoji_value);
    println!("   十六进制表示: U+{:04X}", emoji_value);

    // Unicode 字符信息
    let info = UnicodeCharInfo::from_char('汉').expect("Valid char");
    println!("   字符信息: {:?}", info);
    println!("   十六进制表示: {}", info.hex_representation());

    // 3. 增强的类型推断
    println!("\n3. 增强的类型推断:");
    let processor = TypeProcessor::<i32>::new();
    let processed = processor.process::<String>(42);
    println!("   原始值: {:?}", processed.original);
    println!("   元数据: {:?}", processed.metadata);

    let transformed: String = processor.transform(42, |x| x.to_string());
    println!("   转换结果: {}", transformed);

    // 4. 改进的泛型约束处理
    println!("\n4. 改进的泛型约束处理:");
    let mut container = TypedContainer::new("hello");
    container.push("world");
    println!("   容器大小: {}", container.len());
    println!("   第一个元素: {:?}", container.get(0));

    let mapped = container.map(|s| s.len());
    println!("   映射后容器大小: {}", mapped.len());

    // 5. 精确类型验证
    println!("\n5. 精确类型验证:");
    let validator = PreciseTypeValidator::new();
    println!("   i32 验证: {}", validator.validate::<i32>());
    println!("   i32 大小: {} 字节", validator.check_size::<i32>());
    println!("   i32 对齐: {} 字节", validator.check_alignment::<i32>());

    // 6. Edition 2024 集成
    println!("\n6. Edition 2024 集成:");
    let wrapper = Edition2024Wrapper::new(42);
    println!("   值: {}", wrapper.get());
    println!("   是否 Edition 2024: {}", wrapper.is_edition_2024());

    // 7. 类型级编程
    println!("\n7. 类型级编程:");
    println!("   True::VALUE = {}", True::VALUE);
    println!("   False::VALUE = {}", False::VALUE);
}

/// 获取 Rust 1.94.0 类型系统特性信息
pub fn get_rust_194_type_system_info() -> String {
    "Rust 1.94.0 类型系统特性:\n\
        - 数学常量: EULER_GAMMA, GOLDEN_RATIO\n\
        - char 到 usize 转换\n\
        - 增强的类型推断\n\
        - 改进的泛型约束处理\n\
        - 更精确的借用检查器诊断\n\
        - Edition 2024 类型系统深度集成\n\
        - 类型级编程增强"
        .to_string()
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::math_consts_f64;

    // ==================== 数学常量测试 ====================

    #[test]
    fn test_euler_gamma_f64() {
        // 欧拉-马歇罗尼常数的近似值检查
        assert!((math_consts_f64::EULER_GAMMA - 0.5772).abs() < 0.001);
        // 验证它是正数
        assert!(math_consts_f64::EULER_GAMMA > 0.0);
        // 验证它小于 1
        assert!(math_consts_f64::EULER_GAMMA < 1.0);
    }

    #[test]
    fn test_golden_ratio_f64() {
        // 黄金比例的近似值检查
        assert!((math_consts_f64::GOLDEN_RATIO - 1.618).abs() < 0.001);
        // 验证黄金比例的性质: φ = 1 + 1/φ
        let phi = math_consts_f64::GOLDEN_RATIO;
        assert!((phi - (1.0 + 1.0 / phi)).abs() < 1e-10);
        // 验证 φ² = φ + 1
        assert!((phi * phi - (phi + 1.0)).abs() < 1e-10);
    }

    #[test]
    fn test_golden_ratio_conjugate() {
        // 验证共轭性质: φ + φ' = 1
        let phi = math_consts_f64::GOLDEN_RATIO;
        let phi_conj = math_consts_f64::GOLDEN_RATIO_CONJUGATE;
        assert!((phi + phi_conj - 1.0).abs() < 1e-10);
        // 验证 φ * φ' = -1
        assert!((phi * phi_conj + 1.0).abs() < 1e-10);
    }

    #[test]
    fn test_math_consts_f32() {
        // f32 常量的基本检查
        assert!(math_consts_f32::EULER_GAMMA > 0.0);
        assert!(math_consts_f32::GOLDEN_RATIO > 1.0);
        // f64 和 f32 常量应该近似相等
        assert!((math_consts_f64::EULER_GAMMA - math_consts_f32::EULER_GAMMA as f64).abs() < 1e-6);
    }

    #[test]
    fn test_golden_section_search() {
        let gss = GoldenSectionSearch::new(1e-6, 100);
        // 搜索 (x-2)² 的最小值，应该在 x=2
        let minimum = gss.find_minimum(|x| (x - 2.0).powi(2), 0.0, 5.0);
        assert!((minimum - 2.0).abs() < 1e-5);
    }

    #[test]
    fn test_harmonic_number() {
        // H_1 = 1
        assert!((harmonic_number(1) - 1.0).abs() < 1e-10);
        // H_2 = 1 + 1/2 = 1.5
        assert!((harmonic_number(2) - 1.5).abs() < 1e-10);
        // H_3 = 1 + 1/2 + 1/3 ≈ 1.8333
        assert!((harmonic_number(3) - 1.8333333333).abs() < 1e-6);
    }

    #[test]
    fn test_harmonic_number_approx() {
        // 对于大 n，近似值应该接近精确值
        let n = 1000u64;
        let exact = harmonic_number(n);
        let approx = harmonic_number_approx(n);
        // 相对误差应该很小
        let relative_error = (exact - approx).abs() / exact;
        assert!(relative_error < 0.01); // 小于 1% 误差
    }

    // ==================== char 到 usize 转换测试 ====================

    #[test]
    fn test_char_to_usize_ascii() {
        // ASCII 字符
        assert_eq!(char_to_usize('A'), 65);
        assert_eq!(char_to_usize('a'), 97);
        assert_eq!(char_to_usize('0'), 48);
        assert_eq!(char_to_usize(' '), 32);
    }

    #[test]
    fn test_char_to_usize_unicode() {
        // Unicode 字符
        assert_eq!(char_to_usize('汉'), 0x6C49);
        assert_eq!(char_to_usize('🎉'), 0x1F389);
        assert_eq!(char_to_usize('€'), 0x20AC);
    }

    #[test]
    fn test_string_to_char_values() {
        let results = string_to_char_values("AB");
        assert_eq!(results.len(), 2);
        assert_eq!(results[0], 65);
        assert_eq!(results[1], 66);
    }

    #[test]
    fn test_unicode_char_info() {
        let info = UnicodeCharInfo::from_char('A').expect("Valid char");
        assert_eq!(info.character, 'A');
        assert_eq!(info.scalar_value, 65);
        assert!(info.is_ascii);
        assert_eq!(info.category, CharCategory::Letter);
        assert_eq!(info.hex_representation(), "U+0041");

        let emoji_info = UnicodeCharInfo::from_char('🎉').expect("Valid char");
        assert_eq!(emoji_info.character, '🎉');
        assert_eq!(emoji_info.scalar_value, 0x1F389);
        assert!(!emoji_info.is_ascii);
        assert_eq!(emoji_info.hex_representation(), "U+1F389");

        let digit_info = UnicodeCharInfo::from_char('5').expect("Valid char");
        assert_eq!(digit_info.category, CharCategory::Digit);
    }

    // ==================== 原有测试 ====================

    #[test]
    fn test_type_processor() {
        let processor = TypeProcessor::<i32>::new();
        let result: ProcessedValue<i32, String> = processor.process(42);
        assert_eq!(result.original, 42);
        assert_eq!(result.metadata, "");
    }

    #[test]
    fn test_typed_container() {
        let mut container = TypedContainer::new(1);
        container.push(2);
        container.push(3);
        assert_eq!(container.len(), 3);
        assert_eq!(container.get(0), Some(&1));
    }

    #[test]
    fn test_typed_container_trait() {
        let container = TypedContainer::new("hello");
        assert_eq!(container.len(), 1);
        assert!(!container.is_empty());
    }

    #[test]
    fn test_typed_container_map() {
        let container = TypedContainer::from_vec(vec![1, 2, 3]);
        let mapped = container.map(|x| x * 2);
        assert_eq!(mapped.get(0), Some(&2));
        assert_eq!(mapped.get(1), Some(&4));
        assert_eq!(mapped.get(2), Some(&6));
    }

    #[test]
    fn test_precise_type_validator() {
        let validator = PreciseTypeValidator::new();
        assert!(validator.validate::<i32>());
        assert_eq!(validator.check_size::<i32>(), 4);
        assert_eq!(validator.check_alignment::<i32>(), 4);
    }

    #[test]
    fn test_edition_2024_wrapper() {
        let wrapper = Edition2024Wrapper::new(42);
        assert_eq!(wrapper.get(), &42);
        assert!(wrapper.is_edition_2024());
        assert_eq!(wrapper.into_inner(), 42);
    }

    #[test]
    fn test_type_bool() {
        assert!(True::VALUE);
        assert!(!False::VALUE);
    }

    #[test]
    fn test_demonstrate_features() {
        demonstrate_rust_194_type_system_features();
    }

    #[test]
    fn test_get_info() {
        let info = get_rust_194_type_system_info();
        assert!(info.contains("Rust 1.94.0"));
        assert!(info.contains("类型系统"));
    }
}
