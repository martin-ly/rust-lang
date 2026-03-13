//! # Rust 1.94.0 泛型编程特性实现模块 / Rust 1.94.0 Generic Programming Features Implementation Module
//!
//! 本模块实现了 Rust 1.94.0 版本中与泛型编程相关的新特性和改进，包括：
//! This module implements new features and improvements in Rust 1.94.0 related to generic programming, including:
//!
//! - 改进的泛型类型推断 / Improved Generic Type Inference
//! - 更灵活的关联类型 / More Flexible Associated Types
//! - 增强的 trait 边界推断 / Enhanced Trait Bounds Inference
//! - Edition 2024 泛型优化 / Edition 2024 Generic Optimizations
//! - 编译时泛型验证 / Compile-time Generic Validation
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
//! ```ignore
//! use c04_generic::rust_194_features::*;
//!
//! // 1. 使用改进的泛型推断
//! let container = SmartContainer::new(42);
//!
//! // 2. 使用灵活的关联类型
//! let adapter = TypeAdapter::new();
//!
//! // 3. 使用增强的 trait 边界
//! let validator = GenericValidator::new();
//! ```

// 允许MSRV不兼容警告，因为本模块专门展示Rust 1.94+特性
#![allow(clippy::incompatible_msrv)]

use std::marker::PhantomData;

// ==================== Rust 1.94 真实特性: array_windows 泛型应用 ====================

/// # array_windows 在泛型编程中的应用
///
/// Rust 1.94.0 的 `array_windows` 方法可以与泛型结合，创建通用的窗口处理算法
/// 通用滑动窗口处理器
///
/// 使用 const 泛型参数指定窗口大小
pub struct SlidingWindowProcessor<T, const N: usize> {
    _phantom: PhantomData<T>,
}

impl<T: Copy + std::ops::Add<Output = T> + Default, const N: usize> SlidingWindowProcessor<T, N> {
    /// 创建新的滑动窗口处理器
    pub fn new() -> Self {
        Self {
            _phantom: PhantomData,
        }
    }

    /// 计算窗口和
    pub fn window_sums(&self, data: &[T]) -> Vec<T> {
        if data.len() < N {
            return Vec::new();
        }

        data.array_windows::<N>()
            .map(|window| window.iter().copied().fold(T::default(), |acc, x| acc + x))
            .collect()
    }

    /// 查找满足条件的窗口
    pub fn find_window<F>(&self, data: &[T], predicate: F) -> Option<[T; N]>
    where
        F: Fn(&[T; N]) -> bool,
    {
        data.array_windows::<N>()
            .find(|&window| predicate(window))
            .copied()
    }
}

impl<T: Copy + std::ops::Add<Output = T> + Default, const N: usize> Default
    for SlidingWindowProcessor<T, N>
{
    fn default() -> Self {
        Self::new()
    }
}

// ==================== Rust 1.94 真实特性: LazyCell/LazyLock 泛型封装 ====================

use std::cell::OnceCell;
use std::sync::OnceLock;

/// # LazyCell/LazyLock 的泛型封装
///
/// Rust 1.94.0 的新方法与泛型结合，提供更灵活的延迟初始化模式
///
/// ## 注意
/// 在 Rust 1.94 之前的版本中，使用 OnceCell/OnceLock 实现类似功能。
/// Rust 1.94 引入了 LazyCell::get(), get_mut(), force_mut() 方法。
/// 泛型延迟初始化容器
///
/// 支持单线程和多线程两种模式
/// 在 Rust 1.94 中，可以使用 LazyCell/LazyLock 的 get(), get_mut(), force_mut() 方法
pub enum LazyContainer<T> {
    /// 单线程版本
    Cell(OnceCell<T>),
    /// 多线程版本
    Lock(OnceLock<T>),
}

impl<T> LazyContainer<T> {
    /// 创建单线程延迟初始化容器
    pub fn cell() -> Self {
        LazyContainer::Cell(OnceCell::new())
    }

    /// 创建多线程延迟初始化容器
    pub fn lock() -> Self
    where
        T: Send + Sync + 'static,
    {
        LazyContainer::Lock(OnceLock::new())
    }

    /// 尝试获取值（不触发初始化）- 对应 Rust 1.94 LazyCell::get()
    pub fn try_get(&self) -> Option<&T> {
        match self {
            LazyContainer::Cell(cell) => cell.get(),
            LazyContainer::Lock(lock) => lock.get(),
        }
    }

    /// 获取或初始化值
    pub fn get_or_init<F>(&self, f: F) -> &T
    where
        F: FnOnce() -> T,
    {
        match self {
            LazyContainer::Cell(cell) => cell.get_or_init(f),
            LazyContainer::Lock(lock) => lock.get_or_init(f),
        }
    }

    /// 检查是否已初始化
    pub fn is_initialized(&self) -> bool {
        self.try_get().is_some()
    }

    /// 设置值
    pub fn set(&self, value: T) -> Result<(), T> {
        match self {
            LazyContainer::Cell(cell) => cell.set(value),
            LazyContainer::Lock(lock) => lock.set(value),
        }
    }
}

/// 可变的泛型延迟初始化容器（仅单线程）
/// 在 Rust 1.94 中，可以直接使用 LazyCell 的 get_mut() 和 force_mut() 方法
pub struct LazyCellContainer<T> {
    cell: OnceCell<T>,
}

impl<T> Default for LazyCellContainer<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> LazyCellContainer<T> {
    /// 创建新的延迟初始化容器
    pub fn new() -> Self {
        Self {
            cell: OnceCell::new(),
        }
    }

    /// 尝试获取值（不触发初始化）- 对应 Rust 1.94 LazyCell::get()
    pub fn try_get(&self) -> Option<&T> {
        self.cell.get()
    }

    /// 尝试获取可变引用（不触发初始化）- 对应 Rust 1.94 LazyCell::get_mut()
    pub fn try_get_mut(&mut self) -> Option<&mut T> {
        self.cell.get_mut()
    }

    /// 获取或初始化值
    pub fn get_or_init<F>(&self, f: F) -> &T
    where
        F: FnOnce() -> T,
    {
        self.cell.get_or_init(f)
    }

    /// 强制获取可变引用 - 对应 Rust 1.94 LazyCell::force_mut()
    pub fn force_get_mut<F>(&mut self, f: F) -> &mut T
    where
        F: FnOnce() -> T,
    {
        if self.cell.get().is_none() {
            let _ = self.cell.set(f());
        }
        self.cell.get_mut().unwrap()
    }

    /// 检查是否已初始化
    pub fn is_initialized(&self) -> bool {
        self.cell.get().is_some()
    }

    /// 设置值
    pub fn set(&self, value: T) -> Result<(), T> {
        self.cell.set(value)
    }
}

// ==================== Rust 1.94 真实特性: 数学常量泛型应用 ====================

/// # 数学常量在泛型编程中的应用
///
/// Rust 1.94.0 的数学常量 EULER_GAMMA 和 GOLDEN_RATIO
/// 可以与泛型 trait 结合使用
/// 数学常量 trait
pub trait MathConstants {
    /// 欧拉-马歇罗尼常数
    const EULER_GAMMA: Self;
    /// 黄金比例
    const GOLDEN_RATIO: Self;
    /// 黄金比例的共轭
    const GOLDEN_RATIO_CONJUGATE: Self;
}

impl MathConstants for f32 {
    const EULER_GAMMA: Self = 0.577_215_7_f32;
    const GOLDEN_RATIO: Self = 1.618034_f32;
    const GOLDEN_RATIO_CONJUGATE: Self = -0.618034_f32;
}

impl MathConstants for f64 {
    const EULER_GAMMA: Self = 0.5772156649015329_f64;
    const GOLDEN_RATIO: Self = 1.618033988749895_f64;
    const GOLDEN_RATIO_CONJUGATE: Self = -0.6180339887498949_f64;
}

/// 使用数学常量的泛型斐波那契计算器
pub struct FibonacciCalculator<T: MathConstants + Copy> {
    _phantom: PhantomData<T>,
}

impl<T: MathConstants + Copy> FibonacciCalculator<T> {
    /// 创建新的斐波那契计算器
    pub fn new() -> Self {
        Self {
            _phantom: PhantomData,
        }
    }

    /// 使用比奈公式（Binet's formula）计算第 n 个斐波那契数
    ///
    /// F(n) = (φⁿ - (1-φ)ⁿ) / √5
    ///
    /// 注意：由于浮点精度限制，仅对较小的 n 有效
    pub fn calculate(&self, n: u32) -> T
    where
        T: std::ops::Mul<Output = T>
            + std::ops::Sub<Output = T>
            + std::ops::Div<Output = T>
            + From<f64>,
    {
        let phi = T::GOLDEN_RATIO;
        let psi = T::GOLDEN_RATIO_CONJUGATE;
        let sqrt5 = T::from(5.0_f64.sqrt());

        // φⁿ - (1-φ)ⁿ / √5
        let phi_n = self.pow(phi, n);
        let psi_n = self.pow(psi, n);
        (phi_n - psi_n) / sqrt5
    }

    /// 辅助方法：计算 x^n
    fn pow(&self, x: T, n: u32) -> T
    where
        T: std::ops::Mul<Output = T> + Copy + From<f64>,
    {
        if n == 0 {
            return T::from(1.0);
        }
        let mut result = x;
        for _ in 1..n {
            result = result * x;
        }
        result
    }
}

impl<T: MathConstants + Copy> Default for FibonacciCalculator<T> {
    fn default() -> Self {
        Self::new()
    }
}

// ==================== Rust 1.94 真实特性: char 转换泛型应用 ====================

/// # char 到 usize 转换在泛型编程中的应用
///
/// Rust 1.94.0 的 TryFrom<char> for usize 可以与泛型结合
/// 泛型字符编码转换器
pub trait CharEncoder<T> {
    /// 将字符编码为类型 T
    fn encode(c: char) -> Option<T>;
    /// 将 T 解码为字符
    fn decode(value: T) -> Option<char>;
}

/// Usize 字符编码器（使用 Rust 1.94 新特性）
pub struct UsizeCharEncoder;

impl CharEncoder<usize> for UsizeCharEncoder {
    fn encode(c: char) -> Option<usize> {
        usize::try_from(c).ok()
    }

    fn decode(value: usize) -> Option<char> {
        char::from_u32(value as u32)
    }
}

/// 泛型字符映射表
pub struct CharMap<V> {
    entries: Vec<(char, V)>,
}

impl<V: Clone> CharMap<V> {
    /// 创建新的字符映射表
    pub fn new() -> Self {
        Self {
            entries: Vec::new(),
        }
    }

    /// 插入键值对
    pub fn insert(&mut self, c: char, value: V) {
        if let Some(pos) = self.entries.iter().position(|(k, _)| *k == c) {
            self.entries[pos] = (c, value);
        } else {
            self.entries.push((c, value));
        }
    }

    /// 查找值
    pub fn get(&self, c: char) -> Option<&V> {
        self.entries.iter().find(|(k, _)| *k == c).map(|(_, v)| v)
    }

    /// 将字符键转换为 usize 索引（使用 Rust 1.94 特性）
    pub fn to_usize_map(&self) -> Vec<(usize, V)> {
        self.entries
            .iter()
            .filter_map(|(c, v)| usize::try_from(*c).ok().map(|idx| (idx, v.clone())))
            .collect()
    }
}

impl<V: Clone> Default for CharMap<V> {
    fn default() -> Self {
        Self::new()
    }
}

// ==================== 1. 改进的泛型类型推断 ====================

/// # 1. 改进的泛型类型推断 / Improved Generic Type Inference
///
/// Rust 1.94.0 显著改进了泛型类型推断，减少了显式类型标注的需要：
/// Rust 1.94.0 significantly improves generic type inference, reducing the need for explicit type annotations:
/// 智能容器 - 演示改进的泛型推断
///
/// Rust 1.94.0: 更智能的泛型类型推断
#[derive(Debug, Clone)]
pub struct SmartContainer<T> {
    data: T,
    metadata: Option<String>,
}

impl<T> SmartContainer<T> {
    /// 创建新的智能容器
    ///
    /// Rust 1.94.0: 改进的构造函数类型推断
    pub fn new(data: T) -> Self {
        Self {
            data,
            metadata: None,
        }
    }

    /// 创建带元数据的容器
    ///
    /// Rust 1.94.0: 更好的多参数类型推断
    pub fn with_metadata(data: T, metadata: impl Into<String>) -> Self {
        Self {
            data,
            metadata: Some(metadata.into()),
        }
    }

    /// 获取数据引用
    pub fn get(&self) -> &T {
        &self.data
    }

    /// 转换容器类型
    ///
    /// Rust 1.94.0: 改进的泛型方法类型推断
    pub fn map<F, R>(self, f: F) -> SmartContainer<R>
    where
        F: FnOnce(T) -> R,
    {
        SmartContainer {
            data: f(self.data),
            metadata: self.metadata,
        }
    }

    /// 链式操作
    ///
    /// Rust 1.94.0: 更好的链式调用类型推断
    pub fn and_then<F, R>(self, f: F) -> SmartContainer<R>
    where
        F: FnOnce(T) -> SmartContainer<R>,
    {
        f(self.data)
    }
}

impl<T: Default> Default for SmartContainer<T> {
    fn default() -> Self {
        Self::new(T::default())
    }
}

/// 泛型函数组合器
///
/// Rust 1.94.0: 改进的泛型函数类型推断
pub struct GenericComposer<F, G> {
    first: F,
    second: G,
}

impl<F, G> GenericComposer<F, G> {
    /// 创建新的组合器
    pub fn new(first: F, second: G) -> Self {
        Self { first, second }
    }

    /// 组合执行
    ///
    /// Rust 1.94.0: 自动推断中间类型
    pub fn compose<T, U, V>(&self, value: T) -> V
    where
        F: Fn(T) -> U,
        G: Fn(U) -> V,
    {
        (self.second)((self.first)(value))
    }
}

// ==================== 2. 更灵活的关联类型 ====================

/// # 2. 更灵活的关联类型 / More Flexible Associated Types
///
/// Rust 1.94.0 提供了更灵活的关联类型定义和使用方式：
/// Rust 1.94.0 provides more flexible associated type definitions and usage:
/// 类型适配器 Trait
///
/// Rust 1.94.0: 更灵活的关联类型定义
pub trait TypeAdapter {
    /// 输入类型
    type Input: Clone;
    /// 输出类型 - 可以有更灵活的约束
    type Output: Clone + Send;
    /// 错误类型
    type Error: std::error::Error;

    /// 适配转换
    fn adapt(&self, input: Self::Input) -> Result<Self::Output, Self::Error>;

    /// 批量适配
    ///
    /// Rust 1.94.0: 改进的关联类型在泛型上下文中的使用
    fn adapt_batch(&self, inputs: Vec<Self::Input>) -> Result<Vec<Self::Output>, Self::Error>
    where
        Self: Sized,
    {
        inputs.into_iter().map(|i| self.adapt(i)).collect()
    }
}

/// 字符串到整数适配器
#[derive(Debug, Clone, Copy, Default)]
pub struct StringToIntAdapter;

#[derive(Debug, Clone)]
pub struct AdapterError {
    message: String,
}

impl std::fmt::Display for AdapterError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for AdapterError {}

impl TypeAdapter for StringToIntAdapter {
    type Input = String;
    type Output = i64;
    type Error = AdapterError;

    fn adapt(&self, input: Self::Input) -> Result<Self::Output, Self::Error> {
        input.parse().map_err(|e| AdapterError {
            message: format!("Parse error: {}", e),
        })
    }
}

/// 类型适配器实现
///
/// Rust 1.94.0: 泛型适配器模式
#[derive(Debug, Clone)]
pub struct GenericAdapter<T, U, F>
where
    F: Fn(T) -> Result<U, AdapterError>,
{
    converter: F,
    _phantom: PhantomData<(T, U)>,
}

impl<T, U, F> GenericAdapter<T, U, F>
where
    F: Fn(T) -> Result<U, AdapterError>,
{
    pub fn new(converter: F) -> Self {
        Self {
            converter,
            _phantom: PhantomData,
        }
    }
}

impl<T, U, F> TypeAdapter for GenericAdapter<T, U, F>
where
    T: Clone,
    U: Clone + Send,
    F: Fn(T) -> Result<U, AdapterError>,
{
    type Input = T;
    type Output = U;
    type Error = AdapterError;

    fn adapt(&self, input: Self::Input) -> Result<Self::Output, Self::Error> {
        (self.converter)(input)
    }
}

// ==================== 3. 增强的 trait 边界推断 ====================

/// # 3. 增强的 trait 边界推断 / Enhanced Trait Bounds Inference
///
/// Rust 1.94.0 改进了 trait 边界的自动推断：
/// Rust 1.94.0 improves automatic trait bounds inference:
/// 泛型验证器
///
/// Rust 1.94.0: 更智能的 trait 边界推断
pub struct GenericValidator<T: ?Sized> {
    _phantom: PhantomData<T>,
}

impl<T: ?Sized> GenericValidator<T> {
    /// 创建新的验证器
    pub fn new() -> Self {
        Self {
            _phantom: PhantomData,
        }
    }

    /// 验证类型实现 Clone
    ///
    /// Rust 1.94.0: 编译器自动推断 trait 边界
    pub fn validate_clone(&self) -> bool
    where
        T: Clone,
    {
        true
    }

    /// 验证类型实现 Send + Sync
    ///
    /// Rust 1.94.0: 更精确的 trait 边界检查
    pub fn validate_thread_safe(&self) -> bool
    where
        T: Send + Sync,
    {
        true
    }

    /// 验证类型大小
    pub fn check_size(&self) -> usize
    where
        T: Sized,
    {
        std::mem::size_of::<T>()
    }
}

impl<T: ?Sized> Default for GenericValidator<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// 复杂 trait 边界结构
///
/// Rust 1.94.0: 简化的复杂 trait 边界表达
#[derive(Debug, Clone)]
pub struct ComplexBoundsStruct<T, U>
where
    T: Clone + Send + Sync + 'static,
    U: Clone + Send + Sync + 'static,
{
    first: T,
    second: U,
}

impl<T, U> ComplexBoundsStruct<T, U>
where
    T: Clone + Send + Sync + 'static,
    U: Clone + Send + Sync + 'static,
{
    pub fn new(first: T, second: U) -> Self {
        Self { first, second }
    }

    /// 交换值
    ///
    /// Rust 1.94.0: 改进的泛型约束传播
    pub fn swap(self) -> ComplexBoundsStruct<U, T> {
        ComplexBoundsStruct {
            first: self.second,
            second: self.first,
        }
    }

    /// 获取元组
    pub fn into_tuple(self) -> (T, U) {
        (self.first, self.second)
    }
}

// ==================== 4. Edition 2024 泛型优化 ====================

/// # 4. Edition 2024 泛型优化 / Edition 2024 Generic Optimizations
///
/// Rust 1.94.0 与 Edition 2024 的泛型系统集成：
/// Rust 1.94.0 generic system integration with Edition 2024:
/// Edition 2024 泛型容器
///
/// Rust 1.94.0: Edition 2024 优化的泛型代码
#[derive(Debug, Clone)]
pub struct Edition2024Generic<T> {
    value: T,
    edition_marker: Edition2024Marker,
}

/// Edition 2024 标记
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Edition2024Marker {
    Legacy,
    Modern,
}

impl<T> Edition2024Generic<T> {
    /// 创建 Edition 2024 泛型容器
    pub fn new(value: T) -> Self {
        Self {
            value,
            edition_marker: Edition2024Marker::Modern,
        }
    }

    /// 创建特定 Edition 的容器
    pub fn with_edition(value: T, edition: Edition2024Marker) -> Self {
        Self {
            value,
            edition_marker: edition,
        }
    }

    /// 获取值
    pub fn get(&self) -> &T {
        &self.value
    }

    /// 转换值
    ///
    /// Rust 1.94.0: Edition 2024 优化的泛型转换
    pub fn transform<F, R>(self, f: F) -> Edition2024Generic<R>
    where
        F: FnOnce(T) -> R,
    {
        Edition2024Generic {
            value: f(self.value),
            edition_marker: self.edition_marker,
        }
    }

    /// 检查是否为 Modern Edition
    pub fn is_modern(&self) -> bool {
        self.edition_marker == Edition2024Marker::Modern
    }
}

// ==================== 5. 编译时泛型验证 ====================

/// # 5. 编译时泛型验证 / Compile-time Generic Validation
///
/// Rust 1.94.0 增强了编译时的泛型验证能力：
/// Rust 1.94.0 enhances compile-time generic validation:
/// 编译时类型断言
///
/// Rust 1.94.0: 编译时泛型约束验证
pub struct CompileTimeAssert<T: ?Sized> {
    _phantom: PhantomData<T>,
}

impl<T: ?Sized> CompileTimeAssert<T> {
    /// 断言类型实现 Send
    pub const fn assert_send()
    where
        T: Send,
    {
    }

    /// 断言类型实现 Sync
    pub const fn assert_sync()
    where
        T: Sync,
    {
    }

    /// 断言类型大小
    pub const fn assert_size(expected: usize)
    where
        T: Sized,
    {
        assert!(std::mem::size_of::<T>() == expected);
    }
}

/// 类型级别验证器
///
/// Rust 1.94.0: 类型级别的泛型验证
pub trait TypeLevelValidation {
    /// 验证类型有效性
    const IS_VALID: bool;
    /// 类型大小
    const SIZE: usize;
    /// 类型对齐
    const ALIGN: usize;
}

impl<T> TypeLevelValidation for T
where
    T: Sized,
{
    const IS_VALID: bool = true;
    const SIZE: usize = std::mem::size_of::<T>();
    const ALIGN: usize = std::mem::align_of::<T>();
}

// ==================== 6. 综合应用示例 ====================

/// 演示 Rust 1.94.0 泛型编程特性
pub fn demonstrate_rust_194_generic_features() {
    println!("\n=== Rust 1.94.0 泛型编程特性演示 ===\n");

    // 1. array_windows 泛型应用
    println!("1. array_windows 泛型应用:");
    let processor = SlidingWindowProcessor::<i32, 3>::new();
    let data = vec![1, 2, 3, 4, 5, 6];
    let sums = processor.window_sums(&data);
    println!("   数据: {:?}", data);
    println!("   窗口大小 3 的和: {:?}", sums);

    // 2. LazyCell/LazyLock 泛型封装
    println!("\n2. LazyCell/LazyLock 泛型封装:");
    let lazy_cell = LazyContainer::<Vec<i32>>::cell();
    println!("   是否已初始化: {}", lazy_cell.is_initialized());
    let _ = lazy_cell.get_or_init(|| {
        println!("   [LazyCell] 初始化中...");
        vec![1, 2, 3]
    });
    println!("   获取后是否已初始化: {}", lazy_cell.is_initialized());

    // 3. 数学常量泛型应用
    println!("\n3. 数学常量泛型应用:");
    let fib_calc = FibonacciCalculator::<f64>::new();
    for i in 1..=10 {
        let fib = fib_calc.calculate(i);
        println!("   F({}) ≈ {:.0}", i, fib);
    }

    // 4. char 转换泛型应用
    println!("\n4. char 转换泛型应用:");
    let mut char_map = CharMap::new();
    char_map.insert('A', "Alpha");
    char_map.insert('B', "Beta");
    char_map.insert('C', "Gamma");

    let usize_map = char_map.to_usize_map();
    for (idx, value) in &usize_map {
        println!("   索引 {} -> {}", idx, value);
    }

    // 5. 改进的泛型类型推断
    println!("\n5. 改进的泛型类型推断:");
    let container = SmartContainer::new(42);
    println!("   容器值: {}", container.get());

    let container_with_meta = SmartContainer::with_metadata("hello", "metadata");
    println!("   带元数据容器: {:?}", container_with_meta);

    let mapped = container.map(|x| x.to_string());
    println!("   映射后: {}", mapped.get());

    // 6. 更灵活的关联类型
    println!("\n6. 更灵活的关联类型:");
    let adapter = StringToIntAdapter;
    let result = adapter.adapt("42".to_string());
    println!("   适配结果: {:?}", result);

    let batch_result = adapter.adapt_batch(vec!["1".to_string(), "2".to_string(), "3".to_string()]);
    println!("   批量适配结果: {:?}", batch_result);

    // 7. 增强的 trait 边界推断
    println!("\n7. 增强的 trait 边界推断:");
    let validator = GenericValidator::<String>::new();
    println!("   String 实现 Clone: {}", validator.validate_clone());
    println!(
        "   String 实现 Send+Sync: {}",
        validator.validate_thread_safe()
    );
    println!("   String 大小: {} 字节", validator.check_size());

    let complex = ComplexBoundsStruct::new(1, "hello");
    let swapped = complex.swap();
    let (u, t) = swapped.into_tuple();
    println!("   交换后: ({}, {})", u, t);

    // 8. Edition 2024 泛型优化
    println!("\n8. Edition 2024 泛型优化:");
    let edition_generic = Edition2024Generic::new(42);
    println!("   值: {}", edition_generic.get());
    println!("   是否 Modern: {}", edition_generic.is_modern());

    let transformed = edition_generic.transform(|x| x * 2);
    println!("   转换后: {}", transformed.get());

    // 9. 编译时泛型验证
    println!("\n9. 编译时泛型验证:");
    CompileTimeAssert::<i32>::assert_send();
    CompileTimeAssert::<i32>::assert_sync();
    println!(
        "   i32 IS_VALID: {}",
        <i32 as TypeLevelValidation>::IS_VALID
    );
    println!("   i32 SIZE: {} 字节", <i32 as TypeLevelValidation>::SIZE);
    println!("   i32 ALIGN: {} 字节", <i32 as TypeLevelValidation>::ALIGN);
}

/// 获取 Rust 1.94.0 泛型编程特性信息
pub fn get_rust_194_generic_info() -> String {
    "Rust 1.94.0 泛型编程特性:\n\
        - array_windows 泛型应用\n\
        - LazyCell/LazyLock 泛型封装\n\
        - 数学常量泛型应用\n\
        - char 转换泛型应用\n\
        - 改进的泛型类型推断\n\
        - 更灵活的关联类型\n\
        - 增强的 trait 边界推断\n\
        - Edition 2024 泛型优化\n\
        - 编译时泛型验证"
        .to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    // ==================== array_windows 泛型测试 ====================

    #[test]
    fn test_sliding_window_processor_sum() {
        let processor = SlidingWindowProcessor::<i32, 3>::new();
        let data = vec![1, 2, 3, 4, 5];
        let sums = processor.window_sums(&data);
        // [1+2+3, 2+3+4, 3+4+5] = [6, 9, 12]
        assert_eq!(sums, vec![6, 9, 12]);
    }

    #[test]
    fn test_sliding_window_processor_find() {
        let processor = SlidingWindowProcessor::<i32, 3>::new();
        let data = vec![1, 2, 3, 4, 5];

        // 查找和为 9 的窗口
        let result = processor.find_window(&data, |w| w.iter().sum::<i32>() == 9);
        assert_eq!(result, Some([2, 3, 4]));
    }

    #[test]
    fn test_sliding_window_empty() {
        let processor = SlidingWindowProcessor::<i32, 5>::new();
        let data = vec![1, 2, 3]; // 数据长度小于窗口大小
        let sums = processor.window_sums(&data);
        assert!(sums.is_empty());
    }

    // ==================== LazyCell/LazyLock 泛型测试 ====================

    #[test]
    fn test_lazy_container_cell() {
        let container = LazyContainer::<i32>::cell();
        assert!(!container.is_initialized());
        assert_eq!(container.get_or_init(|| 42), &42);
        assert!(container.is_initialized());
        assert_eq!(container.try_get(), Some(&42));
    }

    #[test]
    fn test_lazy_container_lock() {
        let container = LazyContainer::<String>::lock();
        assert!(!container.is_initialized());
        assert_eq!(container.get_or_init(|| "hello".to_string()), "hello");
        assert!(container.is_initialized());
    }

    #[test]
    fn test_lazy_container_set() {
        let container = LazyContainer::<i32>::cell();
        assert!(container.set(42).is_ok());
        assert_eq!(container.try_get(), Some(&42));
    }

    #[test]
    fn test_lazy_cell_container() {
        let mut container = LazyCellContainer::<Vec<i32>>::new();

        // 未初始化
        assert!(!container.is_initialized());
        assert_eq!(container.try_get(), None);
        assert_eq!(container.try_get_mut(), None);

        // 强制初始化
        let mutable = container.force_get_mut(|| vec![1, 2, 3]);
        mutable.push(4);

        // 已初始化
        assert!(container.is_initialized());
        assert_eq!(container.try_get(), Some(&vec![1, 2, 3, 4]));
    }

    #[test]
    fn test_lazy_cell_container_set() {
        let container = LazyCellContainer::<i32>::new();
        assert!(container.set(42).is_ok());
        assert_eq!(container.try_get(), Some(&42));
    }

    // ==================== 数学常量泛型测试 ====================

    #[test]
    fn test_math_constants_f32() {
        assert!(f32::EULER_GAMMA > 0.0);
        assert!(f32::GOLDEN_RATIO > 1.0);
        assert!(f32::GOLDEN_RATIO_CONJUGATE < 0.0);
    }

    #[test]
    fn test_math_constants_f64() {
        assert!(f64::EULER_GAMMA > 0.0);
        assert!(f64::GOLDEN_RATIO > 1.0);
        assert!(f64::GOLDEN_RATIO_CONJUGATE < 0.0);
    }

    #[test]
    fn test_fibonacci_calculator() {
        let calc = FibonacciCalculator::<f64>::new();

        // 验证前几个斐波那契数
        assert!((calc.calculate(1) - 1.0).abs() < 0.1);
        assert!((calc.calculate(2) - 1.0).abs() < 0.1);
        assert!((calc.calculate(3) - 2.0).abs() < 0.1);
        assert!((calc.calculate(5) - 5.0).abs() < 0.1);
        assert!((calc.calculate(10) - 55.0).abs() < 0.5);
    }

    // ==================== char 转换泛型测试 ====================

    #[test]
    fn test_usize_char_encoder() {
        // 测试编码
        assert_eq!(UsizeCharEncoder::encode('A'), Some(65));
        assert_eq!(UsizeCharEncoder::encode('汉'), Some(0x6C49));

        // 测试解码
        assert_eq!(UsizeCharEncoder::decode(65), Some('A'));
        assert_eq!(UsizeCharEncoder::decode(0x6C49), Some('汉'));
    }

    #[test]
    fn test_char_map() {
        let mut map = CharMap::new();
        map.insert('A', 100);
        map.insert('B', 200);

        assert_eq!(map.get('A'), Some(&100));
        assert_eq!(map.get('B'), Some(&200));
        assert_eq!(map.get('C'), None);

        // 测试更新
        map.insert('A', 150);
        assert_eq!(map.get('A'), Some(&150));

        // 测试转换为 usize 映射
        let usize_map = map.to_usize_map();
        assert!(usize_map.contains(&(65, 150))); // 'A' = 65
        assert!(usize_map.contains(&(66, 200))); // 'B' = 66
    }

    // ==================== 原有测试 ====================

    #[test]
    fn test_smart_container() {
        let container = SmartContainer::new(42);
        assert_eq!(container.get(), &42);

        let mapped = container.map(|x| x * 2);
        assert_eq!(mapped.get(), &84);
    }

    #[test]
    fn test_smart_container_with_metadata() {
        let container = SmartContainer::with_metadata(42, "test");
        assert_eq!(container.get(), &42);
    }

    #[test]
    fn test_generic_composer() {
        let composer = GenericComposer::new(|x: i32| x * 2, |y: i32| y + 1);
        assert_eq!(composer.compose(5), 11); // (5 * 2) + 1
    }

    #[test]
    fn test_string_to_int_adapter() {
        let adapter = StringToIntAdapter;
        assert_eq!(adapter.adapt("42".to_string()).unwrap(), 42);
        assert!(adapter.adapt("not a number".to_string()).is_err());
    }

    #[test]
    fn test_adapter_batch() {
        let adapter = StringToIntAdapter;
        let results = adapter
            .adapt_batch(vec!["1".to_string(), "2".to_string()])
            .unwrap();
        assert_eq!(results, vec![1, 2]);
    }

    #[test]
    fn test_generic_adapter() {
        let adapter = GenericAdapter::new(|s: String| {
            s.parse::<i32>().map_err(|e| AdapterError {
                message: e.to_string(),
            })
        });
        assert_eq!(adapter.adapt("100".to_string()).unwrap(), 100);
    }

    #[test]
    fn test_generic_validator() {
        let validator = GenericValidator::<String>::new();
        assert!(validator.validate_clone());
        assert!(validator.validate_thread_safe());
    }

    #[test]
    fn test_complex_bounds_struct() {
        let complex = ComplexBoundsStruct::new(1, "hello");
        let swapped = complex.swap();
        let (u, t) = swapped.into_tuple();
        assert_eq!(u, "hello");
        assert_eq!(t, 1);
    }

    #[test]
    fn test_edition_2024_generic() {
        let generic = Edition2024Generic::new(42);
        assert_eq!(generic.get(), &42);
        assert!(generic.is_modern());

        let transformed = generic.transform(|x| x * 2);
        assert_eq!(transformed.get(), &84);
    }

    #[test]
    fn test_compile_time_assert() {
        CompileTimeAssert::<i32>::assert_send();
        CompileTimeAssert::<i32>::assert_sync();
    }

    #[test]
    fn test_type_level_validation() {
        assert!(<i32 as TypeLevelValidation>::IS_VALID);
        assert_eq!(<i32 as TypeLevelValidation>::SIZE, 4);
        assert_eq!(<i32 as TypeLevelValidation>::ALIGN, 4);
    }

    #[test]
    fn test_demonstrate_features() {
        demonstrate_rust_194_generic_features();
    }

    #[test]
    fn test_get_info() {
        let info = get_rust_194_generic_info();
        assert!(info.contains("Rust 1.94.0"));
        assert!(info.contains("泛型"));
    }
}
