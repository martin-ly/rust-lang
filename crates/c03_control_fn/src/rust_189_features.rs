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
//! # Rust 1.89 最新特性模块
//!
//! 包含异步trait、GATs、常量泛型等核心新特性

use std::collections::HashMap;
use std::fmt::Display;
use std::future::Future;

/// 异步trait实现示例（避免在trait中直接使用 async fn）
pub trait AsyncProcessor {
    fn process(
        &self,
        data: &[u8],
    ) -> impl Future<Output = Result<Vec<u8>, Box<dyn std::error::Error + Send + Sync>>> + Send;
    fn validate(&self, input: &str) -> impl Future<Output = bool> + Send;
}

/// 文本处理器实现
pub struct TextProcessor;

impl AsyncProcessor for TextProcessor {
    async fn process(
        &self,
        data: &[u8],
    ) -> Result<Vec<u8>, Box<dyn std::error::Error + Send + Sync>>
    {
        // 模拟异步处理
        tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
        Ok(data.to_vec())
    }

    async fn validate(&self, input: &str) -> bool { !input.is_empty() }
}

/// 数据处理器trait
pub trait DataProcessor {
    type Input;
    type Output;

    fn process(&self, input: &Self::Input) -> Self::Output;
}

/// 简单处理器实现
pub struct SimpleProcessor;

impl DataProcessor for SimpleProcessor {
    type Input = String;
    type Output = usize;

    fn process(&self, input: &Self::Input) -> Self::Output {
        input.len()
    }
}

/// 高级处理器实现
pub struct AdvancedProcessor<T: Display + Clone> {
    _phantom: std::marker::PhantomData<T>,
}

impl<T: Display + Clone> Default for AdvancedProcessor<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Display + Clone> AdvancedProcessor<T> {
    pub fn new() -> Self {
        Self {
            _phantom: std::marker::PhantomData,
        }
    }
}

impl<T: Display + Clone> DataProcessor for AdvancedProcessor<T> {
    type Input = T;
    type Output = String;

    fn process(&self, input: &Self::Input) -> Self::Output {
        format!("Processed: {}", input)
    }
}

/// 向量包装器
pub struct VecWrapper<T> {
    data: Vec<T>,
}

impl<T> VecWrapper<T> {
    pub fn new() -> Self {
        Self { data: Vec::new() }
    }

    pub fn push(&mut self, item: T) {
        self.data.push(item);
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }

    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    pub fn iter(&self) -> std::slice::Iter<'_, T> {
        self.data.iter()
    }

    pub fn iter_mut(&mut self) -> std::slice::IterMut<'_, T> {
        self.data.iter_mut()
    }
}

impl<T> Default for VecWrapper<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// GATs (Generic Associated Types) 实现示例
pub trait Collection {
    type Item;
    type Iterator<'a>: Iterator<Item = &'a Self::Item>
    where
        Self: 'a;

    fn iter(&self) -> Self::Iterator<'_>;
}

/// 向量集合实现
pub struct VecCollection<T> {
    pub items: Vec<T>,
}

impl<T> Collection for VecCollection<T> {
    type Item = T;
    type Iterator<'a>
        = std::slice::Iter<'a, T>
    where
        Self: 'a;

    fn iter(&self) -> Self::Iterator<'_> {
        self.items.iter()
    }
}

/// 为VecWrapper实现Collection trait
impl<T> Collection for VecWrapper<T> {
    type Item = T;
    type Iterator<'a>
        = std::slice::Iter<'a, T>
    where
        Self: 'a;

    fn iter(&self) -> Self::Iterator<'_> {
        self.data.iter()
    }
}

/// 常量泛型示例
pub struct Matrix<T, const ROWS: usize, const COLS: usize> {
    data: [[T; COLS]; ROWS],
}

impl<T: Default + Copy, const ROWS: usize, const COLS: usize> Default for Matrix<T, ROWS, COLS> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Default + Copy, const ROWS: usize, const COLS: usize> Matrix<T, ROWS, COLS> {
    pub fn new() -> Self {
        Self {
            data: [[T::default(); COLS]; ROWS],
        }
    }

    pub fn get(&self, row: usize, col: usize) -> Option<&T> {
        if row < ROWS && col < COLS {
            Some(&self.data[row][col])
        } else {
            None
        }
    }

    pub fn set(&mut self, row: usize, col: usize, value: T) -> bool {
        if row < ROWS && col < COLS {
            self.data[row][col] = value;
            true
        } else {
            false
        }
    }

    pub fn dimensions() -> (usize, usize) {
        (ROWS, COLS)
    }
}

/// 编译时计算示例
pub const fn calculate_matrix_size<const ROWS: usize, const COLS: usize>() -> usize {
    ROWS * COLS
}

/// 编译时常量
pub const FACTORIAL_10: u64 = {
    let mut result = 1;
    let mut i = 1;
    while i <= 10 {
        result *= i;
        i += 1;
    }
    result
};

pub const PRIME_17: bool = {
    let n = 17;
    let mut is_prime = true;
    let mut i = 2;
    while i * i <= n {
        if n % i == 0 {
            is_prime = false;
            break;
        }
        i += 1;
    }
    is_prime
};

/// 生命周期推断优化示例
pub fn process_strings(strings: &[String]) -> Vec<&str> {
    strings.iter().map(|s| s.as_str()).collect()
}

/// 类型推导增强示例
pub fn create_map() -> HashMap<String, i32> {
    let mut map = HashMap::new();
    map.insert("key1".to_string(), 1);
    map.insert("key2".to_string(), 2);
    map
}

/// 类型级数字
pub struct Type0;
pub struct Type1;
pub struct Type2;
pub struct Type3;
pub struct Type4;

impl Type0 {
    pub const VALUE: usize = 0;
}

impl Type1 {
    pub const VALUE: usize = 1;
}

impl Type2 {
    pub const VALUE: usize = 2;
}

impl Type3 {
    pub const VALUE: usize = 3;
}

impl Type4 {
    pub const VALUE: usize = 4;
}

/// 编译时验证函数
pub const fn is_square_matrix<const ROWS: usize, const COLS: usize>() -> bool {
    ROWS == COLS
}

/// 编译时阶乘计算
pub const fn compile_time_factorial(n: u64) -> u64 {
    if n <= 1 {
        1
    } else {
        n * compile_time_factorial(n - 1)
    }
}

/// 编译时素数检查
pub const fn is_prime(n: u64) -> bool {
    if n < 2 {
        false
    } else if n == 2 {
        true
    } else if n.is_multiple_of(2) {
        false
    } else {
        let mut i = 3;
        while i * i <= n {
            if n.is_multiple_of(i) {
                return false;
            }
            i += 2;
        }
        true
    }
}
