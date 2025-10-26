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
//! # Rust 1.89 泛型系统特性示例
//!
//! 本示例展示了Rust 1.89版本中的泛型系统增强特性：
//! - 常量泛型改进
//! - 生命周期推断优化
//! - 简化的类型级编程

//use std::collections::HashMap;
use anyhow::Result;
use std::fmt::Display;
use std::ops::{Add, Mul};

/// Rust 1.89 常量泛型改进示例
///
/// 常量泛型现在支持更复杂的编译时计算和类型推导
struct Matrix<T, const ROWS: usize, const COLS: usize> {
    data: [[T; COLS]; ROWS],
}

impl<T: Default + Copy, const ROWS: usize, const COLS: usize> Matrix<T, ROWS, COLS> {
    fn new() -> Self {
        Self {
            data: [[T::default(); COLS]; ROWS],
        }
    }

    fn get(&self, row: usize, col: usize) -> Option<&T> {
        if row < ROWS && col < COLS {
            Some(&self.data[row][col])
        } else {
            None
        }
    }

    fn set(&mut self, row: usize, col: usize, value: T) -> Result<()> {
        if row < ROWS && col < COLS {
            self.data[row][col] = value;
            Ok(())
        } else {
            Err(anyhow::anyhow!("索引超出范围"))
        }
    }
}

/// 常量泛型与类型级编程结合
#[allow(dead_code)]
impl<T: Add<Output = T> + Copy + Default, const ROWS: usize, const COLS: usize>
    Matrix<T, ROWS, COLS>
where
    T: Mul<Output = T>,
{
    /// 矩阵乘法：要求维度兼容
    fn multiply<const OTHER_COLS: usize>(
        &self,
        other: &Matrix<T, COLS, OTHER_COLS>,
    ) -> Matrix<T, ROWS, OTHER_COLS> {
        let mut result = Matrix::new();

        for i in 0..ROWS {
            for j in 0..OTHER_COLS {
                let mut sum = T::default();
                for k in 0..COLS {
                    if let (Some(a), Some(b)) = (self.get(i, k), other.get(k, j)) {
                        sum = sum + *a * *b;
                    }
                }
                let _ = result.set(i, j, sum);
            }
        }

        result
    }
}

/// 常量泛型函数示例
#[allow(dead_code)]
const fn calculate_size<const N: usize>() -> usize {
    N * N
}

/// 生命周期推断优化示例
///
/// Rust 1.89中生命周期推断有了显著改进，减少显式生命周期标注的需求
trait DataProcessor {
    type Input;
    type Output;

    fn process(&self, input: &Self::Input) -> Self::Output;
}

/// 改进的生命周期推断允许更简洁的代码
struct SimpleProcessor;

impl DataProcessor for SimpleProcessor {
    type Input = String;
    type Output = String;

    // Rust 1.89中，编译器可以自动推断生命周期，无需显式标注
    fn process(&self, input: &Self::Input) -> Self::Output {
        input.to_uppercase()
    }
}

/// 高级生命周期推断示例
struct AdvancedProcessor<T> {
    _phantom: std::marker::PhantomData<T>,
}

impl<T> AdvancedProcessor<T> {
    fn new() -> Self {
        Self {
            _phantom: std::marker::PhantomData,
        }
    }
}

impl<T: Display + Clone> DataProcessor for AdvancedProcessor<T> {
    type Input = T;
    type Output = String;

    // 编译器自动推断生命周期
    fn process(&self, input: &Self::Input) -> Self::Output {
        format!("处理结果: {}", input)
    }
}

/// 简化的类型级编程示例
trait TypeLevel {
    const VALUE: usize;
}

/// 具体数值类型
struct N<const N: usize>;

impl<const N: usize> TypeLevel for N<{ N }> {
    const VALUE: usize = N;
}

/// 类型级计算示例
type Sum = N<8>;
type Product = N<24>;

/// 编译时类型检查
const _: () = {
    assert!(Sum::VALUE == 8);
    assert!(Product::VALUE == 24);
};

/// 简化的集合示例
struct SimpleCollection<T> {
    items: Vec<T>,
}

impl<T> SimpleCollection<T> {
    fn new() -> Self {
        Self { items: Vec::new() }
    }

    fn push(&mut self, item: T) {
        self.items.push(item);
    }

    fn len(&self) -> usize {
        self.items.len()
    }

    fn iter(&self) -> std::slice::Iter<'_, T> {
        self.items.iter()
    }
}

/// 主函数
fn main() -> Result<()> {
    println!("🚀 Rust 1.89 泛型系统特性演示");
    println!("{}", "=".repeat(50));

    // 1. 常量泛型示例
    println!("\n1. 常量泛型改进示例");
    let mut matrix: Matrix<i32, 2, 3> = Matrix::new();
    matrix.set(0, 0, 1)?;
    matrix.set(0, 1, 2)?;
    matrix.set(1, 0, 3)?;
    matrix.set(1, 1, 4)?;

    println!("矩阵[0,0]: {:?}", matrix.get(0, 0));
    println!("矩阵[1,1]: {:?}", matrix.get(1, 1));

    // 2. 生命周期推断示例
    println!("\n2. 生命周期推断优化示例");
    let processor = SimpleProcessor;
    let input = "hello world".to_string();
    let output = processor.process(&input);
    println!("处理结果: {}", output);

    let advanced_processor = AdvancedProcessor::<i32>::new();
    let number = 42;
    let result = advanced_processor.process(&number);
    println!("高级处理结果: {}", result);

    // 3. 类型级编程示例
    println!("\n3. 类型级编程增强示例");
    println!(
        "类型级数值: {} + {} = {}",
        N::<5>::VALUE,
        N::<3>::VALUE,
        Sum::VALUE
    );
    println!(
        "类型级数值: {} * {} = {}",
        N::<4>::VALUE,
        N::<6>::VALUE,
        Product::VALUE
    );

    // 4. 简化集合示例
    println!("\n4. 简化集合示例");
    let mut collection = SimpleCollection::new();
    collection.push(1);
    collection.push(2);
    collection.push(3);

    println!("集合长度: {}", collection.len());
    let sum: i32 = collection.iter().sum();
    println!("元素总和: {}", sum);

    println!("\n✅ Rust 1.89 泛型特性演示完成！");
    Ok(())
}
