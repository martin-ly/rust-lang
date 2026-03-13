#![allow(clippy::type_complexity)]

//! 零成本抽象验证示例
//!
//! 本示例展示Rust泛型的零成本抽象特性：
//! - 编译时单态化（Monomorphization）
//! - 性能对比（泛型 vs 具体类型）
//! - 零运行时开销验证
//!
//! 运行方式:
//! ```bash
//! cargo run --example generic_zero_cost_demo
//! ```
use std::time::Instant;

/// 泛型计算函数
fn calculate_generic<T>(value: T) -> T
where
    T: std::ops::Add<Output = T> + Copy,
{
    value + value
}

/// 具体类型计算函数
fn calculate_concrete(value: i32) -> i32 {
    value + value
}

/// 泛型容器
struct GenericContainer<T> {
    items: Vec<T>,
}

impl<T> GenericContainer<T> {
    fn new(items: Vec<T>) -> Self {
        Self { items }
    }

    fn sum(&self) -> T
    where
        T: std::ops::Add<Output = T> + Default + Copy,
    {
        self.items
            .iter()
            .copied()
            .fold(T::default(), |acc, x| acc + x)
    }
}

/// 具体类型容器
struct ConcreteContainer {
    items: Vec<i32>,
}

impl ConcreteContainer {
    fn new(items: Vec<i32>) -> Self {
        Self { items }
    }

    fn sum(&self) -> i32 {
        self.items.iter().sum()
    }
}

fn main() {
    println!("🚀 零成本抽象验证示例\n");
    println!("{}", "=".repeat(60));

    let iterations = 10_000_000;

    // 1. 函数性能对比
    println!("\n⚡ 函数性能对比:");
    println!("{}", "-".repeat(60));

    // 泛型函数
    let start = Instant::now();
    for i in 0..iterations {
        let _ = calculate_generic(i);
    }
    let generic_time = start.elapsed();

    // 具体类型函数
    let start = Instant::now();
    for i in 0..iterations {
        let _ = calculate_concrete(i);
    }
    let concrete_time = start.elapsed();

    println!("泛型函数耗时: {:?}", generic_time);
    println!("具体类型函数耗时: {:?}", concrete_time);
    println!(
        "性能差异: {:.2}%",
        ((generic_time.as_nanos() as f64 - concrete_time.as_nanos() as f64)
            / concrete_time.as_nanos() as f64)
            * 100.0
    );

    // 2. 容器性能对比
    println!("\n⚡ 容器性能对比:");
    println!("{}", "-".repeat(60));

    let data: Vec<i32> = (0..1000).collect();

    // 泛型容器
    let generic_container = GenericContainer::new(data.clone());
    let start = Instant::now();
    for _ in 0..10_000 {
        let _ = generic_container.sum();
    }
    let generic_container_time = start.elapsed();

    // 具体类型容器
    let concrete_container = ConcreteContainer::new(data);
    let start = Instant::now();
    for _ in 0..10_000 {
        let _ = concrete_container.sum();
    }
    let concrete_container_time = start.elapsed();

    println!("泛型容器耗时: {:?}", generic_container_time);
    println!("具体类型容器耗时: {:?}", concrete_container_time);
    println!(
        "性能差异: {:.2}%",
        ((generic_container_time.as_nanos() as f64 - concrete_container_time.as_nanos() as f64)
            / concrete_container_time.as_nanos() as f64)
            * 100.0
    );

    // 3. 编译时单态化说明
    println!("\n💡 零成本抽象原理:");
    println!("{}", "-".repeat(60));
    println!("  ✅ 编译时单态化（Monomorphization）");
    println!("  ✅ 为每个具体类型生成专用代码");
    println!("  ✅ 零运行时开销");
    println!("  ✅ 与手写代码性能相同");

    println!("\n✅ 演示完成！");
}
