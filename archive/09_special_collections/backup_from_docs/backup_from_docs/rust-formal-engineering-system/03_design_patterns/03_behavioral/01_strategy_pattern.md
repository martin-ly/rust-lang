# 策略模式（Strategy Pattern）

> **创建日期**: 2025-11-15
> **最后更新**: 2025-11-15
> **Rust 版本**: 1.91.1+ (Edition 2024) ✅
> **状态**: ✅ 已完善

---

## 📊 目录

- [策略模式（Strategy Pattern）](#策略模式strategy-pattern)
  - [📊 目录](#-目录)
  - [概述](#概述)
  - [问题场景](#问题场景)
  - [解决方案](#解决方案)
  - [Rust 实现](#rust-实现)
    - [使用 Trait 对象](#使用-trait-对象)
    - [使用泛型和闭包](#使用泛型和闭包)
  - [实践示例](#实践示例)
    - [示例 1：压缩策略](#示例-1压缩策略)
    - [示例 2：验证策略](#示例-2验证策略)
    - [示例 3：路由策略](#示例-3路由策略)
  - [优缺点](#优缺点)
    - [优点](#优点)
    - [缺点](#缺点)
  - [参考资料](#参考资料)

---

## 概述

策略模式（Strategy Pattern）是一种行为型设计模式，它定义了一系列算法，把它们一个个封装起来，并且使它们可相互替换。策略模式让算法独立于使用它的客户而变化。

## 问题场景

假设我们需要实现一个排序系统，支持多种排序算法（快速排序、归并排序、堆排序等），并且需要在运行时动态选择排序算法。

## 解决方案

使用策略模式，将每种排序算法封装为一个独立的策略，通过 Trait 定义统一的接口：

```rust
// 策略接口
trait SortStrategy<T> {
    fn sort(&self, data: &mut [T]);
}

// 快速排序策略
struct QuickSort;

impl<T: Ord + Clone> SortStrategy<T> for QuickSort {
    fn sort(&self, data: &mut [T]) {
        quick_sort(data);
    }
}

// 归并排序策略
struct MergeSort;

impl<T: Ord + Clone> SortStrategy<T> for MergeSort {
    fn sort(&self, data: &mut [T]) {
        merge_sort(data);
    }
}

// 上下文
struct Sorter<T> {
    strategy: Box<dyn SortStrategy<T>>,
}

impl<T> Sorter<T> {
    fn new(strategy: Box<dyn SortStrategy<T>>) -> Self {
        Sorter { strategy }
    }

    fn set_strategy(&mut self, strategy: Box<dyn SortStrategy<T>>) {
        self.strategy = strategy;
    }

    fn sort(&self, data: &mut [T]) {
        self.strategy.sort(data);
    }
}
```

## Rust 实现

### 使用 Trait 对象

```rust
// 策略 Trait
trait PaymentStrategy {
    fn pay(&self, amount: f64) -> Result<(), String>;
}

// 信用卡支付策略
struct CreditCardPayment {
    card_number: String,
}

impl PaymentStrategy for CreditCardPayment {
    fn pay(&self, amount: f64) -> Result<(), String> {
        println!("使用信用卡 {} 支付 {:.2}", self.card_number, amount);
        Ok(())
    }
}

// PayPal 支付策略
struct PayPalPayment {
    email: String,
}

impl PaymentStrategy for PayPalPayment {
    fn pay(&self, amount: f64) -> Result<(), String> {
        println!("使用 PayPal {} 支付 {:.2}", self.email, amount);
        Ok(())
    }
}

// 上下文
struct PaymentProcessor {
    strategy: Box<dyn PaymentStrategy>,
}

impl PaymentProcessor {
    fn new(strategy: Box<dyn PaymentStrategy>) -> Self {
        PaymentProcessor { strategy }
    }

    fn set_strategy(&mut self, strategy: Box<dyn PaymentStrategy>) {
        self.strategy = strategy;
    }

    fn process_payment(&self, amount: f64) -> Result<(), String> {
        self.strategy.pay(amount)
    }
}
```

### 使用泛型和闭包

```rust
// 使用闭包作为策略
struct Calculator<F> {
    operation: F,
}

impl<F> Calculator<F>
where
    F: Fn(f64, f64) -> f64,
{
    fn new(operation: F) -> Self {
        Calculator { operation }
    }

    fn calculate(&self, a: f64, b: f64) -> f64 {
        (self.operation)(a, b)
    }
}

// 使用
let add = Calculator::new(|a, b| a + b);
let multiply = Calculator::new(|a, b| a * b);

println!("{}", add.calculate(5.0, 3.0));      // 8.0
println!("{}", multiply.calculate(5.0, 3.0)); // 15.0
```

## 实践示例

### 示例 1：压缩策略

```rust
trait CompressionStrategy {
    fn compress(&self, data: &[u8]) -> Vec<u8>;
    fn decompress(&self, data: &[u8]) -> Vec<u8>;
}

struct GzipCompression;

impl CompressionStrategy for GzipCompression {
    fn compress(&self, data: &[u8]) -> Vec<u8> {
        // 使用 gzip 压缩
        // 实际实现应使用 flate2 等库
        println!("使用 Gzip 压缩");
        data.to_vec() // 简化实现
    }

    fn decompress(&self, data: &[u8]) -> Vec<u8> {
        println!("使用 Gzip 解压");
        data.to_vec() // 简化实现
    }
}

struct Bzip2Compression;

impl CompressionStrategy for Bzip2Compression {
    fn compress(&self, data: &[u8]) -> Vec<u8> {
        println!("使用 Bzip2 压缩");
        data.to_vec() // 简化实现
    }

    fn decompress(&self, data: &[u8]) -> Vec<u8> {
        println!("使用 Bzip2 解压");
        data.to_vec() // 简化实现
    }
}

struct FileCompressor {
    strategy: Box<dyn CompressionStrategy>,
}

impl FileCompressor {
    fn new(strategy: Box<dyn CompressionStrategy>) -> Self {
        FileCompressor { strategy }
    }

    fn set_strategy(&mut self, strategy: Box<dyn CompressionStrategy>) {
        self.strategy = strategy;
    }

    fn compress_file(&self, data: &[u8]) -> Vec<u8> {
        self.strategy.compress(data)
    }

    fn decompress_file(&self, data: &[u8]) -> Vec<u8> {
        self.strategy.decompress(data)
    }
}
```

### 示例 2：验证策略

```rust
trait ValidationStrategy {
    fn validate(&self, input: &str) -> Result<(), String>;
}

struct EmailValidation;

impl ValidationStrategy for EmailValidation {
    fn validate(&self, input: &str) -> Result<(), String> {
        if input.contains('@') && input.contains('.') {
            Ok(())
        } else {
            Err("无效的邮箱地址".to_string())
        }
    }
}

struct PhoneValidation;

impl ValidationStrategy for PhoneValidation {
    fn validate(&self, input: &str) -> Result<(), String> {
        if input.chars().all(|c| c.is_ascii_digit()) && input.len() == 11 {
            Ok(())
        } else {
            Err("无效的手机号码".to_string())
        }
    }
}

struct Validator {
    strategy: Box<dyn ValidationStrategy>,
}

impl Validator {
    fn new(strategy: Box<dyn ValidationStrategy>) -> Self {
        Validator { strategy }
    }

    fn set_strategy(&mut self, strategy: Box<dyn ValidationStrategy>) {
        self.strategy = strategy;
    }

    fn validate(&self, input: &str) -> Result<(), String> {
        self.strategy.validate(input)
    }
}
```

### 示例 3：路由策略

```rust
trait RoutingStrategy {
    fn route(&self, destination: &str) -> String;
}

struct ShortestPathRouting;

impl RoutingStrategy for ShortestPathRouting {
    fn route(&self, destination: &str) -> String {
        format!("最短路径到: {}", destination)
    }
}

struct FastestPathRouting;

impl RoutingStrategy for FastestPathRouting {
    fn route(&self, destination: &str) -> String {
        format!("最快路径到: {}", destination)
    }
}

struct CheapestPathRouting;

impl RoutingStrategy for CheapestPathRouting {
    fn route(&self, destination: &str) -> String {
        format!("最便宜路径到: {}", destination)
    }
}

struct Router {
    strategy: Box<dyn RoutingStrategy>,
}

impl Router {
    fn new(strategy: Box<dyn RoutingStrategy>) -> Self {
        Router { strategy }
    }

    fn set_strategy(&mut self, strategy: Box<dyn RoutingStrategy>) {
        self.strategy = strategy;
    }

    fn calculate_route(&self, destination: &str) -> String {
        self.strategy.route(destination)
    }
}
```

## 优缺点

### 优点

1. **开闭原则**：可以在不修改上下文的情况下引入新的策略
2. **单一职责原则**：每个策略类只负责一种算法
3. **消除条件语句**：避免使用大量的 if-else 或 switch-case
4. **运行时切换**：可以在运行时动态选择策略

### 缺点

1. **客户端必须了解所有策略**：客户端需要知道有哪些策略可用
2. **策略对象数量增加**：如果策略很多，会产生大量的策略类
3. **性能开销**：使用 Trait 对象会有动态分发的开销

## 参考资料

- [行为型模式索引](./00_index.md)
- [设计模式实现](../../../../crates/c09_design_pattern/src/behavioral/)
- [设计模式总索引](../00_index.md)

---

**导航**:

- 返回索引: [`00_index.md`](./00_index.md)
- 返回设计模式: [`../00_index.md`](../00_index.md)
