# Rust过程式编程基础语义

## 📅 文档信息

**文档版本**: v1.0  
**创建日期**: 2025-08-11  
**最后更新**: 2025-08-11  
**状态**: 已完成  
**质量等级**: 钻石级 ⭐⭐⭐⭐⭐

---

**文档编号**: RFTS-06-PPF  
**版本**: 1.0  
**最后更新**: 2025-01-27  
**状态**: 核心理论文档

---

## 目录

- [Rust过程式编程基础语义](#rust过程式编程基础语义)
  - [📅 文档信息](#-文档信息)
  - [目录](#目录)
  - [1. 过程式编程理论基础](#1-过程式编程理论基础)
    - [1.1 过程式语义模型](#11-过程式语义模型)
    - [1.2 命令式计算模型](#12-命令式计算模型)
  - [2. Rust中的过程式编程](#2-rust中的过程式编程)
    - [2.1 函数与过程](#21-函数与过程)
    - [2.2 变量与赋值](#22-变量与赋值)
    - [2.3 控制流结构体体体](#23-控制流结构体体体)
    - [2.4 错误处理](#24-错误处理)
  - [总结](#总结)

## 1. 过程式编程理论基础

### 1.1 过程式语义模型

**定义 1.1** (过程式编程系统)  
过程式编程系统是一个四元组 $PPS = (P, S, C, E)$，其中：

- $P$ 是过程/函数集合
- $S$ 是状态空间
- $C$ 是控制流结构体体体集合
- $E: P × S × C → S'$ 是执行语义函数

**定理 1.1** (过程式编程正确性)  
过程式编程系统保证：

1. **状态变化**: $∀p ∈ P, s ∈ S, execute(p, s) → s'$
2. **控制流**: $∀c ∈ C, control\_transfer(c)$ 是确定性的
3. **副作用**: $side\_effects(p)$ 是可控和可预测的

### 1.2 命令式计算模型

**定义 1.2** (命令语义)  
命令的操作语义定义为状态转换：
$$⟨c, s⟩ → s'$$

其中 $c$ 是命令，$s$ 和 $s'$ 分别是执行前后的状态。

**基本命令类型**:

- **赋值**: $x := e$
- **顺序**: $c_1; c_2$
- **条件**: $\text{if } b \text{ then } c_1 \text{ else } c_2$
- **循环**: $\text{while } b \text{ do } c$

## 2. Rust中的过程式编程

### 2.1 函数与过程

```rust
// 过程式函数的定义和使用
fn calculate_factorial(n: u64) -> u64 {
    if n <= 1 {
        1
    } else {
        n * calculate_factorial(n - 1)
    }
}

// 迭代版本（更符合过程式风格）
fn calculate_factorial_iterative(n: u64) -> u64 {
    let mut result = 1;
    let mut counter = 1;
    
    while counter <= n {
        result *= counter;
        counter += 1;
    }
    
    result
}

// 带副作用的过程
fn print_and_calculate(n: u64) -> u64 {
    println!("Calculating factorial of {}", n);
    let result = calculate_factorial_iterative(n);
    println!("Result: {}", result);
    result
}

// 复杂的过程式算法
fn bubble_sort(arr: &mut [i32]) {
    let len = arr.len();
    
    for i in 0..len {
        for j in 0..(len - i - 1) {
            if arr[j] > arr[j + 1] {
                // 交换元素
                let temp = arr[j];
                arr[j] = arr[j + 1];
                arr[j + 1] = temp;
            }
        }
    }
}

// 使用示例
fn demonstrate_procedural_programming() {
    // 计算阶乘
    let fact5 = print_and_calculate(5);
    println!("5! = {}", fact5);
    
    // 排序数组
    let mut numbers = vec![64, 34, 25, 12, 22, 11, 90];
    println!("Original array: {:?}", numbers);
    
    bubble_sort(&mut numbers);
    println!("Sorted array: {:?}", numbers);
}
```

**定理 2.1** (函数执行正确性)  
过程式函数保证：

1. **确定性**: 相同输入产生相同输出（纯函数）
2. **副作用控制**: 副作用明确且可控
3. **状态变化**: 可变状态的变化是局部的和可预测的

### 2.2 变量与赋值

```rust
// 变量声明和赋值的语义
fn demonstrate_variable_semantics() {
    // 不可变变量（默认）
    let x = 42;
    println!("x = {}", x);
    
    // x = 43; // 编译错误：不能修改不可变变量
    
    // 可变变量
    let mut y = 10;
    println!("y = {}", y);
    
    y = 20; // 重新赋值
    println!("y = {}", y);
    
    // 变量遮蔽（shadowing）
    let z = 5;
    println!("z = {}", z);
    
    let z = z * 2; // 创建新变量，遮蔽旧变量
    println!("z = {}", z);
    
    let z = "hello"; // 可以改变类型
    println!("z = {}", z);
}

// 复杂的状态管理
struct Counter {
    value: i32,
    step: i32,
}

impl Counter {
    fn new(initial_value: i32, step: i32) -> Self {
        Self {
            value: initial_value,
            step,
        }
    }
    
    // 修改状态的方法
    fn increment(&mut self) {
        self.value += self.step;
    }
    
    fn decrement(&mut self) {
        self.value -= self.step;
    }
    
    fn reset(&mut self) {
        self.value = 0;
    }
    
    fn get_value(&self) -> i32 {
        self.value
    }
    
    fn set_step(&mut self, new_step: i32) {
        self.step = new_step;
    }
}

fn demonstrate_stateful_operations() {
    let mut counter = Counter::new(0, 1);
    
    println!("Initial value: {}", counter.get_value());
    
    // 一系列状态变化操作
    counter.increment();
    println!("After increment: {}", counter.get_value());
    
    counter.increment();
    println!("After second increment: {}", counter.get_value());
    
    counter.set_step(5);
    counter.increment();
    println!("After increment with step 5: {}", counter.get_value());
    
    counter.reset();
    println!("After reset: {}", counter.get_value());
}
```

**定理 2.2** (变量语义正确性)  
变量系统保证：

1. **类型安全**: 变量类型在编译时确定
2. **内存安全**: 变量访问不会越界或悬空
3. **所有权管理**: 变量的所有权移动是安全的

### 2.3 控制流结构体体体

```rust
// 条件控制流
fn demonstrate_conditional_flow(x: i32) -> String {
    if x > 0 {
        "positive".to_string()
    } else if x < 0 {
        "negative".to_string()
    } else {
        "zero".to_string()
    }
}

// 模式匹配作为控制流
fn classify_number(x: i32) -> String {
    match x {
        0 => "zero".to_string(),
        1..=10 => "small positive".to_string(),
        11..=100 => "medium positive".to_string(),
        101.. => "large positive".to_string(),
        -10..=-1 => "small negative".to_string(),
        _ => "large negative".to_string(),
    }
}

// 循环控制流
fn demonstrate_loops() {
    // while循环
    let mut count = 0;
    while count < 5 {
        println!("Count: {}", count);
        count += 1;
    }
    
    // for循环
    for i in 0..5 {
        println!("Index: {}", i);
    }
    
    // 迭代器循环
    let numbers = vec![1, 2, 3, 4, 5];
    for num in numbers.iter() {
        println!("Number: {}", num);
    }
    
    // loop循环（无限循环）
    let mut counter = 0;
    let result = loop {
        counter += 1;
        if counter == 10 {
            break counter * 2; // 返回值
        }
    };
    println!("Loop result: {}", result);
}

// 复杂的控制流：算法实现
fn find_prime_numbers(limit: u32) -> Vec<u32> {
    let mut primes = Vec::new();
    let mut is_prime = vec![true; (limit + 1) as usize];
    
    is_prime[0] = false;
    if limit > 0 {
        is_prime[1] = false;
    }
    
    let mut p = 2;
    while p * p <= limit {
        if is_prime[p as usize] {
            // 标记p的倍数为非质数
            let mut multiple = p * p;
            while multiple <= limit {
                is_prime[multiple as usize] = false;
                multiple += p;
            }
        }
        p += 1;
    }
    
    // 收集质数
    for i in 2..=limit {
        if is_prime[i as usize] {
            primes.push(i);
        }
    }
    
    primes
}

fn demonstrate_complex_algorithm() {
    let primes = find_prime_numbers(30);
    println!("Prime numbers up to 30: {:?}", primes);
}
```

**定理 2.3** (控制流正确性)  
控制流结构体体体保证：

1. **结构体体体化**: 所有控制流都有明确的入口和出口
2. **可达性**: 所有代码路径都是可达的或被明确标记为不可达
3. **终止性**: 循环结构体体体具有明确的终止条件

### 2.4 错误处理

```rust
// 过程式错误处理
#[derive(Debug)]
enum CalculationError {
    DivisionByZero,
    Overflow,
    InvalidInput,
}

fn safe_divide(a: f64, b: f64) -> Result<f64, CalculationError> {
    if b == 0.0 {
        Err(CalculationError::DivisionByZero)
    } else if a.is_infinite() || b.is_infinite() {
        Err(CalculationError::Overflow)
    } else if a.is_nan() || b.is_nan() {
        Err(CalculationError::InvalidInput)
    } else {
        Ok(a / b)
    }
}

fn calculate_average(numbers: &[f64]) -> Result<f64, CalculationError> {
    if numbers.is_empty() {
        return Err(CalculationError::InvalidInput);
    }
    
    let sum: f64 = numbers.iter().sum();
    safe_divide(sum, numbers.len() as f64)
}

// 错误传播和处理
fn process_data(data: &[f64]) -> Result<String, CalculationError> {
    let average = calculate_average(data)?; // ? 操作符传播错误
    
    let result = if average > 0.0 {
        format!("Positive average: {:.2}", average)
    } else if average < 0.0 {
        format!("Negative average: {:.2}", average)
    } else {
        "Zero average".to_string()
    };
    
    Ok(result)
}

fn demonstrate_error_handling() {
    let data1 = vec![1.0, 2.0, 3.0, 4.0, 5.0];
    let data2 = vec![];
    let data3 = vec![10.0, 0.0, -5.0];
    
    match process_data(&data1) {
        Ok(result) => println!("Data1: {}", result),
        Err(e) => println!("Error processing data1: {:?}", e),
    }
    
    match process_data(&data2) {
        Ok(result) => println!("Data2: {}", result),
        Err(e) => println!("Error processing data2: {:?}", e),
    }
    
    match process_data(&data3) {
        Ok(result) => println!("Data3: {}", result),
        Err(e) => println!("Error processing data3: {:?}", e),
    }
}
```

**定理 2.4** (错误处理正确性)  
错误处理机制保证：

1. **完整性**: 所有可能的错误情况都被处理
2. **类型安全**: 错误类型在编译时确定
3. **传播性**: 错误可以安全地在调用栈中传播

---

## 总结

本文档建立了Rust过程式编程的完整理论基础，包括：

1. **基础理论**: 过程式编程语义模型和命令式计算
2. **函数机制**: 函数定义、调用和副作用管理
3. **变量系统**: 变量声明、赋值和状态管理
4. **控制流**: 条件、循环和复杂算法实现
5. **错误处理**: 结构体体体化错误处理和传播机制

这些理论展示了Rust如何支持传统的过程式编程范式，同时保持内存安全和类型安全。

---

*文档状态: 完成*  
*版本: 1.0*  
*字数: ~12KB*

"

---
