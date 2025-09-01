# 函数调用语义分析

## 目录

- [函数调用语义分析](#函数调用语义分析)
  - [目录](#目录)
  - [概述](#概述)
  - [1. 函数调用理论基础](#1-函数调用理论基础)
    - [1.1 函数调用模型](#11-函数调用模型)
    - [1.2 调用约定](#12-调用约定)
  - [2. 参数传递机制](#2-参数传递机制)
    - [2.1 值传递](#21-值传递)
    - [2.2 引用传递](#22-引用传递)
    - [2.3 所有权传递](#23-所有权传递)
  - [3. 函数签名与类型](#3-函数签名与类型)
    - [3.1 函数类型](#31-函数类型)
    - [3.2 闭包类型](#32-闭包类型)
  - [4. 返回值处理](#4-返回值处理)
    - [4.1 单值返回](#41-单值返回)
    - [4.2 多值返回](#42-多值返回)
    - [4.3 错误返回](#43-错误返回)
  - [5. 调用约定与ABI](#5-调用约定与abi)
    - [5.1 系统调用约定](#51-系统调用约定)
    - [5.2 内联函数](#52-内联函数)
  - [6. 函数重载与特化](#6-函数重载与特化)
    - [6.1 函数重载模拟](#61-函数重载模拟)
    - [6.2 方法重载](#62-方法重载)
  - [7. 性能优化](#7-性能优化)
    - [7.1 零成本抽象](#71-零成本抽象)
    - [7.2 尾调用优化](#72-尾调用优化)
  - [8. 形式化证明](#8-形式化证明)
    - [8.1 函数调用安全定理](#81-函数调用安全定理)
    - [8.2 参数传递定理](#82-参数传递定理)
  - [9. 工程实践](#9-工程实践)
    - [9.1 最佳实践](#91-最佳实践)
    - [9.2 常见陷阱](#92-常见陷阱)
  - [10. 交叉引用](#10-交叉引用)
  - [11. 参考文献](#11-参考文献)

## 概述

本文档详细分析Rust中函数调用的语义，包括其理论基础、实现机制和形式化定义。

## 1. 函数调用理论基础

### 1.1 函数调用模型

**定义 1.1.1 (函数调用)**
函数调用是程序执行的基本操作，包括参数传递、控制转移、执行和返回。

**函数调用阶段**：

1. **参数准备**：计算参数值
2. **控制转移**：跳转到函数入口
3. **函数执行**：执行函数体
4. **返回值处理**：处理返回值
5. **控制返回**：返回到调用点

### 1.2 调用约定

**Rust调用约定**：

```rust
// 标准函数调用
fn add(x: i32, y: i32) -> i32 {
    x + y
}

// 调用示例
let result = add(5, 3); // 函数调用
```

## 2. 参数传递机制

### 2.1 值传递

**值传递语义**：

```rust
fn value_pass(x: i32) {
    println!("Received: {}", x);
}

fn main() {
    let a = 42;
    value_pass(a);  // a 的值被复制到函数参数
    println!("Original: {}", a);  // a 仍然可用
}
```

### 2.2 引用传递

**引用传递语义**：

```rust
fn reference_pass(x: &i32) {
    println!("Received: {}", x);
}

fn mutable_reference_pass(x: &mut i32) {
    *x += 1;  // 修改原始值
}

fn main() {
    let mut a = 42;
    reference_pass(&a);  // 不可变引用
    mutable_reference_pass(&mut a);  // 可变引用
    println!("Modified: {}", a);  // a 被修改
}
```

### 2.3 所有权传递

**所有权传递语义**：

```rust
fn ownership_pass(x: String) {
    println!("Owned: {}", x);
    // x 在这里被销毁
}

fn main() {
    let s = String::from("hello");
    ownership_pass(s);  // s 的所有权转移给函数
    // println!("{}", s);  // 编译错误：s 已被移动
}
```

## 3. 函数签名与类型

### 3.1 函数类型

**函数类型定义**：

```rust
// 函数指针类型
type MathFn = fn(i32, i32) -> i32;

// 函数类型示例
fn add(x: i32, y: i32) -> i32 { x + y }
fn multiply(x: i32, y: i32) -> i32 { x * y }

// 使用函数类型
fn apply_operation(f: MathFn, x: i32, y: i32) -> i32 {
    f(x, y)
}

fn main() {
    let result1 = apply_operation(add, 5, 3);
    let result2 = apply_operation(multiply, 5, 3);
}
```

### 3.2 闭包类型

**闭包类型**：

```rust
// 闭包类型推断
let add_closure = |x, y| x + y;
let multiply_closure = |x: i32, y: i32| -> i32 { x * y };

// 使用闭包
fn apply_closure<F>(f: F, x: i32, y: i32) -> i32
where
    F: Fn(i32, i32) -> i32,
{
    f(x, y)
}
```

## 4. 返回值处理

### 4.1 单值返回

**单值返回**：

```rust
fn single_return() -> i32 {
    42
}

fn conditional_return(x: i32) -> i32 {
    if x > 0 {
        x * 2
    } else {
        -x
    }
}
```

### 4.2 多值返回

**多值返回**：

```rust
fn multiple_return() -> (i32, String) {
    (42, String::from("hello"))
}

fn main() {
    let (number, text) = multiple_return();
    println!("Number: {}, Text: {}", number, text);
}
```

### 4.3 错误返回

**错误返回**：

```rust
fn error_return(x: i32) -> Result<i32, String> {
    if x >= 0 {
        Ok(x * 2)
    } else {
        Err("Negative number".to_string())
    }
}

fn main() {
    match error_return(5) {
        Ok(result) => println!("Success: {}", result),
        Err(error) => println!("Error: {}", error),
    }
}
```

## 5. 调用约定与ABI

### 5.1 系统调用约定

**系统调用约定**：

```rust
// 外部函数接口
extern "C" {
    fn printf(format: *const i8, ...) -> i32;
}

// 自定义调用约定
extern "system" fn windows_api_function() -> i32;

// Rust调用约定（默认）
fn rust_function() -> i32 {
    42
}
```

### 5.2 内联函数

**内联函数**：

```rust
#[inline]
fn inline_function(x: i32) -> i32 {
    x * 2
}

#[inline(always)]
fn always_inline(x: i32) -> i32 {
    x + 1
}

#[inline(never)]
fn never_inline(x: i32) -> i32 {
    x - 1
}
```

## 6. 函数重载与特化

### 6.1 函数重载模拟

**函数重载模拟**：

```rust
// 使用泛型模拟重载
fn process<T>(x: T) -> String {
    format!("Generic: {:?}", x)
}

// 为特定类型提供特化
fn process(x: i32) -> String {
    format!("Integer: {}", x)
}

fn process(x: &str) -> String {
    format!("String: {}", x)
}
```

### 6.2 方法重载

**方法重载**：

```rust
struct Calculator;

impl Calculator {
    fn add(&self, x: i32, y: i32) -> i32 {
        x + y
    }
    
    fn add_float(&self, x: f64, y: f64) -> f64 {
        x + y
    }
    
    fn add_string(&self, x: &str, y: &str) -> String {
        format!("{}{}", x, y)
    }
}
```

## 7. 性能优化

### 7.1 零成本抽象

**零成本抽象**：

```rust
// 零成本函数调用
fn zero_cost_function(x: i32) -> i32 {
    x * 2 + 1
}

// 编译时优化
const fn const_function(x: i32) -> i32 {
    x * 2 + 1
}
```

### 7.2 尾调用优化

**尾调用优化**：

```rust
// 尾递归函数
fn tail_recursive_factorial(n: u64, acc: u64) -> u64 {
    if n <= 1 {
        acc
    } else {
        tail_recursive_factorial(n - 1, n * acc)
    }
}

// 使用尾调用优化
fn factorial(n: u64) -> u64 {
    tail_recursive_factorial(n, 1)
}
```

## 8. 形式化证明

### 8.1 函数调用安全定理

**定理 8.1.1 (函数调用安全)**
如果函数调用通过类型检查，则调用是类型安全的。

**证明**：
通过类型推导规则证明函数调用保持类型安全。

### 8.2 参数传递定理

**定理 8.2.1 (参数传递安全)**
参数传递机制保证内存安全和类型安全。

**证明**：
通过所有权系统和借用检查器证明参数传递的安全性。

## 9. 工程实践

### 9.1 最佳实践

**最佳实践**：

1. **明确函数签名**：提供清晰的参数和返回类型
2. **使用适当的参数传递方式**：根据需要选择值传递、引用传递或所有权传递
3. **处理错误情况**：使用Result类型处理可能的错误
4. **优化性能**：合理使用内联和尾调用优化

### 9.2 常见陷阱

**常见陷阱**：

1. **生命周期问题**：

   ```rust
   // 错误：生命周期不匹配
   fn bad_lifetime<'a>(x: &'a i32) -> &'static i32 {
       x  // 编译错误：生命周期不匹配
   }
   ```

2. **所有权问题**：

   ```rust
   // 错误：重复使用已移动的值
   fn main() {
       let s = String::from("hello");
       ownership_pass(s);
       ownership_pass(s);  // 编译错误：s 已被移动
   }
   ```

3. **类型推断问题**：

   ```rust
   // 错误：类型推断失败
   fn ambiguous_call() {
       let closure = |x| x + 1;  // 类型不明确
       // closure(42);  // 编译错误：无法推断类型
   }
   ```

## 10. 交叉引用

- [类型系统分析](./type_system_analysis.md) - 类型系统深度分析
- [生命周期语义](./06_lifetime_semantics.md) - 生命周期系统
- [错误处理语义](./10_error_handling_semantics.md) - 错误处理机制
- [性能分析语义](./20_performance_analysis_semantics.md) - 性能分析

## 11. 参考文献

1. Rust Reference - Functions
2. The Rust Programming Language - Functions
3. Rustonomicon - FFI
4. System V ABI
