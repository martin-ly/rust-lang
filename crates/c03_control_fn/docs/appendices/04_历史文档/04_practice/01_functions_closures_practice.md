# 01. 函数与闭包实践 (Functions & Closures Practice)

> **文档类型**：实践  
> **难度等级**：⭐⭐⭐  
> **预计阅读时间**：2小时  
> **前置知识**：函数与闭包基础、trait 系统


## 📊 目录

- [📖 内容概述](#内容概述)
- [🎯 学习目标](#学习目标)
- [📚 目录](#目录)
- [函数基础](#函数基础)
  - [函数定义](#函数定义)
  - [函数参数](#函数参数)
  - [语句与表达式](#语句与表达式)
- [函数参数与返回值](#函数参数与返回值)
  - [返回值](#返回值)
  - [多个参数](#多个参数)
  - [引用参数](#引用参数)
- [闭包](#闭包)
  - [基本闭包语法](#基本闭包语法)
  - [闭包捕获环境](#闭包捕获环境)
  - [闭包类型推断](#闭包类型推断)
  - [闭包所有权](#闭包所有权)
- [高阶函数](#高阶函数)
  - [函数作为参数](#函数作为参数)
  - [返回闭包](#返回闭包)
  - [闭包作为结构体字段](#闭包作为结构体字段)
- [函数指针](#函数指针)
  - [函数指针类型](#函数指针类型)
  - [函数指针与闭包的区别](#函数指针与闭包的区别)
- [函数式编程模式](#函数式编程模式)
  - [迭代器与函数式编程](#迭代器与函数式编程)
  - [自定义迭代器](#自定义迭代器)
  - [函数组合](#函数组合)
  - [柯里化](#柯里化)
- [性能考虑](#性能考虑)
  - [闭包性能](#闭包性能)
  - [函数指针 vs 闭包](#函数指针-vs-闭包)
- [最佳实践](#最佳实践)
- [相关主题](#相关主题)


## 📖 内容概述

本文档通过丰富的实例深入介绍 Rust 中的函数定义、调用、闭包以及函数式编程概念，提供大量实战代码和最佳实践指导。

## 🎯 学习目标

完成本文档学习后，你将能够：

- [ ] 掌握函数的各种定义和调用方式
- [ ] 理解闭包的捕获机制和使用场景
- [ ] 编写高阶函数和返回闭包
- [ ] 应用函数式编程模式
- [ ] 理解函数指针与闭包的区别
- [ ] 在实际项目中灵活运用函数和闭包

## 📚 目录

- [01. 函数与闭包实践 (Functions \& Closures Practice)](#01-函数与闭包实践-functions--closures-practice)
  - [📖 内容概述](#-内容概述)
  - [🎯 学习目标](#-学习目标)
  - [📚 目录](#-目录)
  - [函数基础](#函数基础)
    - [函数定义](#函数定义)
    - [函数参数](#函数参数)
    - [语句与表达式](#语句与表达式)
  - [函数参数与返回值](#函数参数与返回值)
    - [返回值](#返回值)
    - [多个参数](#多个参数)
    - [引用参数](#引用参数)
  - [闭包](#闭包)
    - [基本闭包语法](#基本闭包语法)
    - [闭包捕获环境](#闭包捕获环境)
    - [闭包类型推断](#闭包类型推断)
    - [闭包所有权](#闭包所有权)
  - [高阶函数](#高阶函数)
    - [函数作为参数](#函数作为参数)
    - [返回闭包](#返回闭包)
    - [闭包作为结构体字段](#闭包作为结构体字段)
  - [函数指针](#函数指针)
    - [函数指针类型](#函数指针类型)
    - [函数指针与闭包的区别](#函数指针与闭包的区别)
  - [函数式编程模式](#函数式编程模式)
    - [迭代器与函数式编程](#迭代器与函数式编程)
    - [自定义迭代器](#自定义迭代器)
    - [函数组合](#函数组合)
    - [柯里化](#柯里化)
  - [性能考虑](#性能考虑)
    - [闭包性能](#闭包性能)
    - [函数指针 vs 闭包](#函数指针-vs-闭包)
  - [最佳实践](#最佳实践)
  - [相关主题](#相关主题)

## 函数基础

### 函数定义

```rust
fn main() {
    println!("Hello, world!");
    another_function();
}

fn another_function() {
    println!("Another function.");
}
```

### 函数参数

```rust
fn main() {
    print_labeled_measurement(5, 'h');
}

fn print_labeled_measurement(value: i32, unit_label: char) {
    println!("The measurement is: {}{}", value, unit_label);
}
```

### 语句与表达式

```rust
fn main() {
    let y = {
        let x = 3;
        x + 1  // 表达式，没有分号
    };

    println!("The value of y is: {}", y);
}
```

## 函数参数与返回值

### 返回值

```rust
fn five() -> i32 {
    5  // 没有分号，这是一个表达式
}

fn plus_one(x: i32) -> i32 {
    x + 1  // 表达式作为返回值
}

fn main() {
    let x = five();
    let y = plus_one(5);
    
    println!("The value of x is: {}", x);
    println!("The value of y is: {}", y);
}
```

### 多个参数

```rust
fn calculate_length(s: String) -> (String, usize) {
    let length = s.len();
    (s, length)  // 返回元组
}

fn main() {
    let s1 = String::from("hello");
    let (s2, len) = calculate_length(s1);
    
    println!("The length of '{}' is {}.", s2, len);
}
```

### 引用参数

```rust
fn calculate_length(s: &String) -> usize {
    s.len()
} // s 离开作用域，但因为它没有 s 的所有权，所以什么也不会发生

fn main() {
    let s1 = String::from("hello");
    let len = calculate_length(&s1);
    
    println!("The length of '{}' is {}.", s1, len);
}
```

## 闭包

### 基本闭包语法

```rust
fn main() {
    let add_one = |x: i32| -> i32 { x + 1 };
    let add_one_v2 = |x| x + 1;  // 类型推断
    
    println!("{}", add_one(5));
    println!("{}", add_one_v2(5));
}
```

### 闭包捕获环境

```rust
fn main() {
    let x = 4;
    
    let equal_to_x = |z| z == x;  // 闭包可以访问外部变量
    
    let y = 4;
    assert!(equal_to_x(y));
}
```

### 闭包类型推断

```rust
fn main() {
    let example_closure = |x| x;
    
    let s = example_closure(String::from("hello"));
    // let n = example_closure(5);  // 错误！类型已经推断为 String
}
```

### 闭包所有权

```rust
fn main() {
    let x = vec![1, 2, 3];
    
    let equal_to_x = move |z| z == x;  // move 关键字强制获取所有权
    
    // println!("can't use x here: {:?}", x);  // 错误！x 已被移动
    
    let y = vec![1, 2, 3];
    assert!(equal_to_x(y));
}
```

## 高阶函数

### 函数作为参数

```rust
fn apply_twice<F>(f: F, x: i32) -> i32 
where 
    F: Fn(i32) -> i32,
{
    f(f(x))
}

fn square(x: i32) -> i32 {
    x * x
}

fn main() {
    let result = apply_twice(square, 3);
    println!("{}", result);  // 输出: 81
}
```

### 返回闭包

```rust
fn returns_closure() -> Box<dyn Fn(i32) -> i32> {
    Box::new(|x| x + 1)
}

fn main() {
    let closure = returns_closure();
    println!("{}", closure(5));  // 输出: 6
}
```

### 闭包作为结构体字段

```rust
struct Cacher<T>
where
    T: Fn(u32) -> u32,
{
    calculation: T,
    value: Option<u32>,
}

impl<T> Cacher<T>
where
    T: Fn(u32) -> u32,
{
    fn new(calculation: T) -> Cacher<T> {
        Cacher {
            calculation,
            value: None,
        }
    }

    fn value(&mut self, arg: u32) -> u32 {
        match self.value {
            Some(v) => v,
            None => {
                let v = (self.calculation)(arg);
                self.value = Some(v);
                v
            }
        }
    }
}

fn main() {
    let mut expensive_result = Cacher::new(|num| {
        println!("calculating slowly...");
        num
    });
    
    println!("{}", expensive_result.value(1));
    println!("{}", expensive_result.value(1));  // 不会重新计算
}
```

## 函数指针

### 函数指针类型

```rust
fn add_one(x: i32) -> i32 {
    x + 1
}

fn do_twice(f: fn(i32) -> i32, arg: i32) -> i32 {
    f(f(arg))
}

fn main() {
    let answer = do_twice(add_one, 5);
    println!("The answer is: {}", answer);
}
```

### 函数指针与闭包的区别

```rust
fn main() {
    let list_of_numbers = vec![1, 2, 3];
    let list_of_strings: Vec<String> = list_of_numbers
        .iter()
        .map(|i| i.to_string())  // 闭包
        .collect();
    
    let list_of_strings: Vec<String> = list_of_numbers
        .iter()
        .map(ToString::to_string)  // 函数指针
        .collect();
}
```

## 函数式编程模式

### 迭代器与函数式编程

```rust
fn main() {
    let v1 = vec![1, 2, 3];
    let v1_iter = v1.iter();
    
    for val in v1_iter {
        println!("Got: {}", val);
    }
    
    // 链式调用
    let sum: i32 = v1.iter()
        .map(|x| x * 2)
        .filter(|&x| x > 2)
        .sum();
    
    println!("Sum: {}", sum);
}
```

### 自定义迭代器

```rust
struct Counter {
    count: u32,
}

impl Counter {
    fn new() -> Counter {
        Counter { count: 0 }
    }
}

impl Iterator for Counter {
    type Item = u32;

    fn next(&mut self) -> Option<Self::Item> {
        if self.count < 5 {
            self.count += 1;
            Some(self.count)
        } else {
            None
        }
    }
}

fn main() {
    let counter = Counter::new();
    
    for count in counter {
        println!("{}", count);
    }
    
    // 使用迭代器适配器
    let sum: u32 = Counter::new()
        .zip(Counter::new().skip(1))
        .map(|(a, b)| a * b)
        .filter(|x| x % 3 == 0)
        .sum();
    
    println!("Sum: {}", sum);
}
```

### 函数组合

```rust
fn compose<F, G, A, B, C>(f: F, g: G) -> impl Fn(A) -> C
where
    F: Fn(B) -> C,
    G: Fn(A) -> B,
{
    move |x| f(g(x))
}

fn add_one(x: i32) -> i32 {
    x + 1
}

fn multiply_by_two(x: i32) -> i32 {
    x * 2
}

fn main() {
    let add_one_then_double = compose(multiply_by_two, add_one);
    println!("{}", add_one_then_double(5));  // 输出: 12
}
```

### 柯里化

```rust
fn add(x: i32) -> impl Fn(i32) -> i32 {
    move |y| x + y
}

fn main() {
    let add_five = add(5);
    println!("{}", add_five(3));  // 输出: 8
}
```

## 性能考虑

### 闭包性能

```rust
// 零成本抽象：闭包在编译时会被内联
fn main() {
    let expensive_closure = |num: u32| -> u32 {
        println!("calculating slowly...");
        num
    };
    
    // 编译器会优化这个闭包调用
    let result = expensive_closure(5);
}
```

### 函数指针 vs 闭包

```rust
// 函数指针：更小的内存占用
fn square(x: i32) -> i32 { x * x }

// 闭包：可能捕获环境，内存占用更大
let square_closure = |x: i32| x * x;

fn main() {
    // 两者性能基本相同
    println!("{}", square(5));
    println!("{}", square_closure(5));
}
```

## 最佳实践

1. **优先使用闭包而不是函数指针**：闭包更灵活，可以捕获环境
2. **使用类型推断**：让编译器推断闭包类型，除非需要明确指定
3. **合理使用 move 关键字**：在需要转移所有权时使用
4. **函数式编程风格**：使用迭代器和适配器链式调用
5. **性能优化**：闭包在编译时会被优化，通常没有运行时开销

## 相关主题

- [控制流基础](./control_flow_fundamentals.md)
- [错误处理最佳实践](./error_handling.md)
- [异步编程指南](./async_programming.md)
- [迭代器详解](./iterators.md)
