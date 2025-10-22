# Rust 1.89 基础语法全面指南

> **文档类型**：指南/基础  
> **难度等级**：⭐⭐  
> **预计阅读时间**：3-4小时  
> **前置知识**：编程基础、Rust 入门

## 📖 内容概述

本指南系统介绍 Rust 1.89 版本的基础语法，包括变量声明、数据类型、控制流、函数定义、表达式与语句、错误处理等核心概念，适合初学者全面学习。

## 🎯 学习目标

完成本文档学习后，你将能够：

- [ ] 掌握 Rust 1.89 的变量声明和绑定
- [ ] 理解所有基础数据类型及其使用
- [ ] 熟练运用控制流结构
- [ ] 编写和调用函数
- [ ] 理解表达式与语句的区别
- [ ] 进行基本的错误处理

---

## 📚 目录

- [Rust 1.89 基础语法全面指南](#rust-189-基础语法全面指南)
  - [� 内容概述](#-内容概述)
  - [🎯 学习目标](#-学习目标)
  - [📚 目录](#-目录)
  - [概述](#概述)
  - [变量声明与绑定](#变量声明与绑定)
    - [基础变量声明](#基础变量声明)
    - [变量遮蔽（Shadowing）](#变量遮蔽shadowing)
    - [复杂类型变量声明](#复杂类型变量声明)
    - [模式匹配变量绑定](#模式匹配变量绑定)
  - [数据类型与类型推断](#数据类型与类型推断)
    - [基础数据类型](#基础数据类型)
    - [复合数据类型](#复合数据类型)
    - [类型推断](#类型推断)
  - [控制流结构](#控制流结构)
    - [条件语句](#条件语句)
    - [循环语句](#循环语句)
    - [模式匹配](#模式匹配)
  - [函数定义与调用](#函数定义与调用)
    - [基础函数](#基础函数)
    - [高级函数特性](#高级函数特性)
    - [泛型函数](#泛型函数)
  - [表达式与语句](#表达式与语句)
    - [表达式](#表达式)
    - [语句](#语句)
  - [错误处理](#错误处理)
    - [基础错误处理](#基础错误处理)
    - [高级错误处理](#高级错误处理)
  - [Rust 1.89 新特性](#rust-189-新特性)
    - [let\_chains 稳定化](#let_chains-稳定化)
    - [cfg\_boolean\_literals 稳定化](#cfg_boolean_literals-稳定化)
    - [增强的模式匹配](#增强的模式匹配)
    - [增强的类型推断](#增强的类型推断)
    - [新的控制流特性](#新的控制流特性)
    - [改进的错误处理](#改进的错误处理)
  - [最佳实践](#最佳实践)
    - [变量命名](#变量命名)
    - [类型注解](#类型注解)
    - [错误处理1](#错误处理1)
    - [模式匹配1](#模式匹配1)
  - [性能优化](#性能优化)
    - [零拷贝操作](#零拷贝操作)
    - [内存高效的数据结构](#内存高效的数据结构)
    - [编译时计算](#编译时计算)
  - [常见问题](#常见问题)
    - [Q: 什么时候使用 let 和 let mut？](#q-什么时候使用-let-和-let-mut)
    - [Q: 如何选择合适的整数类型？](#q-如何选择合适的整数类型)
    - [Q: 什么时候使用 Option 和 Result？](#q-什么时候使用-option-和-result)
    - [Q: 如何避免所有权问题？](#q-如何避免所有权问题)
    - [Q: 如何编写高效的循环？](#q-如何编写高效的循环)
  - [总结](#总结)

## 概述

Rust 1.89 版本在基础语法方面带来了许多重要的改进和新特性，主要包括：

- **let_chains 稳定化**: 在 if 和 while 条件中使用 && 操作符
- **cfg_boolean_literals 稳定化**: 在条件编译中使用布尔字面量
- **增强的模式匹配**: 更强大的模式匹配功能
- **改进的类型推断**: 更智能的类型推断机制
- **新的控制流特性**: 更灵活的控制流结构
- **改进的错误处理**: 更优雅的错误处理方式

## 变量声明与绑定

### 基础变量声明

Rust 中的变量默认是不可变的，使用 `let` 关键字声明：

```rust
// 不可变变量（默认）
let x = 42;
let name = "Rust";

// 可变变量（使用 mut 关键字）
let mut y = 10;
y += 5;

// 显式类型注解
let z: i32 = 100;
let text: String = "Hello".to_string();
```

### 变量遮蔽（Shadowing）

Rust 允许变量遮蔽，可以在同一作用域中重新声明同名变量：

```rust
let x = 5;
let x = x + 1;  // 遮蔽第一个 x
let x = x * 2;  // 再次遮蔽
println!("x = {}", x); // 输出: x = 12
```

### 复杂类型变量声明

```rust
// 数组类型
let array: [i32; 5] = [1, 2, 3, 4, 5];

// 切片类型
let slice: &[i32] = &array[1..4];

// 元组类型
let tuple: (i32, f64, String) = (42, 3.14, "Rust".to_string());

// 向量类型
let mut vector: Vec<i32> = vec![1, 2, 3];
vector.push(4);

// HashMap 类型
let mut map: HashMap<String, i32> = HashMap::new();
map.insert("apple".to_string(), 5);
```

### 模式匹配变量绑定

```rust
// 元组解构
let tuple = (1, 2.0, "three");
let (a, b, c) = tuple;

// 结构体解构
struct Point { x: i32, y: i32 }
let point = Point { x: 10, y: 20 };
let Point { x, y } = point;

// 数组/切片解构
let array = [1, 2, 3, 4, 5];
let [first, second, .., last] = array;
```

## 数据类型与类型推断

### 基础数据类型

```rust
// 整数类型
let int8: i8 = 127;
let uint8: u8 = 255;
let int32: i32 = 2147483647;
let int64: i64 = 9223372036854775807;
let int128: i128 = 170141183460469231731687303715884105727;

// 浮点数类型
let float32: f32 = 3.14159;
let float64: f64 = 3.141592653589793;

// 布尔类型
let boolean: bool = true;

// 字符类型
let character: char = 'R';
let emoji: char = '🚀';

// 字符串类型
let string_slice: &str = "Hello, Rust!";
let owned_string: String = String::from("Hello, World!");
```

### 复合数据类型

```rust
// 元组类型
let tuple: (i32, f64, char) = (42, 3.14, 'R');

// 数组类型
let array: [i32; 5] = [1, 2, 3, 4, 5];

// 切片类型
let slice: &[i32] = &array[1..4];

// 向量类型
let mut vector: Vec<i32> = vec![1, 2, 3];
vector.push(4);
```

### 类型推断

Rust 具有强大的类型推断能力：

```rust
// 基础类型推断
let x = 42;           // 推断为 i32
let y = 3.14;         // 推断为 f64
let z = true;         // 推断为 bool
let s = "Hello";      // 推断为 &str

// 函数返回类型推断
let result = add_numbers(10, 20);

// 闭包类型推断
let closure = |x: i32| x * 2;
let result = closure(21);

// 泛型类型推断
let demo = BasicSyntaxDemo::new(100);
```

## 控制流结构

### 条件语句

```rust
let number = 42;

// 简单 if 语句
if number > 0 {
    println!("数字 {} 是正数", number);
}

// if-else 语句
if number % 2 == 0 {
    println!("数字 {} 是偶数", number);
} else {
    println!("数字 {} 是奇数", number);
}

// if-else if-else 语句
if number < 0 {
    println!("数字 {} 是负数", number);
} else if number == 0 {
    println!("数字 {} 是零", number);
} else if number < 100 {
    println!("数字 {} 是小于100的正数", number);
} else {
    println!("数字 {} 是大于等于100的正数", number);
}

// 条件表达式（三元运算符的替代）
let message = if number > 50 {
    "大数字"
} else {
    "小数字"
};
```

### 循环语句

```rust
// loop 循环（无限循环）
let mut counter = 0;
loop {
    counter += 1;
    if counter > 3 {
        break;
    }
    println!("loop 循环: counter = {}", counter);
}

// while 循环
let mut number = 10;
while number > 0 {
    println!("while 循环: number = {}", number);
    number -= 2;
}

// for 循环 - 范围
for i in 1..=5 {
    println!("i = {}", i);
}

// for 循环 - 数组/向量
let numbers = vec![10, 20, 30, 40, 50];
for (index, value) in numbers.iter().enumerate() {
    println!("[{}] = {}", index, value);
}

// for 循环 - 字符串
let text = "Rust";
for ch in text.chars() {
    println!("字符: {}", ch);
}

// 循环控制 - break 和 continue
for i in 1..=10 {
    if i % 3 == 0 {
        continue; // 跳过能被3整除的数
    }
    if i > 7 {
        break; // 当 i > 7 时退出循环
    }
    println!("有效数字: {}", i);
}
```

### 模式匹配

```rust
let number = 42;

// 基础模式匹配
match number {
    0 => println!("数字是零"),
    1..=10 => println!("数字在1到10之间"),
    11..=50 => println!("数字在11到50之间"),
    51..=100 => println!("数字在51到100之间"),
    _ => println!("数字大于100"),
}

// 枚举模式匹配
enum Direction {
    North,
    South,
    East,
    West,
}

let direction = Direction::North;
match direction {
    Direction::North => println!("向北"),
    Direction::South => println!("向南"),
    Direction::East => println!("向东"),
    Direction::West => println!("向西"),
}

// 带数据的枚举模式匹配
enum Message {
    Quit,
    Move { x: i32, y: i32 },
    Write(String),
    ChangeColor(i32, i32, i32),
}

let msg = Message::Move { x: 10, y: 20 };
match msg {
    Message::Quit => println!("收到退出消息"),
    Message::Move { x, y } => println!("移动到位置: ({}, {})", x, y),
    Message::Write(text) => println!("写入文本: {}", text),
    Message::ChangeColor(r, g, b) => println!("改变颜色为: RGB({}, {}, {})", r, g, b),
}

// 守卫条件（guard）
let pair = (2, 4);
match pair {
    (x, y) if x == y => println!("两个数相等"),
    (x, y) if x > y => println!("第一个数大于第二个数"),
    (x, y) if x < y => println!("第一个数小于第二个数"),
    _ => println!("其他情况"),
}

// 绑定变量
let value = Some(42);
match value {
    Some(x) if x > 40 => println!("值 {} 大于40", x),
    Some(x) => println!("值 {} 小于等于40", x),
    None => println!("没有值"),
}
```

## 函数定义与调用

### 基础函数

```rust
// 无参数无返回值函数
fn greet() {
    println!("Hello, Rust!");
}

// 有参数无返回值函数
fn greet_person(name: &str) {
    println!("Hello, {}!", name);
}

// 有参数有返回值函数
fn add(a: i32, b: i32) -> i32 {
    a + b
}

// 多个参数函数
fn calculate(a: i32, b: i32, c: i32) -> i32 {
    a * b + c
}

// 返回元组的函数
fn find_min_max(slice: &[i32]) -> (i32, i32) {
    let mut min = slice[0];
    let mut max = slice[0];
    
    for &value in slice {
        if value < min {
            min = value;
        }
        if value > max {
            max = value;
        }
    }
    
    (min, max)
}
```

### 高级函数特性

```rust
// 闭包
let add_one = |x: i32| x + 1;
println!("闭包 add_one(5) = {}", add_one(5));

// 高阶函数
let numbers = vec![1, 2, 3, 4, 5];
let doubled: Vec<i32> = numbers.iter().map(|x| x * 2).collect();

// 函数作为参数
fn apply_operation<F>(a: i32, b: i32, operation: F) -> i32
where
    F: Fn(i32, i32) -> i32,
{
    operation(a, b)
}

let result = apply_operation(10, 20, |a, b| a + b);

// 返回闭包的函数
fn create_multiplier(factor: i32) -> impl Fn(i32) -> i32 {
    move |x| x * factor
}

let multiplier = create_multiplier(3);
println!("乘数器(3) * 5 = {}", multiplier(5));

// 递归函数
fn factorial(n: u32) -> u32 {
    if n <= 1 {
        1
    } else {
        n * factorial(n - 1)
    }
}
```

### 泛型函数

```rust
// 基础泛型函数
fn identity<T>(x: T) -> T {
    x
}

let int_result = identity(42);
let string_result = identity("Hello");

// 泛型函数与约束
fn max_value<T>(a: T, b: T) -> T
where
    T: PartialOrd,
{
    if a > b { a } else { b }
}

let max_int = max_value(10, 20);
let max_float = max_value(3.14, 2.71);
```

## 表达式与语句

### 表达式

在 Rust 中，几乎所有的代码都是表达式：

```rust
// 基础表达式
let x = 5;        // 表达式
let y = x + 2;    // 表达式
let z = {         // 块表达式
    let temp = x + 2;
    temp * 2
};

// 条件表达式
let result = if x > 0 { "正数" } else { "非正数" };

// 循环表达式
let sum = {
    let mut total = 0;
    for i in 1..=10 {
        total += i;
    }
    total  // 返回 total 的值
};
```

### 语句

语句是执行某种操作的代码片段，但不返回值：

```rust
// 变量声明语句
let x = 5;

// 函数调用语句
println!("x is {}", x);

// 循环语句
for i in 0..10 {
    println!("i is {}", i);
}

// 条件语句
if x > 0 {
    println!("x is positive");
} else {
    println!("x is negative");
}
```

## 错误处理

### 基础错误处理

```rust
// Option 类型
let some_value = Some(42);
let none_value: Option<i32> = None;

match some_value {
    Some(value) => println!("有值: {}", value),
    None => println!("没有值"),
}

// Result 类型
let success_result: Result<i32, &str> = Ok(42);
let error_result: Result<i32, &str> = Err("出错了");

match success_result {
    Ok(value) => println!("成功: {}", value),
    Err(error) => println!("错误: {}", error),
}

// 字符串解析错误处理
let valid_number = "42".parse::<i32>();
let invalid_number = "abc".parse::<i32>();

match valid_number {
    Ok(value) => println!("解析成功: {}", value),
    Err(error) => println!("解析失败: {}", error),
}
```

### 高级错误处理

```rust
// 使用 ? 操作符
fn parse_and_double(s: &str) -> Result<i32, ParseIntError> {
    let number = s.parse::<i32>()?;
    Ok(number * 2)
}

// 自定义错误类型
#[derive(Debug)]
enum CustomError {
    ParseError(ParseIntError),
    DivisionByZero,
    NegativeNumber,
}

impl std::fmt::Display for CustomError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CustomError::ParseError(e) => write!(f, "解析错误: {}", e),
            CustomError::DivisionByZero => write!(f, "除零错误"),
            CustomError::NegativeNumber => write!(f, "负数错误"),
        }
    }
}

impl std::error::Error for CustomError {}

// 使用自定义错误
fn safe_divide(a: i32, b: i32) -> Result<i32, CustomError> {
    if b == 0 {
        return Err(CustomError::DivisionByZero);
    }
    if a < 0 {
        return Err(CustomError::NegativeNumber);
    }
    Ok(a / b)
}
```

## Rust 1.89 新特性

### let_chains 稳定化

let_chains 允许在 if 和 while 条件中使用 && 操作符：

```rust
// 基础 let_chains 语法
let x = Some(42);
let y = Some("hello");
let z = Some(3.14);

// 使用 let_chains 进行多重条件检查
if let Some(value) = x && let Some(text) = y && let Some(pi) = z {
    println!("所有值都存在: x = {}, y = {}, z = {}", value, text, pi);
}

// 复杂条件组合
let numbers = vec![1, 2, 3, 4, 5];
let threshold = 3;

if let Some(first) = numbers.first() && 
   let Some(last) = numbers.last() && 
   *first < threshold && 
   *last > threshold {
    println!("数组满足条件: 首元素 {} < {}, 末元素 {} > {}", 
            first, threshold, last, threshold);
}

// 嵌套 Option 处理
let nested_option = Some(Some(42));
if let Some(inner) = nested_option && let Some(value) = inner {
    println!("嵌套 Option 值: {}", value);
}

// while 循环中的 let_chains
let mut stack = vec![Some(1), Some(2), Some(3), None, Some(4)];

while let Some(Some(value)) = stack.pop() && value > 0 {
    println!("处理值: {}", value);
}
```

### cfg_boolean_literals 稳定化

允许在条件编译中使用布尔字面量：

```rust
// 基础布尔字面量使用
#[cfg(feature = "debug")]
println!("调试模式已启用");

#[cfg(not(feature = "debug"))]
println!("调试模式未启用");

// 复杂条件组合
#[cfg(all(feature = "async", feature = "performance"))]
println!("异步性能模式已启用");

#[cfg(any(feature = "dev", feature = "test"))]
println!("开发或测试模式已启用");

// 平台特定编译
#[cfg(target_os = "windows")]
println!("Windows 平台");

#[cfg(target_os = "linux")]
println!("Linux 平台");

// 自定义条件
#[cfg(my_custom_flag)]
println!("自定义标志已设置");

// 版本检查
#[cfg(version("1.89"))]
println!("Rust 1.89 特性可用");
```

### 增强的模式匹配

```rust
// 改进的切片模式
let numbers = vec![1, 2, 3, 4, 5];

match numbers.as_slice() {
    [] => println!("空数组"),
    [single] => println!("单个元素: {}", single),
    [first, second] => println!("两个元素: {}, {}", first, second),
    [first, .., last] => println!("多个元素: 首 = {}, 末 = {}", first, last),
    [first, middle @ .., last] => println!("中间元素数量: {}", middle.len()),
}

// 改进的守卫条件
let value = Some(42);
match value {
    Some(x) if x > 40 && x < 50 => println!("值在范围内: {}", x),
    Some(x) if x % 2 == 0 => println!("偶数值: {}", x),
    Some(x) => println!("其他值: {}", x),
    None => println!("没有值"),
}

// 复杂嵌套模式
let complex_data = Some(Some(Some(42)));
match complex_data {
    Some(Some(Some(value))) if value > 40 => println!("深层嵌套值: {}", value),
    Some(Some(None)) => println!("中间层为 None"),
    Some(None) => println!("内层为 None"),
    None => println!("外层为 None"),
    _ => println!("其他情况"),
}
```

### 增强的类型推断

```rust
// 改进的闭包类型推断
let closure = |x| x * 2;
let result = closure(21);

// 复杂泛型推断
let data = create_generic_data(42);

// 迭代器链式推断
let numbers = vec![1, 2, 3, 4, 5];
let processed: Vec<i32> = numbers
    .iter()
    .filter(|&&x| x % 2 == 0)
    .map(|&x| x * 2)
    .collect();

// 异步类型推断
let async_result = async_operation(10);
```

### 新的控制流特性

```rust
// 改进的 for 循环
let numbers = vec![1, 2, 3, 4, 5];

// 使用 enumerate 获取索引
for (index, value) in numbers.iter().enumerate() {
    println!("索引 {}: 值 {}", index, value);
}

// 复杂迭代器链
let result: Vec<i32> = numbers
    .iter()
    .filter(|&&x| x % 2 == 0)
    .map(|&x| x * x)
    .take(3)
    .collect();

// 嵌套控制流
let matrix = vec![
    vec![1, 2, 3],
    vec![4, 5, 6],
    vec![7, 8, 9],
];

'outer: for (row_idx, row) in matrix.iter().enumerate() {
    for (col_idx, &value) in row.iter().enumerate() {
        if value == 5 {
            println!("找到5在位置: ({}, {})", row_idx, col_idx);
            break 'outer;
        }
    }
}
```

### 改进的错误处理

```rust
// 改进的 Result 处理
let results = vec![
    Ok(42),
    Err("错误1"),
    Ok(100),
    Err("错误2"),
];

for result in results {
    match result {
        Ok(value) => println!("成功: {}", value),
        Err(error) => println!("错误: {}", error),
    }
}

// 自定义错误类型
#[derive(Debug)]
enum CustomResult {
    Success(i32),
    Warning(String),
    Error(String),
}

let results = vec![
    CustomResult::Success(42),
    CustomResult::Warning("警告信息".to_string()),
    CustomResult::Error("错误信息".to_string()),
];

for result in results {
    match result {
        CustomResult::Success(value) => println!("成功: {}", value),
        CustomResult::Warning(msg) => println!("警告: {}", msg),
        CustomResult::Error(msg) => println!("错误: {}", msg),
    }
}
```

## 最佳实践

### 变量命名

```rust
// 使用有意义的变量名
let user_count = 42;
let max_retry_attempts = 3;
let is_authenticated = true;

// 使用 snake_case 命名风格
let first_name = "Alice";
let last_name = "Smith";
let full_name = format!("{} {}", first_name, last_name);
```

### 类型注解

```rust
// 在类型不明确时使用显式类型注解
let numbers: Vec<i32> = vec![1, 2, 3, 4, 5];
let config: HashMap<String, String> = HashMap::new();

// 在函数签名中使用明确的类型
fn process_data(data: &[i32]) -> Result<Vec<i32>, String> {
    // 函数实现
}
```

### 错误处理1

```rust
// 使用 Result 类型进行错误处理
fn read_file(path: &str) -> Result<String, std::io::Error> {
    std::fs::read_to_string(path)
}

// 使用 ? 操作符简化错误处理
fn process_file(path: &str) -> Result<String, Box<dyn std::error::Error>> {
    let content = read_file(path)?;
    Ok(content.to_uppercase())
}

// 使用 match 进行详细的错误处理
match process_file("config.txt") {
    Ok(content) => println!("文件内容: {}", content),
    Err(error) => eprintln!("处理文件失败: {}", error),
}
```

### 模式匹配1

```rust
// 使用模式匹配处理 Option 和 Result
let result = "42".parse::<i32>();
match result {
    Ok(value) => println!("解析成功: {}", value),
    Err(error) => println!("解析失败: {}", error),
}

// 使用 if let 简化模式匹配
if let Ok(value) = "42".parse::<i32>() {
    println!("解析成功: {}", value);
}

// 使用 while let 处理迭代
let mut stack = vec![1, 2, 3, 4, 5];
while let Some(value) = stack.pop() {
    println!("弹出值: {}", value);
}
```

## 性能优化

### 零拷贝操作

```rust
// 使用切片避免数据复制
fn process_slice(data: &[i32]) -> i32 {
    data.iter().sum()
}

// 使用引用避免所有权转移
fn process_reference(data: &Vec<i32>) -> i32 {
    data.iter().sum()
}
```

### 内存高效的数据结构

```rust
// 使用 Vec 的 with_capacity 预分配内存
let mut numbers = Vec::with_capacity(1000);
for i in 0..1000 {
    numbers.push(i);
}

// 使用 HashMap 的 with_capacity
let mut map = HashMap::with_capacity(100);
for i in 0..100 {
    map.insert(i, i * 2);
}
```

### 编译时计算

```rust
// 使用 const fn 进行编译时计算
const fn calculate_square(x: i32) -> i32 {
    x * x
}

const SQUARE_OF_FIVE: i32 = calculate_square(5);

// 使用 const 进行编译时常量
const MAX_BUFFER_SIZE: usize = 1024;
const PI: f64 = 3.141592653589793;
```

## 常见问题

### Q: 什么时候使用 let 和 let mut？

A: 默认使用 `let` 声明不可变变量，只有在需要修改变量值时才使用 `let mut`。这有助于提高代码的安全性和可读性。

```rust
// 不可变变量（推荐）
let x = 42;
let name = "Rust";

// 可变变量（仅在需要时使用）
let mut counter = 0;
counter += 1;
```

### Q: 如何选择合适的整数类型？

A: 根据数据范围和内存使用情况选择：

- `i32` 和 `u32`: 默认选择，平衡性能和内存使用
- `i64` 和 `u64`: 需要更大范围时使用
- `i8` 和 `u8`: 节省内存，用于小范围数据
- `isize` 和 `usize`: 用于索引和大小，与平台相关

### Q: 什么时候使用 Option 和 Result？

A:

- 使用 `Option<T>` 当值可能不存在时
- 使用 `Result<T, E>` 当操作可能失败时

```rust
// Option 用于可选值
fn find_user(id: u32) -> Option<String> {
    if id > 0 {
        Some(format!("User {}", id))
    } else {
        None
    }
}

// Result 用于可能失败的操作
fn parse_number(s: &str) -> Result<i32, ParseIntError> {
    s.parse::<i32>()
}
```

### Q: 如何避免所有权问题？

A: 使用引用和借用：

```rust
// 使用引用避免所有权转移
fn process_data(data: &[i32]) -> i32 {
    data.iter().sum()
}

// 使用 clone 创建副本
let original = vec![1, 2, 3];
let copy = original.clone();

// 使用 move 语义转移所有权
let moved = original; // original 不再可用
```

### Q: 如何编写高效的循环？

A: 使用迭代器和方法链：

```rust
// 高效的迭代器链
let numbers = vec![1, 2, 3, 4, 5];
let result: Vec<i32> = numbers
    .iter()
    .filter(|&&x| x % 2 == 0)
    .map(|&x| x * 2)
    .collect();

// 避免不必要的索引访问
// 不好的做法
for i in 0..numbers.len() {
    println!("{}", numbers[i]);
}

// 好的做法
for number in &numbers {
    println!("{}", number);
}
```

## 总结

Rust 1.89 的基础语法提供了强大而安全的编程体验。通过合理使用变量声明、类型系统、控制流、函数、模式匹配和错误处理，可以编写出高效、安全和可维护的代码。

新特性如 let_chains 和 cfg_boolean_literals 进一步增强了语言的表达能力，使得代码更加简洁和易读。遵循最佳实践和性能优化建议，可以充分发挥 Rust 的优势。

---

*本指南基于 Rust 1.89 版本编写，涵盖了基础语法的所有重要方面。建议结合实际项目练习，深入理解这些概念和特性。*
