# 🔄 Rust 控制流与函数速查卡

> **快速参考** | [完整文档](../../crates/c03_control_fn/docs/) | [代码示例](../../crates/c03_control_fn/examples/)
> **最后更新**: 2025-11-15 | **Rust 版本**: 1.91.1+ | **Edition**: 2024

---

## 📋 目录

- [🔄 Rust 控制流与函数速查卡](#-rust-控制流与函数速查卡)
  - [📋 目录](#-目录)
  - [🎯 条件语句](#-条件语句)
    - [if 表达式](#if-表达式)
    - [match 表达式](#match-表达式)
    - [if let 表达式](#if-let-表达式)
    - [let-else 语句 (Rust 1.65+)](#let-else-语句-rust-165)
  - [🔁 循环结构](#-循环结构)
    - [loop 循环](#loop-循环)
    - [while 循环](#while-循环)
    - [for 循环](#for-循环)
    - [循环控制](#循环控制)
  - [🎭 模式匹配](#-模式匹配)
    - [基本模式](#基本模式)
    - [解构模式](#解构模式)
    - [引用模式](#引用模式)
  - [📝 函数定义](#-函数定义)
    - [基本函数](#基本函数)
    - [函数参数](#函数参数)
    - [函数返回值](#函数返回值)
    - [函数指针](#函数指针)
  - [🔒 闭包](#-闭包)
    - [基本闭包](#基本闭包)
    - [闭包捕获](#闭包捕获)
    - [闭包类型](#闭包类型)
    - [闭包作为参数](#闭包作为参数)
    - [闭包作为返回值](#闭包作为返回值)
  - [🎯 常用模式](#-常用模式)
    - [早期返回](#早期返回)
    - [链式调用](#链式调用)
    - [模式匹配与解构](#模式匹配与解构)
    - [函数式编程](#函数式编程)
    - [递归函数](#递归函数)
  - [📚 相关资源](#-相关资源)

---

## 🎯 条件语句

### if 表达式

```rust
// 基本 if
if condition {
    // 代码块
}

// if-else
if condition {
    // true 分支
} else {
    // false 分支
}

// if-else if-else
if condition1 {
    // 分支1
} else if condition2 {
    // 分支2
} else {
    // 默认分支
}

// if 作为表达式（必须返回相同类型）
let result = if condition {
    "true"
} else {
    "false"
};
```

### match 表达式

```rust
// 基本 match
match value {
    pattern1 => expression1,
    pattern2 => expression2,
    _ => default_expression,
}

// 匹配多个值
match number {
    1 | 2 | 3 => println!("小数字"),
    4..=10 => println!("中等数字"),
    _ => println!("大数字"),
}

// 带守卫的 match
match value {
    x if x > 0 => println!("正数"),
    x if x < 0 => println!("负数"),
    _ => println!("零"),
}

// 绑定变量
match value {
    Some(x) => println!("值: {}", x),
    None => println!("无值"),
}
```

### if let 表达式

```rust
// 基本 if let
if let Some(value) = option {
    println!("有值: {}", value);
}

// if let-else
if let Some(value) = option {
    println!("有值: {}", value);
} else {
    println!("无值");
}

// 链式 if let (Rust 1.92.0+)
if let Some(a) = option1 && let Some(b) = option2 {
    println!("都有值: {} {}", a, b);
}
```

### let-else 语句 (Rust 1.65+)

```rust
// 基本 let-else
let Some(value) = option else {
    return; // 或 panic! 或其他控制流
};

// 使用示例
fn process(value: Option<i32>) -> i32 {
    let Some(x) = value else {
        return 0;
    };
    x * 2
}
```

---

## 🔁 循环结构

### loop 循环

```rust
// 无限循环
loop {
    // 代码
    if condition {
        break; // 退出循环
    }
}

// 返回值
let result = loop {
    counter += 1;
    if counter > 10 {
        break counter * 2; // 返回值
    }
};
```

### while 循环

```rust
// 基本 while
while condition {
    // 代码
}

// while let
while let Some(item) = iterator.next() {
    println!("{}", item);
}
```

### for 循环

```rust
// 遍历范围
for i in 1..=10 {
    println!("{}", i);
}

// 遍历集合
for item in vec {
    println!("{}", item);
}

// 遍历引用
for item in &vec {
    println!("{}", item);
}

// 遍历可变引用
for item in &mut vec {
    *item += 1;
}

// 带索引遍历
for (index, value) in vec.iter().enumerate() {
    println!("{}: {}", index, value);
}
```

### 循环控制

```rust
// break 和 continue
for i in 1..=10 {
    if i == 5 {
        continue; // 跳过本次循环
    }
    if i == 8 {
        break; // 退出循环
    }
    println!("{}", i);
}

// 循环标签
'outer: loop {
    'inner: loop {
        break 'outer; // 退出外层循环
    }
}
```

---

## 🎭 模式匹配

### 基本模式

```rust
// 字面量模式
match x {
    1 => println!("一"),
    2 => println!("二"),
    _ => println!("其他"),
}

// 变量模式
match x {
    y => println!("值: {}", y),
}

// 通配符模式
match x {
    _ => println!("忽略"),
}

// 范围模式
match x {
    1..=5 => println!("1到5"),
    6..=10 => println!("6到10"),
    _ => println!("其他"),
}
```

### 解构模式

```rust
// 元组解构
let tuple = (1, 2, 3);
match tuple {
    (x, y, z) => println!("{}, {}, {}", x, y, z),
}

// 结构体解构
struct Point { x: i32, y: i32 }
let point = Point { x: 0, y: 0 };
match point {
    Point { x, y } => println!("({}, {})", x, y),
    Point { x: 0, y } => println!("x=0, y={}", y),
}

// 枚举解构
enum Message {
    Quit,
    Move { x: i32, y: i32 },
    Write(String),
}
match msg {
    Message::Quit => println!("退出"),
    Message::Move { x, y } => println!("移动到 ({}, {})", x, y),
    Message::Write(s) => println!("写入: {}", s),
}
```

### 引用模式

```rust
// 引用模式
let value = Some(5);
match &value {
    Some(x) => println!("值: {}", x),
    None => println!("无值"),
}

// ref 和 ref mut
match value {
    ref r => println!("引用: {:p}", r),
}

match mut_value {
    ref mut m => *m = 10,
}
```

---

## 📝 函数定义

### 基本函数

```rust
// 无参数无返回值
fn greet() {
    println!("Hello!");
}

// 有参数
fn add(a: i32, b: i32) {
    println!("{}", a + b);
}

// 有返回值
fn add(a: i32, b: i32) -> i32 {
    a + b  // 最后一行表达式作为返回值
}

// 显式 return
fn add(a: i32, b: i32) -> i32 {
    return a + b;
}
```

### 函数参数

```rust
// 值传递
fn take_ownership(s: String) {
    println!("{}", s);
}

// 引用传递
fn borrow(s: &String) {
    println!("{}", s);
}

// 可变引用
fn modify(s: &mut String) {
    s.push_str(" world");
}

// 多个参数
fn process(x: i32, y: i32, z: i32) -> i32 {
    x + y + z
}
```

### 函数返回值

```rust
// 返回单个值
fn get_value() -> i32 {
    42
}

// 返回元组
fn get_pair() -> (i32, String) {
    (42, "hello".to_string())
}

// 返回 Option
fn find_item() -> Option<i32> {
    Some(42)
}

// 返回 Result
fn parse_number(s: &str) -> Result<i32, std::num::ParseIntError> {
    s.parse()
}
```

### 函数指针

```rust
// 函数指针类型
fn add(a: i32, b: i32) -> i32 {
    a + b
}

let func: fn(i32, i32) -> i32 = add;
let result = func(1, 2);

// 作为参数
fn apply(f: fn(i32, i32) -> i32, x: i32, y: i32) -> i32 {
    f(x, y)
}
```

---

## 🔒 闭包

### 基本闭包

```rust
// 基本语法
let add = |x, y| x + y;
let result = add(1, 2);

// 带类型注解
let add = |x: i32, y: i32| -> i32 {
    x + y
};

// 多行闭包
let multiply = |x, y| {
    let result = x * y;
    result
};
```

### 闭包捕获

```rust
// 不可变借用
let x = 5;
let borrow = || println!("{}", x);

// 可变借用
let mut x = 5;
let mut_borrow = || {
    x += 1;
    println!("{}", x);
};

// 移动捕获
let x = vec![1, 2, 3];
let move_closure = move || {
    println!("{:?}", x);
};
// x 不再可用
```

### 闭包类型

```rust
// Fn - 不可变借用
fn call_fn<F: Fn()>(f: F) {
    f();
}

// FnMut - 可变借用
fn call_fn_mut<F: FnMut()>(mut f: F) {
    f();
}

// FnOnce - 获取所有权
fn call_fn_once<F: FnOnce()>(f: F) {
    f();
}
```

### 闭包作为参数

```rust
// 接受闭包
fn apply<F>(f: F) -> i32
where
    F: Fn(i32) -> i32,
{
    f(5)
}

// 使用示例
let double = |x| x * 2;
let result = apply(double);

// 内联闭包
let result = apply(|x| x * 3);
```

### 闭包作为返回值

```rust
// 返回闭包
fn make_adder(x: i32) -> impl Fn(i32) -> i32 {
    move |y| x + y
}

// 使用
let add5 = make_adder(5);
let result = add5(3); // 8
```

---

## 🎯 常用模式

### 早期返回

```rust
fn process(value: Option<i32>) -> i32 {
    let Some(x) = value else {
        return 0;
    };
    x * 2
}
```

### 链式调用

```rust
// Option 链式调用
let result = Some(5)
    .map(|x| x * 2)
    .filter(|&x| x > 5)
    .unwrap_or(0);

// Result 链式调用
let result = "42"
    .parse::<i32>()
    .map(|x| x * 2)
    .map_err(|e| format!("错误: {}", e));
```

### 模式匹配与解构

```rust
// if let 解构
if let Some(x) = option {
    println!("{}", x);
}

// while let 解构
while let Some(item) = stack.pop() {
    process(item);
}

// match 解构
match result {
    Ok(value) => println!("成功: {}", value),
    Err(e) => println!("错误: {}", e),
}
```

### 函数式编程

```rust
// map
let doubled: Vec<i32> = vec![1, 2, 3]
    .iter()
    .map(|x| x * 2)
    .collect();

// filter
let evens: Vec<i32> = vec![1, 2, 3, 4, 5]
    .iter()
    .filter(|&&x| x % 2 == 0)
    .copied()
    .collect();

// fold
let sum: i32 = vec![1, 2, 3, 4, 5]
    .iter()
    .fold(0, |acc, x| acc + x);
```

### 递归函数

```rust
// 基本递归
fn factorial(n: u64) -> u64 {
    if n <= 1 {
        1
    } else {
        n * factorial(n - 1)
    }
}

// 尾递归（Rust 不保证尾递归优化）
fn factorial_tail(n: u64, acc: u64) -> u64 {
    if n <= 1 {
        acc
    } else {
        factorial_tail(n - 1, n * acc)
    }
}
```

---

## 📚 相关资源

- [Rust 控制流文档](https://doc.rust-lang.org/book/ch03-05-control-flow.html)
- [Rust 函数文档](https://doc.rust-lang.org/book/ch03-03-how-functions-work.html)
- [Rust 闭包文档](https://doc.rust-lang.org/book/ch13-01-closures.html)
- [完整控制流文档](../../crates/c03_control_fn/docs/)

---

**最后更新**: 2025-11-15
**维护者**: 文档团队
**状态**: 持续更新中 📝

🎯 **掌握控制流，编写清晰代码！**
