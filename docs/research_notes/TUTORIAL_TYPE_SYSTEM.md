# 教程：类型系统

> **创建日期**: 2026-02-24
> **最后更新**: 2026-02-28
> **目标受众**: 初学者-进阶
> **预计阅读时间**: 40分钟
> **级别**: L1/L2

---

## 引言

Rust的类型系统是其保证内存安全、线程安全和零成本抽象的基础。本教程将深入讲解Rust类型系统的核心概念和高级特性。

---

## 第一部分：类型基础

### 标量类型

```rust
// 整数
let i: i32 = 42;        // 有符号32位
let u: u64 = 100;       // 无符号64位
let hex = 0xff;         // 十六进制
let bin = 0b1010;       // 二进制
let oct = 0o77;         // 八进制

// 浮点数
let f: f64 = 3.14;      // 64位浮点
let g: f32 = 2.5;       // 32位浮点

// 布尔
let b: bool = true;

// 字符
let c: char = '中';     // Unicode标量值
```

### 复合类型

```rust
// 元组
let tup: (i32, f64, &str) = (500, 6.4, "hi");
let (x, y, z) = tup;           // 解构
let first = tup.0;              // 索引访问

// 数组
let arr: [i32; 5] = [1, 2, 3, 4, 5];
let first = arr[0];
let zeros = [0; 5];             // [0, 0, 0, 0, 0]

// 切片
let slice = &arr[1..3];         // [2, 3]
```

---

## 第二部分：自定义类型

### 结构体

```rust
// 命名字段结构体
struct User {
    username: String,
    email: String,
    sign_in_count: u64,
    active: bool,
}

let user = User {
    email: String::from("a@b.com"),
    username: String::from("alice"),
    active: true,
    sign_in_count: 1,
};

// 元组结构体
struct Point(i32, i32, i32);
let origin = Point(0, 0, 0);

// 单元结构体
struct AlwaysEqual;
let subject = AlwaysEqual;
```

### 枚举

```rust
// 基本枚举
enum Message {
    Quit,                           // 无数据
    Move { x: i32, y: i32 },        // 匿名结构体
    Write(String),                  // 单个值
    ChangeColor(i32, i32, i32),     // 元组
}

// Option枚举 (标准库)
enum Option<T> {
    Some(T),
    None,
}

// Result枚举 (标准库)
enum Result<T, E> {
    Ok(T),
    Err(E),
}
```

### 变体与数据

```rust
let msg1 = Message::Quit;
let msg2 = Message::Move { x: 10, y: 20 };
let msg3 = Message::Write(String::from("hello"));

// 使用match处理
match msg {
    Message::Quit => println!("Quit"),
    Message::Move { x, y } => println!("Move to ({}, {})", x, y),
    Message::Write(text) => println!("Text: {}", text),
    Message::ChangeColor(r, g, b) => println!("RGB({}, {}, {})", r, g, b),
}
```

---

## 第三部分：模式匹配

### match表达式

```rust
enum Coin {
    Penny,
    Nickel,
    Dime,
    Quarter(String),  // 关联数据
}

fn value_in_cents(coin: Coin) -> u8 {
    match coin {
        Coin::Penny => {
            println!("Lucky penny!");
            1
        }
        Coin::Nickel => 5,
        Coin::Dime => 10,
        Coin::Quarter(state) => {
            println!("State quarter from {:?}!", state);
            25
        }
    }
}
```

### if let简化

```rust
// 完整match
match some_option {
    Some(value) => println!("{}", value),
    _ => (),
}

// 简化版
if let Some(value) = some_option {
    println!("{}", value);
}
```

### 匹配守卫

```rust
let num = Some(4);

match num {
    Some(x) if x < 5 => println!("less than five: {}", x),
    Some(x) => println!("{}", x),
    None => (),
}
```

### @绑定

```rust
enum Message {
    Hello { id: i32 },
}

let msg = Message::Hello { id: 5 };

match msg {
    Message::Hello {
        id: id_variable @ 3..=7,  // 绑定并匹配范围
    } => println!("Found an id in range: {}", id_variable),
    Message::Hello { id: 10..=12 } => println!("Found an id in another range"),
    Message::Hello { id } => println!("Found some other id: {}", id),
}
```

---

## 第四部分：泛型

### 泛型函数

```rust
// 交换两个值
fn swap<T>(a: T, b: T) -> (T, T) {
    (b, a)
}

let (x, y) = swap(1, 2);        // T = i32
let (a, b) = swap("hi", "bye"); // T = &str

// 多个类型参数
fn pair<T, U>(first: T, second: U) -> (T, U) {
    (first, second)
}
```

### 泛型结构体

```rust
struct Point<T> {
    x: T,
    y: T,
}

let integer = Point { x: 5, y: 10 };
let float = Point { x: 1.0, y: 4.0 };

// 多类型参数
struct Point2<T, U> {
    x: T,
    y: U,
}

let mixed = Point2 { x: 5, y: 4.0 };
```

### 泛型枚举

```rust
// Option<T>定义
enum Option<T> {
    Some(T),
    None,
}

// 使用
let some_number = Some(5);        // Option<i32>
let some_string = Some("a");      // Option<&str>
let absent_number: Option<i32> = None;
```

---

## 第五部分：Trait

### 定义与实现

```rust
// 定义trait
pub trait Summary {
    fn summarize(&self) -> String;

    // 默认实现
    fn summarize_author(&self) -> String {
        String::from("(read more...)")
    }
}

// 为类型实现trait
pub struct NewsArticle {
    pub headline: String,
    pub location: String,
    pub author: String,
    pub content: String,
}

impl Summary for NewsArticle {
    fn summarize(&self) -> String {
        format!("{}, by {} ({})", self.headline, self.author, self.location)
    }
}
```

### Trait作为参数

```rust
// 接受实现Summary的参数
pub fn notify(item: &impl Summary) {
    println!("Breaking news! {}", item.summarize());
}

// Trait Bound语法 (等效)
pub fn notify<T: Summary>(item: &T) {
    println!("Breaking news! {}", item.summarize());
}

// 多个trait bound
pub fn notify(item: &(impl Summary + Display)) { }
pub fn notify<T: Summary + Display>(item: &T) { }
```

### where子句

```rust
// 复杂约束用where更清晰
fn some_function<T, U>(t: &T, u: &U) -> i32
where
    T: Display + Clone,
    U: Clone + Debug,
{ }
```

### 关联类型

```rust
pub trait Iterator {
    type Item;  // 关联类型

    fn next(&mut self) -> Option<Self::Item>;
}

// 实现
impl Iterator for Counter {
    type Item = u32;

    fn next(&mut self) -> Option<Self::Item> {
        // ...
    }
}
```

---

## 第六部分：类型推导与标注

### 自动推导

```rust
let guess: u32 = "42".parse().expect("Not a number!");
// 必须标注，因为parse可能返回多种类型

// 编译器能推导的情况
let v = vec![1, 2, 3];  // Vec<i32>
let s = "hello";        // &str
```

### 类型别名

```rust
type Kilometers = i32;

let x: i32 = 5;
let y: Kilometers = 5;

assert_eq!(x, y);  // 类型别名只是别名，不是新类型

// 复杂类型简化
type Thunk = Box<dyn Fn() + Send + 'static>;

fn takes_long_type(f: Thunk) { }
```

### Never类型

```rust
fn bar() -> ! {  // !表示never type
    panic!();
}

// 用于控制流
let guess: u32 = match guess.trim().parse() {
    Ok(num) => num,
    Err(_) => continue,  // continue的类型是!
};
```

---

## 第七部分：高级类型特性

### 动态大小类型 (DST)

```rust
// Sized trait自动为固定大小类型实现
fn generic<T: Sized>(t: T) { }

// ?Sized允许动态大小类型
fn generic<T: ?Sized>(t: &T) { }  // T可以是str或[DST]

// 常见DST: str, [T], dyn Trait
let s: &str = "hello";           // 大小在运行时确定
let slice: &[i32] = &[1, 2, 3];  // 大小在运行时确定
```

### 函数指针

```rust
fn add_one(x: i32) -> i32 {
    x + 1
}

// 函数指针类型
let f: fn(i32) -> i32 = add_one;
let f = add_one;  // 类型推导

// 与闭包不同
fn do_twice(f: fn(i32) -> i32, arg: i32) -> i32 {
    f(arg) + f(arg)
}
```

### 类型转换

```rust
// 显式转换 (as)
let a: i32 = 10;
let b: i64 = a as i64;

// From/Into trait
let s = String::from("hello");  // From<&str>
let s: String = "hello".into(); // Into<String>

// TryFrom/TryInto (可能失败)
let a: i32 = 300;
let b: Result<i8, _> = a.try_into();  // Err, 溢出
```

---

## 第八部分：形式化视角

### 类型安全定理

**进展性 (Progress)**: 良类型的表达式要么是值，要么可以进一步求值。

**保持性 (Preservation)**: 如果表达式`e`有类型`T`，且`e`求值为`e'`，则`e'`也有类型`T`。

**类型安全**: 进展性 + 保持性

### 与形式化文档关联

| 概念 | 形式化定义 | 文档位置 |
| :--- | :--- | :--- |
| 类型推导 | `Γ ⊢ e : τ` | type_system_foundations.md |
| Trait | `impl Trait for Type` | trait_system_formalization.md |
| 泛型 | `∀T. F<T>` | variance_theory.md |
| 模式匹配 | 穷尽性检查 | type_system_foundations.md |

---

## 总结

```
Rust类型系统
    │
    ├── 基础类型
    │   ├── 标量: i32, f64, bool, char
    │   └── 复合: tuple, array, slice
    │
    ├── 自定义类型
    │   ├── struct: 命名字段, 元组, 单元
    │   └── enum: 变体, 关联数据
    │
    ├── 泛型
    │   ├── 类型参数 <T>
    │   ├── 约束: T: Trait
    │   └── 实现代码复用
    │
    ├── Trait
    │   ├── 接口定义
    │   ├── 默认实现
    │   └── 泛型编程基础
    │
    └── 类型安全
        ├── 编译期检查
        ├── 零运行时开销
        └── 形式化保证
```

## 引言

Rust的类型系统不仅帮你捕获错误，它还保证程序的安全性。本教程解释类型系统如何保证内存安全和线程安全。

---

## 第一部分：类型安全基础

### 什么是类型安全？

**定义**: 良类型的程序不会陷入未定义行为。

```
Γ ⊢ e : τ  →  程序e不会崩溃
```

### Rust的类型安全保证

1. **内存安全**: 不会访问无效内存
2. **类型安全**: 不会类型混淆
3. **线程安全**: 不会数据竞争

---

## 第二部分：类型安全定理

### 进展性 (Progress)

**定理**: 良类型的表达式要么是值，要么可以进一步求值。

```
Γ ⊢ e : τ → (value(e) ∨ ∃e', e → e')
```

**直觉**: 程序不会"卡住"。

### 保持性 (Preservation)

**定理**: 求值保持类型。

```
Γ ⊢ e : τ ∧ e → e' → Γ ⊢ e' : τ
```

**直觉**: 计算不会改变类型。

### 类型安全

**类型安全 = 进展性 + 保持性**

---

## 第三部分：内存安全

### 所有权保证

```rust
let s = String::from("hello");
let t = s;  // 所有权转移
// s 不再有效
```

**保证**: 不会使用已释放内存。

### 借用保证

```rust
let mut x = 5;
let r = &mut x;
// 在此期间，没有其他引用
```

**保证**: 不会数据竞争。

---

## 第四部分：线程安全

### Send与Sync

```rust
// T: Send - 可安全跨线程转移
// T: Sync - 可安全跨线程共享

let data = Arc::new(5);
thread::spawn(move || {
    println!("{}", data);  // OK，Arc是Send+Sync
});
```

**保证**: 借用检查器阻止不安全的数据共享。

---

## 第五部分：形式化证明

### 定理 T-TY3

**类型安全定理**: 良类型的Rust程序不会崩溃。

**证明概要**:

1. 对所有表达式进行类型检查
2. 证明进展性: 良类型表达式可求值
3. 证明保持性: 求值保持类型
4. 归纳: 程序不会遇到类型错误

---

## 总结

```
Rust类型系统
    │
    ├──→ 内存安全
    │       ├── 所有权
    │       ├── 借用
    │       └── 生命周期
    │
    ├──→ 线程安全
    │       ├── Send
    │       └── Sync
    │
    └──→ 形式化保证
            ├── 进展性
            ├── 保持性
            └── 类型安全定理
```

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-28
**状态**: ✅ 已扩展 - 类型系统教程完整版
