# 🔷 Rust 类型系统速查卡

> **快速参考** | [完整文档](../../crates/c02_type_system/docs/) | [代码示例](../../crates/c02_type_system/examples/)

---

## 🎯 核心概念

### 类型安全三支柱

```text
1. 静态类型检查（编译期）
2. 类型推导（省略显式标注）
3. 零成本抽象（无运行时开销）
```

---

## 📐 基本类型速查

### 标量类型

```rust
// 整数
let a: i8 = -128;      // 8位有符号
let b: u8 = 255;       // 8位无符号
let c: i32 = -100;     // 32位有符号（默认）
let d: usize = 100;    // 指针大小

// 浮点
let e: f32 = 3.14;     // 32位
let f: f64 = 2.71;     // 64位（默认）

// 布尔
let g: bool = true;

// 字符
let h: char = '🦀';    // Unicode 字符
```

---

### 复合类型

```rust
// 元组
let tuple: (i32, f64, char) = (500, 6.4, '🦀');
let (x, y, z) = tuple;  // 解构

// 数组
let array: [i32; 5] = [1, 2, 3, 4, 5];
let slice: &[i32] = &array[1..3];  // [2, 3]

// 字符串
let s1: &str = "hello";           // 字符串切片
let s2: String = String::from("world");  // 堆字符串
```

---

## 🏗️ Trait 系统

### 定义与实现

```rust
trait Summary {
    fn summarize(&self) -> String;

    // 默认实现
    fn default_summary(&self) -> String {
        String::from("(Read more...)")
    }
}

struct Article {
    title: String,
    content: String,
}

impl Summary for Article {
    fn summarize(&self) -> String {
        format!("{}: {}", self.title, self.content)
    }
}
```

---

### Trait 作为参数

```rust
// 方式 1: impl Trait
fn notify(item: &impl Summary) {
    println!("{}", item.summarize());
}

// 方式 2: Trait bound
fn notify<T: Summary>(item: &T) {
    println!("{}", item.summarize());
}

// 方式 3: where 子句（复杂约束）
fn notify<T>(item: &T)
where
    T: Summary + Display,
{
    println!("{}", item.summarize());
}
```

---

### Trait 作为返回值

```rust
// impl Trait 语法
fn returns_summarizable() -> impl Summary {
    Article {
        title: String::from("Hello"),
        content: String::from("World"),
    }
}

// Trait 对象（动态分派）
fn returns_trait_object() -> Box<dyn Summary> {
    Box::new(Article { /* ... */ })
}
```

---

## 🔄 类型转换

### From/Into

```rust
// From trait
impl From<i32> for MyType {
    fn from(val: i32) -> Self {
        MyType(val)
    }
}

let my = MyType::from(42);

// Into trait（自动实现）
let my: MyType = 42.into();
```

---

### TryFrom/TryInto（可失败转换）

```rust
use std::convert::TryFrom;

impl TryFrom<i32> for PositiveInt {
    type Error = &'static str;

    fn try_from(value: i32) -> Result<Self, Self::Error> {
        if value > 0 {
            Ok(PositiveInt(value))
        } else {
            Err("Value must be positive")
        }
    }
}

let pos = PositiveInt::try_from(42)?;
```

---

### as 转换（基本类型）

```rust
let a = 3.14f64;
let b = a as i32;      // 3（截断）
let c = 100i32 as u8;  // 100
```

---

## 📦 泛型编程

### 泛型函数

```rust
fn largest<T: PartialOrd>(list: &[T]) -> &T {
    let mut largest = &list[0];
    for item in list {
        if item > largest {
            largest = item;
        }
    }
    largest
}
```

---

### 泛型结构体

```rust
struct Point<T> {
    x: T,
    y: T,
}

impl<T> Point<T> {
    fn new(x: T, y: T) -> Self {
        Point { x, y }
    }
}

// 为特定类型实现方法
impl Point<f32> {
    fn distance_from_origin(&self) -> f32 {
        (self.x.powi(2) + self.y.powi(2)).sqrt()
    }
}
```

---

### 关联类型

```rust
trait Iterator {
    type Item;  // 关联类型

    fn next(&mut self) -> Option<Self::Item>;
}

impl Iterator for Counter {
    type Item = u32;

    fn next(&mut self) -> Option<Self::Item> {
        // ...
    }
}
```

---

## 🎭 型变（Variance）

### 协变（Covariant）- &T

```rust
// 'long 是 'short 的子类型
fn covariant<'long, 'short>(x: &'long str) -> &'short str
where
    'long: 'short,  // 'long 活得更久
{
    x  // ✅ OK: &'long str 可以转为 &'short str
}
```

---

### 逆变（Contravariant）- fn(T)

```rust
// 函数参数是逆变的
fn contravariant<'short, 'long>(
    f: fn(&'long str),
    s: &'short str,
) where
    'short: 'long,
{
    f(s);  // ✅ OK
}
```

---

### 不变（Invariant）- &mut T

```rust
// &mut T 是不变的
fn invariant<'a, 'b>(x: &'a mut i32, y: &'b mut i32) {
    // x 和 y 必须精确匹配生命周期
}
```

---

## 🔍 常用 Trait

### Debug & Display

```rust
#[derive(Debug)]
struct Point { x: i32, y: i32 }

impl std::fmt::Display for Point {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "({}, {})", self.x, self.y)
    }
}

let p = Point { x: 1, y: 2 };
println!("{:?}", p);  // Debug
println!("{}", p);    // Display
```

---

### Clone & Copy

```rust
// Copy: 隐式复制（栈上简单类型）
#[derive(Copy, Clone)]
struct Point { x: i32, y: i32 }

// Clone: 显式深拷贝
#[derive(Clone)]
struct Data { vec: Vec<i32> }

let d1 = Data { vec: vec![1, 2, 3] };
let d2 = d1.clone();  // 显式克隆
```

---

### PartialEq & Eq

```rust
#[derive(PartialEq, Eq)]
struct Point { x: i32, y: i32 }

let p1 = Point { x: 1, y: 2 };
let p2 = Point { x: 1, y: 2 };
assert_eq!(p1, p2);
```

---

### PartialOrd & Ord

```rust
#[derive(PartialOrd, Ord, PartialEq, Eq)]
struct Point { x: i32, y: i32 }

use std::cmp::Ordering;

let p1 = Point { x: 1, y: 2 };
let p2 = Point { x: 3, y: 4 };
assert!(p1 < p2);
```

---

## 🧬 高级类型

### 类型别名

```rust
type Kilometers = i32;
type Result<T> = std::result::Result<T, std::io::Error>;

fn distance() -> Kilometers {
    100
}
```

---

### Never 类型

```rust
fn never_returns() -> ! {
    panic!("This function never returns!");
}

let x: i32 = if some_condition {
    42
} else {
    never_returns()  // ! 可以转换为任何类型
};
```

---

### PhantomData（零大小类型标记）

```rust
use std::marker::PhantomData;

struct MyType<T> {
    data: *const u8,
    _marker: PhantomData<T>,  // 告诉编译器"拥有" T
}
```

---

## 🎯 常见模式

### 新类型模式（Newtype）

```rust
struct Meters(u32);
struct Seconds(u32);

// 防止类型混淆
fn run(distance: Meters, time: Seconds) {
    // ...
}

// ❌ 编译错误
// run(Seconds(10), Meters(100));
```

---

### 类型状态模式

```rust
struct Locked;
struct Unlocked;

struct Door<State> {
    _state: PhantomData<State>,
}

impl Door<Locked> {
    fn unlock(self) -> Door<Unlocked> {
        Door { _state: PhantomData }
    }
}

impl Door<Unlocked> {
    fn lock(self) -> Door<Locked> {
        Door { _state: PhantomData }
    }

    fn open(&self) {
        println!("Door opened");
    }
}

let door = Door::<Locked> { _state: PhantomData };
// door.open();  // ❌ 编译错误：锁着的门不能开
let door = door.unlock();
door.open();  // ✅ OK
```

---

### Builder 模式（类型安全）

```rust
struct EmailBuilder<Subject, Body> {
    to: String,
    subject: Subject,
    body: Body,
}

struct Set<T>(T);
struct Unset;

impl EmailBuilder<Unset, Unset> {
    fn new(to: String) -> Self {
        EmailBuilder { to, subject: Unset, body: Unset }
    }
}

impl<B> EmailBuilder<Unset, B> {
    fn subject(self, subject: String) -> EmailBuilder<Set<String>, B> {
        EmailBuilder {
            to: self.to,
            subject: Set(subject),
            body: self.body,
        }
    }
}

// 只有 subject 和 body 都设置后才能 build
impl EmailBuilder<Set<String>, Set<String>> {
    fn build(self) -> Email {
        Email {
            to: self.to,
            subject: self.subject.0,
            body: self.body.0,
        }
    }
}
```

---

## ⚡ 性能提示

### 单态化（Monomorphization）

```rust
// 泛型函数会为每个具体类型生成一份代码
fn generic<T: Display>(t: T) {
    println!("{}", t);
}

// 调用时
generic(5);       // 生成 generic::<i32>
generic("hello"); // 生成 generic::<&str>
```

**优势**: 零运行时开销
**劣势**: 增加编译时间和二进制大小

---

### 动态分派 vs 静态分派

```rust
// 静态分派（单态化）
fn static_dispatch<T: Summary>(item: &T) {
    item.summarize();
}
// ✅ 性能：无虚表开销
// ⚠️ 代价：代码膨胀

// 动态分派（trait 对象）
fn dynamic_dispatch(item: &dyn Summary) {
    item.summarize();
}
// ✅ 性能：小二进制
// ⚠️ 代价：虚表查找开销
```

---

## 🔗 快速跳转

### 深入学习

- [类型系统理论](../../crates/c02_type_system/docs/tier_04_advanced/)
- [型变详解](../../crates/c02_type_system/docs/tier_03_references/02_类型型变参考.md)
- [Trait 系统](../../crates/c02_type_system/docs/tier_02_guides/02_trait系统实践.md)

### 代码示例

- [泛型示例](../../crates/c02_type_system/examples/)
- [类型转换](../../crates/c02_type_system/src/conversions/)

### 形式化理论

- [类型理论基础](../../crates/c02_type_system/docs/tier_04_advanced/01_类型理论基础.md)

---

**最后更新**: 2025-10-30
**Rust 版本**: 1.90 (Edition 2024)

🔷 **Rust 类型系统，安全与表达力的极致！**
