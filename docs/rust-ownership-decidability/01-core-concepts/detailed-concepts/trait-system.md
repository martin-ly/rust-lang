# Trait 系统详解

> **目标**: 全面掌握 Rust trait 系统，包括泛型、关联类型、trait 对象、泛型特化以及孤儿规则等高级概念。

---

## 目录

- [Trait 系统详解](#trait-系统详解)
  - [目录](#目录)
  - [1. 形式化定义](#1-形式化定义)
    - [1.1 Trait 的形式化模型](#11-trait-的形式化模型)
    - [1.2 Trait 与类型系统的关系](#12-trait-与类型系统的关系)
  - [2. 泛型与 Trait Bound](#2-泛型与-trait-bound)
    - [2.1 基本泛型语法](#21-基本泛型语法)
    - [2.2 Trait Bound 详解](#22-trait-bound-详解)
    - [2.3 生命周期与泛型](#23-生命周期与泛型)
    - [2.4 默认泛型参数](#24-默认泛型参数)
    - [2.5 泛型的单态化](#25-泛型的单态化)
  - [3. 关联类型](#3-关联类型)
    - [3.1 关联类型的形式化定义](#31-关联类型的形式化定义)
    - [3.2 关联类型 vs 泛型参数](#32-关联类型-vs-泛型参数)
    - [3.3 关联类型的约束](#33-关联类型的约束)
    - [3.4 关联常量](#34-关联常量)
  - [4. Trait 对象与动态分发](#4-trait-对象与动态分发)
    - [4.1 Trait 对象的形式化定义](#41-trait-对象的形式化定义)
    - [4.2 Trait 对象的内存布局](#42-trait-对象的内存布局)
    - [4.3 对象安全 (Object Safety)](#43-对象安全-object-safety)
    - [4.4 动态分发的使用场景](#44-动态分发的使用场景)
    - [4.5 静态分发 vs 动态分发](#45-静态分发-vs-动态分发)
  - [5. 高级 Trait 特性](#5-高级-trait-特性)
    - [5.1 完全限定语法](#51-完全限定语法)
    - [5.2 超 trait (Supertraits)](#52-超-trait-supertraits)
    - [5.3 关联类型构造函数](#53-关联类型构造函数)
    - [5.4 泛型特化（不稳定特性）](#54-泛型特化不稳定特性)
    - [5.5 自动 trait](#55-自动-trait)
  - [6. 常见陷阱与解决方案](#6-常见陷阱与解决方案)
    - [陷阱 1: 孤儿规则 (Orphan Rules)](#陷阱-1-孤儿规则-orphan-rules)
    - [陷阱 2: 递归类型限制](#陷阱-2-递归类型限制)
    - [陷阱 3: 生命周期推断失败](#陷阱-3-生命周期推断失败)
    - [陷阱 4: 过多的 trait bound](#陷阱-4-过多的-trait-bound)
    - [陷阱 5: 过度使用动态分发](#陷阱-5-过度使用动态分发)
  - [7. 与其他语言对比](#7-与其他语言对比)
    - [7.1 Java: 接口与泛型](#71-java-接口与泛型)
    - [7.2 C++: 模板与概念](#72-c-模板与概念)
    - [7.3 Go: 接口](#73-go-接口)
    - [7.4 Haskell: Typeclass](#74-haskell-typeclass)
  - [8. 性能影响分析](#8-性能影响分析)
    - [8.1 单态化的代码膨胀](#81-单态化的代码膨胀)
    - [8.2 静态分发 vs 动态分发性能](#82-静态分发-vs-动态分发性能)
    - [8.3 关联类型的零成本](#83-关联类型的零成本)
    - [8.4 泛型缓存优化](#84-泛型缓存优化)
  - [9. 设计模式](#9-设计模式)
    - [9.1 类型状态模式](#91-类型状态模式)
    - [9.2 Builder 模式](#92-builder-模式)
    - [9.3 访问者模式](#93-访问者模式)
    - [9.4 策略模式](#94-策略模式)
    - [9.5 装饰器模式](#95-装饰器模式)
  - [总结](#总结)

---

## 1. 形式化定义

### 1.1 Trait 的形式化模型

**定义 1.1** (Trait): Trait 是定义类型行为的接口，可以包含方法签名、关联类型、关联常量等。

**形式化表示**:

```
trait TraitName {
    type AssocType;           // 关联类型
    const CONST: Type;        // 关联常量
    fn method(&self) -> Type; // 方法
}

impl TraitName for Type {
    // 实现
}
```

**定义 1.2** (Trait Bound): Trait bound 是对类型参数的约束，形式为 `T: Trait`。

**形式化规则**:

```
T: Trait  ≡  T 实现了 Trait 中定义的所有方法
T: Trait1 + Trait2  ≡  T 同时实现 Trait1 和 Trait2
T: ?Sized  ≡  T 可以是动态大小类型
```

### 1.2 Trait 与类型系统的关系

```
类型层次结构:

                    Any
                     │
        ┌────────────┼────────────┐
        │            │            │
      Sized      ?Sized        Dyn Trait
        │            │            │
    ┌───┴───┐    ┌───┴───┐    ┌───┴───┐
    │       │    │       │    │       │
  具体类型  数组  切片    trait对象  函数指针
```

---

## 2. 泛型与 Trait Bound

### 2.1 基本泛型语法

```rust
// 函数泛型
fn identity<T>(value: T) -> T {
    value
}

// 结构体泛型
struct Point<T> {
    x: T,
    y: T,
}

// 枚举泛型
enum Option<T> {
    Some(T),
    None,
}

// 实现块中的泛型
impl<T> Point<T> {
    fn x(&self) -> &T {
        &self.x
    }
}
```

### 2.2 Trait Bound 详解

```rust
// 简单 trait bound
fn print<T: Display>(value: T) {
    println!("{}", value);
}

// 多个 trait bound
fn process<T: Display + Clone>(value: T) {
    println!("{}", value.clone());
}

// where 子句（推荐用于复杂约束）
fn complex_process<T, U>(t: T, u: U) -> i32
where
    T: Display + Clone,
    U: Debug + PartialEq,
{
    // 函数体
    42
}

// 关联类型的约束
fn compare<T>(a: T::Item, b: T::Item) -> bool
where
    T: Iterator,
    T::Item: PartialOrd,
{
    a < b
}
```

### 2.3 生命周期与泛型

```rust
// 泛型与生命周期结合
fn longest<'a, T>(x: &'a T, y: &'a T) -> &'a T
where
    T: PartialOrd,
{
    if x > y { x } else { y }
}

// 泛型结构体的生命周期
struct Ref<'a, T: 'a> {
    value: &'a T,
}

// 复杂约束
fn process_refs<'a, 'b, T, U>(x: &'a T, y: &'b U) -> &'a T
where
    T: 'a + Display,
    U: 'b + Debug,
    'b: 'a,  // 'b 至少和 'a 一样长
{
    x
}
```

### 2.4 默认泛型参数

```rust
trait Add<Rhs = Self> {
    type Output;
    fn add(self, rhs: Rhs) -> Self::Output;
}

// 使用默认参数
impl Add for Point {
    type Output = Point;
    fn add(self, rhs: Point) -> Point {
        Point { x: self.x + rhs.x, y: self.y + rhs.y }
    }
}

// 自定义 Rhs 类型
impl Add<f64> for Point {
    type Output = Point;
    fn add(self, rhs: f64) -> Point {
        Point { x: self.x + rhs, y: self.y + rhs }
    }
}
```

### 2.5 泛型的单态化

Rust 使用单态化实现泛型，为每个具体类型生成专门的代码：

```rust
fn identity<T>(x: T) -> T { x }

// 编译器生成：
// fn identity_i32(x: i32) -> i32 { x }
// fn identity_f64(x: f64) -> f64 { x }
// fn identity_string(x: String) -> String { x }

identity(5i32);      // 调用 identity_i32
identity(3.14f64);   // 调用 identity_f64
identity(String::new()); // 调用 identity_string
```

---

## 3. 关联类型

### 3.1 关联类型的形式化定义

**定义 3.1** (关联类型): 关联类型是 trait 中定义的类型占位符，由实现者指定具体类型。

```rust
trait Iterator {
    type Item;  // 关联类型
    fn next(&mut self) -> Option<Self::Item>;
}

// 实现时指定关联类型
impl Iterator for Counter {
    type Item = u32;
    fn next(&mut self) -> Option<Self::Item> {
        // 实现
        Some(0)
    }
}
```

### 3.2 关联类型 vs 泛型参数

```rust
// 泛型参数版本
trait GenericProcessor<T> {
    fn process(&self, input: T) -> T;
}

// 关联类型版本
trait AssociatedProcessor {
    type Input;
    type Output;
    fn process(&self, input: Self::Input) -> Self::Output;
}
```

**设计选择指南**:

| 场景 | 使用泛型参数 | 使用关联类型 |
|------|--------------|--------------|
| 一个实现对应一种类型 | ❌ | ✅ |
| 一个实现对应多种类型 | ✅ | ❌ |
| 类型之间有映射关系 | - | ✅ |

### 3.3 关联类型的约束

```rust
trait Graph {
    type Node: Clone + Debug;
    type Edge: Clone;

    fn nodes(&self) -> Vec<Self::Node>;
    fn edges(&self) -> Vec<Self::Edge>;
    fn connect(&mut self, from: Self::Node, to: Self::Node);
}

// 实现时关联类型必须满足约束
struct MyGraph;

impl Graph for MyGraph {
    type Node = String;  // String 实现了 Clone + Debug
    type Edge = (String, String);

    fn nodes(&self) -> Vec<Self::Node> { vec![] }
    fn edges(&self) -> Vec<Self::Edge> { vec![] }
    fn connect(&mut self, _from: Self::Node, _to: Self::Node) {}
}
```

### 3.4 关联常量

```rust
trait Shape {
    const SIDES: u32;
    const NAME: &'static str;

    fn describe(&self) {
        println!("I am a {} with {} sides", Self::NAME, Self::SIDES);
    }
}

struct Triangle;
impl Shape for Triangle {
    const SIDES: u32 = 3;
    const NAME: &'static str = "Triangle";
}

struct Square;
impl Shape for Square {
    const SIDES: u32 = 4;
    const NAME: &'static str = "Square";
}
```

---

## 4. Trait 对象与动态分发

### 4.1 Trait 对象的形式化定义

**定义 4.1** (Trait Object): Trait 对象是实现了特定 trait 的具体类型的擦除类型，表示为 `dyn Trait`。

```rust
// 静态分发（单态化）
fn static_dispatch<T: Drawable>(item: T) {
    item.draw();
}

// 动态分发（trait 对象）
fn dynamic_dispatch(item: &dyn Drawable) {
    item.draw();
}
```

### 4.2 Trait 对象的内存布局

```rust
// &dyn Trait 的内存布局
// ┌─────────────────┬─────────────────┐
// │   data ptr      │   vtable ptr    │
// │  (指向具体值)    │  (指向方法表)    │
// └────────┬────────┴────────┬────────┘
//          │                 │
//          ▼                 ▼
//     具体类型的值      vtable 结构
//                      ┌───────────┐
//                      │ drop ptr  │
//                      │ size      │
//                      │ align     │
//                      │ method1   │ ──────► Drawable::draw
//                      │ method2   │ ──────► Drawable::area
//                      └───────────┘
```

### 4.3 对象安全 (Object Safety)

不是所有 trait 都可以作为 trait 对象使用。一个 trait 是对象安全的，当且仅当：

1. 不要求 `Self: Sized`
2. 所有方法都是对象安全的
3. 不使用关联类型（作为 trait 对象时）

```rust
// ✅ 对象安全的 trait
trait Drawable {
    fn draw(&self);
    fn area(&self) -> f64;
}

// ❌ 不是对象安全的 trait
trait NotObjectSafe {
    fn new() -> Self;           // 返回 Self，需要知道具体类型
    fn compare<T>(&self, other: T);  // 泛型方法
}

// 修正为对象安全
trait ObjectSafe {
    fn draw(&self);
    fn clone_box(&self) -> Box<dyn ObjectSafe>;  // 替代返回 Self
}
```

### 4.4 动态分发的使用场景

```rust
// 场景 1: 异构集合
fn draw_all(items: &[&dyn Drawable]) {
    for item in items {
        item.draw();
    }
}

// 使用
let circle = Circle::new(5.0);
let square = Square::new(4.0);
draw_all(&[&circle, &square]);

// 场景 2: 运行时类型选择
fn create_drawable(kind: &str) -> Box<dyn Drawable> {
    match kind {
        "circle" => Box::new(Circle::new(1.0)),
        "square" => Box::new(Square::new(1.0)),
        _ => panic!("Unknown kind"),
    }
}

// 场景 3: 回调函数
type Callback = Box<dyn Fn(&Event) + Send + Sync>;

struct EventSystem {
    handlers: Vec<Callback>,
}
```

### 4.5 静态分发 vs 动态分发

| 特性 | 静态分发 (`impl Trait`/泛型) | 动态分发 (`dyn Trait`) |
|------|------------------------------|------------------------|
| 编译期确定 | ✅ | ❌ |
| 运行时开销 | 无 | 间接调用 (vptr) |
| 代码大小 | 可能膨胀（单态化）| 较小 |
| 异构集合 | ❌ | ✅ |
| 运行时选择 | ❌ | ✅ |

```rust
// 静态分发 - 零运行时开销
fn process_static<T: Processor>(p: T) {
    p.process();  // 直接调用，内联可能
}

// 动态分发 - 运行时查找
fn process_dynamic(p: &dyn Processor) {
    p.process();  // 通过 vtable 间接调用
}
```

---

## 5. 高级 Trait 特性

### 5.1 完全限定语法

```rust
trait Animal {
    fn name(&self) -> &str;
}

trait Pet: Animal {
    fn name(&self) -> &str;  // 与 Animal::name 冲突
}

struct Dog;

impl Animal for Dog {
    fn name(&self) -> &str { "Animal dog" }
}

impl Pet for Dog {
    fn name(&self) -> &str { "Pet dog" }
}

fn main() {
    let dog = Dog;

    // 完全限定语法调用特定 trait 的方法
    println!("{}", <Dog as Animal>::name(&dog));  // Animal dog
    println!("{}", <Dog as Pet>::name(&dog));     // Pet dog
}
```

### 5.2 超 trait (Supertraits)

```rust
// Pet 是 Animal 的子 trait
trait Animal {
    fn species(&self) -> &str;
}

trait Pet: Animal {
    fn owner(&self) -> &str;
}

// 实现 Pet 必须同时实现 Animal
struct Cat;

impl Animal for Cat {
    fn species(&self) -> &str { "Felis catus" }
}

impl Pet for Cat {
    fn owner(&self) -> &str { "Alice" }
}
```

### 5.3 关联类型构造函数

```rust
trait Collection {
    type Item;
    type Iterator: Iterator<Item = Self::Item>;

    fn iter(&self) -> Self::Iterator;
    fn from_iter(iter: Self::Iterator) -> Self;
}

// 实现
struct MyVec<T>(Vec<T>);

impl<T> Collection for MyVec<T> {
    type Item = T;
    type Iterator = std::vec::IntoIter<T>;

    fn iter(&self) -> Self::Iterator {
        self.0.clone().into_iter()
    }

    fn from_iter(iter: Self::Iterator) -> Self {
        MyVec(iter.collect())
    }
}
```

### 5.4 泛型特化（不稳定特性）

```rust
#![feature(min_specialization)]

// 通用实现
trait ToDebugString {
    fn to_debug_string(&self) -> String;
}

impl<T: std::fmt::Debug> ToDebugString for T {
    default fn to_debug_string(&self) -> String {
        format!("{:?}", self)
    }
}

// 对 String 的特化实现
impl ToDebugString for String {
    fn to_debug_string(&self) -> String {
        format!("String({})", self)
    }
}
```

### 5.5 自动 trait

```rust
// 自动 trait（以前叫 OIBIT）
// 自动为满足条件的类型实现

auto trait Send {}
auto trait Sync {}

// !Send 和 !Sync 的自定义类型
struct RawPointer(*const u8);

// 手动标记为非 Send/Sync
impl !Send for RawPointer {}
impl !Sync for RawPointer {}
```

---

## 6. 常见陷阱与解决方案

### 陷阱 1: 孤儿规则 (Orphan Rules)

```rust
// ❌ 编译错误：违反孤儿规则
impl Display for Vec<i32> {
    fn fmt(&self, f: &mut Formatter) -> Result {
        write!(f, "{:?}", self)
    }
}
```

**解决方案 1: Newtype 模式**

```rust
struct MyVec(Vec<i32>);

impl Display for MyVec {
    fn fmt(&self, f: &mut Formatter) -> Result {
        write!(f, "{:?}", self.0)
    }
}
```

**解决方案 2: 包装 trait**

```rust
trait MyDisplay {
    fn my_display(&self) -> String;
}

impl MyDisplay for Vec<i32> {
    fn my_display(&self) -> String {
        format!("{:?}", self)
    }
}
```

### 陷阱 2: 递归类型限制

```rust
// ❌ 编译错误：递归类型没有固定大小
enum Json {
    Null,
    Bool(bool),
    Number(f64),
    String(String),
    Array(Vec<Json>),  // 递归
    Object(HashMap<String, Json>),  // 递归
}
```

**解决方案**: 使用 Box 提供间接层

```rust
enum Json {
    Null,
    Bool(bool),
    Number(f64),
    String(String),
    Array(Vec<Json>),
    Object(HashMap<String, Box<Json>>),  // Box 提供固定大小
}
```

### 陷阱 3: 生命周期推断失败

```rust
// ❌ 编译错误：生命周期不明确
fn make_iterator(data: &[i32]) -> impl Iterator<Item = &i32> {
    data.iter()
}
```

**解决方案**: 显式生命周期标注

```rust
fn make_iterator<'a>(data: &'a [i32]) -> impl Iterator<Item = &'a i32> + 'a {
    data.iter()
}
```

### 陷阱 4: 过多的 trait bound

```rust
// ❌ 过于复杂，难以阅读和维护
fn process<T, U, V>(x: T, y: U, z: V)
where
    T: Clone + Send + Sync + Display + Debug,
    U: Iterator<Item = T> + ExactSizeIterator,
    V: AsRef<[T]> + IntoIterator<Item = T>,
{}
```

**解决方案**: 定义组合 trait

```rust
trait Processable: Clone + Send + Sync + Display + Debug {}
impl<T: Clone + Send + Sync + Display + Debug> Processable for T {}

fn process<T: Processable, U, V>(x: T, y: U, z: V)
where
    U: Iterator<Item = T> + ExactSizeIterator,
    V: AsRef<[T]> + IntoIterator<Item = T>,
{}
```

### 陷阱 5: 过度使用动态分发

```rust
// ❌ 不必要的动态分发
fn process(items: &[Box<dyn Drawable>]) {
    for item in items {
        item.draw();
    }
}

// ✅ 静态分发更优
fn process_static<T: Drawable>(items: &[T]) {
    for item in items {
        item.draw();
    }
}

// ✅ 或使用 impl Trait
fn process_impl(items: &[impl Drawable]) {
    for item in items {
        item.draw();
    }
}
```

---

## 7. 与其他语言对比

### 7.1 Java: 接口与泛型

**Java 版本**:

```java
// 接口
interface Drawable {
    void draw();
    double area();
}

// 泛型类
class Container<T extends Drawable> {
    private T item;

    public Container(T item) {
        this.item = item;
    }

    public void show() {
        item.draw();
    }
}

// 通配符（类似 impl Trait）
void processAll(List<? extends Drawable> items) {
    for (Drawable item : items) {
        item.draw();
    }
}
```

**对比分析**:

| 特性 | Rust | Java |
|------|------|------|
| 接口实现 | 独立 impl 块 | class 内实现 |
| 泛型擦除 | 单态化 | 类型擦除 |
| 关联类型 | 支持 | 不支持 |
| 特化 | 实验性 | 支持（有限）|
| 对象安全 | 编译期检查 | 运行时 |

### 7.2 C++: 模板与概念

**C++20 版本**:

```cpp
// 概念（类似 trait）
template<typename T>
concept Drawable = requires(T t) {
    { t.draw() } -> std::same_as<void>;
    { t.area() } -> std::convertible_to<double>;
};

// 模板约束
void process(Drawable auto& item) {
    item.draw();
}

// 关联类型（通过 traits 类）
template<typename T>
struct iterator_traits;

template<typename T>
struct iterator_traits<std::vector<T>::iterator> {
    using value_type = T;
    using difference_type = std::ptrdiff_t;
};
```

**对比分析**:

| 特性 | Rust | C++ |
|------|------|-----|
| 编译期检查 | 完整 | 模板实例化时 |
| 错误信息 | 清晰 |  notoriously 难读 |
| 编译时间 | 可控 | 可能很长 |
| 动态分发 | trait object | 虚函数 |
| 模板元编程 | 类型系统 | SFINAE/concepts |

### 7.3 Go: 接口

**Go 版本**:

```go
// 隐式接口
type Drawable interface {
    Draw()
    Area() float64
}

// 类型自动实现接口（鸭子类型）
type Circle struct {
    Radius float64
}

func (c Circle) Draw() {
    fmt.Println("Drawing circle")
}

func (c Circle) Area() float64 {
    return math.Pi * c.Radius * c.Radius
}

// 使用
func Process(d Drawable) {
    d.Draw()
}
```

**对比分析**:

| 特性 | Rust | Go |
|------|------|-----|
| 接口实现 | 显式 impl | 隐式 |
| 静态/动态 | 两者皆可 | 运行时动态 |
| 泛型 | 完整 | 1.18+ 有限支持 |
| 类型安全 | 强 | 较弱（运行时检查）|
| 性能 | 单态化优化 | 接口调用开销 |

### 7.4 Haskell: Typeclass

**Haskell 版本**:

```haskell
-- Typeclass（trait 的灵感来源）
class Drawable a where
    draw :: a -> IO ()
    area :: a -> Double

-- 实例实现（类似 impl）
instance Drawable Circle where
    draw c = putStrLn "Drawing circle"
    area c = pi * (radius c) ^ 2

-- 多参数 typeclass（类似多泛型 trait）
class Convertible a b where
    convert :: a -> b

-- 函数式依赖（类似关联类型）
class Collection c a | c -> a where
    empty :: c
    insert :: a -> c -> c
```

**对比分析**:

| 特性 | Rust | Haskell |
|------|------|---------|
| 类型类 | 类似 trait | typeclass |
| 实例一致性 | 每个类型唯一实现 | 允许多实例（Newtype）|
| 高阶类型 | 有限 | 完整支持 |
| 类型推导 | 局部 | 全局 |
| 副作用控制 | 类型系统 | Monad |

---

## 8. 性能影响分析

### 8.1 单态化的代码膨胀

```rust
// 单态化导致代码复制
fn process<T: Drawable>(item: T) {
    item.draw();
}

// 编译后生成多个版本：
// fn process_Circle(item: Circle)
// fn process_Square(item: Square)
// fn process_Triangle(item: Triangle)
```

**缓解策略**:

```rust
// 使用 trait object 减少代码膨胀
trait Drawable {
    fn draw(&self);
}

fn process_dynamic(items: &[&dyn Drawable]) {
    for item in items {
        item.draw();  // 共享同一份代码
    }
}
```

### 8.2 静态分发 vs 动态分发性能

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion};

// 静态分发
fn static_dispatch<T: Fn(i32) -> i32>(f: T, x: i32) -> i32 {
    f(x)
}

// 动态分发
fn dynamic_dispatch(f: &dyn Fn(i32) -> i32, x: i32) -> i32 {
    f(x)
}

fn bench_dispatch(c: &mut Criterion) {
    let closure = |x| x * 2;

    c.bench_function("static", |b| {
        b.iter(|| static_dispatch(closure, black_box(5)));
    });

    c.bench_function("dynamic", |b| {
        b.iter(|| dynamic_dispatch(&closure, black_box(5)));
    });
}
```

**预期结果**:

```
static   time: [0.5 ns]    # 可以内联优化
dynamic  time: [2.5 ns]    # vtable 查找开销
```

### 8.3 关联类型的零成本

关联类型在编译期解析，无运行时开销：

```rust
trait Iterator {
    type Item;
    fn next(&mut self) -> Option<Self::Item>;
}

// Vec<i32>::Item 编译时确定为 i32
// 无运行时查找
```

### 8.4 泛型缓存优化

```rust
// 使用泛型缓存重复计算
struct CachedFn<F, T> {
    f: F,
    cache: RefCell<Option<T>>,
}

impl<F, T> CachedFn<F, T>
where
    F: Fn() -> T,
    T: Clone,
{
    fn call(&self) -> T {
        if self.cache.borrow().is_none() {
            *self.cache.borrow_mut() = Some((self.f)());
        }
        self.cache.borrow().as_ref().unwrap().clone()
    }
}
```

---

## 9. 设计模式

### 9.1 类型状态模式

```rust
// 使用类型系统编码状态机
struct Draft;
struct PendingReview;
struct Published;

struct Post<State> {
    content: String,
    state: std::marker::PhantomData<State>,
}

impl Post<Draft> {
    fn new() -> Self {
        Post {
            content: String::new(),
            state: std::marker::PhantomData,
        }
    }

    fn add_text(&mut self, text: &str) {
        self.content.push_str(text);
    }

    fn request_review(self) -> Post<PendingReview> {
        Post {
            content: self.content,
            state: std::marker::PhantomData,
        }
    }
}

impl Post<PendingReview> {
    fn approve(self) -> Post<Published> {
        Post {
            content: self.content,
            state: std::marker::PhantomData,
        }
    }
}

impl Post<Published> {
    fn content(&self) -> &str {
        &self.content
    }
}
```

### 9.2 Builder 模式

```rust
#[derive(Debug)]
struct HttpRequest {
    method: String,
    url: String,
    headers: Vec<(String, String)>,
    body: Option<String>,
}

struct HttpRequestBuilder {
    method: String,
    url: String,
    headers: Vec<(String, String)>,
    body: Option<String>,
}

impl HttpRequestBuilder {
    fn new() -> Self {
        HttpRequestBuilder {
            method: "GET".to_string(),
            url: "".to_string(),
            headers: Vec::new(),
            body: None,
        }
    }

    fn method(mut self, method: &str) -> Self {
        self.method = method.to_string();
        self
    }

    fn url(mut self, url: &str) -> Self {
        self.url = url.to_string();
        self
    }

    fn header(mut self, key: &str, value: &str) -> Self {
        self.headers.push((key.to_string(), value.to_string()));
        self
    }

    fn body(mut self, body: &str) -> Self {
        self.body = Some(body.to_string());
        self
    }

    fn build(self) -> HttpRequest {
        HttpRequest {
            method: self.method,
            url: self.url,
            headers: self.headers,
            body: self.body,
        }
    }
}

// 使用
let request = HttpRequestBuilder::new()
    .method("POST")
    .url("https://api.example.com/users")
    .header("Content-Type", "application/json")
    .body(r#"{"name": "Alice"}"#)
    .build();
```

### 9.3 访问者模式

```rust
// AST 节点
trait Expr {
    fn accept(&self, visitor: &mut dyn ExprVisitor);
}

struct Lit(i32);
struct Add(Box<dyn Expr>, Box<dyn Expr>);

impl Expr for Lit {
    fn accept(&self, visitor: &mut dyn ExprVisitor) {
        visitor.visit_lit(self);
    }
}

impl Expr for Add {
    fn accept(&self, visitor: &mut dyn ExprVisitor) {
        visitor.visit_add(self);
    }
}

// 访问者 trait
trait ExprVisitor {
    fn visit_lit(&mut self, lit: &Lit);
    fn visit_add(&mut self, add: &Add);
}

// 求值访问者
struct Evaluator;

impl ExprVisitor for Evaluator {
    fn visit_lit(&mut self, lit: &Lit) {
        println!("Literal: {}", lit.0);
    }

    fn visit_add(&mut self, add: &Add) {
        println!("Add expression");
        add.0.accept(self);
        add.1.accept(self);
    }
}
```

### 9.4 策略模式

```rust
trait SortStrategy {
    fn sort(&self, data: &mut [i32]);
}

struct QuickSort;
struct MergeSort;

impl SortStrategy for QuickSort {
    fn sort(&self, data: &mut [i32]) {
        data.sort_unstable();
    }
}

impl SortStrategy for MergeSort {
    fn sort(&self, data: &mut [i32]) {
        data.sort();
    }
}

struct Sorter<'a> {
    strategy: &'a dyn SortStrategy,
}

impl<'a> Sorter<'a> {
    fn new(strategy: &'a dyn SortStrategy) -> Self {
        Sorter { strategy }
    }

    fn sort(&self, data: &mut [i32]) {
        self.strategy.sort(data);
    }
}

// 使用
let quick = QuickSort;
let sorter = Sorter::new(&quick);
let mut data = vec![3, 1, 4, 1, 5];
sorter.sort(&mut data);
```

### 9.5 装饰器模式

```rust
trait DataSource {
    fn read(&self) -> String;
    fn write(&mut self, data: &str);
}

struct FileDataSource {
    filename: String,
}

impl DataSource for FileDataSource {
    fn read(&self) -> String {
        format!("Data from {}", self.filename)
    }

    fn write(&mut self, data: &str) {
        println!("Writing '{}' to {}", data, self.filename);
    }
}

// 加密装饰器
struct EncryptionDecorator<T: DataSource> {
    inner: T,
}

impl<T: DataSource> DataSource for EncryptionDecorator<T> {
    fn read(&self) -> String {
        let data = self.inner.read();
        format!("decrypt({})", data)
    }

    fn write(&mut self, data: &str) {
        let encrypted = format!("encrypt({})", data);
        self.inner.write(&encrypted);
    }
}

// 压缩装饰器
struct CompressionDecorator<T: DataSource> {
    inner: T,
}

impl<T: DataSource> DataSource for CompressionDecorator<T> {
    fn read(&self) -> String {
        let data = self.inner.read();
        format!("decompress({})", data)
    }

    fn write(&mut self, data: &str) {
        let compressed = format!("compress({})", data);
        self.inner.write(&compressed);
    }
}
```

---

## 总结

Rust 的 trait 系统是类型系统的核心，提供了：

1. **零成本抽象** - 泛型通过单态化实现，trait object 提供动态分发
2. **表达能力** - 关联类型、泛型、生命周期可以组合表达复杂约束
3. **类型安全** - 编译期保证 trait bound 的满足
4. **灵活性** - 支持静态和动态分发，适配不同场景

掌握 trait 系统是编写高质量 Rust 代码的基础。

---

*本系列文档结束。希望这些深入的分析能帮助你掌握 Rust 的所有权系统！*
