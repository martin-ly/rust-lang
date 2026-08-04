# 子类型论 (Subtyping Theory)

## 目录

- [子类型论 (Subtyping Theory)](#子类型论-subtyping-theory)
  - [目录](#目录)
  - [引言](#引言)
    - [子类型的直觉](#子类型的直觉)
    - [子类型的作用](#子类型的作用)
  - [子类型基础](#子类型基础)
    - [形式化定义](#形式化定义)
    - [子类型的偏序性质](#子类型的偏序性质)
  - [子类型规则](#子类型规则)
    - [基本规则](#基本规则)
      - [1. Width Subtyping (记录宽度)](#1-width-subtyping-记录宽度)
      - [2. Depth Subtyping (字段深度)](#2-depth-subtyping-字段深度)
      - [3. Permutation Subtyping (字段顺序)](#3-permutation-subtyping-字段顺序)
  - [型变 (Variance)](#型变-variance)
    - [定义](#定义)
    - [型变规则推导](#型变规则推导)
      - [函数类型的型变](#函数类型的型变)
    - [Rust 中的型变](#rust-中的型变)
    - [型变表](#型变表)
    - [为什么 `&mut T` 对 T 不变?](#为什么-mut-t-对-t-不变)
  - [生命周期子类型](#生命周期子类型)
    - [生命周期偏序](#生命周期偏序)
    - [生命周期约束](#生命周期约束)
      - [Outlives 约束: 'a: 'b](#outlives-约束-a-b)
      - [生命周期交集](#生命周期交集)
    - [高阶生命周期约束 (HRTB)](#高阶生命周期约束-hrtb)
  - [Trait 对象与子类型](#trait-对象与子类型)
    - [Trait 继承](#trait-继承)
    - [Trait 对象的型变](#trait-对象的型变)
    - [Supertrait 约束](#supertrait-约束)
  - [协变、逆变与不变](#协变逆变与不变)
    - [协变示例](#协变示例)
    - [逆变示例](#逆变示例)
    - [不变示例](#不变示例)
    - [PhantomData 与型变](#phantomdata-与型变)
  - [子类型与类型转换](#子类型与类型转换)
    - [子类型强制转换 (Subtyping Coercion)](#子类型强制转换-subtyping-coercion)
    - [Deref 强制转换 vs 子类型](#deref-强制转换-vs-子类型)
  - [高级子类型](#高级子类型)
    - [Higher-Rank Trait Bounds (HRTB)](#higher-rank-trait-bounds-hrtb)
    - [生命周期省略与子类型](#生命周期省略与子类型)
    - [关联类型与子类型](#关联类型与子类型)
    - [泛型型变](#泛型型变)
  - [子类型健全性](#子类型健全性)
    - [类型健全性定理](#类型健全性定理)
    - [生命周期健全性](#生命周期健全性)
    - [型变健全性](#型变健全性)
  - [实践应用](#实践应用)
    - [1. 灵活的 API 设计](#1-灵活的-api-设计)
    - [2. Trait 对象的向上转型](#2-trait-对象的向上转型)
    - [3. 协变容器](#3-协变容器)
    - [4. 高阶函数与逆变](#4-高阶函数与逆变)
    - [5. 零成本抽象与子类型](#5-零成本抽象与子类型)
  - [参考文献](#参考文献)
    - [子类型理论](#子类型理论)
    - [型变理论](#型变理论)
    - [Rust 子类型](#rust-子类型)
    - [生命周期与子类型](#生命周期与子类型)
  - [总结](#总结)

---

## 引言

**子类型 (Subtyping)** 是类型系统中的一个核心概念,它定义了类型之间的"更具体"或"可替换性"关系。在 Rust 中,子类型主要体现在**生命周期系统**和**型变规则**中。

### 子类型的直觉

```text
如果 S <: T (S 是 T 的子类型),
则任何期望 T 的地方都可以安全地使用 S。
```

**经典例子** (OOP):

```text
Dog <: Animal
可以将 Dog 传给期望 Animal 的函数
```

**Rust 例子** (生命周期):

```text
'static <: 'a (任意 'a)
可以将 'static 引用传给期望 'a 引用的函数
```

### 子类型的作用

| 作用 | 说明 | Rust 例子 |
|------|------|----------|
| **灵活性** | 允许更具体的值替换一般值 | 长生命周期 → 短生命周期 |
| **多态性** | 支持子类型多态 | Trait 对象 |
| **类型安全** | 保持类型系统健全性 | 型变规则 |
| **代码复用** | 一个函数处理多种类型 | 泛型约束 |

---

## 子类型基础

### 形式化定义

**子类型关系** S <: T 满足:

```text
Γ ⊢ e: S    S <: T
───────────────────  (Subsumption)
Γ ⊢ e: T
```

**Liskov 替换原则** (LSP):

```text
如果 S <: T, 则类型为 T 的对象可以被类型为 S 的对象替换,
而不影响程序的正确性。
```

### 子类型的偏序性质

子类型关系 <: 是一个**偏序**:

1. **自反性** (Reflexivity): T <: T
2. **传递性** (Transitivity): 若 S <: T 且 T <: U, 则 S <: U
3. **反对称性** (Antisymmetry): 若 S <: T 且 T <: S, 则 S = T

```rust
// 示例: 生命周期是偏序
fn subtyping_reflexive<'a>(x: &'a str) -> &'a str {
    x // 'a <: 'a (自反)
}

fn subtyping_transitive<'a, 'b, 'c>(x: &'a str) -> &'c str
where
    'a: 'b,
    'b: 'c,
{
    x // 'a <: 'b <: 'c ⇒ 'a <: 'c (传递)
}
```

---

## 子类型规则

### 基本规则

#### 1. Width Subtyping (记录宽度)

```text
{x: T, y: U, z: V} <: {x: T, y: U}
```

记录可以有额外字段。

**Rust 不直接支持** (结构体类型精确匹配), 但 Trait 对象支持类似概念:

```rust
trait Minimal {
    fn foo(&self);
}

trait Extended: Minimal {
    fn bar(&self);
}

// Extended 对象可转换为 Minimal 对象
fn width_subtyping(e: &dyn Extended) -> &dyn Minimal {
    e // Extended <: Minimal
}
```

#### 2. Depth Subtyping (字段深度)

```text
如果 S <: T, 则 {x: S} <: {x: T}
```

字段类型可以是子类型。

**Rust 例子**:

```rust
struct Container<'a> {
    data: &'a str,
}

fn depth_subtyping<'a, 'b>(c: Container<'a>) -> Container<'b>
where
    'a: 'b,
{
    Container { data: c.data } // &'a str <: &'b str
}
```

#### 3. Permutation Subtyping (字段顺序)

Rust 结构体字段顺序固定, 不支持排列子类型。

---

## 型变 (Variance)

### 定义

**型变** 描述类型构造器如何保持或反转子类型关系。

| 型变 | 定义 | 子类型传播 |
|------|------|-----------|
| **协变** (Covariant) | F(S) <: F(T) 当 S <: T | 保持方向 |
| **逆变** (Contravariant) | F(T) <: F(S) 当 S <: T | 反转方向 |
| **不变** (Invariant) | F(S) 与 F(T) 不相关 | 无关系 |

### 型变规则推导

#### 函数类型的型变

函数类型 `fn(A) -> B`:

```text
参数位置: 逆变
返回位置: 协变
```

**推导**:

假设 S <: T (S 更具体)

- **返回**: 如果函数返回 S, 可以视为返回 T (✅ 安全)
  → fn() -> S <: fn() -> T (协变)
- **参数**: 如果函数期望 T, 不能传入 S (❌ 不安全)
  → fn(T) -> R <: fn(S) -> R (逆变)

### Rust 中的型变

```rust
// 协变: &'a T
// 'a 是协变的
fn covariant<'a, 'b>(x: &'a str) -> &'b str
where
    'a: 'b, // 'a 存活更久
{
    x // OK: &'a str <: &'b str
}

// 逆变: fn(&'a T)
// 函数参数位置的生命周期是逆变的
fn contravariant<'a, 'b>(f: fn(&'a str)) -> fn(&'b str)
where
    'a: 'b,
{
    f // OK: fn(&'a str) <: fn(&'b str)
}

// 不变: &'a mut T
// 可变引用对 'a 是不变的
fn invariant<'a, 'b>(x: &'a mut i32) -> &'b mut i32
where
    'a: 'b,
{
    // x // 编译错误: &'a mut i32 不能转为 &'b mut i32
    unimplemented!()
}
```

### 型变表

| 类型 | 'a 的型变 | T 的型变 |
|------|-----------|----------|
| `&'a T` | 协变 | 协变 |
| `&'a mut T` | 协变 | **不变** |
| `Box<T>` | - | 协变 |
| `Vec<T>` | - | 协变 |
| `Cell<T>` | - | 不变 |
| `fn(T) -> U` | - | T: 逆变, U: 协变 |
| `*const T` | - | 协变 |
| `*mut T` | - | **不变** |

### 为什么 `&mut T` 对 T 不变?

```rust
// 反例: 如果 &mut T 对 T 协变
fn unsound_covariance<'a>(x: &'a mut &'static str) -> &'a mut &'a str {
    // 假设 &'static str <: &'a str
    // 则 &mut &'static str <: &mut &'a str (如果协变)
    // x // 这会导致悬垂引用!
    unimplemented!()
}

// 正确: &mut T 对 T 不变
fn sound_invariance() {
    let mut s: &'static str = "hello";
    let r: &mut &'static str = &mut s;
    
    // 不能将 &mut &'static str 转为 &mut &'short str
    // 否则可以通过 &mut &'short str 写入短生命周期引用
    // 导致 s 持有悬垂引用
}
```

---

## 生命周期子类型

### 生命周期偏序

**生命周期** 'a 形成偏序:

```text
'a <: 'b  ⇔  'a 的区域包含 'b 的区域
```

直觉: **更长的生命周期是更小的类型** (更具体)。

```rust
// 'static 是最小的生命周期 (最具体)
// 'static <: 'a 对所有 'a
fn static_subtyping<'a>() {
    let s: &'static str = "hello";
    let r: &'a str = s; // OK: 'static <: 'a
}
```

### 生命周期约束

#### Outlives 约束: 'a: 'b

```rust
fn outlives_constraint<'a, 'b>(x: &'a str, y: &'b str) -> &'b str
where
    'a: 'b, // 'a 至少和 'b 一样长
{
    x // OK: &'a str <: &'b str
}
```

#### 生命周期交集

```rust
// 多个引用的公共生命周期
fn min_lifetime<'a, 'b>(x: &'a str, y: &'b str) -> &'min str
where
    'a: 'min,
    'b: 'min,
{
    if x.len() > y.len() { x } else { y }
}
// 实际实现:
fn min_lifetime_actual<'a, 'b>(x: &'a str, y: &'b str) -> &'a str
where
    'b: 'a, // 'b 至少和 'a 一样长
{
    if x.len() > y.len() { x } else { y }
}
```

### 高阶生命周期约束 (HRTB)

```rust
// for<'a> 量化所有生命周期
trait Apply {
    fn apply<'a>(&self, x: &'a str) -> &'a str;
}

// HRTB: 对所有 'a, 'static <: 'a
fn hrtb_subtyping<T>(f: T)
where
    T: for<'a> Fn(&'a str) -> &'a str,
{
    let result = f("test");
}
```

---

## Trait 对象与子类型

### Trait 继承

```rust
trait Animal {
    fn name(&self) -> &str;
}

trait Dog: Animal {
    fn bark(&self);
}

// Dog <: Animal (子 trait)
struct Labrador;

impl Animal for Labrador {
    fn name(&self) -> &str {
        "Labrador"
    }
}

impl Dog for Labrador {
    fn bark(&self) {
        println!("Woof!");
    }
}

// Trait 对象子类型
fn trait_subtyping(dog: &dyn Dog) -> &dyn Animal {
    dog // OK: &dyn Dog <: &dyn Animal
}
```

### Trait 对象的型变

```rust
// Trait 对象对生命周期协变
fn trait_object_covariance<'a, 'b>(x: &'a dyn Animal) -> &'b dyn Animal
where
    'a: 'b,
{
    x // OK: &'a dyn Animal <: &'b dyn Animal
}
```

### Supertrait 约束

```rust
trait Shape {
    fn area(&self) -> f64;
}

trait Circle: Shape {
    fn radius(&self) -> f64;
}

// Circle 对象可以转为 Shape 对象
fn supertrait_coercion(c: Box<dyn Circle>) -> Box<dyn Shape> {
    c // OK: 自动强制转换
}
```

---

## 协变、逆变与不变

### 协变示例

```rust
// Box<T> 对 T 协变
fn box_covariance<'a, 'b>(x: Box<&'a str>) -> Box<&'b str>
where
    'a: 'b,
{
    x // OK: Box<&'a str> <: Box<&'b str>
}

// Vec<T> 对 T 协变
fn vec_covariance<'a, 'b>(x: Vec<&'a str>) -> Vec<&'b str>
where
    'a: 'b,
{
    x // OK: Vec<&'a str> <: Vec<&'b str>
}
```

### 逆变示例

```rust
// fn(T) 对 T 逆变
fn function_contravariance<'a, 'b>(f: fn(&'b str) -> i32) -> fn(&'a str) -> i32
where
    'a: 'b, // 'a 更长
{
    f // OK: fn(&'b str) <: fn(&'a str)
      // 参数位置逆变: 可以接受更一般的输入
}

// 实际应用
fn contravariance_example() {
    fn short_handler(_: &'static str) -> i32 {
        42
    }
    
    let f: fn(&'static str) -> i32 = short_handler;
    let g: fn(&str) -> i32 = f; // OK: 逆变
    
    println!("{}", g("hello"));
}
```

### 不变示例

```rust
use std::cell::Cell;

// Cell<T> 对 T 不变
fn cell_invariance<'a, 'b>(x: Cell<&'a str>) -> Cell<&'b str>
where
    'a: 'b,
{
    // x // 编译错误: Cell<&'a str> 不能转为 Cell<&'b str>
    unimplemented!()
}

// 原因: 内部可变性打破了子类型安全性
fn why_cell_invariant() {
    let long: &'static str = "long";
    let cell = Cell::new(long);
    
    // 如果 Cell 协变:
    // let cell_short: Cell<&'short str> = cell;
    // cell_short.set("short"); // 短生命周期
    // let retrieved: &'static str = cell.get(); // 悬垂引用!
}
```

### PhantomData 与型变

```rust
use std::marker::PhantomData;

// 协变
struct CovariantType<T> {
    _marker: PhantomData<T>,
}

// 逆变
struct ContravariantType<T> {
    _marker: PhantomData<fn(T) -> ()>,
}

// 不变
struct InvariantType<T> {
    _marker: PhantomData<Cell<T>>,
}

// 验证型变
fn variance_check<'a, 'b>(
    cov: CovariantType<&'a str>,
    contra: ContravariantType<&'b str>,
) where
    'a: 'b,
{
    let _: CovariantType<&'b str> = cov; // OK: 协变
    let _: ContravariantType<&'a str> = contra; // OK: 逆变
}
```

---

## 子类型与类型转换

### 子类型强制转换 (Subtyping Coercion)

Rust 支持的隐式强制转换:

| 从 | 到 | 类型 |
|----|----|----|
| `&T` | `&U` | T <: U |
| `&mut T` | `&mut U` | T <: U (不变!) |
| `&mut T` | `&T` | 可变 → 不可变 |
| `*mut T` | `*const T` | 可变 → 不可变 |
| `&[T; n]` | `&[T]` | 数组 → 切片 |
| `fn(args) -> T` | `fn(args) -> U` | T <: U |

```rust
fn subtyping_coercion() {
    // 1. 生命周期协变
    let s: &'static str = "hello";
    let r: &str = s; // 'static <: 'a
    
    // 2. 可变 → 不可变
    let mut x = 42;
    let r1: &mut i32 = &mut x;
    let r2: &i32 = r1; // &mut T → &T
    
    // 3. 数组 → 切片
    let arr: &[i32; 3] = &[1, 2, 3];
    let slice: &[i32] = arr;
    
    // 4. 函数指针
    fn specific() -> &'static str { "hello" }
    let f: fn() -> &'static str = specific;
    let g: fn() -> &str = f; // 返回类型协变
}
```

### Deref 强制转换 vs 子类型

```rust
use std::ops::Deref;

struct MyBox<T>(T);

impl<T> Deref for MyBox<T> {
    type Target = T;
    
    fn deref(&self) -> &T {
        &self.0
    }
}

fn deref_vs_subtyping() {
    let boxed = MyBox("hello");
    
    // Deref 强制转换: MyBox<T> → &T
    let s: &str = &boxed;
    
    // 这不是子类型! MyBox<T> 和 &T 没有子类型关系
    // 只是隐式调用 deref()
}
```

---

## 高级子类型

### Higher-Rank Trait Bounds (HRTB)

```rust
// for<'a> 表示对所有生命周期
trait HigherRank {
    fn method<'a>(&self, x: &'a str) -> &'a str;
}

// HRTB 在闭包中
fn hrtb_closure<F>(f: F)
where
    F: for<'a> Fn(&'a str) -> &'a str,
{
    println!("{}", f("test"));
}

fn hrtb_example() {
    hrtb_closure(|x| x); // OK: 对所有 'a 都成立
}
```

### 生命周期省略与子类型

```rust
// 省略前
fn explicit<'a, 'b>(x: &'a str, y: &'b str) -> &'a str
where
    'b: 'a,
{
    x
}

// 省略后
fn elided(x: &str, y: &str) -> &str {
    x // 编译器推断生命周期约束
}
```

### 关联类型与子类型

```rust
trait Container {
    type Item;
    fn get(&self) -> &Self::Item;
}

// 关联类型不支持型变 (不变)
fn associated_type_invariance<C1, C2>(c: C1) -> C2
where
    C1: Container<Item = &'static str>,
    C2: Container<Item = &'static str>,
{
    // c // 编译错误: C1 和 C2 不相关
    unimplemented!()
}
```

### 泛型型变

```rust
struct Wrapper<'a, T> {
    data: &'a T,
}

// T 协变, 'a 协变
fn generic_variance<'a, 'b, T, U>(w: Wrapper<'a, T>) -> Wrapper<'b, U>
where
    'a: 'b,
    T: 'static,
    U: 'static,
    T: Into<U>,
{
    // 如果 T <: U 且 'a <: 'b
    // 则 Wrapper<'a, T> <: Wrapper<'b, U>
    unimplemented!()
}
```

---

## 子类型健全性

### 类型健全性定理

**定理**: Rust 的子类型系统是健全的。

```text
如果 S <: T 且 Γ ⊢ e: S, 则 Γ ⊢ e: T
且运行时不会出现类型错误。
```

### 生命周期健全性

**定理**: 如果程序通过借用检查, 则不会出现悬垂引用。

```rust
// 反例: 不健全的子类型
/*
fn unsound<'a>(x: &'a str) -> &'static str {
    x // 编译错误: 不能将 &'a str 转为 &'static str
      // 'a 不是 'static 的子类型!
}
*/

// 健全: 只能反向转换
fn sound<'a>(x: &'static str) -> &'a str {
    x // OK: 'static <: 'a
}
```

### 型变健全性

**为什么 &mut T 对 T 必须不变?**

```rust
// 不健全的反例
fn unsound_mut_variance<'a>(
    longer: &mut &'static str,
    shorter: &mut &'a str,
) {
    // 假设 &mut &'static str <: &mut &'a str (如果协变)
    // std::mem::swap(longer, shorter); // 交换
    // 现在 longer 可能持有短生命周期引用!
    // let dangling: &'static str = *longer; // 悬垂!
}

// Rust 通过不变性阻止这种错误
fn sound_mut_invariance<'a>(
    longer: &mut &'static str,
    _shorter: &mut &'a str,
) {
    // std::mem::swap(longer, shorter); // 编译错误: 生命周期不匹配
}
```

---

## 实践应用

### 1. 灵活的 API 设计

```rust
// 使用生命周期子类型设计灵活 API
pub struct Config<'a> {
    pub host: &'a str,
    pub port: u16,
}

impl<'a> Config<'a> {
    // 接受任意生命周期
    pub fn new(host: &'a str, port: u16) -> Self {
        Config { host, port }
    }
    
    // 返回更长生命周期 (协变)
    pub fn host(&self) -> &'a str {
        self.host
    }
}

fn flexible_api() {
    let static_host: &'static str = "localhost";
    let config = Config::new(static_host, 8080);
    
    let host: &str = config.host(); // 'static <: 'a
}
```

### 2. Trait 对象的向上转型

```rust
trait Base {
    fn base_method(&self);
}

trait Derived: Base {
    fn derived_method(&self);
}

struct MyStruct;

impl Base for MyStruct {
    fn base_method(&self) {
        println!("Base");
    }
}

impl Derived for MyStruct {
    fn derived_method(&self) {
        println!("Derived");
    }
}

fn upcast(d: Box<dyn Derived>) -> Box<dyn Base> {
    d // 自动向上转型
}
```

### 3. 协变容器

```rust
// 利用协变设计灵活容器
struct Storage<'a, T> {
    items: Vec<&'a T>,
}

impl<'a, T> Storage<'a, T> {
    fn new() -> Self {
        Storage { items: Vec::new() }
    }
    
    fn add(&mut self, item: &'a T) {
        self.items.push(item);
    }
    
    // 返回更短生命周期 (协变)
    fn get(&self, index: usize) -> Option<&'a T> {
        self.items.get(index).copied()
    }
}

fn covariant_container() {
    let static_val: &'static str = "hello";
    let mut storage = Storage::new();
    storage.add(static_val);
    
    let val: &str = storage.get(0).unwrap(); // 协变
}
```

### 4. 高阶函数与逆变

```rust
// 利用逆变设计回调系统
struct EventHandler<T> {
    callback: Box<dyn Fn(&T)>,
}

impl<T> EventHandler<T> {
    fn new<F>(callback: F) -> Self
    where
        F: Fn(&T) + 'static,
    {
        EventHandler {
            callback: Box::new(callback),
        }
    }
    
    fn handle(&self, event: &T) {
        (self.callback)(event);
    }
}

fn contravariant_callback() {
    let handler = EventHandler::new(|s: &str| {
        println!("Event: {}", s);
    });
    
    handler.handle("test");
}
```

### 5. 零成本抽象与子类型

```rust
// 利用子类型实现零成本抽象
trait Processor {
    type Output;
    fn process(&self, input: &str) -> Self::Output;
}

struct UpperCase;
struct LowerCase;

impl Processor for UpperCase {
    type Output = String;
    
    fn process(&self, input: &str) -> String {
        input.to_uppercase()
    }
}

impl Processor for LowerCase {
    type Output = String;
    
    fn process(&self, input: &str) -> String {
        input.to_lowercase()
    }
}

// 泛型 + 子类型 = 零成本
fn generic_processor<P: Processor>(p: &P, input: &str) -> P::Output {
    p.process(input) // 单态化, 无虚拟调用
}
```

---

## 参考文献

### 子类型理论

1. **Cardelli, L.** (1984). "A Semantics of Multiple Inheritance"
2. **Mitchell, J.** (1984). "Coercion and Type Inference"
3. **Pierce, B.C.** (2002). "Types and Programming Languages" (Chapter 15: Subtyping)
4. **Abadi, M., & Cardelli, L.** (1996). "A Theory of Objects"

### 型变理论

1. **Liskov, B., & Wing, J.** (1994). "A Behavioral Notion of Subtyping"
2. **Kennedy, A., & Pierce, B.C.** (2007). "On Decidability of Nominal Subtyping with Variance"

### Rust 子类型

1. **The Rust Reference: Subtyping and Variance**
   <https://doc.rust-lang.org/reference/subtyping.html>
2. **Jung, R., et al.** (2017). "RustBelt: Securing the Foundations of the Rust Programming Language"
3. **Matsakis, N.** (2015). "Subtyping and Variance in Rust"
   <https://doc.rust-lang.org/nomicon/subtyping.html>

### 生命周期与子类型

1. **Reed, E.** (2015). "Patina: A Formalization of the Rust Programming Language"
2. **Weiss, A., et al.** (2019). "Oxide: The Essence of Rust"

---

## 总结

子类型论为 Rust 的生命周期系统和类型安全提供了理论基础:

| 概念 | 子类型论 | Rust 实现 |
|------|---------|----------|
| 子类型关系 | S <: T | 'static <: 'a |
| 协变 | F(S) <: F(T) | &'a T, `Box<T>` |
| 逆变 | F(T) <: F(S) | fn(&'a T) |
| 不变 | 无关系 | &mut T, `Cell<T>` |
| Liskov 替换 | 可替换性 | Trait 对象 |

**核心洞察**:

1. **生命周期 = 子类型**: 更长的生命周期是更小(更具体)的类型
2. **型变 = 安全性**: 型变规则确保引用安全
3. **不变性 = 防御**: 内部可变性必须不变以防止悬垂引用
4. **协变 = 灵活性**: 不可变结构可以协变以提供灵活API

**实践价值**:

- 理解为什么某些类型转换被允许或禁止
- 设计灵活且类型安全的 API
- 利用子类型实现零成本抽象
- 避免生命周期和型变相关的常见错误

**下一步**: 探索 [类型推断理论](./35_type_inference_theory.md) 了解 Rust 编译器如何自动推断类型。

---

*文档版本: 1.0*  
*最后更新: 2025-10-19*  
*Rust 版本: 1.90+*
