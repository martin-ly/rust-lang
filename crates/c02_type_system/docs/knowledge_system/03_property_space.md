# 类型系统 - 属性空间

> **文档类型**: 📐 属性空间 | 📊 多维分析  
> **创建日期**: 2025-10-19  
> **Rust 版本**: 1.90+

---

## 目录

- [类型系统 - 属性空间](#类型系统---属性空间)
  - [目录](#目录)
  - [📋 文档概述](#-文档概述)
    - [属性空间的作用](#属性空间的作用)
  - [🎯 属性维度分类](#-属性维度分类)
  - [1️⃣ 类型维度 (Type Dimensions)](#1️⃣-类型维度-type-dimensions)
    - [1.1 大小属性 (Size Properties)](#11-大小属性-size-properties)
    - [1.2 布局属性 (Layout Properties)](#12-布局属性-layout-properties)
    - [1.3 对齐属性 (Alignment Properties)](#13-对齐属性-alignment-properties)
  - [2️⃣ 安全维度 (Safety Dimensions)](#2️⃣-安全维度-safety-dimensions)
    - [2.1 类型安全 (Type Safety)](#21-类型安全-type-safety)
    - [2.2 内存安全 (Memory Safety)](#22-内存安全-memory-safety)
    - [2.3 线程安全 (Thread Safety)](#23-线程安全-thread-safety)
  - [3️⃣ 性能维度 (Performance Dimensions)](#3️⃣-性能维度-performance-dimensions)
    - [3.1 编译时性能 (Compile-time Performance)](#31-编译时性能-compile-time-performance)
    - [3.2 运行时性能 (Runtime Performance)](#32-运行时性能-runtime-performance)
    - [3.3 内存性能 (Memory Performance)](#33-内存性能-memory-performance)
  - [4️⃣ 表达维度 (Expressiveness Dimensions)](#4️⃣-表达维度-expressiveness-dimensions)
    - [4.1 抽象能力 (Abstraction Capability)](#41-抽象能力-abstraction-capability)
    - [4.2 组合能力 (Composition Capability)](#42-组合能力-composition-capability)
    - [4.3 多态能力 (Polymorphism Capability)](#43-多态能力-polymorphism-capability)
  - [5️⃣ 工程维度 (Engineering Dimensions)](#5️⃣-工程维度-engineering-dimensions)
    - [5.1 可维护性 (Maintainability)](#51-可维护性-maintainability)
    - [5.2 可测试性 (Testability)](#52-可测试性-testability)
    - [5.3 可扩展性 (Extensibility)](#53-可扩展性-extensibility)
  - [📊 多维属性雷达图](#-多维属性雷达图)
    - [基本类型属性](#基本类型属性)
    - [泛型类型属性](#泛型类型属性)
    - [特征对象属性](#特征对象属性)
  - [🔬 属性对比分析](#-属性对比分析)
    - [静态分派 vs 动态分派](#静态分派-vs-动态分派)
    - [Copy vs Move vs Borrow](#copy-vs-move-vs-borrow)
    - [关联类型 vs GATs](#关联类型-vs-gats)
  - [💡 属性应用指南](#-属性应用指南)
    - [根据属性选择类型](#根据属性选择类型)
    - [根据属性优化设计](#根据属性优化设计)
  - [📚 参考资料](#-参考资料)
    - [Rust性能](#rust性能)
    - [类型系统](#类型系统)
    - [工程实践](#工程实践)

## 📋 文档概述

本文档定义 Rust 类型系统中各个概念的**多维属性空间**，提供定量和定性的分析框架。

### 属性空间的作用

1. **量化评估**: 对类型特性进行量化分析
2. **对比决策**: 多维度对比不同设计选择
3. **优化指导**: 基于属性进行性能优化
4. **权衡分析**: 理解不同选择的权衡(trade-offs)

---

## 🎯 属性维度分类

```text
属性空间 (Property Space)
├── 类型维度
│   ├── 大小 (Size)
│   ├── 布局 (Layout)
│   └── 对齐 (Alignment)
├── 安全维度
│   ├── 类型安全 (Type Safety)
│   ├── 内存安全 (Memory Safety)
│   └── 线程安全 (Thread Safety)
├── 性能维度
│   ├── 编译时性能 (Compile-time)
│   ├── 运行时性能 (Runtime)
│   └── 内存性能 (Memory)
├── 表达维度
│   ├── 抽象能力 (Abstraction)
│   ├── 组合能力 (Composition)
│   └── 多态能力 (Polymorphism)
└── 工程维度
    ├── 可维护性 (Maintainability)
    ├── 可测试性 (Testability)
    └── 可扩展性 (Extensibility)
```

---

## 1️⃣ 类型维度 (Type Dimensions)

### 1.1 大小属性 (Size Properties)

**属性定义**:

| 属性 | 定义 | 度量单位 |
|------|------|---------|
| **编译时大小** | `size_of::<T>()` 是否在编译时已知 | Boolean (Sized/!Sized) |
| **实际大小** | 类型占用的字节数 | Bytes |
| **对齐要求** | `align_of::<T>()` | Bytes (power of 2) |

**类型分类**:

| 类型 | 编译时大小 | 实际大小示例 | Sized Trait |
|------|-----------|------------|-------------|
| `i32` | 已知 | 4 bytes | ✓ |
| `bool` | 已知 | 1 byte | ✓ |
| `[i32; 5]` | 已知 | 20 bytes | ✓ |
| `[i32]` | 未知 | 运行时确定 | ✗ (DST) |
| `str` | 未知 | 运行时确定 | ✗ (DST) |
| `dyn Trait` | 未知 | 运行时确定 | ✗ (DST) |
| `()` | 已知 | 0 bytes | ✓ (ZST) |
| `PhantomData<T>` | 已知 | 0 bytes | ✓ (ZST) |

**示例分析**:

```rust
// 大小属性示例
use std::mem::{size_of, align_of};

// Sized类型
assert_eq!(size_of::<i32>(), 4);
assert_eq!(size_of::<[i32; 5]>(), 20);

// 零大小类型 (ZST)
assert_eq!(size_of::<()>(), 0);
assert_eq!(size_of::<PhantomData<i32>>(), 0);

// DST (通过指针访问)
let slice: &[i32] = &[1, 2, 3];
assert_eq!(size_of_val(slice), 12);  // 3 * 4 bytes

// 胖指针大小
assert_eq!(size_of::<&[i32]>(), 16);  // 指针 + 长度
assert_eq!(size_of::<&dyn Display>(), 16);  // 指针 + vtable
```

### 1.2 布局属性 (Layout Properties)

**属性定义**:

| 属性 | 定义 | 可能值 |
|------|------|--------|
| **内存布局** | 字段在内存中的排列方式 | Rust默认 / `#[repr(C)]` / `#[repr(packed)]` |
| **填充字节** | 对齐导致的额外字节 | 0-N bytes |
| **字段顺序** | 字段在内存中的顺序 | 编译器优化 / 声明顺序 |

**布局类型**:

```rust
// Rust默认布局（编译器可优化）
struct DefaultLayout {
    a: u8,   // 可能被重排序
    b: u32,
    c: u16,
}

// #[repr(C)] - C兼容布局
#[repr(C)]
struct CLayout {
    a: u8,   // 声明顺序
    b: u32,  // 有填充字节
    c: u16,
}

// #[repr(packed)] - 紧凑布局
#[repr(packed)]
struct PackedLayout {
    a: u8,   // 无填充字节
    b: u32,  // 可能未对齐
    c: u16,
}

// 布局分析
println!("Default: {} bytes", size_of::<DefaultLayout>());
println!("C:       {} bytes", size_of::<CLayout>());
println!("Packed:  {} bytes", size_of::<PackedLayout>());
```

### 1.3 对齐属性 (Alignment Properties)

**属性定义**:

| 类型 | 对齐要求 | 说明 |
|------|---------|------|
| `u8`, `i8`, `bool` | 1 byte | 最小对齐 |
| `u16`, `i16` | 2 bytes | |
| `u32`, `i32`, `f32` | 4 bytes | |
| `u64`, `i64`, `f64` | 8 bytes | |
| `u128`, `i128` | 16 bytes (平台相关) | |
| 结构体 | max(字段对齐) | 最大字段对齐 |
| 数组 `[T; N]` | `align_of::<T>()` | 元素类型对齐 |

**对齐影响**:

```rust
// 对齐影响大小
struct Aligned {
    a: u8,    // 1 byte
    // 3 bytes padding
    b: u32,   // 4 bytes
    c: u8,    // 1 byte
    // 3 bytes padding
}
// 总大小: 12 bytes (不是 6 bytes)

// 字段重排可以减少填充
struct Optimized {
    b: u32,   // 4 bytes
    a: u8,    // 1 byte
    c: u8,    // 1 byte
    // 2 bytes padding
}
// 总大小: 8 bytes
```

---

## 2️⃣ 安全维度 (Safety Dimensions)

### 2.1 类型安全 (Type Safety)

**属性量化**:

| 维度 | 度量 | 评分 (1-5) |
|------|------|-----------|
| **静态类型检查** | 编译时类型验证 | 5 (完全) |
| **强类型** | 无隐式类型转换 | 5 (完全) |
| **类型推断** | 自动推断程度 | 4 (高) |
| **泛型类型安全** | 泛型参数检查 | 5 (完全) |

**类型安全保证**:

```rust
// 编译时类型检查
let x: i32 = 5;
// let y: String = x;  // 编译错误：类型不匹配

// 无隐式转换
let a: i32 = 5;
let b: i64 = 10;
// let c = a + b;  // 编译错误：类型不匹配

// 泛型类型安全
fn add<T: std::ops::Add<Output = T>>(a: T, b: T) -> T {
    a + b
}
// add(5, "hello");  // 编译错误：类型不匹配
```

### 2.2 内存安全 (Memory Safety)

**属性量化**:

| 维度 | 检查时机 | 成本 | 保证程度 |
|------|---------|------|---------|
| **无悬垂指针** | 编译时 | 零成本 | 100% |
| **无数据竞争** | 编译时 | 零成本 | 100% |
| **无缓冲区溢出** | 编译时+运行时 | 边界检查 | 100% |
| **无use-after-free** | 编译时 | 零成本 | 100% |
| **无double-free** | 编译时 | 零成本 | 100% |

**内存安全机制**:

```rust
// 防止悬垂指针
fn no_dangling() -> &'static str {
    // let s = String::from("hello");
    // &s  // 编译错误：返回对局部变量的引用
    "valid static"
}

// 防止use-after-free
let s = String::from("hello");
drop(s);
// println!("{}", s);  // 编译错误：use after move

// 防止数据竞争
let mut data = vec![1, 2, 3];
// let r1 = &mut data;
// let r2 = &mut data;  // 编译错误：不能有多个可变引用

// 边界检查
let arr = [1, 2, 3];
// let x = arr[10];  // panic!（运行时检查）
```

### 2.3 线程安全 (Thread Safety)

**属性矩阵**:

| 类型 | Send | Sync | 说明 |
|------|------|------|------|
| `i32` | ✓ | ✓ | 基本类型 |
| `String` | ✓ | ✓ | 可发送和共享 |
| `Rc<T>` | ✗ | ✗ | 非线程安全引用计数 |
| `Arc<T>` | ✓ (if T: Send) | ✓ (if T: Sync) | 线程安全引用计数 |
| `Cell<T>` | ✓ (if T: Send) | ✗ | 内部可变性，非Sync |
| `RefCell<T>` | ✓ (if T: Send) | ✗ | 运行时借用检查，非Sync |
| `Mutex<T>` | ✓ (if T: Send) | ✓ (if T: Send) | 互斥锁保护 |
| `RwLock<T>` | ✓ (if T: Send) | ✓ (if T: Send + Sync) | 读写锁保护 |

**线程安全示例**:

```rust
use std::sync::{Arc, Mutex};
use std::thread;

// Send + Sync: 可以跨线程传递和共享
fn thread_safe<T: Send + Sync + 'static>(data: Arc<T>) {
    thread::spawn(move || {
        // 可以在新线程中使用
    });
}

// Mutex提供内部可变性和线程安全
let counter = Arc::new(Mutex::new(0));
let handles: Vec<_> = (0..10)
    .map(|_| {
        let counter = Arc::clone(&counter);
        thread::spawn(move || {
            let mut num = counter.lock().unwrap();
            *num += 1;
        })
    })
    .collect();
```

---

## 3️⃣ 性能维度 (Performance Dimensions)

### 3.1 编译时性能 (Compile-time Performance)

**属性量化**:

| 特性 | 编译时成本 | 影响因素 |
|------|-----------|---------|
| **泛型单态化** | 高 | 泛型实例数量 |
| **类型推断** | 中 | 类型约束复杂度 |
| **宏展开** | 高 | 宏复杂度 |
| **借用检查** | 中-高 | 引用复杂度 |
| **LLVM优化** | 高 | 优化级别 |

**编译时成本对比**:

```rust
// 低编译成本：具体类型
fn add_i32(a: i32, b: i32) -> i32 {
    a + b
}

// 高编译成本：泛型（每个实例化都编译一次）
fn add_generic<T: std::ops::Add<Output = T>>(a: T, b: T) -> T {
    a + b
}
// add_generic(1i32, 2i32);    // 编译 i32 版本
// add_generic(1.0f64, 2.0f64); // 编译 f64 版本
// ... 每个类型一个版本

// 更高编译成本：复杂泛型约束
fn complex<T, U, V>(t: T, u: U) -> V
where
    T: Clone + Debug + Send + Sync,
    U: Into<V> + Display,
    V: From<U> + Default,
{
    u.into()
}
```

### 3.2 运行时性能 (Runtime Performance)

**性能对比表**:

| 特性 | 运行时成本 | 零成本抽象 | 说明 |
|------|-----------|-----------|------|
| **泛型（静态分派）** | 无 | ✓ | 单态化，内联优化 |
| **特征对象（动态分派）** | 虚表查找 | ✗ | 运行时多态 |
| **借用检查** | 无 | ✓ | 编译时检查 |
| **Option/Result** | 无 | ✓ | 编译器优化 |
| **迭代器** | 无 | ✓ | 迭代器融合 |
| **智能指针** | 引用计数 | 部分 | Box无成本，Rc/Arc有成本 |

**零成本抽象示例**:

```rust
// 静态分派：零成本
fn process<T: Display>(value: T) {
    println!("{}", value);
}
// 编译后与直接调用相同

// 动态分派：有运行时成本
fn process_dyn(value: &dyn Display) {
    println!("{}", value);  // 虚表查找
}

// 迭代器：零成本抽象
let sum: i32 = (1..100)
    .filter(|x| x % 2 == 0)
    .map(|x| x * 2)
    .sum();
// 编译后与手写循环性能相同

// 手写等价代码
let mut sum = 0;
for x in 1..100 {
    if x % 2 == 0 {
        sum += x * 2;
    }
}
```

### 3.3 内存性能 (Memory Performance)

**内存属性**:

| 类型 | 栈分配 | 堆分配 | 内存开销 | 缓存友好性 |
|------|-------|-------|---------|----------|
| `i32` | ✓ | ✗ | 4 bytes | 高 |
| `[i32; 100]` | ✓ | ✗ | 400 bytes | 高 |
| `Vec<i32>` | 部分 | ✓ | 24 + capacity * 4 bytes | 中 |
| `Box<i32>` | 指针 | ✓ | 8 + 4 bytes | 低 |
| `Rc<i32>` | 指针 | ✓ | 8 + 4 + 8 bytes (引用计数) | 低 |
| `Arc<i32>` | 指针 | ✓ | 8 + 4 + 16 bytes (原子计数) | 低 |

**内存布局优化**:

```rust
// 栈分配：高性能
fn stack_allocation() {
    let x = [0; 1000];  // 栈分配
    // 快速，但栈空间有限
}

// 堆分配：灵活但较慢
fn heap_allocation() {
    let x = vec![0; 1000000];  // 堆分配
    // 慢但可以分配大空间
}

// 内联数组 vs Vec
struct InlineArray {
    data: [i32; 100],  // 400 bytes 栈
}

struct HeapVector {
    data: Vec<i32>,  // 24 bytes 栈 + 堆
}
```

---

## 4️⃣ 表达维度 (Expressiveness Dimensions)

### 4.1 抽象能力 (Abstraction Capability)

**抽象层次**:

| 抽象机制 | 抽象能力 | 性能成本 | 类型安全 |
|---------|---------|---------|---------|
| **函数** | 基础 | 无（内联） | 完全 |
| **泛型** | 高 | 无（单态化） | 完全 |
| **特征** | 高 | 无（静态分派） | 完全 |
| **特征对象** | 高 | 虚表查找 | 完全 |
| **GATs** | 很高 | 无（单态化） | 完全 |
| **宏** | 最高 | 编译时 | 有限 |

**抽象能力示例**:

```rust
// 低抽象：具体类型
fn add_i32(a: i32, b: i32) -> i32 {
    a + b
}

// 中抽象：泛型
fn add<T: std::ops::Add<Output = T>>(a: T, b: T) -> T {
    a + b
}

// 高抽象：特征
trait Addable {
    type Output;
    fn add(self, other: Self) -> Self::Output;
}

// 很高抽象：GATs
trait Container {
    type Item<'a> where Self: 'a;
    fn get<'a>(&'a self) -> Option<Self::Item<'a>>;
}
```

### 4.2 组合能力 (Composition Capability)

**组合模式**:

| 模式 | 组合方式 | 灵活性 | 示例 |
|------|---------|-------|------|
| **结构体组合** | 字段组合 | 低 | `struct Point { x: f64, y: f64 }` |
| **枚举组合** | 变体组合 | 中 | `enum Option<T> { Some(T), None }` |
| **特征组合** | 特征边界 | 高 | `T: Display + Clone` |
| **高阶类型** | 类型构造器 | 很高 | `F: Fn(T) -> U` |

**组合示例**:

```rust
// 特征组合
fn process<T: Display + Clone + Send>(value: T) {
    // T 组合了三个特征的能力
}

// 类型组合
struct Composite<T, U> {
    first: T,
    second: U,
}

// 实现组合
impl<T: Display, U: Display> Display for Composite<T, U> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "({}, {})", self.first, self.second)
    }
}
```

### 4.3 多态能力 (Polymorphism Capability)

**多态类型**:

| 多态类型 | 实现方式 | 性能 | 灵活性 |
|---------|---------|------|-------|
| **参数多态** | 泛型 | 高（单态化） | 高 |
| **Ad-hoc多态** | 特征重载 | 高（静态分派） | 高 |
| **子类型多态** | 特征对象 | 中（虚表） | 很高 |
| **行多态** | 结构体 | 高 | 中 |

**多态示例**:

```rust
// 参数多态
fn identity<T>(x: T) -> T { x }

// Ad-hoc多态（特征重载）
trait Display {
    fn display(&self) -> String;
}
impl Display for i32 { /* ... */ }
impl Display for String { /* ... */ }

// 子类型多态（特征对象）
let shapes: Vec<Box<dyn Draw>> = vec![
    Box::new(Circle),
    Box::new(Square),
];
```

---

## 5️⃣ 工程维度 (Engineering Dimensions)

### 5.1 可维护性 (Maintainability)

**可维护性指标**:

| 维度 | 度量 | 影响因素 |
|------|------|---------|
| **可读性** | 代码清晰度 | 类型标注、命名、文档 |
| **可修改性** | 修改难度 | 耦合度、抽象层次 |
| **可理解性** | 理解复杂度 | 类型复杂度、泛型嵌套 |

**可维护性对比**:

```rust
// 高可维护性：清晰的类型和接口
struct User {
    name: String,
    email: String,
}

impl User {
    fn new(name: String, email: String) -> Self {
        User { name, email }
    }
    
    fn display(&self) -> String {
        format!("{} <{}>", self.name, self.email)
    }
}

// 低可维护性：复杂的泛型嵌套
type Complex<'a, T, U, F> = 
    Box<dyn Fn(&'a T) -> Result<U, Box<dyn Error>> + F>;
```

### 5.2 可测试性 (Testability)

**可测试性属性**:

| 特性 | 可测试性 | 测试策略 |
|------|---------|---------|
| **泛型函数** | 高 | 多种类型测试 |
| **特征** | 很高 | Mock实现 |
| **纯函数** | 最高 | 单元测试 |
| **副作用函数** | 低 | 集成测试 |

**可测试设计**:

```rust
// 高可测试性：特征抽象
trait DataStore {
    fn get(&self, key: &str) -> Option<String>;
    fn set(&mut self, key: &str, value: String);
}

struct RealStore { /* ... */ }
impl DataStore for RealStore { /* ... */ }

// 测试用Mock
struct MockStore {
    data: HashMap<String, String>,
}
impl DataStore for MockStore { /* ... */ }

// 可以用Mock轻松测试
fn process_data<S: DataStore>(store: &mut S) {
    store.set("key", "value".to_string());
}

#[test]
fn test_process() {
    let mut mock = MockStore::new();
    process_data(&mut mock);
    assert_eq!(mock.get("key"), Some("value".to_string()));
}
```

### 5.3 可扩展性 (Extensibility)

**可扩展性模式**:

| 模式 | 扩展方式 | 灵活性 | 侵入性 |
|------|---------|-------|-------|
| **特征扩展** | 为类型实现新特征 | 高 | 无 |
| **泛型参数** | 添加类型参数 | 中 | 中 |
| **关联类型** | 扩展特征定义 | 高 | 低 |
| **枚举变体** | 添加新变体 | 低 | 高（破坏性） |

**可扩展设计**:

```rust
// 可扩展：特征系统
trait Drawable {
    fn draw(&self);
}

// 可以为任何类型实现Drawable，无需修改原类型
struct Circle;
impl Drawable for Circle {
    fn draw(&self) { println!("Drawing circle"); }
}

struct Square;
impl Drawable for Square {
    fn draw(&self) { println!("Drawing square"); }
}

// 可扩展：泛型容器
struct Container<T> {
    items: Vec<T>,
}

impl<T> Container<T> {
    fn new() -> Self {
        Container { items: Vec::new() }
    }
    
    fn add(&mut self, item: T) {
        self.items.push(item);
    }
}

// 可以通过特征扩展功能，无需修改Container
trait Filterable<T> {
    fn filter<F: Fn(&T) -> bool>(&self, predicate: F) -> Vec<&T>;
}

impl<T> Filterable<T> for Container<T> {
    fn filter<F: Fn(&T) -> bool>(&self, predicate: F) -> Vec<&T> {
        self.items.iter().filter(|item| predicate(item)).collect()
    }
}
```

---

## 📊 多维属性雷达图

### 基本类型属性

```text
基本类型 (i32, f64, bool, char)

         类型安全 5
              |
        4.5  / \  4
           /     \
      编译 /       \ 运行
      性能 5-------5 性能
           \       /
            \     /
             \   /
         0.5  \ /  0
        复杂度 1 内存占用 0.5
```

**属性评分**:

- 类型安全: 5/5 (完全静态检查)
- 内存安全: 5/5 (无指针，Copy语义)
- 编译性能: 5/5 (简单类型)
- 运行性能: 5/5 (直接操作)
- 内存占用: 5/5 (固定小尺寸)
- 表达能力: 2/5 (具体类型)
- 可维护性: 5/5 (简单直观)
- 复杂度: 1/5 (极简单)

### 泛型类型属性

```text
泛型类型 (Vec<T>, Option<T>)

         类型安全 5
              |
        3    / \  4.5
           /     \
      编译 /       \ 运行
      性能 3-------5 性能
           \       /
            \     /
             \   /
         3   \ /  3
        复杂度 3 表达能力 5
```

**属性评分**:

- 类型安全: 5/5 (泛型参数检查)
- 编译性能: 3/5 (单态化成本)
- 运行性能: 5/5 (零成本抽象)
- 表达能力: 5/5 (高度抽象)
- 复杂度: 3/5 (中等复杂)
- 可维护性: 4/5 (清晰的抽象)

### 特征对象属性

```text
特征对象 (Box<dyn Trait>)

         类型安全 5
              |
        2    / \  3
           /     \
      编译 /       \ 运行
      性能 4-------3 性能
           \       /
            \     /
             \   /
         4   \ /  5
        灵活性 5 复杂度 4
```

**属性评分**:

- 类型安全: 5/5 (类型擦除但安全)
- 编译性能: 4/5 (无单态化)
- 运行性能: 3/5 (虚表查找)
- 灵活性: 5/5 (动态分派)
- 复杂度: 4/5 (对象安全规则)
- 表达能力: 5/5 (运行时多态)

---

## 🔬 属性对比分析

### 静态分派 vs 动态分派

| 属性维度 | 静态分派 (泛型) | 动态分派 (trait object) |
|---------|---------------|----------------------|
| **编译时间** | 慢（单态化） | 快（无单态化） |
| **二进制大小** | 大（每个类型一份代码） | 小（共享代码） |
| **运行时性能** | 快（直接调用+内联） | 慢（虚表查找） |
| **内存占用** | 正常指针（8 bytes） | 胖指针（16 bytes） |
| **灵活性** | 编译时确定 | 运行时确定 |
| **类型擦除** | 否 | 是 |

**选择指南**:

```rust
// 使用静态分派（泛型）当：
// - 性能关键
// - 类型在编译时已知
// - 需要内联优化
fn process<T: Display>(value: T) {
    println!("{}", value);
}

// 使用动态分派（特征对象）当：
// - 需要运行时多态
// - 减小二进制大小
// - 需要存储不同类型
let shapes: Vec<Box<dyn Draw>> = vec![
    Box::new(Circle),
    Box::new(Square),
];
```

### Copy vs Move vs Borrow

| 维度 | Copy | Move | Borrow |
|------|------|------|--------|
| **所有权** | 复制所有权 | 转移所有权 | 临时借用 |
| **性能** | 快（小类型） | 零成本 | 零成本 |
| **内存** | 复制数据 | 无复制 | 无复制 |
| **使用后原值** | 仍可用 | 不可用 | 可用（借用结束后） |
| **适用类型** | 基本类型、小结构体 | 所有非Copy类型 | 所有类型 |
| **生命周期** | 无关 | 无关 | 有约束 |

**选择指南**:

```rust
// Copy: 小型、简单类型
#[derive(Copy, Clone)]
struct Point {
    x: i32,
    y: i32,
}

// Move: 拥有堆数据的类型
let s1 = String::from("hello");
let s2 = s1;  // s1 moved

// Borrow: 临时访问
fn print(s: &String) {  // 借用
    println!("{}", s);
}
let s = String::from("hello");
print(&s);  // s 仍可用
```

### 关联类型 vs GATs

| 维度 | Associated Types | GATs (Generic Associated Types) |
|------|-----------------|--------------------------------|
| **参数化** | 无参数 | 带类型/生命周期参数 |
| **表达能力** | 中 | 高 |
| **复杂度** | 低 | 高 |
| **编译支持** | Rust 1.0+ | Rust 1.65+ |
| **使用场景** | 简单关联 | 高阶类型、Lending Iterator |

**对比示例**:

```rust
// 关联类型：简单但有限
trait Iterator {
    type Item;
    fn next(&mut self) -> Option<Self::Item>;
}

// GATs：复杂但强大
trait LendingIterator {
    type Item<'a> where Self: 'a;
    fn next<'a>(&'a mut self) -> Option<Self::Item<'a>>;
}

// GATs可以表达借用迭代器
impl LendingIterator for VecDeque<String> {
    type Item<'a> = &'a String;
    
    fn next<'a>(&'a mut self) -> Option<Self::Item<'a>> {
        self.front()
    }
}
```

---

## 💡 属性应用指南

### 根据属性选择类型

**性能优先**:

```rust
// 使用栈分配、Copy类型
struct FastPoint {
    x: i32,
    y: i32,
}

// 使用数组而非Vec（已知大小时）
let data: [i32; 100] = [0; 100];

// 使用静态分派而非动态分派
fn process<T: Display>(value: T) { /* ... */ }
```

**灵活性优先**:

```rust
// 使用特征对象实现运行时多态
let plugins: Vec<Box<dyn Plugin>> = vec![
    Box::new(PluginA),
    Box::new(PluginB),
];

// 使用枚举实现封闭的变体
enum Message {
    Text(String),
    Image(Vec<u8>),
    Video { url: String, duration: u32 },
}
```

**安全性优先**:

```rust
// 使用所有权避免生命周期问题
struct Owner {
    data: String,  // 拥有数据
}

// 使用智能指针管理共享
use std::sync::Arc;
let shared = Arc::new(expensive_data);
```

### 根据属性优化设计

**编译时优化**:

```rust
// 使用const泛型避免运行时检查
struct Buffer<const N: usize> {
    data: [u8; N],
}

// 使用零大小类型作为标记
struct Initialized;
struct Uninitialized;

struct State<S> {
    _marker: PhantomData<S>,
}
```

**运行时优化**:

```rust
// 使用内联优化小函数
#[inline(always)]
fn add(a: i32, b: i32) -> i32 {
    a + b
}

// 使用迭代器而非手写循环
let sum: i32 = data.iter().filter(|&&x| x > 0).sum();
```

**内存优化**:

```rust
// 字段重排减少填充
struct Optimized {
    large: u64,   // 8 bytes
    medium: u32,  // 4 bytes
    small: u8,    // 1 byte
    tiny: bool,   // 1 byte
}  // 16 bytes (vs 24 if not ordered)

// 使用Cow避免不必要的克隆
use std::borrow::Cow;
fn process(s: Cow<str>) {
    // 只在需要时克隆
}
```

---

## 📚 参考资料

### Rust性能

- [The Rust Performance Book](https://nnethercote.github.io/perf-book/)
- [Rust Compiler Performance](https://doc.rust-lang.org/nightly/cargo/reference/profiles.html)

### 类型系统

- [Rust Reference - Type System](https://doc.rust-lang.org/reference/types.html)
- [Rust Nomicon - Exotic Sizes](https://doc.rust-lang.org/nomicon/exotic-sizes.html)

### 工程实践

- [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)
- [Rust Design Patterns](https://rust-unofficial.github.io/patterns/)

---

**文档维护**: Rust 学习社区  
**更新频率**: 跟随Rust版本更新  
**文档版本**: v1.0  
**Rust 版本**: 1.90+  
**最后更新**: 2025-10-19
