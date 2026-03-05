# 常量泛型与类型级计算

> 权威来源: Rust RFC 2000 (min_const_generics, adt_const_params)

---

## 目录

- [常量泛型与类型级计算](#常量泛型与类型级计算)
  - [目录](#目录)
  - [1. 概述](#1-概述)
    - [1.1 什么是常量泛型](#11-什么是常量泛型)
    - [1.2 为什么需要常量泛型](#12-为什么需要常量泛型)
    - [1.3 与泛型的关系](#13-与泛型的关系)
  - [2. 基础语法](#2-基础语法)
    - [2.1 声明常量泛型](#21-声明常量泛型)
    - [2.2 函数中的常量泛型](#22-函数中的常量泛型)
    - [2.3 多个常量泛型参数](#23-多个常量泛型参数)
    - [2.4 默认值（即将支持）](#24-默认值即将支持)
  - [3. 类型级编程](#3-类型级编程)
    - [3.1 类型作为计算](#31-类型作为计算)
    - [3.2 泛型特化](#32-泛型特化)
    - [3.3 递归类型定义](#33-递归类型定义)
  - [4. 可判定性分析](#4-可判定性分析)
    - [4.1 停机问题](#41-停机问题)
    - [4.2 Rust的解决方案](#42-rust的解决方案)
    - [4.3 可判定性分类](#43-可判定性分类)
    - [4.4 实践中的限制](#44-实践中的限制)
  - [5. 内存布局优化](#5-内存布局优化)
    - [5.1 静态大小优化](#51-静态大小优化)
    - [5.2 栈分配 vs 堆分配](#52-栈分配-vs-堆分配)
    - [5.3 SIMD优化](#53-simd优化)
  - [6. 高级模式](#6-高级模式)
    - [6.1 类型状态模式](#61-类型状态模式)
    - [6.2 编译期配置](#62-编译期配置)
    - [6.3 维度分析](#63-维度分析)
  - [7. 与依赖类型对比](#7-与依赖类型对比)
    - [7.1 依赖类型简介](#71-依赖类型简介)
    - [7.2 Rust常量泛型的限制](#72-rust常量泛型的限制)
    - [7.3 对比表](#73-对比表)
    - [7.4 为什么Rust选择受限设计](#74-为什么rust选择受限设计)
  - [8. 实践案例](#8-实践案例)
    - [8.1 固定大小环形缓冲](#81-固定大小环形缓冲)
    - [8.2 编译期解析器](#82-编译期解析器)
    - [8.3 单位系统](#83-单位系统)
  - [9. 限制与未来](#9-限制与未来)
    - [9.1 当前限制](#91-当前限制)
    - [9.2 即将支持的功能](#92-即将支持的功能)
    - [9.3 使用建议](#93-使用建议)
  - [总结](#总结)

---

## 1. 概述

### 1.1 什么是常量泛型

**常量泛型(Const Generics)** 允许类型由**常量值**参数化，而不仅仅是其他类型或生命周期。

```rust
// 类型由常量N参数化
struct Array<T, const N: usize> {
    data: [T; N],
}

// 使用
let arr: Array<i32, 5> = Array { data: [1, 2, 3, 4, 5] };
```

### 1.2 为什么需要常量泛型

**问题：固定大小数组的类型化**:

```rust
// 没有常量泛型时：需要为每个大小定义新类型
struct Array2<T>([T; 2]);
struct Array3<T>([T; 3]);
struct Array4<T>([T; 4]);
// ... 无限重复
```

**常量泛型解决方案**:

```rust
// 一个定义，无限大小
struct Array<T, const N: usize>([T; N]);
```

### 1.3 与泛型的关系

| 特性 | `类型泛型<T>` | `常量泛型<const N>` |
|------|-------------|-------------------|
| 参数化 | 类型 | 常量值 |
| 单态化 | 是 | 是 |
| 运行时开销 | 无 | 无 |
| 类型安全 | 编译期检查 | 编译期检查 |

---

## 2. 基础语法

### 2.1 声明常量泛型

**支持的常量类型**:

- 整数: `i8`, `i16`, `i32`, `i64`, `i128`, `isize`
- 无符号整数: `u8`, `u16`, `u32`, `u64`, `u128`, `usize`
- 字符: `char`
- 布尔: `bool`

```rust
// 结构体
struct Point<const DIM: usize> {
    coords: [f64; DIM],
}

// 枚举
enum Axis<const N: usize> {
    X,
    Y,
    Other([f64; N]),
}

// 类型别名
type Vector3 = Point<3>;
```

### 2.2 函数中的常量泛型

```rust
// 泛型函数
fn create_array<T: Default, const N: usize>() -> [T; N] {
    let mut arr: [T; N] = unsafe { std::mem::zeroed() };
    for i in 0..N {
        arr[i] = T::default();
    }
    arr
}

// 使用
let zeros: [i32; 5] = create_array::<i32, 5>();
```

### 2.3 多个常量泛型参数

```rust
struct Matrix<T, const ROWS: usize, const COLS: usize> {
    data: [[T; COLS]; ROWS],
}

impl<T: Default + Copy, const R: usize, const C: usize> Matrix<T, R, C> {
    fn new() -> Self {
        Self {
            data: [[T::default(); C]; R],
        }
    }

    fn shape(&self) -> (usize, usize) {
        (R, C)  // 编译期已知的大小
    }
}

// 3x4矩阵
let m: Matrix<f64, 3, 4> = Matrix::new();
```

### 2.4 默认值（即将支持）

```rust
// 目前不支持，但计划中
struct Buffer<T, const SIZE: usize = 1024> {
    data: [T; SIZE],
}

// 使用默认值
let buf: Buffer<u8> = Buffer { data: [0; 1024] };
// 显式指定
let buf: Buffer<u8, 2048> = Buffer { data: [0; 2048] };
```

---

## 3. 类型级编程

### 3.1 类型作为计算

常量泛型允许在**类型级别**进行计算：

```rust
// 类型级算术（编译期计算）
struct Add<const A: usize, const B: usize>;

// 实际值
const fn add<const A: usize, const B: usize>() -> usize {
    A + B
}

type Sum = Add<3, 5>;  // 类型表示 3 + 5
const RESULT: usize = add::<3, 5>();  // 值 8
```

### 3.2 泛型特化

基于常量值的特化（部分支持）：

```rust
// 通用实现
impl<T, const N: usize> Array<T, N> {
    fn len(&self) -> usize { N }
}

// 特定大小的优化实现
impl<T> Array<T, 0> {
    fn is_empty(&self) -> bool { true }
}

impl<T: Default + Copy> Array<T, 1> {
    fn singleton(value: T) -> Self {
        Self { data: [value] }
    }
}
```

### 3.3 递归类型定义

```rust
// 类型级链表（实验性）
struct Cons<const H: usize, T>(T);
struct Nil;

type List3 = Cons<1, Cons<2, Cons<3, Nil>>>;

// 计算长度（编译期）
const fn length<T>(_: &T) -> usize {
    std::mem::size_of::<T>()  // 间接计算
}
```

---

## 4. 可判定性分析

### 4.1 停机问题

常量求值涉及**停机问题**：

```rust
const fn compute() -> usize {
    // 这个函数会停机吗？
    loop {}  // 编译期无限循环
}

fn use_it<T, const N: usize>()
where
    [T; N]: Sized,
{
    // 使用N
}

// 尝试使用
use_it::<i32, { compute() }>();  // 编译会挂起！
```

### 4.2 Rust的解决方案

**策略1: 求值步骤限制**:

```text
默认限制: 1,000,000 步
可通过: RUST_CONST_EVAL_LIMIT 环境变量调整
```

**策略2: 禁止循环和递归（早期版本）**:

Rust 1.46+ 允许在const fn中使用循环，但有步骤限制。

**策略3: 类型系统限制**:

```rust
// 禁止复杂类型级递归
struct Bad<const N: usize>
where
    Self: Sized,  // 禁止递归定义
{
    data: [u8; N],
}
```

### 4.3 可判定性分类

| 特性 | 可判定性 | 说明 |
|------|----------|------|
| 简单常量 | ✅ 可判定 | 字面量、基本运算 |
| const fn | ⚠️ 近似 | 有步骤限制 |
| 类型级递归 | ❌ 不可判定 | 可能导致无限递归 |
| 通用停机 | ❌ 不可判定 | 停机问题不可解 |

### 4.4 实践中的限制

```rust
// 好的：简单表达式
struct Good<const N: usize>([u8; N * 2]);

// 坏的：复杂递归（可能导致编译器崩溃）
const fn fib<const N: usize>() -> usize {
    match N {
        0 | 1 => N,
        _ => fib::<{N - 1}>() + fib::<{N - 2}>(),
    }
}

// fib::<100>() 可能导致编译期栈溢出
```

---

## 5. 内存布局优化

### 5.1 静态大小优化

常量泛型使编译器知道确切大小：

```rust
struct Packet<const SIZE: usize> {
    header: [u8; 4],
    payload: [u8; SIZE],
    checksum: u32,
}

// Packet<256> 的大小编译期确定
// size = 4 + 256 + 4 = 264 字节
```

### 5.2 栈分配 vs 堆分配

```rust
// 小的数组：栈分配（高效）
struct SmallBuf([u8; 64]);

// 大的数组：可能需要在堆上分配
struct LargeBuf([u8; 1024 * 1024]);

// 使用常量泛型根据大小选择分配策略
trait Buffer<const N: usize> {
    fn new() -> Self;
}

// 小缓冲：内联存储
impl Buffer<64> for SmallBuf {
    fn new() -> Self { Self([0; 64]) }
}

// 大缓冲：Box分配
impl Buffer<{1024 * 1024}> for Box<[u8; 1024 * 1024]> {
    fn new() -> Self { Box::new([0; 1024 * 1024]) }
}
```

### 5.3 SIMD优化

```rust
// 根据大小选择SIMD宽度
struct SimdVec<T, const N: usize>([T; N]);

impl SimdVec<f32, 4> {
    // 使用SSE
    fn add(&self, other: &Self) -> Self {
        // 128-bit SIMD
    }
}

impl SimdVec<f32, 8> {
    // 使用AVX
    fn add(&self, other: &Self) -> Self {
        // 256-bit SIMD
    }
}
```

---

## 6. 高级模式

### 6.1 类型状态模式

```rust
// 编译期状态机
struct Connection<const STATE: ConnectionState>;

#[derive(Clone, Copy)]
struct ConnectionState(u8);
const DISCONNECTED: ConnectionState = ConnectionState(0);
const CONNECTING: ConnectionState = ConnectionState(1);
const CONNECTED: ConnectionState = ConnectionState(2);

// 只有DISCONNECTED状态可以connect
impl Connection<DISCONNECTED> {
    fn connect(self) -> Connection<CONNECTING> {
        // ...
        Connection
    }
}

// 只有CONNECTED状态可以send
impl Connection<CONNECTED> {
    fn send(&self, data: &[u8]) {
        // ...
    }
}
```

### 6.2 编译期配置

```rust
// 编译期特性开关
struct Features<const FLAGS: u32>;

const ENABLE_CACHE: u32 = 0b0001;
const ENABLE_LOG: u32 = 0b0010;
const ENABLE_DEBUG: u32 = 0b0100;

impl<const F: u32> Features<F> {
    const HAS_CACHE: bool = F & ENABLE_CACHE != 0;
    const HAS_LOG: bool = F & ENABLE_LOG != 0;

    fn maybe_cache(&self) {
        if Self::HAS_CACHE {
            // 编译期条件（可能单态化优化）
        }
    }
}

// 使用
type ProdFeatures = Features<ENABLE_CACHE | ENABLE_LOG>;
type DebugFeatures = Features<0b0111>;
```

### 6.3 维度分析

```rust
// 编译期单位检查
struct Quantity<T, const M: i32, const L: i32, const T: i32>(T);
// M: 质量维度, L: 长度维度, T: 时间维度

type Mass = Quantity<f64, 1, 0, 0>;
type Length = Quantity<f64, 0, 1, 0>;
type Time = Quantity<f64, 0, 0, 1>;
type Velocity = Quantity<f64, 0, 1, -1>;  // L/T
type Acceleration = Quantity<f64, 0, 1, -2>;  // L/T²

impl<const M1: i32, const L1: i32, const T1: i32>
    Quantity<f64, M1, L1, T1>
{
    fn new(value: f64) -> Self { Self(value) }

    fn value(&self) -> f64 { self.0 }
}

// 乘法：维度相加
impl<const M1: i32, const L1: i32, const T1: i32,
     const M2: i32, const L2: i32, const T2: i32>
    Mul<Quantity<f64, M2, L2, T2>> for Quantity<f64, M1, L1, T1>
{
    type Output = Quantity<f64, {M1 + M2}, {L1 + L2}, {T1 + T2}>;

    fn mul(self, rhs: Quantity<f64, M2, L2, T2>) -> Self::Output {
        Quantity(self.0 * rhs.0)
    }
}

// 使用
let distance = Length::new(100.0);
let time = Time::new(10.0);
let velocity: Velocity = distance / time;  // 编译期维度检查！
```

---

## 7. 与依赖类型对比

### 7.1 依赖类型简介

**依赖类型(Dependent Types)** 允许类型依赖于值：

```idris
-- Idris: 向量长度在类型中
Vect : Nat -> Type -> Type
Vect 0 a = Nil
Vect (S n) a = Cons a (Vect n a)

-- 安全的head函数
head : Vect (S n) a -> a  -- 只接受非空向量
```

### 7.2 Rust常量泛型的限制

```rust
// Rust: 可以表示大小，但不能依赖值进行类型分支
struct Vec<T, const N: usize>([T; N]);

// 不能这样：
// Vec 0 T = EmptyVec
// Vec n T = ConsVec T (Vec (n-1) T)
```

### 7.3 对比表

| 特性 | Rust常量泛型 | 依赖类型(Idris/Agda) |
|------|-------------|---------------------|
| 类型依赖值 | ✅ 有限支持 | ✅ 完全支持 |
| 类型级计算 | ⚠️ 受限 | ✅ 图灵完备 |
| 证明能力 | ❌ 无 | ✅ 可作为证明 |
| 编译期执行 | ⚠️ 有步骤限制 | ✅ 完全求值 |
| 学习曲线 | 中等 | 陡峭 |
| 工业应用 | ✅ 广泛 | ⚠️ 有限 |

### 7.4 为什么Rust选择受限设计

1. **可判定性**: 保持类型检查可判定
2. **编译时间**: 避免复杂类型级计算
3. **错误信息**: 更好的用户体验
4. **与现有代码兼容**: 渐进式采用

---

## 8. 实践案例

### 8.1 固定大小环形缓冲

```rust
pub struct RingBuffer<T, const N: usize> {
    buffer: [Option<T>; N],
    head: usize,
    tail: usize,
    count: usize,
}

impl<T: Default + Copy, const N: usize> RingBuffer<T, N> {
    pub fn new() -> Self {
        Self {
            buffer: [None; N],
            head: 0,
            tail: 0,
            count: 0,
        }
    }

    pub const fn capacity(&self) -> usize { N }

    pub fn push(&mut self, item: T) -> Result<(), T> {
        if self.count == N {
            return Err(item);  // 满
        }
        self.buffer[self.head] = Some(item);
        self.head = (self.head + 1) % N;
        self.count += 1;
        Ok(())
    }

    pub fn pop(&mut self) -> Option<T> {
        if self.count == 0 {
            return None;  // 空
        }
        let item = self.buffer[self.tail].take();
        self.tail = (self.tail + 1) % N;
        self.count -= 1;
        item
    }
}

// 使用
let mut buf: RingBuffer<i32, 16> = RingBuffer::new();
buf.push(1).unwrap();
```

### 8.2 编译期解析器

```rust
// 编译期正则表达式（简化示例）
struct RegexMatcher<const PATTERN: &'static str>;

impl<const P: &'static str> RegexMatcher<P> {
    const PATTERN: &'static str = P;

    fn is_match(&self, input: &str) -> bool {
        // 运行时匹配
        regex::Regex::new(P).unwrap().is_match(input)
    }
}

// 编译期已知的模式
type EmailMatcher = RegexMatcher<r"^\S+@\S+\.\S+$">;
type PhoneMatcher = RegexMatcher<r"^\d{11}$">;

let email = EmailMatcher;
assert!(email.is_match("test@example.com"));
```

### 8.3 单位系统

```rust
use std::ops::{Add, Sub, Mul, Div};

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Quantity<T, const M: i8, const L: i8, const T: i8>(pub T);

// 基本量
type Scalar<T> = Quantity<T, 0, 0, 0>;
type Mass<T> = Quantity<T, 1, 0, 0>;
type Length<T> = Quantity<T, 0, 1, 0>;
type Time<T> = Quantity<T, 0, 0, 1>;
type Velocity<T> = Quantity<T, 0, 1, -1>;
type Acceleration<T> = Quantity<T, 0, 1, -2>;
type Force<T> = Quantity<T, 1, 1, -2>;  // M·L/T²

// 算术运算保持维度正确
impl<T: Add<Output=T>, const M: i8, const L: i8, const T: i8>
    Add for Quantity<T, M, L, T>
{
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        Quantity(self.0 + rhs.0)
    }
}

impl<T: Mul<Output=T>, const M1: i8, const L1: i8, const T1: i8,
     const M2: i8, const L2: i8, const T2: i8>
    Mul<Quantity<T, M2, L2, T2>> for Quantity<T, M1, L1, T1>
{
    type Output = Quantity<T, {M1 + M2}, {L1 + L2}, {T1 + T2}>;
    fn mul(self, rhs: Quantity<T, M2, L2, T2>) -> Self::Output {
        Quantity(self.0 * rhs.0)
    }
}

// 牛顿第二定律：F = ma
fn calculate_force<T: Mul<Output=T>>(
    mass: Mass<T>,
    acceleration: Acceleration<T>
) -> Force<T::Output> {
    mass * acceleration
}

// 使用
let m = Mass(10.0_f64);  // 10 kg
let a = Acceleration(9.8);  // 9.8 m/s²
let f: Force<f64> = calculate_force(m, a);  // 98 N，编译期维度检查！
```

---

## 9. 限制与未来

### 9.1 当前限制

**1. 参数类型受限**:

```rust
// 目前只支持：整数、bool、char
struct Good<const N: usize>([u8; N]);

// 不支持：浮点数、字符串、自定义类型
// struct Bad<const S: String>;  // 错误！
// struct Bad<const F: f64>;     // 错误！
```

**2. 复杂表达式**:

```rust
// 简单的可以
fn simple<const N: usize>() -> [u8; N + 1] { ... }

// 复杂的类型操作不行
// fn complex<const N: usize>() -> Vec<[u8; N]> where N > 0 { ... }
```

**3. 泛型关联常量**:

```rust
trait Config {
    const SIZE: usize;
}

// 目前不能这样使用
// struct Buffer<T: Config>([u8; T::SIZE]);  // 错误！
```

### 9.2 即将支持的功能

**1. 更多常量类型** (adt_const_params)

```rust
// 未来可能支持
struct Config<const NAME: &'static str>;
struct Point<const LABEL: char>;
```

**2. 常量泛型表达式**:

```rust
// 更复杂的编译期计算
fn split<const N: usize>(arr: [u8; N * 2]) -> ([u8; N], [u8; N]) {
    // ...
}
```

**3. 默认参数值**:

```rust
struct Buffer<T, const N: usize = 1024> {
    data: [T; N],
}
```

### 9.3 使用建议

**应该使用**:

- 固定大小的数组/矩阵
- 编译期已知的配置
- 类型级状态机
- 内存布局优化

**避免使用**:

- 过度复杂的类型级计算
- 可能导致编译时间过长的递归
- 动态大小的场景（用Vec代替）

---

## 总结

常量泛型是Rust类型系统的强大扩展：

1. **类型安全**: 编译期检查数组大小
2. **零成本**: 无运行时开销
3. **表达力**: 支持类型级编程
4. **可判定性**: 受限但实用

尽管不如依赖类型强大，常量泛型在系统编程中提供了恰到好处的类型级抽象能力。
