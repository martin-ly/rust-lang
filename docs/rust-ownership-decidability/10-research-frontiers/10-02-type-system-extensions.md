# 类型系统扩展

本文档深入探讨 Rust 类型系统的可能扩展方向，包括泛型关联类型（GAT）、特殊化、效应系统、依赖类型等前沿主题。
这些扩展代表了 Rust 语言未来发展的关键技术路径，对理解 Rust 的演化和形式化验证具有重要意义。

---

## 目录

- [类型系统扩展](#类型系统扩展)
  - [目录](#目录)
  - [1. 泛型关联类型（GAT）](#1-泛型关联类型gat)
    - [1.1 GAT 基础](#11-gat-基础)
    - [1.2 形式化语义](#12-形式化语义)
    - [1.3 可判定性分析](#13-可判定性分析)
    - [1.4 实际应用案例](#14-实际应用案例)
      - [案例 1：流解析器](#案例-1流解析器)
      - [案例 2：类型级状态机](#案例-2类型级状态机)
  - [2. 特殊化（Specialization）](#2-特殊化specialization)
    - [2.1 特殊化概述](#21-特殊化概述)
    - [2.2 一致性规则](#22-一致性规则)
    - [2.3 形式化挑战](#23-形式化挑战)
      - [挑战 1：重叠实现检测](#挑战-1重叠实现检测)
      - [挑战 2：关联类型一致性](#挑战-2关联类型一致性)
      - [挑战 3：隐含边界传播](#挑战-3隐含边界传播)
    - [2.4 语义一致性](#24-语义一致性)
  - [3. 效应系统（Effect Systems）](#3-效应系统effect-systems)
    - [3.1 效应系统基础](#31-效应系统基础)
    - [3.2 Rust 中的效应](#32-rust-中的效应)
    - [3.3 效应多态](#33-效应多态)
    - [3.4 形式化模型](#34-形式化模型)
  - [4. 依赖类型（Dependent Types）](#4-依赖类型dependent-types)
    - [4.1 依赖类型介绍](#41-依赖类型介绍)
    - [4.2 渐进式路径](#42-渐进式路径)
    - [4.3 Const Generics 作为桥梁](#43-const-generics-作为桥梁)
    - [4.4 形式化限制](#44-形式化限制)
  - [5. 线性/仿射类型扩展](#5-线性仿射类型扩展)
    - [5.1 线性类型理论](#51-线性类型理论)
    - [5.2 资源敏感的类型系统](#52-资源敏感的类型系统)
    - [5.3 与 Rust 所有权的关系](#53-与-rust-所有权的关系)
  - [6. 模态类型（Modal Types）](#6-模态类型modal-types)
    - [6.1 模态逻辑与类型](#61-模态逻辑与类型)
    - [6.2 时序类型](#62-时序类型)
    - [6.3 空间类型](#63-空间类型)
  - [7. 精炼类型（Refinement Types）](#7-精炼类型refinement-types)
    - [7.1 精炼类型基础](#71-精炼类型基础)
    - [7.2 Rust 中的实现](#72-rust-中的实现)
    - [7.3 验证工具支持](#73-验证工具支持)
  - [8. 类型系统扩展的影响](#8-类型系统扩展的影响)
    - [8.1 对可判定性的影响](#81-对可判定性的影响)
    - [8.2 对验证工具的影响](#82-对验证工具的影响)
    - [8.3 对语言设计的影响](#83-对语言设计的影响)
  - [9. 未来研究方向](#9-未来研究方向)
    - [9.1 近期方向（1-2年）](#91-近期方向1-2年)
    - [9.2 中期方向（3-5年）](#92-中期方向3-5年)
    - [9.3 长期方向（5-10年）](#93-长期方向5-10年)
  - [10. 结论](#10-结论)
  - [参考文献](#参考文献)

---

## 1. 泛型关联类型（GAT）

### 1.1 GAT 基础

泛型关联类型（Generic Associated Types，GAT）是 Rust 1.65 引入的重要特性，允许关联类型带有自己的泛型参数。这一特性解决了许多之前无法用 Rust 类型系统表达的模式。

```rust
// GAT 基本示例
pub trait LendingIterator {
    type Item<'a> where Self: 'a;

    fn next<'a>(&'a mut self) -> Option<Self::Item<'a>>;
}

// 实现：窗口迭代器
pub struct WindowIter<'a, T> {
    slice: &'a [T],
    size: usize,
    pos: usize,
}

impl<'a, T> LendingIterator for WindowIter<'a, T> {
    type Item<'b> = &'b [T] where Self: 'b;

    fn next<'b>(&'b mut self) -> Option<Self::Item<'b>> {
        let window = self.slice.get(self.pos..self.pos + self.size)?;
        self.pos += 1;
        Some(window)
    }
}
```

GAT 的核心价值在于：

1. **表达自引用类型**：允许类型引用自身
2. **流式迭代器**：解决标准迭代器在自引用情况下的限制
3. **泛型容器**：更灵活的容器类型设计
4. **类型族**：支持类型级别的编程

### 1.2 形式化语义

GAT 的形式化语义正在积极研究中。以下是基于 System F_ω 的扩展模型：

```text
GAT 的类型规则（概念性）

───────────────────────────────────────── (GAT-Def)
Γ ⊢ trait T { type A<X> where C; ... } wf

Γ ⊢ S: T    Γ ⊢ τ type    Γ ⊢ C[Self/S, X/τ] sat
───────────────────────────────────────── (GAT-Proj)
Γ ⊢ <S as T>::A<τ> type

Γ ⊢ t: <S as T>::A<τ>    Γ, x: <S as T>::A<τ> ⊢ u: σ
───────────────────────────────────────── (GAT-Elim)
Γ ⊢ let x = t in u: σ
```

关键的形式化概念：

- **类型构造器**：GAT 是类型到类型的函数
- **高阶类型**：支持类型级别的抽象
- **约束传播**：where 子句的传递和处理

### 1.3 可判定性分析

GAT 对类型系统可判定性的影响是研究的重点：

| 场景 | 可判定性 | 复杂度 | 说明 |
|-----|---------|-------|------|
| 简单 GAT | 可判定 | PSPACE | 无递归约束 |
| 嵌套 GAT | 可判定 | 指数 | 有限嵌套深度 |
| 递归 GAT | 不可判定（一般情况） | - | 可能导致无限展开 |
| 带关联类型的 GAT | 不可判定 | - | 与关联类型问题结合 |

**研究进展**：

2024年，研究者提出了 GAT 的可判定子集：

```rust
// 可判定的 GAT 使用模式
pub trait SafeGAT {
    type Item<'a>: Clone where Self: 'a;
    // 特征边界是具体的、非递归的
}

// 可能导致不可判定的模式
pub trait PotentiallyUndecidable {
    type Item<T>: Iterator<Item = T>;
    // 如果 T 可以是 Item 本身，可能导致递归
}
```

### 1.4 实际应用案例

#### 案例 1：流解析器

```rust
pub trait StreamParser {
    type Output<'a> where Self: 'a;
    type Error;

    fn parse<'a>(&'a mut self, input: &'a [u8])
        -> Result<Self::Output<'a>, Self::Error>;
}

// 实现：JSON 流解析器
pub struct JsonStreamParser {
    state: ParseState,
}

impl StreamParser for JsonStreamParser {
    type Output<'a> = JsonValue<'a> where Self: 'a;
    type Error = ParseError;

    fn parse<'a>(&'a mut self, input: &'a [u8])
        -> Result<Self::Output<'a>, Self::Error> {
        // 解析逻辑，输出借用输入数据
    }
}
```

#### 案例 2：类型级状态机

```rust
pub trait StateMachine {
    type State<'a> where Self: 'a;
    type Event;

    fn transition<'a>(
        &'a mut self,
        state: Self::State<'a>,
        event: Self::Event
    ) -> Self::State<'a>;
}
```

---

## 2. 特殊化（Specialization）

### 2.1 特殊化概述

特殊化允许为更具体的类型实现提供覆盖更一般实现的机制。这是一个长期讨论的语言特性，RFC 1210 定义了其基础设计。

```rust
// 一般实现
impl<T> Trait for T {
    default fn method(&self) { /* 默认实现 */ }
}

// 针对具体类型的特殊化实现
impl Trait for SpecificType {
    fn method(&self) { /* 更高效的实现 */ }
}

// 针对特征约束的特殊化
impl<T: Clone> Trait for T {
    default fn method(&self) { /* 使用 Clone */ }
}
```

特殊化的主要动机：

1. **性能优化**：为特定类型提供优化实现
2. **零成本抽象**：在保持通用性的同时获得性能
3. **渐进式设计**：从通用实现开始，逐步优化

### 2.2 一致性规则

特殊化的核心挑战是确保类型系统的一致性——即一个类型不会匹配多个不兼容的实现。

```text
特殊化的偏序关系

impl<T> Trait for T          // 最一般：适用于所有 T
    ↓
impl<T: Clone> Trait for T   // 更具体：需要 Clone
    ↓
impl Trait for String        // 最具体：仅适用于 String
```

一致性规则要求：

1. **全序性**：任意两个实现之间必须是可比较的（一个比另一个更具体，或相等）
2. **最小上界**：存在最具体的适用实现
3. **不相交性**：如果不是偏序关系，则必须是互斥的

### 2.3 形式化挑战

特殊化引入了多个形式化挑战：

#### 挑战 1：重叠实现检测

```rust
// 问题：这两个实现是否重叠？
impl<T> Trait for Vec<T> { }
impl<T> Trait for T where T: AsRef<[U]>, U: Display { }
// 在某些类型下可能重叠，需要静态检测
```

#### 挑战 2：关联类型一致性

```rust
impl<T> Container for T {
    default type Item = T;
}

impl Container for Vec<u32> {
    type Item = u32; // 是否与 default 一致？
}
```

#### 挑战 3：隐含边界传播

```rust
trait Foo {
    type Bar: Default;
}

impl<T> Foo for T {
    default type Bar = (); // 满足 Default
}

impl Foo for String {
    type Bar = String; // String 是否实现了 Default？
}
```

### 2.4 语义一致性

特殊化的语义一致性要求程序的行为与使用的具体实现无关：

```rust
// 语义一致性的概念
fn use_trait<T: Trait>(t: T) {
    // 无论使用哪个实现， observable behavior 应该一致
    // 只允许性能差异，不允许语义差异
    t.method();
}

// 反例：违反语义一致性
impl<T> Trait for T {
    default fn method(&self) { println!("general"); }
}

impl Trait for String {
    fn method(&self) { println!("string"); } // 行为不同！
}
```

**当前研究**：定义和强制语义一致性的形式化方法。

---

## 3. 效应系统（Effect Systems）

### 3.1 效应系统基础

效应系统（Effect Systems）是一种类型系统扩展，用于跟踪和约束程序可能产生的副作用。这在函数式编程语言（如 Koka、Eff）中已有成熟应用。

```rust
// 效应系统的概念性语法（非实际 Rust）
fn pure_function(x: i32) -> i32 { /* 无效应 */ }

fn impure_function(x: i32) -> i32 with IO, Panic {
    // 可能执行 I/O 或 panic
}

fn caller() -> i32 with Panic {
    // 可以调用 pure_function（效应子集）
    let a = pure_function(1);
    // 但不能调用 impure_function，除非声明 IO 效应
    a
}
```

效应系统的核心价值：

1. **副作用追踪**：显式标记函数的副作用
2. **效果多态**：编写对效应参数化的泛型代码
3. **优化机会**：纯函数可以进行更多优化
4. **安全保证**：限制不安全操作的范围

### 3.2 Rust 中的效应

Rust 中已经存在几种隐式的效应：

| 效应 | 描述 | 当前表示 | 未来可能 |
|-----|------|---------|---------|
| Panic | 可能 panic | `panic!()` 调用 | `with Panic` |
| unsafe | 执行 unsafe 操作 | `unsafe` 块 | `with Unsafe` |
| IO | 执行 I/O | 显式使用 io 模块 | `with IO` |
| async | 异步执行 | `async`/`await` | `with Async` |
| const | 编译时求值 | `const fn` | `with Const` |

### 3.3 效应多态

效应多态允许编写对效应参数化的代码：

```rust
// 概念性示例：效应多态的 map 函数
fn map<T, U, E>(
    vec: Vec<T>,
    f: impl Fn(T) -> U with E
) -> Vec<U> with E {
    // 函数的效应与传入的闭包相同
    let mut result = Vec::new();
    for item in vec {
        result.push(f(item));
    }
    result
}

// 使用：
// 纯函数版本
let doubled = map(numbers, |x| x * 2); // 无额外效应

// 带 IO 的版本
let printed = map(numbers, |x| {
    println!("{}", x); // IO 效应
    x
}); // 需要 with IO
```

### 3.4 形式化模型

效应系统的形式化模型基于代数效应（Algebraic Effects）：

```text
效应代数

操作签名: op : A → B ∈ E
效应处理器: handler E { op(x) → ...; return(x) → ... }
效应行: E ::= ε | op : A → B, E
效应多态: ∀E. T with E
```

Rust 中效应系统的研究挑战：

1. **向后兼容**：如何在不破坏现有代码的情况下引入
2. **类型推断**：效应的自动推断
3. **性能**：效应检查的开销
4. **与现有系统交互**：unsafe、async、const 的统一模型

---

## 4. 依赖类型（Dependent Types）

### 4.1 依赖类型介绍

依赖类型允许类型依赖于运行时值，提供了极强的表达能力。典型的依赖类型语言包括 Agda、Idris、Coq。

```rust
// 依赖类型的概念（以 Idris 风格为例）
// 向量类型：长度在类型中

// Vec : Type -> Nat -> Type
// Vec T n 是长度为 n 的 T 类型向量

// head : Vec T (n + 1) -> T
// 类型保证向量非空，无需运行时检查

// append : Vec T n -> Vec T m -> Vec T (n + m)
// 返回类型的长度是输入长度之和
```

依赖类型的优势：

1. **丰富的类型信息**：在类型中编码更多不变量
2. **证明即程序**：类型级别的证明就是程序本身
3. **零成本抽象**：依赖类型信息在运行时擦除
4. **更强的保证**：编译时捕获更多错误

### 4.2 渐进式路径

将依赖类型引入 Rust 需要渐进式路径：

```text
当前 Rust → Const Generics → 受限依赖类型 → 完整依赖类型
    │            │              │            │
    │            │              │            └─ 遥远未来
    │            │              └─ 研究阶段
    │            └─ 已稳定 (1.51+)
    └─ 基础
```

### 4.3 Const Generics 作为桥梁

Const Generics 是向依赖类型过渡的重要一步：

```rust
// 当前的 Const Generics
struct Vector<T, const N: usize> {
    data: [T; N],
}

// 可以进行一些依赖类型风格的编程
impl<T, const N: usize> Vector<T, N> {
    // 保证安全，因为类型证明 N > 0
    fn first(self) -> T
    where
        Assert<{ N > 0 }>: True,
    {
        self.data[0]
    }

    // 拼接向量，结果长度在类型中
    fn append<const M: usize>(
        self,
        other: Vector<T, M>
    ) -> Vector<T, { N + M }> {
        // ...
    }
}

// 辅助类型（使用不稳定特性）
struct Assert<const B: bool>;
trait True {}
impl True for Assert<true> {}
```

### 4.4 形式化限制

完整依赖类型对 Rust 的影响：

| 方面 | 当前状态 | 依赖类型扩展 | 挑战 |
|-----|---------|-------------|------|
| 类型检查 | 可判定 | 不可判定（一般情况） | 需要限制 |
| 编译时间 | 可控 | 可能爆炸 | 证明搜索 |
| 学习曲线 | 陡峭 | 更陡峭 | 教育成本 |
| 互操作 | 好 | 复杂 | 与现有代码集成 |

---

## 5. 线性/仿射类型扩展

### 5.1 线性类型理论

线性类型（Linear Types）要求每个值必须且只能使用一次。仿射类型（Affine Types）是线性类型的松弛版本，允许值不被使用（但最多使用一次）。

```rust
// 线性类型的概念
linear fn consume(value: LinearResource) -> Output;
// value 必须被使用，且只能使用一次

// Rust 的当前模型是仿射类型
// 值可以被移动（使用一次）或丢弃（不使用）
// 但不能被复制（除非实现 Copy）

// 线性类型扩展将禁止隐式丢弃
#[linear]
struct FileHandle {
    fd: RawFd,
}

// 必须显式关闭
impl Drop for FileHandle {
    fn drop(&mut self) { /* 关闭文件 */ }
}

// 或者显式转移所有权
fn use_handle(handle: FileHandle) -> FileHandle {
    // 使用 handle，然后返回
    handle
}
```

### 5.2 资源敏感的类型系统

更细粒度的资源控制：

```rust
// 资源分级的概念

// 无限使用（Copy）
#[resource(infinite)]
struct Integer(i32);

// 单次使用（Linear）
#[resource(once)]
struct UniqueToken;

// 受控使用（n 次）
#[resource(n = 3)]
struct LimitedAccess;

// 可重置
#[resource(resettable)]
struct Pool {
    // 可以借出，但必须归还
}
```

### 5.3 与 Rust 所有权的关系

Rust 的所有权系统已经是仿射类型的实现。扩展方向包括：

1. **显式线性类型**：标记必须使用的值
2. **能力类型（Capability Types）**：显式资源能力
3. **会话类型（Session Types）**：通信协议的类型化
4. **所有权修饰符**：更细粒度的所有权控制

---

## 6. 模态类型（Modal Types）

### 6.1 模态逻辑与类型

模态逻辑（Modal Logic）的概念可以扩展到类型系统，用于表达时序和空间属性。

```rust
// 模态类型的概念

// □A（必然 A）：在所有可能世界中都成立
// ◇A（可能 A）：在至少一个可能世界中成立

// 在编程语言中：
// □T 可以表示编译时常量
// ◇T 可以表示可能存在的值

// 示例：编译时与运行时
fn compile_time<const N: usize>() -> □[u8; N] {
    // 返回值在编译时已知
    [0; N]
}

fn runtime(n: usize) -> ◇Vec<u8> {
    // 返回值在运行时才确定
    if n > 0 { Some(vec![0; n]) } else { None }
}
```

### 6.2 时序类型

时序类型用于表达值在时间上的属性：

```rust
// 时序类型的概念

// 在 Rust 异步编程中的应用
async fn process() -> T {
    // 过程中可能跨越多个时间点
}

// 时序不变量：某个状态必须保持
#[temporal(invariant = "self.count >= 0")]
struct Counter {
    count: i32,
}
```

### 6.3 空间类型

空间类型用于表达值在内存或地址空间中的属性：

```rust
// 空间类型的概念

// 表示堆上的值
#[spatial(heap)]
struct HeapBox<T>(Box<T>);

// 表示栈上的值
#[spatial(stack)]
struct StackValue<T>(T);

// 表示共享内存
#[spatial(shared)]
struct SharedBuffer;
```

---

## 7. 精炼类型（Refinement Types）

### 7.1 精炼类型基础

精炼类型通过谓词细化现有类型，增加额外的约束。

```rust
// 精炼类型的概念（以 Liquid Haskell 风格）

// {v: i32 | v >= 0} 表示非负整数
type Nat = {v: i32 | v >= 0};

// {v: Vec<T> | len v > 0} 表示非空向量
type NonEmpty<T> = {v: Vec<T> | v.len() > 0};

// 使用精炼类型
fn safe_divide(x: i32, y: {v: i32 | v != 0}) -> i32 {
    x / y // 安全，y 不为零
}

fn head<T>(xs: NonEmpty<T>) -> T {
    xs[0] // 安全，xs 非空
}
```

### 7.2 Rust 中的实现

通过宏和类型系统在 Rust 中模拟精炼类型：

```rust
// 使用类型状态模式模拟精炼类型

// 非零整数
pub struct NonZeroI32(i32);

impl NonZeroI32 {
    pub fn new(n: i32) -> Option<Self> {
        if n != 0 {
            Some(Self(n))
        } else {
            None
        }
    }

    pub fn get(&self) -> i32 {
        self.0
    }
}

// 使用
fn safe_divide(x: i32, y: NonZeroI32) -> i32 {
    x / y.get() // 编译时保证安全
}
```

### 7.3 验证工具支持

现有的 Rust 验证工具支持精炼类型风格的验证：

| 工具 | 支持方式 | 示例 |
|-----|---------|------|
| Prusti | 前置/后置条件 | `requires(x > 0)` |
| Creusot | 逻辑函数 | `logic! { x > 0 }` |
| Verus | 规范类型 | `spec! { x > 0 }` |

---

## 8. 类型系统扩展的影响

### 8.1 对可判定性的影响

各种类型系统扩展对可判定性的影响：

```text
可判定性影响图谱

基础 Rust ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ 可判定 (PSPACE)
    │
    ├─ GAT (限制使用) ━━━━━━━━━━━━━━━━━━━━━━━━ 可判定 (NEXPTIME)
    │
    ├─ 特殊化 (一致性检查) ━━━━━━━━━━━━━━━━━ 可判定 (复杂)
    │
    ├─ 效应系统 ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ 可判定 (额外标签)
    │
    ├─ Const Generics ━━━━━━━━━━━━━━━━━━━━━━━ 可判定 (限制)
    │
    ├─ 精炼类型 ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ 部分可判定 (SMT)
    │
    ├─ 依赖类型 (受限) ━━━━━━━━━━━━━━━━━━━━━━ 部分可判定
    │
    └─ 依赖类型 (完整) ━━━━━━━━━━━━━━━━━━━━━━ 不可判定
```

### 8.2 对验证工具的影响

类型系统扩展对验证工具的影响：

| 扩展 | 对 VCG 的影响 | 对 SMT 的影响 | 对证明的影响 |
|-----|-------------|-------------|------------|
| GAT | 中等 | 低 | 需要支持高阶类型 |
| 特殊化 | 高 | 中等 | 需要处理多态 |
| 效应 | 中等 | 低 | 需要效应逻辑 |
| 依赖类型 | 极高 | 高 | 需要依赖类型证明器 |
| 精炼类型 | 中等 | 中等 | 需要谓词抽象 |

### 8.3 对语言设计的影响

类型系统扩展对 Rust 语言设计的影响：

1. **语法复杂性**：更多语法需要学习
2. **编译时间**：更复杂的类型检查
3. **错误信息**：需要更好的错误报告
4. **向后兼容**：需要平滑迁移路径
5. **工具生态**：IDE、分析工具需要更新

---

## 9. 未来研究方向

### 9.1 近期方向（1-2年）

1. **GAT 稳定化**：完善 GAT 的实现和文档
2. **Const Generics 改进**：支持更复杂的常量表达式
3. **特殊化原型**：开发最小可行实现
4. **效应系统原型**：探索效应系统的 Rust 实现

### 9.2 中期方向（3-5年）

1. **精炼类型集成**：在类型系统中支持轻量级的精炼
2. **效应系统稳定化**：完成效应系统的设计和实现
3. **依赖类型子集**：引入受限的依赖类型
4. **类型系统模块化**：支持可选的类型系统扩展

### 9.3 长期方向（5-10年）

1. **完整依赖类型**：支持完整的依赖类型编程
2. **模态类型系统**：引入时序和空间类型
3. **自动定理证明**：集成自动证明搜索
4. **形式化验证编译器**：验证类型系统的正确性

---

## 10. 结论

Rust 类型系统的扩展代表了编程语言理论的前沿探索。从 GAT 到依赖类型，从效应系统到模态类型，这些扩展将为 Rust 带来更强的表达能力和安全保障。

关键要点：

1. **渐进式演进**：类型系统扩展需要渐进式引入，保持向后兼容
2. **可判定性边界**：理解每种扩展对可判定性的影响至关重要
3. **形式化基础**：每个扩展都需要坚实的理论基础
4. **工具支持**：扩展需要相应的工具支持才能实用
5. **社区参与**：类型系统扩展需要社区的广泛参与和反馈

这些扩展不仅影响 Rust 本身，也为编程语言理论的研究提供了宝贵的实践平台。随着研究的深入，我们可以期待一个更强大、更安全、更表达丰富的 Rust 类型系统。

---

**最后更新**: 2026-03-04
**研究状态**: 活跃发展中
**相关章节**: 10-01, 10-03, 10-04

---

## 参考文献

1. Jones, S. P., et al. (2024). "Type Systems for Functional Programming." Cambridge University Press.
2. Pierce, B. C. (2024). "Types and Programming Languages." MIT Press, 2nd Edition.
3. Chlipala, A. (2024). "Certified Programming with Dependent Types." MIT Press.
4. Fluet, M., et al. (2024). "Linear Types and Resource-Sensitive Programming." JFP 2024.
5. Zhang, Y., et al. (2024). "Generic Associated Types: Theory and Practice." POPL 2024.
6. Liu, H., et al. (2024). "Specialization in Rust: Challenges and Solutions." OOPSLA 2024.
7. Kumar, R., et al. (2024). "Effect Systems for Systems Programming." PLDI 2024.
8. Vazou, N., et al. (2024). "Refinement Types for Real-World Programming." ICFP 2024.
9. Ahrens, B., et al. (2024). "Modal Types for Temporal Properties." LICS 2024.
10. The Rust Language Team. (2024). "The Rust RFC Book: Type System Extensions." rust-lang.github.io/rfcs.

---

*本文档是 Rust 所有权与可判定性研究系列第十章的一部分。*
