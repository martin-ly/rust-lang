# Generic Const Expressions (泛型常量表达式)
>
> **相关概念**: [常量](../../../concept/01_foundation/04_type_system.md)

> **Bloom 层级**: 理解

> **特性**: `generic_const_exprs`
> **状态**: 🧪 不稳定 (Unstable)
> **预计稳定**: Rust 1.96+
> **跟踪 Issue**: [#76560](https://github.com/rust-lang/rust/issues/76560)

---

## 📋 目录
>
> **[来源: Rust Official Docs]**

- [Generic Const Expressions (泛型常量表达式)](#generic-const-expressions-泛型常量表达式)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
    - [为什么需要这个特性？](#为什么需要这个特性)
    - [模块 1: 概念定义](#模块-1-概念定义)
      - [1.1 直观定义](#11-直观定义)
      - [1.2 操作定义](#12-操作定义)
      - [1.3 形式化直觉](#13-形式化直觉)
    - [模块 3: 概念依赖图](#模块-3-概念依赖图)
      - [承上（前置知识回溯）](#承上前置知识回溯)
  - [💡 核心概念](#-核心概念)
    - [常量表达式泛型](#常量表达式泛型)
  - [📐 语法详解](#-语法详解)
    - [基础用法](#基础用法)
    - [复杂表达式](#复杂表达式)
    - [类型级计算](#类型级计算)
  - [🚀 实际应用](#-实际应用)
    - [编译时矩阵运算](#编译时矩阵运算)
    - [类型级数值计算](#类型级数值计算)
    - [固定大小数据结构](#固定大小数据结构)
  - [⚠️ 限制与注意事项](#️-限制与注意事项)
    - [当前限制](#当前限制)
    - [递归限制](#递归限制)
  - [🔄 与现有方案对比](#-与现有方案对比)
    - [对比: 使用 const generics vs generic\_const\_exprs](#对比-使用-const-generics-vs-generic_const_exprs)
  - [🗺️ 模块 7: 思维表征](#️-模块-7-思维表征)
    - [表征: 常量表达式方案对比矩阵](#表征-常量表达式方案对比矩阵)
    - [表征: generic\_const\_exprs 能力边界](#表征-generic_const_exprs-能力边界)
  - [📚 模块 8: 国际化对齐](#-模块-8-国际化对齐)
  - [⚖️ 模块 9: 设计权衡](#️-模块-9-设计权衡)
    - [为什么 generic\_const\_exprs 还未稳定？](#为什么-generic_const_exprs-还未稳定)
    - [当前 workaround](#当前-workaround)
  - [📝 模块 10: 自我检测](#-模块-10-自我检测)
  - [🔗 参考资源](#-参考资源)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)

---

## 🎯 概述
>
> **[来源: Rust Official Docs]**

Generic Const Expressions 允许在泛型参数中使用**更复杂的常量表达式**，超越了简单的整数常量。

### 为什么需要这个特性？
>
> **[来源: Rust Official Docs]**

```rust,ignore
// 当前限制: 只能使用简单的常量参数
struct Array<T, const N: usize> {
    data: [T; N],
}

// ❌ 当前不支持: 常量表达式
struct Matrix<T, const N: usize, const M: usize>
where
    [T; N * M]: Sized,  // 需要使用 N * M 作为数组大小
{
    data: [T; N * M],
}
```

---

### 模块 1: 概念定义
>
> **[来源: Rust Official Docs]**

#### 1.1 直观定义
>
> **[来源: Rust Official Docs]**

**Generic Const Expressions** 扩展了 `const generics` 的能力，允许在泛型参数的 `where` 子句中使用**常量表达式**（如 `N * M`、`1 << N`）。

> 💡 关键直觉：普通的 `const generics` 只能使用简单的常量值（如 `const N: usize`），而 `generic_const_exprs` 允许在类型层面进行"编译时计算"。

#### 1.2 操作定义

**普通 const generics（已稳定）**:

```rust
struct Array<T, const N: usize> {
    data: [T; N],  // N 必须是简单的常量参数
}
```

**generic_const_exprs（不稳定）**:

```rust,ignore
struct Matrix<T, const N: usize, const M: usize>
where
    [T; N * M]: Sized,  // ✅ 使用表达式 N * M
{
    data: [T; N * M],
}
```

**允许的操作**: `+`、`-`、`*`、`/`、`<<`、`>>`、比较运算符，以及 `const fn` 调用。

#### 1.3 形式化直觉

`generic_const_exprs` 将 Rust 的类型系统从**简单参数化**提升到**依赖类型（Dependent Types）**的边缘。类型现在可以依赖于通过表达式计算的值：

```
Matrix<i32, 3, 4> 的完整类型:
  • N = 3, M = 4
  • where [i32; 3 * 4]: Sized
  • 即 [i32; 12]: Sized ✅

Matrix<i32, 3, 4> 的 transpose() 返回 Matrix<i32, 4, 3>:
  • N' = M = 4, M' = N = 3
  • where [i32; 4 * 3]: Sized
  • 即 [i32; 12]: Sized ✅
```

编译器在单态化时求值这些表达式，确保类型正确性。

---

### 模块 3: 概念依赖图
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

```mermaid
graph TD
    A[Const Generics] --> B[Generic Const Expressions]
    B --> C[where [T; N * M]: Sized]
    B --> D[Const Eval in Types]
    D --> E[Compile-time Computation]
    E --> F[Matrix<N, M>]
    E --> G[Type-level Factorial]

    style B fill:#f9f,stroke:#333,stroke-width:2px
    style D fill:#bfb,stroke:#333,stroke-width:2px
```

#### 承上（前置知识回溯）

| 前置概念 | 所在文档 | 本章中使用的具体点 |
|----------|----------|-------------------|
| **Const Generics** | `02_intermediate/generics.md` | `const N: usize` 类型参数 |
| **Array Types** | `01_fundamentals/arrays.md` | `[T; N]` 的编译期大小要求 |
| **Where Clauses** | `02_intermediate/generics.md` | 类型约束的语法 |

---

## 💡 核心概念
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 常量表达式泛型
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```rust,ignore
#![feature(generic_const_exprs)]
#![allow(incomplete_features)]

// 现在可以在 where 子句中使用常量表达式
struct Matrix<T, const N: usize, const M: usize>
where
    [T; N * M]: Sized,  // ✅ 使用 N * M
{
    data: [T; N * M],
}

impl<T, const N: usize, const M: usize> Matrix<T, N, M>
where
    [T; N * M]: Sized,
{
    fn new(data: [T; N * M]) -> Self {
        Self { data }
    }

    // 转置: M x N 矩阵
    fn transpose(self) -> Matrix<T, M, N>
    where
        [T; M * N]: Sized,  // M * N == N * M
    {
        // 实现转置逻辑
        Matrix { data: self.data }
    }
}

// 使用
let mat: Matrix<i32, 3, 4> = Matrix::new([0; 12]);  // 3 * 4 = 12
```

---

## 📐 语法详解
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

### 基础用法
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

```rust
#![feature(generic_const_exprs)]

// 数组连接类型
struct ConcatArray<T, const N: usize, const M: usize>
where
    [T; N + M]: Sized,  // 连接后的大小
{
    left: [T; N],
    right: [T; M],
}

impl<T, const N: usize, const M: usize> ConcatArray<T, N, M>
where
    [T; N + M]: Sized,
    T: Default + Copy,
{
    fn concat(self) -> [T; N + M] {
        let mut result = [T::default(); N + M];
        result[..N].copy_from_slice(&self.left);
        result[N..].copy_from_slice(&self.right);
        result
    }
}
```

### 复杂表达式
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

```rust,ignore
#![feature(generic_const_exprs)]

// 使用更复杂的表达式
struct ComplexArray<T, const N: usize>
where
    [T; N * 2 + 1]: Sized,  // 复杂表达式
{
    data: [T; N * 2 + 1],
}

// 幂运算 (必须是编译时可计算的)
struct PowerOfTwoArray<T, const N: usize>
where
    [T; 1 << N]: Sized,  // 2^N
{
    data: [T; 1 << N],
}

// 使用
let arr: PowerOfTwoArray<i32, 3> = PowerOfTwoArray { data: [0; 8] };  // 2^3 = 8
```

### 类型级计算
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```rust,ignore
#![feature(generic_const_exprs)]

// 编译时阶乘
type Factorial<const N: usize> = FactorialImpl<N>;

struct FactorialImpl<const N: usize>;

impl<const N: usize> FactorialImpl<N> {
    const VALUE: usize = if N == 0 { 1 } else { N * FactorialImpl::<{ N - 1 }>::VALUE };
}

// 使用
struct Permutations<T, const N: usize>
where
    [T; FactorialImpl<N>::VALUE]: Sized,
{
    data: [T; FactorialImpl<N>::VALUE],
}
```

---

## 🚀 实际应用
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

### 编译时矩阵运算
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```rust,ignore
#![feature(generic_const_exprs)]

use std::ops::{Add, Mul};

// 编译时已知大小的矩阵
#[derive(Debug, Clone, Copy)]
struct Matrix<T, const N: usize, const M: usize>
where
    [T; N * M]: Sized,
{
    data: [T; N * M],
}

// 矩阵乘法: N x M * M x P = N x P
impl<T, const N: usize, const M: usize, const P: usize> Mul<Matrix<T, M, P>> for Matrix<T, N, M>
where
    [T; N * M]: Sized,
    [T; M * P]: Sized,
    [T; N * P]: Sized,
    T: Default + Copy + Add<Output = T> + Mul<Output = T>,
{
    type Output = Matrix<T, N, P>;

    fn mul(self, rhs: Matrix<T, M, P>) -> Self::Output {
        let mut result = [T::default(); N * P];

        for i in 0..N {
            for j in 0..P {
                let mut sum = T::default();
                for k in 0..M {
                    let left = self.data[i * M + k];
                    let right = rhs.data[k * P + j];
                    sum = sum + left * right;
                }
                result[i * P + j] = sum;
            }
        }

        Matrix { data: result }
    }
}

// 使用
let a: Matrix<i32, 2, 3> = Matrix { data: [1, 2, 3, 4, 5, 6] };
let b: Matrix<i32, 3, 2> = Matrix { data: [1, 2, 3, 4, 5, 6] };
let c = a * b;  // Matrix<i32, 2, 2>
```

### 类型级数值计算
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

```rust,ignore
#![feature(generic_const_exprs)]

// 编译时验证数组大小
type AssertEqual<const A: usize, const B: usize> =
    [(); { A == B as usize } as usize - 1];

// 安全的数组转换
fn safe_convert<T, const N: usize, const M: usize>(
    arr: [T; N]
) -> [T; M]
where
    [T; N]: Sized,
    [T; M]: Sized,
    [(); N - M]: Sized,  // 编译时验证 N == M
{
    // 只有 N == M 时才能编译
    unsafe { std::mem::transmute(arr) }
}

// 使用
let arr: [i32; 5] = [1, 2, 3, 4, 5];
let same: [i32; 5] = safe_convert(arr);  // ✅ 编译通过
// let diff: [i32; 3] = safe_convert(arr);  // ❌ 编译错误
```

### 固定大小数据结构
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

```rust,ignore
#![feature(generic_const_exprs)]

// B树节点，编译时确定分支因子
struct BTreeNode<K, V, const B: usize>
where
    [Option<K>; B - 1]: Sized,
    [Option<V>; B - 1]: Sized,
    [Option<Box<BTreeNode<K, V, B>>>; B]: Sized,
{
    keys: [Option<K>; B - 1],
    values: [Option<V>; B - 1],
    children: [Option<Box<BTreeNode<K, V, B>>>; B],
    len: usize,
}

impl<K, V, const B: usize> BTreeNode<K, V, B>
where
    [Option<K>; B - 1]: Sized,
    [Option<V>; B - 1]: Sized,
    [Option<Box<BTreeNode<K, V, B>>>; B]: Sized,
{
    const MAX_KEYS: usize = B - 1;

    fn new() -> Self {
        Self {
            keys: [(); B - 1].map(|_| None),
            values: [(); B - 1].map(|_| None),
            children: [(); B].map(|_| None),
            len: 0,
        }
    }

    fn is_full(&self) -> bool {
        self.len == Self::MAX_KEYS
    }
}

// 使用: B=4 表示 2-3-4 树
let node: BTreeNode<i32, String, 4> = BTreeNode::new();
```

---

## ⚠️ 限制与注意事项
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 当前限制
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```rust,ignore
#![feature(generic_const_exprs)]

// ❌ 错误: 表达式不能包含类型参数
struct Bad<T, const N: usize>
where
    [T; std::mem::size_of::<T>()]: Sized,  // 错误!
{}

// ❌ 错误: 必须是 const fn
struct AlsoBad<const N: usize>
where
    [i32; random_function(N)]: Sized,  // 错误!
{}

// ✅ 正确: 简单的算术表达式
struct Good<T, const N: usize>
where
    [T; N * 2]: Sized,
{}
```

### 递归限制
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```rust,ignore
#![feature(generic_const_exprs)]

// 递归深度有限制
struct Recursive<const N: usize>
where
    Self: Sized,
    [i32; N]: Sized,
{
    // 深度递归可能导致编译器栈溢出
    next: Option<Box<Recursive<{ N - 1 }>>>,  // 注意递归
}
```

---

## 🔄 与现有方案对比
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

### 对比: 使用 const generics vs generic_const_exprs
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

```rust,ignore
// 方案1: 当前 workaround (使用宏)
macro_rules! define_matrix {
    ($n:expr, $m:expr) => {
        struct Matrix_${n}_${m}<T> {
            data: [T; $n * $m],
        }
    };
}

define_matrix!(3, 4);
define_matrix!(4, 5);
// ... 需要为每种组合定义

// 方案2: 使用 Vec (运行时大小)
struct MatrixVec<T> {
    data: Vec<T>,
    rows: usize,
    cols: usize,
}
// 缺点: 运行时检查，无编译时优化

// 方案3: generic_const_exprs (推荐)
#![feature(generic_const_exprs)]
struct Matrix<T, const N: usize, const M: usize>
where
    [T; N * M]: Sized,
{
    data: [T; N * M],
}
// 优点: 编译时验证，零开销，类型安全
```

---

## 🗺️ 模块 7: 思维表征
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 表征: 常量表达式方案对比矩阵
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

| 方案 | 编译时验证 | 运行时开销 | 类型安全 | 实现复杂度 | 稳定状态 |
|------|-----------|-----------|---------|-----------|---------|
| **普通 const generics** | 尺寸 | 零 | 高 | 低 | ✅ 稳定 |
| **generic_const_exprs** | 表达式 | 零 | 高 | 中 | 🧪 不稳定 |
| **宏（macro_rules）** | 无 | 零 | 中 | 高 | ✅ 稳定 |
| **Vec（运行时）** | 无 | 有 | 低 | 低 | ✅ 稳定 |

### 表征: generic_const_exprs 能力边界
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```text
generic_const_exprs 允许的操作:
═══════════════════════════════════════════════════════════════════

✅ 允许:
  • 算术: N + M, N - M, N * M, N / M
  • 位运算: 1 << N, N >> 1
  • 比较: N == M, N < M (用于类型选择)
  • const fn 调用: factorial(N)::VALUE

❌ 不允许:
  • 类型参数: size_of::<T>()
  • 运行时函数: random(), time()
  • 浮点数: const N: f32
  • 复杂控制流: 循环、match（在 where 子句中）

边界案例:
  • [T; N - 1]: Sized — 当 N = 0 时数组大小为 -1，编译错误
  • 需要 N > 0 的额外约束
```

---

## 📚 模块 8: 国际化对齐
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

| 来源 | 类型 | 说明 |
|------|------|------|
| [RFC 2000](https://rust-lang.github.io/rfcs/2000-const-generics.html) | 官方 | Const Generics 原始 RFC |
| [Tracking Issue #76560](https://github.com/rust-lang/rust/issues/76560) | 官方 | generic_const_exprs 跟踪 Issue |

---

## ⚖️ 模块 9: 设计权衡
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

### 为什么 generic_const_exprs 还未稳定？
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

1. **编译器复杂度**: 常量表达式求值与类型检查的交织增加了编译器的复杂性。
2. **错误信息**: 复杂的类型级表达式失败时，错误信息难以理解和调试。
3. **边界情况**: 如 `[T; N - 1]` 当 `N = 0` 时的处理需要精心设计。

### 当前 workaround
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

在 `generic_const_exprs` 稳定之前，可以使用：

- **typenum crate**: 类型级数值计算
- **generic-array crate**: 泛型大小的数组
- **宏**: 为常用尺寸生成代码

---

## 📝 模块 10: 自我检测
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

1. **`generic_const_exprs` 与普通 `const generics` 的根本区别是什么？** 为什么 `[T; N * M]: Sized` 在普通 const generics 下是编译错误？

2. **以下代码有什么问题？**

```rust,ignore
struct Bad<T, const N: usize>
where
    [T; std::mem::size_of::<T>()]: Sized,
{}
```

<details>
<summary>参考答案</summary>

**问题**: `std::mem::size_of::<T>()` 包含类型参数 `T`，而 `generic_const_exprs` 不允许表达式中包含类型参数。表达式必须是纯粹的常量表达式。

</details>

1. **设计一个 `Matrix<T, N, M>` 类型，要求支持 `transpose()` 返回 `Matrix<T, M, N>`。使用 `generic_const_exprs` 需要哪些 where 子句？**

---

## 🔗 参考资源
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

- [RFC: Const Generics](https://rust-lang.github.io/rfcs/2000-const-generics.html)
- [Tracking Issue](https://github.com/rust-lang/rust/issues/76560)
- [Const Eval](https://doc.rust-lang.org/nightly/unstable-book/language-features/const-eval.html)

---

**文档版本**: 2.0
**对应 Rust 版本**: 1.95.0+ (nightly)
**最后更新**: 2026-05-09
> **权威来源**: [RFC 2000: Const Generics](https://rust-lang.github.io/rfcs/2000-const-generics.html), [Tracking Issue #76560](https://github.com/rust-lang/rust/issues/76560), [Const Eval](https://doc.rust-lang.org/nightly/unstable-book/language-features/const-eval.html)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 RFC 2000 设计决策来源标注、Const Eval 不稳定特性文档引用 [来源: Authority Source Sprint Batch 8]

**状态**: 🧪 权威来源对齐完成 (Batch 8)

---

## 相关概念
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

- [Rust 标准库速查](../../05_reference/std_library_cheatsheet.md)

- [Async Closures (异步闭包)](async_closures.md)
- [Emerging 前沿特性](README.md)

---

## 权威来源索引

> **[来源: [crates.io](https://crates.io/)]**
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**
>
> **[来源: [Type Theory Research](https://en.wikipedia.org/wiki/Type_theory)]**
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
>

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**
