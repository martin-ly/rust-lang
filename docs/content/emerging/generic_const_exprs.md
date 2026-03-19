# Generic Const Expressions (泛型常量表达式)

> **特性**: `generic_const_exprs`
> **状态**: 🧪 不稳定 (Unstable)
> **预计稳定**: Rust 1.96+
> **跟踪 Issue**: [#76560](https://github.com/rust-lang/rust/issues/76560)

---

## 📋 目录

- [Generic Const Expressions (泛型常量表达式)](#generic-const-expressions-泛型常量表达式)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
    - [为什么需要这个特性？](#为什么需要这个特性)
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
  - [🔗 参考资源](#-参考资源)

---

## 🎯 概述

Generic Const Expressions 允许在泛型参数中使用**更复杂的常量表达式**，超越了简单的整数常量。

### 为什么需要这个特性？

```rust
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

## 💡 核心概念

### 常量表达式泛型

```rust
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

### 基础用法

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

```rust
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

```rust
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

### 编译时矩阵运算

```rust
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

```rust
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

```rust
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

### 当前限制

```rust
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

```rust
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

### 对比: 使用 const generics vs generic_const_exprs

```rust
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

## 🔗 参考资源

- [RFC: Const Generics](https://rust-lang.github.io/rfcs/2000-const-generics.html)
- [Tracking Issue](https://github.com/rust-lang/rust/issues/76560)
- [Const Eval](https://doc.rust-lang.org/nightly/unstable-book/language-features/const-eval.html)

---

**最后更新**: 2026-03-15
**状态**: 🧪 不稳定特性，需要 nightly
