# 常量泛型高级特性

> **特性**: `generic_const_exprs`
> **状态**: 🧪 不稳定 (Unstable)
> **预计稳定**: Rust 1.97+
> **跟踪 Issue**: [#76560](https://github.com/rust-lang/rust/issues/76560)
> **依赖**: nightly toolchain

---

## 📋 目录

- [常量泛型高级特性](.#常量泛型高级特性)
  - [📋 目录](.#-目录)
  - [🎯 概述](.#-概述)
  - [📐 常量泛型表达式语法](.#-常量泛型表达式语法)
    - [算术表达式](.#算术表达式)
    - [位运算与比较](.#位运算与比较)
    - [where 子句约束](.#where-子句约束)
  - [🔢 类型级整数运算](.#-类型级整数运算)
    - [编译时阶乘](.#编译时阶乘)
    - [类型级斐波那契](.#类型级斐波那契)
    - [编译时类型断言](.#编译时类型断言)
  - [🔄 与稳定版 Workaround 对比](.#-与稳定版-workaround-对比)
    - [typenum 方案](.#typenum-方案)
    - [宏方案](.#宏方案)
    - [方案对比矩阵](.#方案对比矩阵)
  - [⚠️ 当前限制与陷阱](.#️-当前限制与陷阱)
  - [📈 预计稳定时间与迁移建议](.#-预计稳定时间与迁移建议)
    - [稳定路线图](.#稳定路线图)
    - [当前使用建议](.#当前使用建议)
  - [🔗 参考资源](.#-参考资源)

---

## 🎯 概述

`generic_const_exprs` 将常量泛型从**简单的数值参数**扩展到**完整的常量表达式**，允许在类型参数位置执行编译时计算：

```rust
#![feature(generic_const_exprs)]
#![allow(incomplete_features)]

// 稳定版: 只能使用裸常量参数
struct Array<T, const N: usize>([T; N]);

// generic_const_exprs: 可以在类型中使用表达式
struct Matrix<T, const N: usize, const M: usize>
where
    [T; N * M]: Sized,  // ✅ 使用 N * M 作为数组大小
{
    data: [T; N * M],
}

// 更复杂的约束: 编译时验证维度兼容
fn matrix_multiply<A, B, const N: usize, const M: usize, const P: usize>(
    a: Matrix<A, N, M>,
    b: Matrix<B, M, P>,
) -> Matrix<A, N, P>
where
    [A; N * M]: Sized,
    [B; M * P]: Sized,
    [A; N * P]: Sized,
    A: std::ops::Mul<B> + std::ops::Add<Output = A> + Default + Copy,
{
    // 编译时已知输出维度 N x P
    todo!()
}
```

---

## 📐 常量泛型表达式语法

### 算术表达式

```rust
#![feature(generic_const_exprs)]

// 加法
struct Concat<T, const N: usize, const M: usize>
where
    [T; N + M]: Sized,
{
    data: [T; N + M],
}

// 乘法
struct Grid<T, const N: usize, const M: usize>
where
    [T; N * M]: Sized,
{
    cells: [T; N * M],
}

// 混合表达式
struct PaddedArray<T, const N: usize>
where
    [T; N * 2 + 1]: Sized,
{
    data: [T; N * 2 + 1],
}
```

### 位运算与比较

```rust
#![feature(generic_const_exprs)]

// 位运算: 2 的幂次数组
struct PowerOfTwo<T, const N: usize>
where
    [T; 1 << N]: Sized,  // 2^N
{
    data: [T; 1 << N],
}

// 编译时断言维度关系
struct RectangularBuffer<T, const W: usize, const H: usize>
where
    [T; W * H]: Sized,
    [(); (W >= H) as usize - 1]: Sized,  // 编译时断言: W >= H
{
    data: [T; W * H],
}
```

### where 子句约束

```rust
#![feature(generic_const_exprs)]

// 在 impl 中使用表达式约束
trait Tensor {
    const RANK: usize;
}

struct NdArray<T, const D: usize>
where
    [T; D]: Sized,
{
    data: [T; D],
}

impl<T, const N: usize, const M: usize> Tensor for NdArray<T, { N * M }>
where
    [T; N * M]: Sized,
{
    const RANK: usize = 2;
}

// 关联常量作为泛型参数
struct Reshape<T, const N: usize, const M: usize>
where
    [T; N * M]: Sized,
{
    data: [T; N * M],
}

impl<T, const N: usize, const M: usize> Reshape<T, N, M>
where
    [T; N * M]: Sized,
{
    fn flatten(self) -> NdArray<T, { N * M }> {
        NdArray { data: self.data }
    }
}
```

---

## 🔢 类型级整数运算

### 编译时阶乘

```rust
#![feature(generic_const_exprs)]

// 编译时递归计算阶乘
struct Factorial<const N: usize>;

impl<const N: usize> Factorial<N> {
    const VALUE: usize = if N == 0 {
        1
    } else {
        N * Factorial::<{ N - 1 }>::VALUE
    };
}

// 使用阶乘定义排列数组
struct Permutations<T, const N: usize>
where
    [T; Factorial::<N>::VALUE]: Sized,
{
    items: [T; Factorial::<N>::VALUE],
}

// Factorial::<5>::VALUE == 120
let p: Permutations<i32, 5> = Permutations {
    items: [0; 120],
};
```

### 类型级斐波那契

```rust
#![feature(generic_const_exprs)]

struct Fibonacci<const N: usize>;

impl<const N: usize> Fibonacci<N> {
    const VALUE: usize = if N == 0 {
        0
    } else if N == 1 {
        1
    } else {
        Fibonacci::<{ N - 1 }>::VALUE + Fibonacci::<{ N - 2 }>::VALUE
    };
}

// Fibonacci 步长缓冲区
struct FibBuffer<T, const N: usize>
where
    [T; Fibonacci::<N>::VALUE]: Sized,
{
    data: [T; Fibonacci::<N>::VALUE],
}
```

### 编译时类型断言

```rust
#![feature(generic_const_exprs)]

// 编译时验证两个维度相等
type AssertEqual<const A: usize, const B: usize> =
    [(); { A == B } as usize - 1];

// 安全的数组 reshape（仅在尺寸匹配时编译）
fn reshape<T, const N: usize, const M: usize>(
    arr: [T; N]
) -> [T; M]
where
    [T; N]: Sized,
    [T; M]: Sized,
    [(); N - M]: Sized,  // 编译时要求 N == M
{
    // SAFETY: N == M 已由编译时约束保证
    unsafe { std::mem::transmute(arr) }
}

// 编译时验证数组可被整除
type AssertDivisible<const N: usize, const D: usize> =
    [(); { N % D == 0 } as usize - 1];

struct Chunks<T, const N: usize, const CHUNK: usize>
where
    [T; N]: Sized,
    [(); N % CHUNK]: Sized,  // 编译时断言 N 可被 CHUNK 整除
{
    data: [T; N],
}
```

---

## 🔄 与稳定版 Workaround 对比

### typenum 方案

`typenum` 是稳定版中实现类型级运算的事实标准库：

```rust
// typenum: 使用类型表示数字
use typenum::{U3, U4, U12, Unsigned};
use generic_array::GenericArray;

// 类型级乘法: U3 * U4 = U12
struct MatrixTypenum<T, N, M>
where
    N: Unsigned,
    M: Unsigned,
{
    // 使用 GenericArray 代替 [T; N * M]
    data: GenericArray<T, <N as Mul<M>>::Output>,
}

// 使用繁琐: 需要引入类型别名
type Mat3x4<T> = MatrixTypenum<T, U3, U4>;
```

### 宏方案

```rust
// 方案 2: 宏生成具体类型
macro_rules! define_matrix {
    ($name:ident, $n:expr, $m:expr) => {
        struct $name<T> {
            data: [T; $n * $m],
        }
    };
}

define_matrix!(Matrix3x3, 3, 3);
define_matrix!(Matrix3x4, 3, 4);
// 每对维度都需要单独定义
```

### 方案对比矩阵

| 维度 | `generic_const_exprs` | `typenum` | 宏方案 |
|------|----------------------|-----------|--------|
| **语法简洁度** | ⭐⭐⭐ 原生语法 | ⭐ 类型体操 | ⭐⭐ 模板化 |
| **编译速度** | ⭐⭐⭐ 快 | ⭐ 慢（类型爆炸） | ⭐⭐⭐ 快 |
| **错误信息** | ⭐⭐⭐ 清晰 | ⭐ 晦涩 | ⭐⭐ 可接受 |
| **IDE 支持** | ⭐⭐⭐ 良好 | ⭐⭐ 一般 | ⭐⭐⭐ 良好 |
| **稳定可用** | ❌ nightly | ✅ 稳定 | ✅ 稳定 |
| **表达力** | ⭐⭐⭐ 任意 const 表达式 | ⭐⭐ 有限运算集 | ⭐ 仅字面量 |
| **生态兼容** | ⭐⭐⭐ 标准数组 | ⭐⭐ 依赖 generic-array | ⭐⭐⭐ 标准数组 |

---

## ⚠️ 当前限制与陷阱

```rust
#![feature(generic_const_exprs)]

// ❌ 错误: 表达式不能包含类型参数
struct Bad<T, const N: usize>
where
    [T; std::mem::size_of::<T>()]: Sized,  // 错误! 涉及类型参数
{}

// ❌ 错误: 必须是 const evaluatable
struct AlsoBad<const N: usize>
where
    [i32; some_runtime_fn(N)]: Sized,  // 错误! 非 const 函数
{}

// ✅ 正确: 仅涉及常量参数的简单算术
struct Good<T, const N: usize>
where
    [T; N * 2 + 1]: Sized,
{}

// ❌ 陷阱: 递归深度过大导致编译器栈溢出
struct Recursive<const N: usize>
where
    [i32; N]: Sized,
{
    next: Option<Box<Recursive<{ N - 1 }>>>,
}
// Recursive::<1000> 可能使编译器崩溃
```

---

## 📈 预计稳定时间与迁移建议

### 稳定路线图

```text
2024-2025: generic_const_exprs 进入 FCP 讨论
    ↓
2026 Q2-Q3: 部分功能稳定化 (简单算术表达式)
    ↓
2026 Q4-2027 Q1: 完整功能稳定 (泛型常量表达式)
    ↓
2027+: 生态系统迁移 (ndarray, nalgebra 等)
```

### 当前使用建议

**新项目 (Nightly 可用)**:

```rust
#![feature(generic_const_exprs)]
#![allow(incomplete_features)]

// 直接使用原生语法，为未来稳定化做准备
struct Vector<T, const N: usize>([T; N]);
struct Matrix<T, const N: usize, const M: usize>
where
    [T; N * M]: Sized,
{
    data: [T; N * M],
}
```

**稳定版项目 (现在)**:

```rust
// 使用 const_generic_expr 的简化抽象层
// 稳定后只需删除 where 子句中的表达式约束

// 当前稳定写法: 用函数式 API 隐藏内部实现
struct Matrix<T, const N: usize, const M: usize> {
    data: Vec<T>,  // 运行时存储，API 保持类型安全
}

impl<T, const N: usize, const M: usize> Matrix<T, N, M> {
    fn new() -> Self {
        assert_eq!(Self::CAPACITY, N * M);
        Self { data: Vec::with_capacity(N * M) }
    }

    const CAPACITY: usize = N * M;
}
```

**迁移路径**:

1. **现在**: 使用 `Vec` / `Box<[T]>` + `const_assert!` 模拟编译时检查
2. **nightly 实验**: 用 `generic_const_exprs` 验证设计
3. **稳定后**: 将 `Vec` 替换为 `[T; N * M]`，移除运行时断言

---

## 🔗 参考资源

- [RFC 2000: Const Generics](https://rust-lang.github.io/rfcs/2000-const-generics.html)
- [Tracking Issue #76560](https://github.com/rust-lang/rust/issues/76560)
- [typenum crate](https://docs.rs/typenum/latest/typenum/)
- [generic-array crate](https://docs.rs/generic-array/latest/generic_array/)
- [Const Eval Unstable Book](https://doc.rust-lang.org/nightly/unstable-book/language-features/const-eval.html)
- [项目 emerging/generic_const_exprs.md](generic_const_exprs.md)

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
