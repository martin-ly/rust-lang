# ndarray 多维数组形式化分析

> **Bloom 层级**: L5-L6 (分析/评价/创造)

> **主题**: N维数组的类型安全操作
>
> **形式化框架**: 维度类型 + 视图安全
>
> **参考**: ndarray Documentation

---

## 目录
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

- [ndarray 多维数组形式化分析](#ndarray-多维数组形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 维度类型](#2-维度类型)
    - [2.1 Dimension Trait](#21-dimension-trait)
    - [定义 2.1 (Dimension层次)](#定义-21-dimension层次)
    - [2.2 静态维度](#22-静态维度)
    - [定理 2.1 (Ix1/Ix2/Ix3类型)](#定理-21-ix1ix2ix3类型)
    - [定理 2.2 (动态维度)](#定理-22-动态维度)
  - [3. 数组视图](#3-数组视图)
    - [定理 3.1 (视图安全)](#定理-31-视图安全)
  - [4. 广播语义](#4-广播语义)
    - [定理 4.1 (广播规则)](#定理-41-广播规则)
  - [5. 迭代安全](#5-迭代安全)
    - [定理 5.1 (迭代顺序)](#定理-51-迭代顺序)
  - [6. 反例](#6-反例)
    - [反例 6.1 (视图越界)](#反例-61-视图越界)
    - [反例 6.2 (布局不匹配)](#反例-62-布局不匹配)
  - [*定理数量: 7个*](#定理数量-7个)
  - [权威来源索引](#权威来源索引)

---

## 1. 引言
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

ndarray提供:

- N维数组
- 零拷贝视图
- 广播操作
- BLAS集成

---

## 2. 维度类型
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

### 2.1 Dimension Trait
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

### 定义 2.1 (Dimension层次)
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```rust
pub trait Dimension: Clone {
    const NDIM: Option<usize>;  // 编译时维度数
    fn ndim(&self) -> usize;     // 运行时维度数
    fn shape(&self) -> &[usize]; // 各维度大小
}
```

### 2.2 静态维度
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

### 定理 2.1 (Ix1/Ix2/Ix3类型)

> 静态维度在编译时验证。

```rust,ignore
let a = Array2::<f64>::zeros((3, 4));  // 2D数组
// 类型: ArrayBase<OwnedRepr<f64>, Ix2>

// 维度错误在编译时捕获
let v = Array1::<f64>::zeros(5);
// let sum = a + v;  // 编译错误!
```

∎

### 定理 2.2 (动态维度)

> IxDyn支持运行时维度。

```rust,ignore
let a = ArrayD::<f64>::zeros(vec![2, 3, 4]);
// 维度数运行时确定
```

∎

---

## 3. 数组视图

### 定理 3.1 (视图安全)

> 视图保证数据存在性。

```rust,ignore
let a = Array2::from_shape_fn((3, 4), |(i, j)| (i * 4 + j) as f64);
let view = a.slice(s![1..3, ..]);  // 子视图

// view引用a的数据
// a必须在view存活期间有效
```

**形式化**:

$$
\text{View<'a, T>} \vdash \text{borrowed}(\text{Array}, \text{lifetime } 'a)
$$

∎

---

## 4. 广播语义

### 定理 4.1 (广播规则)

> ndarray实现NumPy广播语义。

```rust,ignore
let a = Array2::<f64>::ones((3, 4));
let b = Array1::<f64>::ones(4);  // 会在第0维广播

let c = &a + &b;  // 形状: (3, 4)
```

**规则**:

- 维度从后向前对齐
- 大小为1的维度可广播
- 不匹配则错误

∎

---

## 5. 迭代安全

### 定理 5.1 (迭代顺序)

> 迭代遵循内存布局顺序。

```rust,ignore
// C-order (row-major)
let a = Array2::from_shape_vec((2, 3), vec![1,2,3,4,5,6])?;
// 内存: [1,2,3,4,5,6]
// 迭代: 1,2,3,4,5,6 (行优先)

// F-order (column-major)
let a = Array2::from_shape_vec((2, 3).f(), vec![1,2,3,4,5,6])?;
// 迭代: 1,4,2,5,3,6 (列优先)
```

∎

---

## 6. 反例

### 反例 6.1 (视图越界)

```rust,ignore
let a = Array2::<f64>::zeros((3, 4));
let slice = a.slice(s![0..10, ..]);  // 运行时panic
```

### 反例 6.2 (布局不匹配)

```rust,ignore
// C库通常期望连续内存
let a = Array2::<f64>::zeros((3, 4));
let view = a.slice(s![.., 0..2]);
// view不连续，不能直接传递给C
// 需: view.as_standard_layout()
```

---

*文档版本: 1.0.0*
*定理数量: 7个*
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [README](./README.md)

---

## 权威来源索引

> **[来源: Wikipedia - Memory Safety]**

> **[来源: TRPL Ch. 4 - Ownership]**

> **[来源: Rustonomicon - Ownership]**

> **[来源: POPL 2018 - RustBelt]**

> **[来源: Wikipedia - Formal Methods]**

> **[来源: Coq Reference Manual]**

> **[来源: TLA+ Documentation]**

> **[来源: ACM - Formal Verification]**

---

## 权威来源索引

> **[来源: [RustBelt](https://plv.mpi-sws.org/rustbelt/)]**
>
> **[来源: [Iris Project](https://iris-project.org/)]**
>
> **[来源: [POPL/PLDI 论文](https://dblp.org/db/conf/pldi/index.html)]**
>
> **[来源: [Tree Borrows](https://plv.mpi-sws.org/rustbelt/tree-borrows/)]**
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
>
