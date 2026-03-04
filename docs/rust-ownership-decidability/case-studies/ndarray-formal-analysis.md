# ndarray 多维数组形式化分析

> **主题**: N维数组的类型安全操作
>
> **形式化框架**: 维度类型 + 视图安全
>
> **参考**: ndarray Documentation

---

## 目录

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

---

## 1. 引言

ndarray提供:

- N维数组
- 零拷贝视图
- 广播操作
- BLAS集成

---

## 2. 维度类型

### 2.1 Dimension Trait

### 定义 2.1 (Dimension层次)

```rust
pub trait Dimension: Clone {
    const NDIM: Option<usize>;  // 编译时维度数
    fn ndim(&self) -> usize;     // 运行时维度数
    fn shape(&self) -> &[usize]; // 各维度大小
}
```

### 2.2 静态维度

### 定理 2.1 (Ix1/Ix2/Ix3类型)

> 静态维度在编译时验证。

```rust
let a = Array2::<f64>::zeros((3, 4));  // 2D数组
// 类型: ArrayBase<OwnedRepr<f64>, Ix2>

// 维度错误在编译时捕获
let v = Array1::<f64>::zeros(5);
// let sum = a + v;  // 编译错误!
```

∎

### 定理 2.2 (动态维度)

> IxDyn支持运行时维度。

```rust
let a = ArrayD::<f64>::zeros(vec![2, 3, 4]);
// 维度数运行时确定
```

∎

---

## 3. 数组视图

### 定理 3.1 (视图安全)

> 视图保证数据存在性。

```rust
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

```rust
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

```rust
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

```rust
let a = Array2::<f64>::zeros((3, 4));
let slice = a.slice(s![0..10, ..]);  // 运行时panic
```

### 反例 6.2 (布局不匹配)

```rust
// C库通常期望连续内存
let a = Array2::<f64>::zeros((3, 4));
let view = a.slice(s![.., 0..2]);
// view不连续，不能直接传递给C
// 需: view.as_standard_layout()
```

---

*文档版本: 1.0.0*
*定理数量: 7个*
