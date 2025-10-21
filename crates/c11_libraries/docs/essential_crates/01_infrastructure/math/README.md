# 数学与数值计算

> **核心库**: num, ndarray, nalgebra, statrs  
> **适用场景**: 数值计算、线性代数、统计分析、科学计算

---

## 📋 目录

- [数学与数值计算](#数学与数值计算)
  - [📋 目录](#-目录)
  - [🎯 核心概念](#-核心概念)
    - [数学计算的挑战](#数学计算的挑战)
  - [🔢 num - 数值类型扩展](#-num---数值类型扩展)
    - [核心特性](#核心特性)
    - [基础用法](#基础用法)
      - [复数运算](#复数运算)
      - [大整数](#大整数)
      - [有理数](#有理数)
  - [📊 ndarray - 多维数组](#-ndarray---多维数组)
    - [核心特性1](#核心特性1)
    - [基础用法1](#基础用法1)
      - [数组创建](#数组创建)
      - [数组操作](#数组操作)
      - [数学运算](#数学运算)
  - [🔷 nalgebra - 线性代数](#-nalgebra---线性代数)
    - [核心特性2](#核心特性2)
    - [基础用法2](#基础用法2)
      - [向量操作](#向量操作)
      - [矩阵操作](#矩阵操作)
  - [📈 statrs - 统计计算](#-statrs---统计计算)
    - [核心特性3](#核心特性3)
    - [基础用法3](#基础用法3)
  - [💡 最佳实践](#-最佳实践)
    - [1. 选择合适的库](#1-选择合适的库)
    - [2. 性能优化](#2-性能优化)
    - [3. 数值稳定性](#3-数值稳定性)
  - [🔧 常见场景](#-常见场景)
    - [场景 1: 数据分析](#场景-1-数据分析)
    - [场景 2: 机器学习预处理](#场景-2-机器学习预处理)
  - [📚 延伸阅读](#-延伸阅读)

---

## 🎯 核心概念

### 数学计算的挑战

1. **精度问题**: 浮点数精度损失
2. **性能要求**: 大规模数据计算
3. **内存管理**: 高维数组的存储
4. **数值稳定性**: 避免溢出和下溢

---

## 🔢 num - 数值类型扩展

### 核心特性

- ✅ 复数、大整数、有理数
- ✅ 数值特征 (Trait)
- ✅ 零依赖核心

### 基础用法

#### 复数运算

```rust
use num::complex::Complex;

fn main() {
    let z1 = Complex::new(3.0, 4.0); // 3 + 4i
    let z2 = Complex::new(1.0, 2.0); // 1 + 2i
    
    println!("z1 + z2 = {}", z1 + z2);
    println!("z1 * z2 = {}", z1 * z2);
    println!("|z1| = {}", z1.norm());
    println!("arg(z1) = {}", z1.arg());
}
```

#### 大整数

```rust
use num::BigInt;

fn factorial(n: u32) -> BigInt {
    (1..=n).map(BigInt::from).product()
}

fn main() {
    let fact_100 = factorial(100);
    println!("100! = {}", fact_100);
}
```

#### 有理数

```rust
use num::rational::Ratio;

fn main() {
    let r1 = Ratio::new(1, 3); // 1/3
    let r2 = Ratio::new(2, 5); // 2/5
    
    println!("1/3 + 2/5 = {}", r1 + r2); // 11/15
}
```

---

## 📊 ndarray - 多维数组

### 核心特性1

- ✅ N 维数组支持
- ✅ 高性能 BLAS 集成
- ✅ 类似 NumPy 的 API

### 基础用法1

#### 数组创建

```rust
use ndarray::{array, Array1, Array2};

fn main() {
    // 1D 数组
    let a: Array1<f64> = array![1.0, 2.0, 3.0, 4.0];
    
    // 2D 数组
    let b: Array2<f64> = array![
        [1.0, 2.0, 3.0],
        [4.0, 5.0, 6.0]
    ];
    
    // 初始化
    let zeros = Array2::<f64>::zeros((3, 3));
    let ones = Array2::<f64>::ones((2, 4));
    let range = Array1::range(0.0, 10.0, 1.0);
    
    println!("Shape: {:?}", b.shape());
}
```

#### 数组操作

```rust
use ndarray::{Array2, s};

fn main() {
    let mut a = Array2::<f64>::zeros((4, 4));
    
    // 切片
    let slice = a.slice(s![1..3, 1..3]);
    
    // 索引
    a[[0, 0]] = 1.0;
    
    // 迭代
    for elem in a.iter() {
        println!("{}", elem);
    }
}
```

#### 数学运算

```rust
use ndarray::{Array1, Array2};

fn main() {
    let a = Array1::from_vec(vec![1.0, 2.0, 3.0]);
    let b = Array1::from_vec(vec![4.0, 5.0, 6.0]);
    
    // 向量运算
    let c = &a + &b;
    let dot = a.dot(&b); // 点积
    
    println!("Sum: {:?}", c);
    println!("Dot: {}", dot);
}
```

---

## 🔷 nalgebra - 线性代数

### 核心特性2

- ✅ 编译时维度检查
- ✅ 几何变换支持
- ✅ 高性能优化

### 基础用法2

#### 向量操作

```rust
use nalgebra::{Vector3, Point3};

fn main() {
    let v1 = Vector3::new(1.0, 2.0, 3.0);
    let v2 = Vector3::new(4.0, 5.0, 6.0);
    
    // 向量运算
    let sum = v1 + v2;
    let dot = v1.dot(&v2);
    let cross = v1.cross(&v2);
    let norm = v1.norm();
    
    println!("Dot: {}", dot);
    println!("Cross: {:?}", cross);
    println!("Norm: {}", norm);
}
```

#### 矩阵操作

```rust
use nalgebra::{Matrix3, Vector3};

fn main() {
    let m = Matrix3::new(
        1.0, 2.0, 3.0,
        4.0, 5.0, 6.0,
        7.0, 8.0, 9.0,
    );
    
    let v = Vector3::new(1.0, 2.0, 3.0);
    
    // 矩阵运算
    let result = m * v;
    let transpose = m.transpose();
    
    println!("Result: {:?}", result);
}
```

---

## 📈 statrs - 统计计算

### 核心特性3

- ✅ 概率分布
- ✅ 统计函数
- ✅ 高精度实现

### 基础用法3

```rust
use statrs::distribution::{Normal, Continuous};
use statrs::statistics::{Statistics, OrderStatistics};

fn main() {
    // 正态分布
    let n = Normal::new(0.0, 1.0).unwrap();
    let pdf = n.pdf(0.0);
    let cdf = n.cdf(1.96);
    
    println!("PDF(0) = {}", pdf);
    println!("CDF(1.96) = {}", cdf);
    
    // 统计计算
    let data = vec![1.0, 2.0, 3.0, 4.0, 5.0];
    let mean = data.mean();
    let std_dev = data.std_dev();
    let median = data.median();
    
    println!("Mean: {}", mean);
    println!("Std Dev: {}", std_dev);
}
```

---

## 💡 最佳实践

### 1. 选择合适的库

| 场景 | 推荐库 |
|------|--------|
| 基础数值类型 | num |
| 大规模数组计算 | ndarray |
| 线性代数 | nalgebra |
| 统计分析 | statrs |

### 2. 性能优化

```rust
// ✅ 使用引用避免拷贝
let c = &a + &b;

// ✅ 预分配空间
let mut result = Array2::<f64>::zeros((1000, 1000));

// ✅ 使用并行计算 (ndarray-parallel)
use ndarray::parallel::prelude::*;
```

### 3. 数值稳定性

```rust
// ✅ 使用稳定算法
use nalgebra::linalg::SVD;

// 避免直接求逆，使用分解
let svd = SVD::new(matrix, true, true);
```

---

## 🔧 常见场景

### 场景 1: 数据分析

```rust
use ndarray::{Array1, Array2};

fn normalize(data: &Array1<f64>) -> Array1<f64> {
    let mean = data.mean().unwrap();
    let std = data.std(0.0);
    (data - mean) / std
}
```

### 场景 2: 机器学习预处理

```rust
use ndarray::Array2;

fn min_max_scale(data: &Array2<f64>) -> Array2<f64> {
    let min = data.fold(f64::INFINITY, |acc, &x| acc.min(x));
    let max = data.fold(f64::NEG_INFINITY, |acc, &x| acc.max(x));
    (data - min) / (max - min)
}
```

---

## 📚 延伸阅读

- [num 官方文档](https://docs.rs/num/)
- [ndarray 官方文档](https://docs.rs/ndarray/)
- [nalgebra 官方文档](https://docs.rs/nalgebra/)
- [statrs 官方文档](https://docs.rs/statrs/)

---

**文档版本**: 1.0.0  
**最后更新**: 2025-10-20
