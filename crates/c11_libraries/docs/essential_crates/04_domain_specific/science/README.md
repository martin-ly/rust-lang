# 科学计算 (Scientific Computing)

**类别**: 领域特定 - 科学计算  
**重要程度**: ⭐⭐⭐⭐ (数据科学必备)  
**更新日期**: 2025-10-20

---

## 📋 目录

- [科学计算 (Scientific Computing)](#科学计算-scientific-computing)
  - [📋 目录](#-目录)
  - [📋 概述](#-概述)
  - [🔧 核心工具](#-核心工具)
    - [1. ndarray (N 维数组 ⭐⭐⭐⭐⭐)](#1-ndarray-n-维数组-)
      - [核心特性](#核心特性)
      - [基础操作](#基础操作)
      - [统计计算](#统计计算)
      - [数组变换](#数组变换)
    - [2. polars (高性能 DataFrame ⭐⭐⭐⭐⭐)](#2-polars-高性能-dataframe-)
      - [核心特性2](#核心特性2)
      - [基础操作2](#基础操作2)
      - [聚合操作](#聚合操作)
      - [CSV 读写](#csv-读写)
    - [3. nalgebra (线性代数 ⭐⭐⭐⭐⭐)](#3-nalgebra-线性代数-)
      - [核心特性3](#核心特性3)
      - [基础操作3](#基础操作3)
      - [矩阵分解](#矩阵分解)
    - [4. plotters (绘图库 ⭐⭐⭐⭐)](#4-plotters-绘图库-)
      - [核心特性4](#核心特性4)
      - [折线图](#折线图)
      - [散点图](#散点图)
  - [💡 最佳实践](#-最佳实践)
    - [1. 性能优化](#1-性能优化)
    - [2. 内存优化](#2-内存优化)
    - [3. 数据管道](#3-数据管道)
  - [📊 工具对比](#-工具对比)
  - [🎯 实战场景](#-实战场景)
    - [场景1: 数据分析](#场景1-数据分析)
    - [场景2: 机器学习预处理](#场景2-机器学习预处理)
  - [🔗 相关资源](#-相关资源)

## 📋 概述

Rust 在科学计算领域快速崛起，提供高性能的数值计算、数据处理和可视化工具，结合内存安全和并行计算优势。

---

## 🔧 核心工具

### 1. ndarray (N 维数组 ⭐⭐⭐⭐⭐)

**添加依赖**: `cargo add ndarray`  
**用途**: NumPy 风格的多维数组

#### 核心特性

- ✅ 多维数组操作
- ✅ 广播机制
- ✅ 切片和迭代
- ✅ 线性代数

#### 基础操作

```rust
use ndarray::prelude::*;

fn main() {
    // 创建数组
    let a = array![[1, 2, 3], [4, 5, 6]];
    let b = array![[1, 1, 1], [2, 2, 2]];
    
    // 数组运算
    let sum = &a + &b;
    println!("Sum:\n{}", sum);
    
    // 矩阵乘法
    let matrix_a = array![[1, 2], [3, 4]];
    let matrix_b = array![[5, 6], [7, 8]];
    let product = matrix_a.dot(&matrix_b);
    println!("Product:\n{}", product);
}
```

#### 统计计算

```rust
use ndarray::prelude::*;

fn statistics() {
    let data = array![1.0, 2.0, 3.0, 4.0, 5.0];
    
    // 均值
    let mean = data.mean().unwrap();
    println!("Mean: {}", mean);
    
    // 标准差
    let std_dev = data.std(0.0);
    println!("Std Dev: {}", std_dev);
    
    // 最小值和最大值
    let min = data.fold(f64::INFINITY, |a, &b| a.min(b));
    let max = data.fold(f64::NEG_INFINITY, |a, &b| a.max(b));
    println!("Min: {}, Max: {}", min, max);
}
```

#### 数组变换

```rust
use ndarray::prelude::*;

fn array_operations() {
    let a = array![[1, 2, 3], [4, 5, 6]];
    
    // 转置
    let transposed = a.t();
    println!("Transposed:\n{}", transposed);
    
    // 重塑
    let reshaped = a.into_shape((3, 2)).unwrap();
    println!("Reshaped:\n{}", reshaped);
    
    // 切片
    let slice = a.slice(s![0..1, ..]);
    println!("Slice:\n{}", slice);
}
```

---

### 2. polars (高性能 DataFrame ⭐⭐⭐⭐⭐)

**添加依赖**: `cargo add polars --features lazy`  
**用途**: 快速的 DataFrame 库

#### 核心特性2

- ✅ 惰性计算
- ✅ 多线程并行
- ✅ SQL 风格查询
- ✅ 零拷贝

#### 基础操作2

```rust
use polars::prelude::*;

fn dataframe_example() -> Result<()> {
    // 创建 DataFrame
    let df = df! {
        "name" => &["Alice", "Bob", "Charlie"],
        "age" => &[25, 30, 35],
        "salary" => &[50000, 60000, 70000],
    }?;
    
    println!("{}", df);
    
    // 过滤
    let filtered = df.filter(
        &df.column("age")?.gt(28)?
    )?;
    println!("\nFiltered:\n{}", filtered);
    
    // 排序
    let sorted = df.sort(["salary"], false)?;
    println!("\nSorted:\n{}", sorted);
    
    Ok(())
}
```

#### 聚合操作

```rust
use polars::prelude::*;

fn aggregation() -> Result<()> {
    let df = df! {
        "department" => &["Sales", "Sales", "IT", "IT"],
        "employee" => &["Alice", "Bob", "Charlie", "David"],
        "salary" => &[50000, 55000, 60000, 65000],
    }?;
    
    // 按部门分组并计算平均工资
    let result = df
        .lazy()
        .groupby([col("department")])
        .agg([col("salary").mean().alias("avg_salary")])
        .collect()?;
    
    println!("{}", result);
    Ok(())
}
```

#### CSV 读写

```rust
use polars::prelude::*;

fn csv_operations() -> Result<()> {
    // 读取 CSV
    let df = CsvReader::from_path("data.csv")?
        .infer_schema(None)
        .has_header(true)
        .finish()?;
    
    // 写入 CSV
    let mut file = std::fs::File::create("output.csv")?;
    CsvWriter::new(&mut file)
        .has_header(true)
        .finish(&mut df.clone())?;
    
    Ok(())
}
```

---

### 3. nalgebra (线性代数 ⭐⭐⭐⭐⭐)

**添加依赖**: `cargo add nalgebra`  
**用途**: 高性能线性代数库

#### 核心特性3

- ✅ 向量和矩阵运算
- ✅ 几何变换
- ✅ 分解算法
- ✅ SIMD 加速

#### 基础操作3

```rust
use nalgebra::{Vector3, Matrix3};

fn linear_algebra() {
    // 向量操作
    let v1 = Vector3::new(1.0, 2.0, 3.0);
    let v2 = Vector3::new(4.0, 5.0, 6.0);
    
    let dot_product = v1.dot(&v2);
    let cross_product = v1.cross(&v2);
    
    println!("Dot product: {}", dot_product);
    println!("Cross product: {}", cross_product);
    
    // 矩阵操作
    let m = Matrix3::new(
        1.0, 2.0, 3.0,
        4.0, 5.0, 6.0,
        7.0, 8.0, 9.0,
    );
    
    let determinant = m.determinant();
    println!("Determinant: {}", determinant);
}
```

#### 矩阵分解

```rust
use nalgebra::{Matrix3, DMatrix};

fn matrix_decomposition() {
    let m = DMatrix::from_row_slice(3, 3, &[
        1.0, 2.0, 3.0,
        4.0, 5.0, 6.0,
        7.0, 8.0, 10.0,
    ]);
    
    // LU 分解
    let lu = m.clone().lu();
    println!("L:\n{}", lu.l());
    println!("U:\n{}", lu.u());
    
    // QR 分解
    let qr = m.clone().qr();
    println!("Q:\n{}", qr.q());
    println!("R:\n{}", qr.r());
    
    // SVD 分解
    let svd = m.svd(true, true);
    println!("Singular values: {}", svd.singular_values);
}
```

---

### 4. plotters (绘图库 ⭐⭐⭐⭐)

**添加依赖**: `cargo add plotters`  
**用途**: 数据可视化

#### 核心特性4

- ✅ 多种图表类型
- ✅ 交互式图表
- ✅ 多种后端 (SVG, PNG, Canvas)
- ✅ 高性能

#### 折线图

```rust
use plotters::prelude::*;

fn plot_line_chart() -> Result<(), Box<dyn std::error::Error>> {
    let root = BitMapBackend::new("plot.png", (640, 480)).into_drawing_area();
    root.fill(&WHITE)?;
    
    let mut chart = ChartBuilder::on(&root)
        .caption("y = x^2", ("sans-serif", 50))
        .margin(5)
        .x_label_area_size(30)
        .y_label_area_size(30)
        .build_cartesian_2d(-3.0..3.0, 0.0..10.0)?;
    
    chart.configure_mesh().draw()?;
    
    chart.draw_series(LineSeries::new(
        (-30..=30).map(|x| {
            let x = x as f64 / 10.0;
            (x, x.powi(2))
        }),
        &RED,
    ))?;
    
    root.present()?;
    Ok(())
}
```

#### 散点图

```rust
use plotters::prelude::*;

fn plot_scatter() -> Result<(), Box<dyn std::error::Error>> {
    let root = BitMapBackend::new("scatter.png", (640, 480)).into_drawing_area();
    root.fill(&WHITE)?;
    
    let data: Vec<(f64, f64)> = (0..100)
        .map(|_| (rand::random::<f64>() * 10.0, rand::random::<f64>() * 10.0))
        .collect();
    
    let mut chart = ChartBuilder::on(&root)
        .caption("Scatter Plot", ("sans-serif", 40))
        .margin(5)
        .build_cartesian_2d(0.0..10.0, 0.0..10.0)?;
    
    chart.configure_mesh().draw()?;
    
    chart.draw_series(
        data.iter().map(|&point| Circle::new(point, 3, BLUE.filled()))
    )?;
    
    root.present()?;
    Ok(())
}
```

---

## 💡 最佳实践

### 1. 性能优化

```rust
use ndarray::prelude::*;
use rayon::prelude::*;

// 并行计算
fn parallel_computation(data: &Array2<f64>) -> Array1<f64> {
    data.axis_iter(Axis(0))
        .into_par_iter()
        .map(|row| row.sum())
        .collect::<Vec<_>>()
        .into()
}
```

### 2. 内存优化

```rust
use ndarray::prelude::*;

// 使用视图避免复制
fn use_views(large_array: &Array2<f64>) -> f64 {
    let view = large_array.slice(s![0..100, 0..100]);
    view.sum()
}
```

### 3. 数据管道

```rust
use polars::prelude::*;

fn data_pipeline() -> Result<DataFrame> {
    let df = CsvReader::from_path("data.csv")?
        .has_header(true)
        .finish()?;
    
    df.lazy()
        .filter(col("age").gt(25))
        .groupby([col("department")])
        .agg([
            col("salary").mean().alias("avg_salary"),
            col("salary").max().alias("max_salary"),
        ])
        .sort("avg_salary", SortOptions::default())
        .collect()
}
```

---

## 📊 工具对比

| 工具 | 用途 | 性能 | 易用性 | 推荐度 |
|------|------|------|--------|--------|
| **ndarray** | 数组计算 | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | 🌟 强推 |
| **polars** | 数据处理 | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | 🌟 强推 |
| **nalgebra** | 线性代数 | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | 🌟 强推 |
| **plotters** | 可视化 | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ | 💡 推荐 |

---

## 🎯 实战场景

### 场景1: 数据分析

```rust
use polars::prelude::*;

fn analyze_sales_data() -> Result<()> {
    let df = CsvReader::from_path("sales.csv")?.finish()?;
    
    // 计算总销售额
    let total_sales: f64 = df
        .column("amount")?
        .sum()
        .unwrap();
    
    println!("Total sales: ${}", total_sales);
    
    // 按产品分组
    let by_product = df
        .lazy()
        .groupby([col("product")])
        .agg([
            col("amount").sum().alias("total"),
            col("amount").mean().alias("average"),
        ])
        .collect()?;
    
    println!("{}", by_product);
    Ok(())
}
```

### 场景2: 机器学习预处理

```rust
use ndarray::prelude::*;

fn normalize_data(data: &Array2<f64>) -> Array2<f64> {
    let mean = data.mean_axis(Axis(0)).unwrap();
    let std = data.std_axis(Axis(0), 0.0);
    
    (data - &mean) / &std
}

fn train_test_split(
    data: &Array2<f64>,
    test_size: f64,
) -> (Array2<f64>, Array2<f64>) {
    let n = data.nrows();
    let split_point = (n as f64 * (1.0 - test_size)) as usize;
    
    let train = data.slice(s![0..split_point, ..]).to_owned();
    let test = data.slice(s![split_point.., ..]).to_owned();
    
    (train, test)
}
```

---

## 🔗 相关资源

- [ndarray Documentation](https://docs.rs/ndarray/)
- [Polars User Guide](https://pola-rs.github.io/polars-book/)
- [nalgebra Documentation](https://nalgebra.org/)
- [Plotters Guide](https://plotters-rs.github.io/book/)

---

**导航**: [返回领域特定](../README.md) | [返回主页](../../README.md)
