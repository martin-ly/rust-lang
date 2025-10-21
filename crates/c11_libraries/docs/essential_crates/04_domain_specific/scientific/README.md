# Scientific Computing - 科学计算

## 📋 目录

- [Scientific Computing - 科学计算](#scientific-computing---科学计算)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [核心依赖](#核心依赖)
  - [数值计算](#数值计算)
    - [基础数学运算](#基础数学运算)
    - [矩阵运算](#矩阵运算)
    - [数值积分](#数值积分)
  - [数据可视化](#数据可视化)
    - [Plotters](#plotters)
    - [散点图](#散点图)
  - [统计分析](#统计分析)
    - [描述统计](#描述统计)
    - [概率分布](#概率分布)
  - [实战示例](#实战示例)
    - [数据拟合](#数据拟合)
    - [蒙特卡洛模拟](#蒙特卡洛模拟)
    - [数值求解器](#数值求解器)
  - [参考资源](#参考资源)

---

## 概述

Rust 在科学计算领域提供高性能的数值库和可视化工具。

### 核心依赖

```toml
[dependencies]
# 数值计算
ndarray = "0.15"
nalgebra = "0.32"
num = "0.4"

# 统计
statrs = "0.17"

# 可视化
plotters = "0.3"

# 数据分析
polars = "0.36"
```

---

## 数值计算

### 基础数学运算

```rust
use num::complex::Complex;

fn complex_numbers() {
    let a = Complex::new(2.0, 3.0);
    let b = Complex::new(1.0, 4.0);
    
    println!("a + b = {:?}", a + b);
    println!("a * b = {:?}", a * b);
    println!("|a| = {}", a.norm());
}
```

### 矩阵运算

```rust
use nalgebra::{Matrix3, Vector3};

fn matrix_operations() {
    let m = Matrix3::new(
        1.0, 2.0, 3.0,
        4.0, 5.0, 6.0,
        7.0, 8.0, 9.0
    );
    
    // 转置
    let mt = m.transpose();
    println!("转置:\n{}", mt);
    
    // 特征值
    if let Some(eigen) = m.symmetric_eigen() {
        println!("特征值: {:?}", eigen.eigenvalues);
    }
}
```

### 数值积分

```rust
fn integrate<F>(f: F, a: f64, b: f64, n: usize) -> f64
where
    F: Fn(f64) -> f64,
{
    let h = (b - a) / n as f64;
    let mut sum = 0.5 * (f(a) + f(b));
    
    for i in 1..n {
        let x = a + i as f64 * h;
        sum += f(x);
    }
    
    sum * h
}

fn main() {
    // 计算 ∫₀¹ x² dx = 1/3
    let result = integrate(|x| x * x, 0.0, 1.0, 1000);
    println!("积分结果: {} (理论值: 0.333...)", result);
}
```

---

## 数据可视化

### Plotters

```rust
use plotters::prelude::*;

fn plot_function() -> Result<(), Box<dyn std::error::Error>> {
    let root = BitMapBackend::new("plot.png", (640, 480)).into_drawing_area();
    root.fill(&WHITE)?;
    
    let mut chart = ChartBuilder::on(&root)
        .caption("y = x²", ("sans-serif", 50))
        .margin(5)
        .x_label_area_size(30)
        .y_label_area_size(30)
        .build_cartesian_2d(-3f32..3f32, 0f32..10f32)?;
    
    chart.configure_mesh().draw()?;
    
    chart.draw_series(LineSeries::new(
        (-300..=300).map(|x| {
            let x = x as f32 / 100.0;
            (x, x * x)
        }),
        &RED,
    ))?;
    
    root.present()?;
    println!("图表已保存到 plot.png");
    Ok(())
}
```

### 散点图

```rust
use plotters::prelude::*;

fn scatter_plot() -> Result<(), Box<dyn std::error::Error>> {
    let root = BitMapBackend::new("scatter.png", (640, 480)).into_drawing_area();
    root.fill(&WHITE)?;
    
    let mut chart = ChartBuilder::on(&root)
        .caption("散点图", ("sans-serif", 40))
        .margin(5)
        .build_cartesian_2d(0f32..10f32, 0f32..10f32)?;
    
    chart.configure_mesh().draw()?;
    
    let data: Vec<(f32, f32)> = (0..50)
        .map(|_| (
            rand::random::<f32>() * 10.0,
            rand::random::<f32>() * 10.0
        ))
        .collect();
    
    chart.draw_series(
        data.iter().map(|(x, y)| Circle::new((*x, *y), 3, BLUE.filled()))
    )?;
    
    root.present()?;
    Ok(())
}
```

---

## 统计分析

### 描述统计

```rust
use statrs::statistics::*;

fn descriptive_stats() {
    let data = vec![1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0];
    
    let mean: f64 = data.mean();
    let std_dev = data.std_dev();
    let variance = data.variance();
    
    println!("均值: {}", mean);
    println!("标准差: {}", std_dev);
    println!("方差: {}", variance);
}
```

### 概率分布

```rust
use statrs::distribution::{Normal, Continuous};

fn probability_distributions() {
    // 正态分布 N(0, 1)
    let n = Normal::new(0.0, 1.0).unwrap();
    
    // PDF (概率密度函数)
    println!("P(X=0) = {}", n.pdf(0.0));
    
    // CDF (累积分布函数)
    println!("P(X≤0) = {}", n.cdf(0.0));
    
    // 分位数
    println!("95th percentile = {}", n.inverse_cdf(0.95));
}
```

---

## 实战示例

### 数据拟合

```rust
use ndarray::{Array1, Array2};
use ndarray_linalg::Solve;

fn polynomial_fit(x: &Array1<f64>, y: &Array1<f64>, degree: usize) -> Array1<f64> {
    let n = x.len();
    let mut design_matrix = Array2::zeros((n, degree + 1));
    
    for i in 0..n {
        for j in 0..=degree {
            design_matrix[[i, j]] = x[i].powi(j as i32);
        }
    }
    
    let xt = design_matrix.t();
    let xtx = xt.dot(&design_matrix);
    let xty = xt.dot(y);
    
    xtx.solve_into(xty).unwrap()
}

fn main() {
    let x = Array1::from_vec(vec![0.0, 1.0, 2.0, 3.0, 4.0]);
    let y = Array1::from_vec(vec![1.0, 2.7, 7.4, 15.9, 28.8]);
    
    let coeffs = polynomial_fit(&x, &y, 2);
    println!("多项式系数: {:?}", coeffs);
}
```

### 蒙特卡洛模拟

```rust
use rand::Rng;

fn monte_carlo_pi(n: usize) -> f64 {
    let mut rng = rand::thread_rng();
    let mut inside = 0;
    
    for _ in 0..n {
        let x: f64 = rng.gen();
        let y: f64 = rng.gen();
        
        if x * x + y * y <= 1.0 {
            inside += 1;
        }
    }
    
    4.0 * inside as f64 / n as f64
}

fn main() {
    let n = 1_000_000;
    let pi_estimate = monte_carlo_pi(n);
    println!("π 的估计值: {} (真实值: 3.14159...)", pi_estimate);
}
```

### 数值求解器

```rust
fn newton_raphson<F, Fprime>(f: F, fprime: Fprime, x0: f64, tol: f64) -> f64
where
    F: Fn(f64) -> f64,
    Fprime: Fn(f64) -> f64,
{
    let mut x = x0;
    
    for _ in 0..100 {
        let fx = f(x);
        if fx.abs() < tol {
            return x;
        }
        
        x -= fx / fprime(x);
    }
    
    x
}

fn main() {
    // 求解 x² - 2 = 0 (即 √2)
    let root = newton_raphson(
        |x| x * x - 2.0,
        |x| 2.0 * x,
        1.0,
        1e-10
    );
    
    println!("√2 ≈ {}", root);
}
```

---

## 参考资源

- [ndarray 文档](https://docs.rs/ndarray/)
- [nalgebra 文档](https://nalgebra.org/)
- [plotters GitHub](https://github.com/plotters-rs/plotters)
- [statrs 文档](https://docs.rs/statrs/)
