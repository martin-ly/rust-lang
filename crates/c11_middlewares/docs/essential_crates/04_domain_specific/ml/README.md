# Machine Learning - 机器学习

## 📋 目录

- [Machine Learning - 机器学习](#machine-learning---机器学习)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [核心依赖](#核心依赖)
  - [数值计算](#数值计算)
    - [ndarray](#ndarray)
    - [线性代数](#线性代数)
  - [深度学习](#深度学习)
    - [PyTorch (tch-rs)](#pytorch-tch-rs)
    - [Burn 框架](#burn-框架)
  - [数据处理](#数据处理)
    - [Polars](#polars)
  - [实战示例](#实战示例)
    - [线性回归](#线性回归)
    - [K-means 聚类](#k-means-聚类)
  - [参考资源](#参考资源)

---

## 概述

Rust 在机器学习领域逐渐崛起，提供高性能的数值计算和数据处理能力。

### 核心依赖

```toml
[dependencies]
# 数值计算
ndarray = "0.15"
nalgebra = "0.32"

# 深度学习
tch = "0.15"  # PyTorch bindings
burn = "0.11"  # 纯 Rust ML 框架

# 数据处理
polars = "0.36"
linfa = "0.7"  # ML 算法
```

---

## 数值计算

### ndarray

```rust
use ndarray::{Array1, Array2, arr2};

fn ndarray_basics() {
    // 1D 数组
    let a = Array1::from_vec(vec![1.0, 2.0, 3.0, 4.0, 5.0]);
    println!("数组: {:?}", a);
    
    // 2D 数组
    let b = arr2(&[[1.0, 2.0],
                   [3.0, 4.0],
                   [5.0, 6.0]]);
    println!("矩阵:\n{:?}", b);
    
    // 矩阵运算
    let c = arr2(&[[1.0, 2.0],
                   [3.0, 4.0]]);
    let d = arr2(&[[5.0, 6.0],
                   [7.0, 8.0]]);
    let result = c + d;
    println!("相加:\n{:?}", result);
}
```

### 线性代数

```rust
use nalgebra::{Matrix2, Vector2};

fn linear_algebra() {
    // 矩阵
    let m = Matrix2::new(1.0, 2.0,
                         3.0, 4.0);
    
    // 向量
    let v = Vector2::new(1.0, 2.0);
    
    // 矩阵-向量乘法
    let result = m * v;
    println!("结果: {:?}", result);
    
    // 矩阵求逆
    if let Some(inv) = m.try_inverse() {
        println!("逆矩阵:\n{}", inv);
    }
}
```

---

## 深度学习

### PyTorch (tch-rs)

```rust
use tch::{nn, nn::Module, nn::OptimizerConfig, Device, Tensor};

fn neural_network() {
    let vs = nn::VarStore::new(Device::Cpu);
    let net = nn::seq()
        .add(nn::linear(&vs.root(), 784, 128, Default::default()))
        .add_fn(|x| x.relu())
        .add(nn::linear(&vs.root(), 128, 10, Default::default()));
    
    let mut opt = nn::Adam::default().build(&vs, 1e-3).unwrap();
    
    for epoch in 1..=10 {
        let input = Tensor::randn(&[64, 784], (tch::Kind::Float, Device::Cpu));
        let target = Tensor::randint(10, &[64], (tch::Kind::Int64, Device::Cpu));
        
        let output = net.forward(&input);
        let loss = output.cross_entropy_for_logits(&target);
        
        opt.backward_step(&loss);
        
        println!("Epoch {}: Loss = {:?}", epoch, loss.double_value(&[]));
    }
}
```

### Burn 框架

```rust
use burn::prelude::*;

#[derive(Module, Debug)]
struct Model<B: Backend> {
    linear1: Linear<B>,
    linear2: Linear<B>,
}

impl<B: Backend> Model<B> {
    fn forward(&self, x: Tensor<B, 2>) -> Tensor<B, 2> {
        let x = self.linear1.forward(x);
        let x = x.relu();
        self.linear2.forward(x)
    }
}

fn burn_example() {
    type MyBackend = burn::backend::NdArray;
    let device = Default::default();
    
    let model: Model<MyBackend> = Model {
        linear1: LinearConfig::new(784, 128).init(&device),
        linear2: LinearConfig::new(128, 10).init(&device),
    };
    
    let input = Tensor::<MyBackend, 2>::random(
        [32, 784],
        Distribution::Default,
        &device,
    );
    
    let output = model.forward(input);
    println!("输出形状: {:?}", output.shape());
}
```

---

## 数据处理

### Polars

```rust
use polars::prelude::*;

fn data_processing() -> Result<(), PolarsError> {
    // 创建 DataFrame
    let df = df! {
        "A" => &[1, 2, 3, 4, 5],
        "B" => &[5, 4, 3, 2, 1],
        "C" => &["a", "b", "c", "d", "e"]
    }?;
    
    println!("{:?}", df);
    
    // 过滤
    let filtered = df.clone().lazy()
        .filter(col("A").gt(lit(2)))
        .collect()?;
    
    println!("过滤后:\n{:?}", filtered);
    
    // 聚合
    let grouped = df.clone().lazy()
        .group_by([col("C")])
        .agg([col("A").sum()])
        .collect()?;
    
    println!("聚合后:\n{:?}", grouped);
    
    Ok(())
}
```

---

## 实战示例

### 线性回归

```rust
use ndarray::{Array1, Array2};
use ndarray_linalg::Solve;

fn linear_regression(x: &Array2<f64>, y: &Array1<f64>) -> Array1<f64> {
    // y = Xβ
    // β = (X^T X)^(-1) X^T y
    
    let xt = x.t();
    let xtx = xt.dot(x);
    let xty = xt.dot(y);
    
    xtx.solve_into(xty).unwrap()
}

fn main() {
    // 示例数据
    let x = Array2::from_shape_vec(
        (5, 2),
        vec![1.0, 1.0, 1.0, 2.0, 1.0, 3.0, 1.0, 4.0, 1.0, 5.0]
    ).unwrap();
    
    let y = Array1::from_vec(vec![2.0, 4.0, 5.0, 4.0, 5.0]);
    
    let beta = linear_regression(&x, &y);
    println!("系数: {:?}", beta);
}
```

### K-means 聚类

```rust
use linfa::prelude::*;
use linfa_clustering::KMeans;
use ndarray::{Array2, Axis};

fn kmeans_example() {
    // 生成数据
    let mut data = Array2::zeros((100, 2));
    for i in 0..50 {
        data[[i, 0]] = rand::random::<f64>();
        data[[i, 1]] = rand::random::<f64>();
    }
    for i in 50..100 {
        data[[i, 0]] = rand::random::<f64>() + 5.0;
        data[[i, 1]] = rand::random::<f64>() + 5.0;
    }
    
    // K-means
    let dataset = DatasetBase::from(data);
    let model = KMeans::params(2)
        .max_n_iterations(100)
        .fit(&dataset)
        .expect("K-means 失败");
    
    let clusters = model.predict(&dataset);
    println!("聚类: {:?}", clusters);
}
```

---

## 参考资源

- [ndarray 文档](https://docs.rs/ndarray/)
- [tch-rs GitHub](https://github.com/LaurentMazare/tch-rs)
- [Burn GitHub](https://github.com/tracel-ai/burn)
- [Polars 文档](https://docs.rs/polars/)
- [linfa GitHub](https://github.com/rust-ml/linfa)
