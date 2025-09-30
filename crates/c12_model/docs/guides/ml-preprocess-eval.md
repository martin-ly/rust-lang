# ML 数据预处理与评估

> 返回索引：`docs/README.md`

本指南给出从数据准备、训练到评估的最小闭环，并对常见坑位进行提示。

## 📋 目录

- [ML 数据预处理与评估](#ml-数据预处理与评估)
  - [📋 目录](#-目录)
  - [目标](#目标)
  - [数据准备](#数据准备)
    - [数据切分（训练/验证/测试）](#数据切分训练验证测试)
  - [回归：LinearRegression](#回归linearregression)
    - [交叉验证（K-Fold）](#交叉验证k-fold)
  - [分类：LogisticRegression](#分类logisticregression)
  - [聚类：KMeans](#聚类kmeans)
    - [管道示例：标准化 → 模型 → 评估](#管道示例标准化--模型--评估)
  - [决策树：DecisionTree](#决策树decisiontree)
  - [常见坑位](#常见坑位)
  - [依赖与复现](#依赖与复现)
  - [小结](#小结)

## 目标

- 规范输入数据形状与缺失处理
- 使用 `LinearRegression`/`LogisticRegression`/`KMeans`/`DecisionTree`
- 计算常见指标（回归 R²、分类准确率、聚类轮廓系数）

## 数据准备

```rust
fn standardize(x: &mut [Vec<f64>]) {
    if x.is_empty() { return; }
    let n_features = x[0].len();
    for j in 0..n_features {
        let mut col: Vec<f64> = x.iter().map(|row| row[j]).collect();
        let mean = col.iter().sum::<f64>() / col.len() as f64;
        let var = col.iter().map(|v| (v - mean).powi(2)).sum::<f64>() / col.len() as f64;
        let std = var.sqrt().max(1e-12);
        for i in 0..x.len() {
            x[i][j] = (x[i][j] - mean) / std;
        }
    }
}
```

要点：

- 缺失值需先处理（删除或填补）
- 列尺度差异大时，标准化有助于收敛

### 数据切分（训练/验证/测试）

```rust
fn train_val_test_split<T: Clone>(data: &[T], ratios: (f64, f64, f64), seed: u64) -> (Vec<T>, Vec<T>, Vec<T>) {
    assert!((ratios.0 + ratios.1 + ratios.2 - 1.0).abs() < 1e-9);
    let mut idx: Vec<usize> = (0..data.len()).collect();
    let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
    idx.shuffle(&mut rng);
    let n = data.len();
    let n_train = (n as f64 * ratios.0).round() as usize;
    let n_val = (n as f64 * ratios.1).round() as usize;
    let train = idx[..n_train].iter().map(|&i| data[i].clone()).collect();
    let val = idx[n_train..n_train+n_val].iter().map(|&i| data[i].clone()).collect();
    let test = idx[n_train+n_val..].iter().map(|&i| data[i].clone()).collect();
    (train, val, test)
}
```

依赖：`rand = "0.8"`

## 回归：LinearRegression

```rust
use c18_model::LinearRegression;

let mut x = vec![vec![1.0], vec![2.0], vec![3.0], vec![4.0], vec![5.0]];
let y = vec![2.0, 4.0, 6.0, 8.0, 10.0];
standardize(&mut x);

let mut lr = LinearRegression::new(0.05, 2000);
lr.fit(&x, &y).expect("训练失败");
let y_pred = lr.predict(&x);
let r2 = lr.score(&x, &y);
println!("R² = {:.4}", r2);
```

### 交叉验证（K-Fold）

```rust
fn kfold_indices(n: usize, k: usize) -> Vec<(Vec<usize>, Vec<usize>)> {
    let mut idx: Vec<usize> = (0..n).collect();
    let fold_size = (n as f64 / k as f64).ceil() as usize;
    let mut folds = Vec::new();
    for f in 0..k {
        let start = f * fold_size;
        let end = usize::min(start + fold_size, n);
        let test: Vec<usize> = idx[start..end].to_vec();
        let mut train = idx.clone();
        train.drain(start..end);
        folds.push((train, test));
    }
    folds
}
```

接口要点：

- `new(lr, max_iter)`，`fit(&[Vec<f64>], &[f64]) -> Result<(), String>`
- `predict(&[Vec<f64>]) -> Vec<f64>`，`score(...) -> f64`

## 分类：LogisticRegression

```rust
use c18_model::LogisticRegression;

let mut x = vec![vec![1.0], vec![2.0], vec![3.0], vec![4.0], vec![5.0]];
let y = vec![0.0, 0.0, 1.0, 1.0, 1.0];
standardize(&mut x);

let mut clf = LogisticRegression::new(0.1, 1000);
clf.fit(&x, &y).expect("训练失败");
let proba = clf.predict_proba(&x);
let y_hat = clf.predict(&x);
let acc = clf.accuracy(&x, &y);
println!("accuracy = {:.3}", acc);
```

接口要点：

- `predict_proba(&[Vec<f64>]) -> Vec<f64>`
- `predict(&[Vec<f64>]) -> Vec<f64>`（阈值 0.5）
- `accuracy(&[Vec<f64>], &[f64]) -> f64`

## 聚类：KMeans

```rust
use c18_model::KMeans;

let x = vec![
    vec![1.0, 1.0],
    vec![1.5, 2.0],
    vec![3.0, 4.0],
    vec![5.0, 7.0],
    vec![3.5, 5.0],
    vec![4.5, 5.0],
    vec![3.5, 4.5],
];

let mut km = KMeans::new(2, 200);
km.fit(&x).expect("训练失败");
let labels = km.predict(&x);
let sil = km.silhouette_score(&x);
println!("silhouette = {:.3}", sil);
```

### 管道示例：标准化 → 模型 → 评估

```rust
struct StandardScaler { mean: Vec<f64>, std: Vec<f64> }

impl StandardScaler {
    fn fit(x: &[Vec<f64>]) -> Self {
        let n_features = x[0].len();
        let mut mean = vec![0.0; n_features];
        let mut std = vec![1.0; n_features];
        for j in 0..n_features {
            let col: Vec<f64> = x.iter().map(|r| r[j]).collect();
            mean[j] = col.iter().sum::<f64>() / col.len() as f64;
            let var = col.iter().map(|v| (v - mean[j]).powi(2)).sum::<f64>() / col.len() as f64;
            std[j] = var.sqrt().max(1e-12);
        }
        Self { mean, std }
    }
    fn transform(&self, x: &mut [Vec<f64>]) { for r in x { for j in 0..r.len() { r[j] = (r[j]-self.mean[j])/self.std[j]; } } }
}

fn pipeline_linear_regression(mut x: Vec<Vec<f64>>, y: Vec<f64>) -> f64 {
    let scaler = StandardScaler::fit(&x);
    let mut x_scaled = x.clone();
    let mut x_slice: &mut [Vec<f64>] = &mut x_scaled;
    scaler.transform(&mut x_slice);
    let mut lr = LinearRegression::new(0.05, 2000);
    lr.fit(&x_slice, &y).unwrap();
    lr.score(&x_slice, &y)
}
```

## 决策树：DecisionTree

```rust
use c18_model::DecisionTree;

let x = vec![
    vec![1.0, 1.0], vec![2.0, 2.0], vec![3.0, 3.0], vec![4.0, 4.0],
    vec![5.0, 5.0], vec![6.0, 6.0], vec![7.0, 7.0], vec![8.0, 8.0],
];
let y = vec![0.0,0.0,0.0,0.0,1.0,1.0,1.0,1.0];

let mut dt = DecisionTree::new(10, 2, 1);
dt.fit(&x, &y).expect("训练失败");
let y_hat = dt.predict(&x);
let acc = dt.accuracy(&x, &y);
println!("tree accuracy = {:.3}", acc);
```

## 常见坑位

- 向量形状不匹配：`x.len() == y.len()` 必须成立
- 训练前清理异常值、空值；必要时归一化/标准化
- 小数据集易过拟合，建议交叉验证/留出集评估

## 依赖与复现

- 建议在 `Cargo.toml` 中固定 `c18_model` 与 `rand` 的确切版本
- 代码片段若使用随机化，显式设置 `seed`

## 小结

- 统一数据预处理规范，保证输入形状与尺度
- 按需选择算法与指标组合，记录实验可重复性（随机种子、版本）
