# 机器学习模型 API 参考

> 返回索引：`docs/README.md`

## 📋 目录

- [机器学习模型 API 参考](#机器学习模型-api-参考)
  - [📋 目录](#-目录)
  - [概述](#概述)
  - [核心类型](#核心类型)
    - [LinearRegression {#linearregression}](#linearregression-linearregression)
    - [LogisticRegression {#logisticregression}](#logisticregression-logisticregression)
    - [KMeans {#kmeans}](#kmeans-kmeans)
    - [DecisionTree {#decisiontree}](#decisiontree-decisiontree)
  - [性能指标](#性能指标)
    - [回归](#回归)
    - [分类](#分类)
    - [聚类](#聚类)
  - [使用示例](#使用示例)
  - [错误处理](#错误处理)
  - [最佳实践](#最佳实践)
  - [接口对齐说明与交叉链接](#接口对齐说明与交叉链接)
  - [术语与形状规范](#术语与形状规范)
  - [版本矩阵](#版本矩阵)
  - [版本](#版本)

## 概述

覆盖常见的监督学习与无监督学习算法，强调类型安全、可组合与可扩展。

## 核心类型

### LinearRegression {#linearregression}

- **描述**: 最小二乘线性回归，支持批量/小批量训练。
- **构造**: `new(learning_rate: f64, epochs: usize) -> LinearRegression`
- **接口**:
  - `fit(x: &Array2<f64>, y: &Array1<f64>) -> Result<(), Error>`
  - `predict(x: &Array2<f64>) -> Array1<f64>`
  - `weights(&self) -> &Array1<f64>`

### LogisticRegression {#logisticregression}

- **描述**: 二分类逻辑回归，带正则项。
- **构造**: `new(lr: f64, epochs: usize, l2: f64) -> LogisticRegression`
- **接口**:
  - `fit(...) -> Result<(), Error>`
  - `predict_proba(...) -> Array1<f64>`
  - `predict(...) -> Array1<u8>`

### KMeans {#kmeans}

- **描述**: K 均值聚类，支持多次初始化与并行计算。
- **构造**: `new(k: usize, max_iter: usize) -> KMeans`
- **接口**:
  - `fit(x: &Array2<f64>) -> Result<KMeansResult, Error>`
  - `predict(x: &Array2<f64>) -> Array1<usize>`

### DecisionTree {#decisiontree}

- **描述**: CART 风格决策树，支持分类/回归。
- **构造**: `new(max_depth: Option<usize>) -> DecisionTree`
- **接口**:
  - `fit(x: &Array2<f64>, y: &Array1<f64>) -> Result<(), Error>`
  - `predict(x: &Array2<f64>) -> Array1<f64>`

## 性能指标

### 回归

- `mse(y_true, y_pred) -> f64`
- `r2(y_true, y_pred) -> f64`

### 分类

- `accuracy(y_true, y_pred) -> f64`
- `precision/recall/f1(y_true, y_pred) -> f64`

### 聚类

- `silhouette_score(x, labels) -> f64`

## 使用示例

```rust
// 线性回归
// let mut lr = LinearRegression::new(0.01, 1000);
// lr.fit(&x, &y)?;
// let y_pred = lr.predict(&x_test);
```

```rust
// KMeans
// let km = KMeans::new(3, 100);
// let result = km.fit(&x)?;
// let labels = km.predict(&x_test);
```

## 错误处理

- 常见错误: 维度不匹配、数据为空、超参数非法、未训练即预测。
- 建议: 使用统一 `Error`/`Result` 别名，并在 `Display` 提供清晰上下文。

## 最佳实践

1. 明确输入数据形状，封装校验逻辑。
2. 为大型数据集提供 `fit_batch` / `partial_fit`。
3. 将随机性通过 `seed` 注入，便于复现实验。

## 接口对齐说明与交叉链接

- 与指南对齐：本页接口与 `guides/ml-preprocess-eval.md` 中的示例一致；若存在命名差异，以示例中的具体签名为准。
- 数据形状：示例多使用 `&[Vec<f64>]` 以便快速上手；在性能敏感场景推荐 `ndarray::Array`。
- 进一步阅读：
  - 预处理/切分/交叉验证/管道：`guides/ml-preprocess-eval.md`
  - 队列与系统性能建模：`api-reference/queueing-models.md`

## 术语与形状规范

- 样本数记为 N，特征数记为 D。
- 回归/分类输入：`x: &[Vec<f64>]` 大小约为 N×D，`y: &[f64]` 长度为 N。
- 聚类输入：`x: &[Vec<f64>]` 大小约为 N×D，输出 `labels: Vec<usize>` 长度为 N。
- 概率输出：二分类中 `predict_proba` 返回每个样本的正类概率 `Vec<f64>`。

校验清单：

- `x.len() == y.len()`
- 所有 `x[i].len()` 一致且 > 0
- 学习率/迭代次数/正则参数为正

## 版本矩阵

- c18_model 0.2.x：稳定接口 `LinearRegression/LogisticRegression/KMeans/DecisionTree`
- Rust 1.70+：示例经验证可编译运行
- `rand 0.8`：示例中使用切分/交叉验证时所需

## 版本

- 适配版本: 0.2.0（Rust 1.70+）。更详细的支持情况见上文“版本矩阵”。
