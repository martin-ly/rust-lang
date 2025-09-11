# 2. 机器学习模型 API 参考

## 2.1 目录

- [2. 机器学习模型 API 参考](#2-机器学习模型-api-参考)
  - [2.1 目录](#21-目录)
  - [2.2 概述](#22-概述)
  - [2.3 主要类型](#23-主要类型)
    - [2.3.1 LinearRegression](#231-linearregression)
      - [2.3.1.1 构造函数](#2311-构造函数)
      - [2.3.1.2 主要方法](#2312-主要方法)
      - [2.3.1.3 使用示例](#2313-使用示例)
    - [2.3.2 LogisticRegression](#232-logisticregression)
      - [2.3.2.1 主要方法](#2321-主要方法)
    - [2.3.3 KMeans](#233-kmeans)
      - [2.3.3.1 构造函数](#2331-构造函数)
      - [2.3.3.2 主要方法](#2332-主要方法)
    - [2.3.4 DecisionTree](#234-decisiontree)
      - [2.3.4.1 构造函数](#2341-构造函数)
      - [2.3.4.2 主要方法](#2342-主要方法)
    - [2.3.5 DecisionTreeNode](#235-decisiontreenode)
  - [2.4 算法细节](#24-算法细节)
    - [2.4.1 线性回归](#241-线性回归)
    - [2.4.2 逻辑回归](#242-逻辑回归)
    - [2.4.3 KMeans聚类](#243-kmeans聚类)
    - [2.4.4 决策树](#244-决策树)
  - [2.5 性能指标](#25-性能指标)
    - [2.5.1 回归指标](#251-回归指标)
    - [2.5.2 分类指标](#252-分类指标)
    - [2.5.3 聚类指标](#253-聚类指标)
  - [2.6 使用建议](#26-使用建议)
    - [2.6.1 数据预处理](#261-数据预处理)
    - [2.6.2 模型选择](#262-模型选择)
    - [2.6.3 超参数调优](#263-超参数调优)
    - [2.6.4 性能优化](#264-性能优化)
  - [2.7 错误处理](#27-错误处理)

## 2.2 概述

机器学习模型模块提供了各种监督学习、无监督学习和强化学习算法的实现，包括线性回归、逻辑回归、KMeans聚类、决策树等。

## 2.3 主要类型

### 2.3.1 LinearRegression

线性回归模型，使用梯度下降算法进行训练。

```rust
pub struct LinearRegression {
    pub weights: Vec<f64>,           // 权重向量
    pub bias: f64,                   // 偏置项
    pub learning_rate: f64,          // 学习率
    pub max_iterations: usize,       // 最大迭代次数
    pub convergence_threshold: f64,  // 收敛阈值
}
```

#### 2.3.1.1 构造函数

```rust
pub fn new(learning_rate: f64, max_iterations: usize) -> Self
```

#### 2.3.1.2 主要方法

```rust
// 训练模型
pub fn fit(&mut self, x: &[Vec<f64>], y: &[f64]) -> Result<(), String>

// 预测
pub fn predict(&self, x: &[Vec<f64>]) -> Vec<f64>

// 计算R²分数
pub fn r2_score(&self, x: &[Vec<f64>], y: &[f64]) -> f64

// 计算均方误差
pub fn mse(&self, x: &[Vec<f64>], y: &[f64]) -> f64
```

#### 2.3.1.3 使用示例

```rust
use c18_model::LinearRegression;

let mut model = LinearRegression::new(0.01, 1000);
let x = vec![vec![1.0, 2.0], vec![2.0, 3.0], vec![3.0, 4.0]];
let y = vec![3.0, 5.0, 7.0];

model.fit(&x, &y)?;
let predictions = model.predict(&x);
let r2 = model.r2_score(&x, &y);
```

### 2.3.2 LogisticRegression

逻辑回归模型，用于二元分类。

```rust
pub struct LogisticRegression {
    pub weights: Vec<f64>,
    pub bias: f64,
    pub learning_rate: f64,
    pub max_iterations: usize,
    pub convergence_threshold: f64,
}
```

#### 2.3.2.1 主要方法

```rust
// 训练模型
pub fn fit(&mut self, x: &[Vec<f64>], y: &[f64]) -> Result<(), String>

// 预测概率
pub fn predict_proba(&self, x: &[Vec<f64>]) -> Vec<f64>

// 预测类别
pub fn predict(&self, x: &[Vec<f64>]) -> Vec<f64>

// 计算准确率
pub fn accuracy(&self, x: &[Vec<f64>], y: &[f64]) -> f64

// 计算交叉熵损失
pub fn cross_entropy_loss(&self, x: &[Vec<f64>], y: &[f64]) -> f64
```

### 2.3.3 KMeans

KMeans聚类算法。

```rust
pub struct KMeans {
    pub k: usize,                    // 聚类数量
    pub max_iterations: usize,       // 最大迭代次数
    pub centroids: Vec<Vec<f64>>,    // 聚类中心
    pub labels: Vec<usize>,          // 聚类标签
}
```

#### 2.3.3.1 构造函数

```rust
pub fn new(k: usize, max_iterations: usize) -> Self
```

#### 2.3.3.2 主要方法

```rust
// 训练模型
pub fn fit(&mut self, x: &[Vec<f64>]) -> Result<(), String>

// 预测聚类标签
pub fn predict(&self, x: &[Vec<f64>]) -> Vec<usize>

// 计算轮廓系数
pub fn silhouette_score(&self, x: &[Vec<f64>]) -> f64

// 计算惯性（簇内平方和）
pub fn inertia(&self, x: &[Vec<f64>]) -> f64
```

### 2.3.4 DecisionTree

决策树分类器。

```rust
pub struct DecisionTree {
    pub max_depth: Option<usize>,    // 最大深度
    pub min_samples_split: usize,    // 最小分割样本数
    pub min_samples_leaf: usize,     // 最小叶子节点样本数
    pub root: Option<Box<DecisionTreeNode>>, // 根节点
}
```

#### 2.3.4.1 构造函数

```rust
pub fn new() -> Self
pub fn with_max_depth(max_depth: usize) -> Self
```

#### 2.3.4.2 主要方法

```rust
// 训练模型
pub fn fit(&mut self, x: &[Vec<f64>], y: &[f64]) -> Result<(), String>

// 预测
pub fn predict(&self, x: &[Vec<f64>]) -> Vec<f64>

// 计算准确率
pub fn accuracy(&self, x: &[Vec<f64>], y: &[f64]) -> f64

// 获取特征重要性
pub fn feature_importance(&self) -> Vec<f64>
```

### 2.3.5 DecisionTreeNode

决策树节点。

```rust
pub struct DecisionTreeNode {
    pub feature_index: Option<usize>, // 分割特征索引
    pub threshold: Option<f64>,       // 分割阈值
    pub left: Option<Box<DecisionTreeNode>>,  // 左子树
    pub right: Option<Box<DecisionTreeNode>>, // 右子树
    pub prediction: Option<f64>,      // 叶子节点预测值
    pub samples: usize,               // 样本数量
}
```

## 2.4 算法细节

### 2.4.1 线性回归

**数学公式**：

- 预测函数: ŷ = w₀ + w₁x₁ + w₂x₂ + ... + wₙxₙ
- 损失函数: MSE = (1/n) * Σ(yᵢ - ŷᵢ)²
- 梯度: ∂MSE/∂wⱼ = (2/n) *Σ(yᵢ - ŷᵢ)* xᵢⱼ

**训练过程**：

1. 初始化权重和偏置
2. 计算预测值和损失
3. 计算梯度
4. 更新参数
5. 检查收敛条件

### 2.4.2 逻辑回归

**数学公式**：

- Sigmoid函数: σ(z) = 1/(1 + e^(-z))
- 预测函数: ŷ = σ(w₀ + w₁x₁ + ... + wₙxₙ)
- 损失函数: BCE = -(1/n) * Σ[yᵢlog(ŷᵢ) + (1-yᵢ)log(1-ŷᵢ)]

### 2.4.3 KMeans聚类

**算法步骤**：

1. 随机初始化k个聚类中心
2. 将每个点分配到最近的聚类中心
3. 更新聚类中心为簇内点的均值
4. 重复步骤2-3直到收敛

**距离度量**：欧几里得距离

### 2.4.4 决策树

**分割准则**：基尼不纯度

- Gini = 1 - Σpᵢ²

**分割过程**：

1. 计算每个特征和阈值的基尼不纯度
2. 选择基尼不纯度最小的分割
3. 递归构建左右子树
4. 设置停止条件

## 2.5 性能指标

### 2.5.1 回归指标

- **R²分数**: 决定系数，衡量模型解释方差的比例
- **MSE**: 均方误差，预测值与真实值差的平方的平均值
- **RMSE**: 均方根误差，MSE的平方根
- **MAE**: 平均绝对误差

### 2.5.2 分类指标

- **准确率**: 正确预测的样本比例
- **精确率**: TP/(TP+FP)
- **召回率**: TP/(TP+FN)
- **F1分数**: 精确率和召回率的调和平均

### 2.5.3 聚类指标

- **轮廓系数**: 衡量聚类质量的指标，范围[-1,1]
- **惯性**: 簇内平方和，越小越好
- **Davies-Bouldin指数**: 聚类有效性指标

## 2.6 使用建议

### 2.6.1 数据预处理

1. **特征缩放**: 对于线性回归和逻辑回归，建议标准化特征
2. **缺失值处理**: 确保数据完整
3. **异常值检测**: 识别和处理异常值

### 2.6.2 模型选择

1. **线性回归**: 适用于线性关系的数据
2. **逻辑回归**: 适用于二元分类问题
3. **KMeans**: 适用于无监督聚类
4. **决策树**: 适用于需要可解释性的分类问题

### 2.6.3 超参数调优

1. **学习率**: 影响收敛速度和稳定性
2. **迭代次数**: 平衡训练时间和性能
3. **聚类数量**: 根据数据特点选择
4. **树深度**: 防止过拟合

### 2.6.4 性能优化

1. **批量处理**: 对于大数据集，使用批量梯度下降
2. **并行计算**: 利用多核CPU加速训练
3. **内存管理**: 避免不必要的数据复制
4. **数值稳定性**: 注意浮点数精度问题

## 2.7 错误处理

所有训练和预测方法都可能返回错误：

- **数据验证错误**: 输入数据格式不正确
- **维度不匹配**: 特征维度不一致
- **数值错误**: 计算过程中出现异常值
- **收敛失败**: 算法无法收敛到解

建议始终处理这些错误情况：

```rust
match model.fit(&x, &y) {
    Ok(()) => println!("训练成功"),
    Err(e) => println!("训练失败: {}", e),
}
```
