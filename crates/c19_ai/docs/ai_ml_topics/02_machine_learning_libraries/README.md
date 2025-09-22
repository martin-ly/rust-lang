# 机器学习库 (Machine Learning Libraries)

## 概述

本文件夹包含Rust 1.90版本中最成熟和最新的传统机器学习库相关内容。

## 主要库

### 1. Linfa

- **版本**: 0.7.1 (2025年最新)
- **特点**: Rust的scikit-learn等价物
- **功能**:
  - 分类、回归、聚类算法
  - 数据预处理和特征工程
  - 模型评估和验证
  - 管道和交叉验证
- **优势**:
  - 完整的机器学习工作流
  - 高性能实现
  - 丰富的算法支持
- **文档**: [Linfa官方文档](https://github.com/rust-ml/linfa)
- **示例**: 见 `examples/` 文件夹

### 2. SmartCore

- **版本**: 0.4.2 (2025年最新)
- **特点**: 纯Rust机器学习库
- **功能**:
  - 多种算法实现
  - Jupyter Notebook支持
  - 完整的API文档
  - 教育友好
- **优势**:
  - 纯Rust实现，无外部依赖
  - 文档完善
  - 适合学习和研究
- **文档**: [SmartCore官方文档](https://github.com/smartcorelib/smartcore)
- **示例**: 见 `examples/` 文件夹

### 3. 数值计算库

#### ndarray

- **版本**: 0.16.1 (2025年最新)
- **特点**: 多维数组库，类似NumPy
- **功能**:
  - 多维数组操作
  - 线性代数运算
  - 随机数生成
  - 并行计算支持
- **文档**: [ndarray官方文档](https://github.com/rust-ndarray/ndarray)

#### nalgebra

- **版本**: 0.34.1 (2025年最新)
- **特点**: 线性代数库
- **功能**:
  - 矩阵和向量运算
  - 几何变换
  - 数值分析
  - 3D图形支持
- **文档**: [nalgebra官方文档](https://github.com/dimforge/nalgebra)

## 算法支持

### 监督学习

- **分类**: 逻辑回归、SVM、随机森林、梯度提升
- **回归**: 线性回归、岭回归、Lasso、弹性网络
- **集成方法**: Bagging、Boosting、Stacking

### 无监督学习

- **聚类**: K-means、DBSCAN、层次聚类
- **降维**: PCA、t-SNE、UMAP
- **异常检测**: 孤立森林、LOF

### 模型评估

- **交叉验证**: K-fold、留一法、时间序列分割
- **指标**: 准确率、精确率、召回率、F1分数
- **可视化**: ROC曲线、混淆矩阵

## 库对比

| 库 | 成熟度 | 算法数量 | 性能 | 文档 | 推荐场景 |
|----|--------|----------|------|------|----------|
| Linfa | 高 | 丰富 | 高 | 完善 | 生产环境、完整工作流 |
| SmartCore | 中 | 中等 | 中 | 完善 | 学习、研究、教育 |
| ndarray | 高 | N/A | 高 | 完善 | 数值计算基础 |
| nalgebra | 高 | N/A | 高 | 完善 | 线性代数运算 |

## 使用建议

### 生产环境

- **首选**: Linfa + ndarray
- **原因**: 成熟稳定、性能优秀、功能完整

### 学习环境

- **首选**: SmartCore + ndarray
- **原因**: 文档完善、纯Rust实现、易于理解

### 研究环境

- **首选**: Linfa + nalgebra
- **原因**: 算法丰富、数学库完善

## 文件结构

```text
02_machine_learning_libraries/
├── README.md                    # 本文件
├── linfa/                       # Linfa相关
│   ├── examples/               # 示例代码
│   ├── docs/                   # 文档
│   ├── algorithms/             # 算法实现
│   └── benchmarks/             # 性能测试
├── smartcore/                  # SmartCore相关
│   ├── examples/               # 示例代码
│   ├── docs/                   # 文档
│   ├── algorithms/             # 算法实现
│   └── benchmarks/             # 性能测试
├── numerical/                  # 数值计算库
│   ├── ndarray/               # ndarray相关
│   ├── nalgebra/              # nalgebra相关
│   └── examples/              # 示例代码
├── algorithms/                 # 算法实现
│   ├── classification/        # 分类算法
│   ├── regression/            # 回归算法
│   ├── clustering/            # 聚类算法
│   └── preprocessing/         # 数据预处理
└── evaluation/                # 模型评估
    ├── metrics/               # 评估指标
    ├── validation/            # 验证方法
    └── visualization/         # 可视化
```

## 快速开始

### Linfa示例

```rust
use linfa::prelude::*;
use linfa_logistic::LogisticRegression;
use ndarray::array;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建示例数据
    let x = array![[1.0, 2.0], [3.0, 4.0], [5.0, 6.0]];
    let y = array![0, 1, 0];
    
    // 创建数据集
    let dataset = Dataset::new(x, y);
    
    // 训练模型
    let model = LogisticRegression::default()
        .fit(&dataset)?;
    
    // 进行预测
    let predictions = model.predict(&dataset);
    println!("预测结果: {:?}", predictions);
    
    Ok(())
}
```

### SmartCore示例

```rust
use smartcore::linalg::basic::matrix::DenseMatrix;
use smartcore::linear::logistic_regression::LogisticRegression;
use smartcore::metrics::accuracy;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建示例数据
    let x = DenseMatrix::from_2d_array(&[
        &[1.0, 2.0],
        &[3.0, 4.0],
        &[5.0, 6.0],
    ]);
    let y = vec![0, 1, 0];
    
    // 训练模型
    let model = LogisticRegression::fit(&x, &y, Default::default())?;
    
    // 进行预测
    let predictions = model.predict(&x)?;
    println!("预测结果: {:?}", predictions);
    
    // 计算准确率
    let acc = accuracy(&y, &predictions);
    println!("准确率: {:.2}", acc);
    
    Ok(())
}
```

### ndarray示例

```rust
use ndarray::{array, Array2, Axis};

fn main() {
    // 创建矩阵
    let a = array![[1.0, 2.0], [3.0, 4.0]];
    let b = array![[5.0, 6.0], [7.0, 8.0]];
    
    // 矩阵运算
    let c = &a + &b;
    println!("矩阵加法: {:?}", c);
    
    // 矩阵乘法
    let d = a.dot(&b);
    println!("矩阵乘法: {:?}", d);
    
    // 统计操作
    let mean = d.mean_axis(Axis(0));
    println!("列均值: {:?}", mean);
}
```

## 性能优化

1. **并行计算**: 使用Rayon进行数据并行
2. **内存优化**: 使用视图避免数据复制
3. **算法选择**: 根据数据规模选择合适的算法
4. **批处理**: 合理设置批处理大小

## 最佳实践

1. **数据预处理**: 标准化、归一化、特征选择
2. **模型选择**: 根据问题类型选择合适的算法
3. **交叉验证**: 使用适当的验证策略
4. **超参数调优**: 网格搜索、随机搜索、贝叶斯优化
5. **模型解释**: 特征重要性、SHAP值

## 相关资源

- [Rust机器学习生态](https://github.com/rust-ai/awesome-rust-ml)
- [机器学习最佳实践](https://github.com/rust-ai/ml-best-practices)
- [性能优化指南](https://github.com/rust-ai/ml-performance-guide)
