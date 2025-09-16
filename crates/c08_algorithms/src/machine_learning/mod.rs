//! 机器学习算法模块
//!
//! 本模块提供了常用的机器学习算法实现，包括：
//! - 聚类算法 (K-means, DBSCAN)
//! - 分类算法 (决策树, SVM)
//! - 神经网络 (基础神经网络)
//! - 回归算法 (线性回归, 逻辑回归)

pub mod clustering;
pub mod decision_tree;
pub mod kmeans;
pub mod naive_bayes;
pub mod neural_network;
pub mod regression;
pub mod svm;

use std::error::Error;
use std::fmt;

/// 机器学习算法错误类型
#[derive(Debug, Clone)]
pub enum MLError {
    /// 输入数据无效
    InvalidInput(String),
    /// 模型未训练
    ModelNotTrained,
    /// 训练失败
    TrainingFailed(String),
    /// 预测失败
    PredictionFailed(String),
    /// 维度不匹配
    DimensionMismatch { expected: usize, actual: usize },
}

impl fmt::Display for MLError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MLError::InvalidInput(msg) => write!(f, "无效输入: {}", msg),
            MLError::ModelNotTrained => write!(f, "模型尚未训练"),
            MLError::TrainingFailed(msg) => write!(f, "训练失败: {}", msg),
            MLError::PredictionFailed(msg) => write!(f, "预测失败: {}", msg),
            MLError::DimensionMismatch { expected, actual } => {
                write!(f, "维度不匹配: 期望 {}, 实际 {}", expected, actual)
            }
        }
    }
}

impl Error for MLError {}

/// 机器学习算法结果类型
pub type MLResult<T> = Result<T, MLError>;

/// 数据点表示
pub type DataPoint = Vec<f64>;

/// 数据集表示
pub type Dataset = Vec<DataPoint>;

/// 标签类型
pub type Label = i32;

/// 标签集合
pub type Labels = Vec<Label>;

/// 监督学习算法 Trait
pub trait SupervisedLearning {
    /// 训练模型
    fn train(&mut self, data: &Dataset, labels: &Labels) -> MLResult<()>;

    /// 预测单个样本
    fn predict(&self, sample: &DataPoint) -> MLResult<Label>;

    /// 批量预测
    fn predict_batch(&self, data: &Dataset) -> MLResult<Labels> {
        data.iter().map(|sample| self.predict(sample)).collect()
    }

    /// 评估模型准确度
    fn accuracy(&self, data: &Dataset, labels: &Labels) -> MLResult<f64> {
        let predictions = self.predict_batch(data)?;
        let correct = predictions
            .iter()
            .zip(labels.iter())
            .filter(|(pred, actual)| pred == actual)
            .count();
        Ok(correct as f64 / labels.len() as f64)
    }
}

/// 无监督学习算法 Trait
pub trait UnsupervisedLearning {
    /// 训练模型
    fn fit(&mut self, data: &Dataset) -> MLResult<()>;

    /// 获取聚类结果
    fn predict(&self, data: &Dataset) -> MLResult<Labels>;

    /// 获取聚类中心（如适用）
    fn cluster_centers(&self) -> Option<Dataset> {
        None
    }
}

/// 回归算法 Trait
pub trait Regression {
    /// 训练模型
    fn train(&mut self, data: &Dataset, targets: &[f64]) -> MLResult<()>;

    /// 预测单个样本
    fn predict(&self, sample: &DataPoint) -> MLResult<f64>;

    /// 批量预测
    fn predict_batch(&self, data: &Dataset) -> MLResult<Vec<f64>> {
        data.iter().map(|sample| self.predict(sample)).collect()
    }

    /// 计算均方误差
    fn mse(&self, data: &Dataset, targets: &[f64]) -> MLResult<f64> {
        let predictions = self.predict_batch(data)?;
        let mse = predictions
            .iter()
            .zip(targets.iter())
            .map(|(pred, actual)| (pred - actual).powi(2))
            .sum::<f64>()
            / targets.len() as f64;
        Ok(mse)
    }

    /// 计算R²分数
    fn r2_score(&self, data: &Dataset, targets: &[f64]) -> MLResult<f64> {
        let predictions = self.predict_batch(data)?;
        let mean_target = targets.iter().sum::<f64>() / targets.len() as f64;

        let ss_res: f64 = predictions
            .iter()
            .zip(targets.iter())
            .map(|(pred, actual)| (actual - pred).powi(2))
            .sum();

        let ss_tot: f64 = targets
            .iter()
            .map(|actual| (actual - mean_target).powi(2))
            .sum();

        Ok(1.0 - ss_res / ss_tot)
    }
}

/// 模型评估指标
pub struct Metrics {
    pub accuracy: f64,
    pub precision: f64,
    pub recall: f64,
    pub f1_score: f64,
}

impl Metrics {
    /// 计算分类指标
    pub fn compute_classification_metrics(predictions: &Labels, actual: &Labels) -> MLResult<Self> {
        if predictions.len() != actual.len() {
            return Err(MLError::DimensionMismatch {
                expected: actual.len(),
                actual: predictions.len(),
            });
        }

        let mut tp = 0;
        let mut fp = 0;
        let mut tn = 0;
        let mut fn_count = 0;

        for (pred, actual) in predictions.iter().zip(actual.iter()) {
            match (pred, actual) {
                (1, 1) => tp += 1,
                (1, 0) => fp += 1,
                (0, 0) => tn += 1,
                (0, 1) => fn_count += 1,
                _ => {} // 多分类情况简化处理
            }
        }

        let accuracy = (tp + tn) as f64 / predictions.len() as f64;
        let precision = if tp + fp > 0 {
            tp as f64 / (tp + fp) as f64
        } else {
            0.0
        };
        let recall = if tp + fn_count > 0 {
            tp as f64 / (tp + fn_count) as f64
        } else {
            0.0
        };
        let f1_score = if precision + recall > 0.0 {
            2.0 * precision * recall / (precision + recall)
        } else {
            0.0
        };

        Ok(Metrics {
            accuracy,
            precision,
            recall,
            f1_score,
        })
    }
}

/// 数据预处理工具
pub mod preprocessing {
    use super::*;

    /// 标准化数据
    pub fn standardize(data: &mut Dataset) -> MLResult<(Vec<f64>, Vec<f64>)> {
        if data.is_empty() {
            return Err(MLError::InvalidInput("数据集为空".to_string()));
        }

        let n_features = data[0].len();
        let mut means = vec![0.0; n_features];
        let mut stds = vec![0.0; n_features];

        // 计算均值
        for sample in data.iter() {
            for (i, &value) in sample.iter().enumerate() {
                means[i] += value;
            }
        }
        for mean in means.iter_mut() {
            *mean /= data.len() as f64;
        }

        // 计算标准差
        for sample in data.iter() {
            for (i, &value) in sample.iter().enumerate() {
                stds[i] += (value - means[i]).powi(2);
            }
        }
        for std in stds.iter_mut() {
            *std = (*std / data.len() as f64).sqrt();
            if *std == 0.0 {
                *std = 1.0; // 避免除零
            }
        }

        // 标准化数据
        for sample in data.iter_mut() {
            for (i, value) in sample.iter_mut().enumerate() {
                *value = (*value - means[i]) / stds[i];
            }
        }

        Ok((means, stds))
    }

    /// 归一化到 [0, 1] 范围
    pub fn normalize(data: &mut Dataset) -> MLResult<(Vec<f64>, Vec<f64>)> {
        if data.is_empty() {
            return Err(MLError::InvalidInput("数据集为空".to_string()));
        }

        let n_features = data[0].len();
        let mut mins = vec![f64::INFINITY; n_features];
        let mut maxs = vec![f64::NEG_INFINITY; n_features];

        // 找到最小值和最大值
        for sample in data.iter() {
            for (i, &value) in sample.iter().enumerate() {
                mins[i] = mins[i].min(value);
                maxs[i] = maxs[i].max(value);
            }
        }

        // 归一化数据
        for sample in data.iter_mut() {
            for (i, value) in sample.iter_mut().enumerate() {
                let range = maxs[i] - mins[i];
                if range > 0.0 {
                    *value = (*value - mins[i]) / range;
                } else {
                    *value = 0.0;
                }
            }
        }

        Ok((mins, maxs))
    }

    /// 训练测试集分割
    pub fn train_test_split(
        data: &Dataset,
        labels: &Labels,
        test_size: f64,
    ) -> MLResult<(Dataset, Dataset, Labels, Labels)> {
        if data.len() != labels.len() {
            return Err(MLError::DimensionMismatch {
                expected: data.len(),
                actual: labels.len(),
            });
        }

        if test_size <= 0.0 || test_size >= 1.0 {
            return Err(MLError::InvalidInput(
                "test_size 必须在 (0, 1) 范围内".to_string(),
            ));
        }

        use rand::seq::SliceRandom;

        let mut indices: Vec<usize> = (0..data.len()).collect();
        use rand::rngs::ThreadRng;
        indices.shuffle(&mut ThreadRng::default());

        let test_count = (data.len() as f64 * test_size).round() as usize;
        let train_count = data.len() - test_count;

        let (train_indices, test_indices) = indices.split_at(train_count);

        let train_data: Dataset = train_indices.iter().map(|&i| data[i].clone()).collect();
        let test_data: Dataset = test_indices.iter().map(|&i| data[i].clone()).collect();
        let train_labels: Labels = train_indices.iter().map(|&i| labels[i]).collect();
        let test_labels: Labels = test_indices.iter().map(|&i| labels[i]).collect();

        Ok((train_data, test_data, train_labels, test_labels))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_standardize() {
        let mut data = vec![vec![1.0, 2.0], vec![3.0, 4.0], vec![5.0, 6.0]];

        let result = preprocessing::standardize(&mut data);
        assert!(result.is_ok());

        let (means, stds) = result.unwrap();
        assert_eq!(means, vec![3.0, 4.0]);
        // population std: sqrt(((4+0+4)/3)) = sqrt(8/3)
        let expected_std = (8.0f64 / 3.0).sqrt();
        assert!((stds[0] - expected_std).abs() < 1e-10);
        assert!((stds[1] - expected_std).abs() < 1e-10);
        // standardized data should have mean ~0
        for feature in 0..2 {
            let mean_after: f64 = data.iter().map(|r| r[feature]).sum::<f64>() / data.len() as f64;
            assert!(mean_after.abs() < 1e-12);
        }
    }

    #[test]
    fn test_normalize() {
        let mut data = vec![vec![1.0, 2.0], vec![3.0, 4.0], vec![5.0, 6.0]];

        let result = preprocessing::normalize(&mut data);
        assert!(result.is_ok());

        let (mins, maxs) = result.unwrap();
        assert_eq!(mins, vec![1.0, 2.0]);
        assert_eq!(maxs, vec![5.0, 6.0]);

        // 检查归一化结果
        assert_eq!(data[0], vec![0.0, 0.0]);
        assert_eq!(data[2], vec![1.0, 1.0]);
    }

    #[test]
    fn test_train_test_split() {
        let data = vec![
            vec![1.0, 2.0],
            vec![3.0, 4.0],
            vec![5.0, 6.0],
            vec![7.0, 8.0],
        ];
        let labels = vec![0, 1, 0, 1];

        let result = preprocessing::train_test_split(&data, &labels, 0.25);
        assert!(result.is_ok());

        let (train_data, test_data, train_labels, test_labels) = result.unwrap();
        assert_eq!(train_data.len(), 3);
        assert_eq!(test_data.len(), 1);
        assert_eq!(train_labels.len(), 3);
        assert_eq!(test_labels.len(), 1);
    }

    #[test]
    fn test_metrics_computation() {
        let predictions = vec![1, 0, 1, 0, 1];
        let actual = vec![1, 0, 0, 0, 1];

        let metrics = Metrics::compute_classification_metrics(&predictions, &actual).unwrap();
        assert_eq!(metrics.accuracy, 0.8);
        assert_eq!(metrics.precision, 2.0 / 3.0);
        assert_eq!(metrics.recall, 1.0);
    }
}
