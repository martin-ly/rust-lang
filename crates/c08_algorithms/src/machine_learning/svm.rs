//! 支持向量机（SVM）算法实现
//!
//! 本模块提供了支持向量机算法的基础实现

use super::*;

/// 支持向量机分类器（简化版本）
#[derive(Debug, Clone)]
pub struct SVMClassifier {
    /// 是否已训练
    is_fitted: bool,
    /// 权重向量
    weights: Option<Vec<f64>>,
    /// 偏置
    bias: Option<f64>,
}

impl SVMClassifier {
    /// 创建新的 SVM 分类器
    pub fn new() -> Self {
        Self {
            is_fitted: false,
            weights: None,
            bias: None,
        }
    }
}

impl Default for SVMClassifier {
    fn default() -> Self {
        Self::new()
    }
}

impl SupervisedLearning for SVMClassifier {
    fn train(&mut self, data: &Dataset, labels: &Labels) -> MLResult<()> {
        if data.is_empty() || labels.is_empty() {
            return Err(MLError::InvalidInput("数据集不能为空".to_string()));
        }

        // 简化实现：使用感知机算法近似
        if let Some(first_sample) = data.first() {
            let mut weights = vec![0.0; first_sample.len()];
            let mut bias = 0.0;
            let learning_rate = 0.1;

            for _ in 0..100 {
                // 简单的迭代次数
                for (sample, &label) in data.iter().zip(labels.iter()) {
                    let prediction = sample
                        .iter()
                        .zip(weights.iter())
                        .map(|(x, w)| x * w)
                        .sum::<f64>()
                        + bias;

                    let predicted_class = if prediction >= 0.0 { 1 } else { 0 };

                    if predicted_class != label {
                        // 更新权重
                        for (w, &x) in weights.iter_mut().zip(sample.iter()) {
                            *w += learning_rate * (label as f64) * x;
                        }
                        bias += learning_rate * (label as f64);
                    }
                }
            }

            self.weights = Some(weights);
            self.bias = Some(bias);
        }

        self.is_fitted = true;
        Ok(())
    }

    fn predict(&self, sample: &DataPoint) -> MLResult<Label> {
        if !self.is_fitted {
            return Err(MLError::ModelNotTrained);
        }

        if let (Some(weights), Some(bias)) = (&self.weights, &self.bias) {
            let prediction = sample
                .iter()
                .zip(weights.iter())
                .map(|(x, w)| x * w)
                .sum::<f64>()
                + bias;

            Ok(if prediction >= 0.0 { 1 } else { 0 })
        } else {
            Err(MLError::ModelNotTrained)
        }
    }
}
