//! 朴素贝叶斯分类器实现
//!
//! 本模块提供了朴素贝叶斯分类器的基础实现

use super::*;
use std::collections::HashMap;

/// 朴素贝叶斯分类器
#[derive(Debug, Clone)]
pub struct NaiveBayesClassifier {
    /// 是否已训练
    is_fitted: bool,
    /// 类别先验概率
    class_priors: Option<HashMap<Label, f64>>,
    /// 特征条件概率
    feature_conditionals: Option<HashMap<Label, Vec<(f64, f64)>>>,
    /// 类别标签
    classes: Option<Vec<Label>>,
    /// 拉普拉斯平滑参数
    alpha: f64,
}

impl NaiveBayesClassifier {
    /// 创建新的朴素贝叶斯分类器
    pub fn new() -> Self {
        Self {
            is_fitted: false,
            class_priors: None,
            feature_conditionals: None,
            classes: None,
            alpha: 1.0, // 拉普拉斯平滑
        }
    }

    /// 设置拉普拉斯平滑参数
    pub fn alpha(mut self, alpha: f64) -> Self {
        self.alpha = alpha;
        self
    }

    /// 计算特征的条件概率（高斯分布假设）
    fn calculate_gaussian_probability(&self, feature_value: f64, mean: f64, variance: f64) -> f64 {
        if variance == 0.0 {
            return if (feature_value - mean).abs() < 1e-10 {
                1.0
            } else {
                0.0
            };
        }

        let coefficient = 1.0 / (2.0 * std::f64::consts::PI * variance).sqrt();
        let exponent = -((feature_value - mean).powi(2)) / (2.0 * variance);

        coefficient * exponent.exp()
    }

    /// 计算特征的均值和方差
    fn calculate_feature_stats(
        &self,
        data: &Dataset,
        labels: &Labels,
        class: Label,
    ) -> Vec<(f64, f64)> {
        let class_data: Vec<&DataPoint> = data
            .iter()
            .zip(labels.iter())
            .filter(|(_, label)| **label == class)
            .map(|(point, _)| point)
            .collect();

        if class_data.is_empty() {
            return vec![(0.0, 1.0); data[0].len()];
        }

        let n_features = data[0].len();
        let mut stats = Vec::with_capacity(n_features);

        for feature_idx in 0..n_features {
            let values: Vec<f64> = class_data.iter().map(|point| point[feature_idx]).collect();

            let mean = values.iter().sum::<f64>() / values.len() as f64;
            let variance =
                values.iter().map(|&x| (x - mean).powi(2)).sum::<f64>() / values.len() as f64;

            stats.push((mean, variance));
        }

        stats
    }
}

impl Default for NaiveBayesClassifier {
    fn default() -> Self {
        Self::new()
    }
}

impl SupervisedLearning for NaiveBayesClassifier {
    fn train(&mut self, data: &Dataset, labels: &Labels) -> MLResult<()> {
        if data.is_empty() || labels.is_empty() {
            return Err(MLError::InvalidInput("数据集不能为空".to_string()));
        }

        if data.len() != labels.len() {
            return Err(MLError::DimensionMismatch {
                expected: data.len(),
                actual: labels.len(),
            });
        }

        // 获取所有类别
        let mut classes: Vec<Label> = labels.to_vec();
        classes.sort();
        classes.dedup();
        self.classes = Some(classes.clone());

        // 计算类别先验概率
        let mut class_counts = HashMap::new();
        for &label in labels.iter() {
            *class_counts.entry(label).or_insert(0) += 1;
        }

        let total_samples = data.len() as f64;
        let mut class_priors = HashMap::new();
        for (class, count) in class_counts.iter() {
            class_priors.insert(
                *class,
                (*count as f64 + self.alpha) / (total_samples + self.alpha * classes.len() as f64),
            );
        }
        self.class_priors = Some(class_priors);

        // 计算每个类别每个特征的条件概率
        let mut feature_conditionals = HashMap::new();
        for &class in classes.iter() {
            let feature_stats = self.calculate_feature_stats(data, labels, class);
            feature_conditionals.insert(class, feature_stats);
        }
        self.feature_conditionals = Some(feature_conditionals);

        self.is_fitted = true;
        Ok(())
    }

    fn predict(&self, sample: &DataPoint) -> MLResult<Label> {
        if !self.is_fitted {
            return Err(MLError::ModelNotTrained);
        }

        let classes = self.classes.as_ref().unwrap();
        let class_priors = self.class_priors.as_ref().unwrap();
        let feature_conditionals = self.feature_conditionals.as_ref().unwrap();

        let mut best_class = classes[0];
        let mut best_log_probability = f64::NEG_INFINITY;

        for &class in classes.iter() {
            let prior = class_priors.get(&class).unwrap_or(&0.0);
            let mut log_probability = prior.ln();

            let feature_stats = feature_conditionals.get(&class).unwrap();
            for (feature_idx, &feature_value) in sample.iter().enumerate() {
                if let Some(&(mean, variance)) = feature_stats.get(feature_idx) {
                    let prob = self.calculate_gaussian_probability(feature_value, mean, variance);
                    if prob > 0.0 {
                        log_probability += prob.ln();
                    } else {
                        log_probability += f64::NEG_INFINITY;
                    }
                }
            }

            if log_probability > best_log_probability {
                best_log_probability = log_probability;
                best_class = class;
            }
        }

        Ok(best_class)
    }
}

/// 多项式朴素贝叶斯分类器（适用于离散特征）
#[derive(Debug, Clone)]
pub struct MultinomialNaiveBayes {
    /// 是否已训练
    is_fitted: bool,
    /// 类别先验概率
    class_priors: Option<HashMap<Label, f64>>,
    /// 特征条件概率
    feature_conditionals: Option<HashMap<Label, Vec<f64>>>,
    /// 类别标签
    classes: Option<Vec<Label>>,
    /// 拉普拉斯平滑参数
    alpha: f64,
}

impl MultinomialNaiveBayes {
    /// 创建新的多项式朴素贝叶斯分类器
    pub fn new() -> Self {
        Self {
            is_fitted: false,
            class_priors: None,
            feature_conditionals: None,
            classes: None,
            alpha: 1.0,
        }
    }

    /// 设置拉普拉斯平滑参数
    pub fn alpha(mut self, alpha: f64) -> Self {
        self.alpha = alpha;
        self
    }
}

impl Default for MultinomialNaiveBayes {
    fn default() -> Self {
        Self::new()
    }
}

impl SupervisedLearning for MultinomialNaiveBayes {
    fn train(&mut self, data: &Dataset, labels: &Labels) -> MLResult<()> {
        if data.is_empty() || labels.is_empty() {
            return Err(MLError::InvalidInput("数据集不能为空".to_string()));
        }

        if data.len() != labels.len() {
            return Err(MLError::DimensionMismatch {
                expected: data.len(),
                actual: labels.len(),
            });
        }

        // 获取所有类别
        let mut classes: Vec<Label> = labels.to_vec();
        classes.sort();
        classes.dedup();
        self.classes = Some(classes.clone());

        // 计算类别先验概率
        let mut class_counts = HashMap::new();
        for &label in labels.iter() {
            *class_counts.entry(label).or_insert(0) += 1;
        }

        let total_samples = data.len() as f64;
        let mut class_priors = HashMap::new();
        for (class, count) in class_counts.iter() {
            class_priors.insert(
                *class,
                (*count as f64 + self.alpha) / (total_samples + self.alpha * classes.len() as f64),
            );
        }
        self.class_priors = Some(class_priors);

        // 计算每个类别每个特征的条件概率
        let mut feature_conditionals = HashMap::new();
        let n_features = data[0].len();

        for &class in classes.iter() {
            let class_data: Vec<&DataPoint> = data
                .iter()
                .zip(labels.iter())
                .filter(|(_, label)| **label == class)
                .map(|(point, _)| point)
                .collect();

            let mut feature_probs = vec![0.0; n_features];
            let mut total_feature_sum = 0.0;

            // 计算每个特征的总和
            for point in class_data.iter() {
                for (i, &value) in point.iter().enumerate() {
                    feature_probs[i] += value;
                    total_feature_sum += value;
                }
            }

            // 应用拉普拉斯平滑
            for prob in feature_probs.iter_mut() {
                *prob = (*prob + self.alpha) / (total_feature_sum + self.alpha * n_features as f64);
            }

            feature_conditionals.insert(class, feature_probs);
        }

        self.feature_conditionals = Some(feature_conditionals);
        self.is_fitted = true;
        Ok(())
    }

    fn predict(&self, sample: &DataPoint) -> MLResult<Label> {
        if !self.is_fitted {
            return Err(MLError::ModelNotTrained);
        }

        let classes = self.classes.as_ref().unwrap();
        let class_priors = self.class_priors.as_ref().unwrap();
        let feature_conditionals = self.feature_conditionals.as_ref().unwrap();

        let mut best_class = classes[0];
        let mut best_log_probability = f64::NEG_INFINITY;

        for &class in classes.iter() {
            let prior = class_priors.get(&class).unwrap_or(&0.0);
            let mut log_probability = prior.ln();

            let feature_probs = feature_conditionals.get(&class).unwrap();
            for (feature_idx, &feature_value) in sample.iter().enumerate() {
                if let Some(&prob) = feature_probs.get(feature_idx)
                    && prob > 0.0 && feature_value > 0.0 {
                        log_probability += feature_value * prob.ln();
                    }
            }

            if log_probability > best_log_probability {
                best_log_probability = log_probability;
                best_class = class;
            }
        }

        Ok(best_class)
    }
}

/// 异步版本的朴素贝叶斯训练
pub async fn naive_bayes_fit_async(
    data: Dataset,
    labels: Labels,
    alpha: Option<f64>,
) -> MLResult<NaiveBayesClassifier> {
    tokio::task::spawn_blocking(move || {
        let mut nb = NaiveBayesClassifier::new();
        if let Some(alpha_val) = alpha {
            nb = nb.alpha(alpha_val);
        }

        nb.train(&data, &labels)?;
        Ok(nb)
    })
    .await
    .map_err(|e| MLError::TrainingFailed(format!("异步训练失败: {}", e)))?
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_naive_bayes_basic() {
        let data = vec![
            vec![1.0, 1.0],
            vec![1.0, 2.0],
            vec![2.0, 1.0],
            vec![2.0, 2.0],
            vec![5.0, 5.0],
            vec![6.0, 5.0],
            vec![5.0, 6.0],
            vec![6.0, 6.0],
        ];
        let labels = vec![0, 0, 0, 0, 1, 1, 1, 1];

        let mut nb = NaiveBayesClassifier::new();
        let result = nb.train(&data, &labels);
        assert!(result.is_ok());

        let prediction = nb.predict(&vec![1.5, 1.5]).unwrap();
        assert_eq!(prediction, 0);

        let prediction = nb.predict(&vec![5.5, 5.5]).unwrap();
        assert_eq!(prediction, 1);
    }

    #[test]
    fn test_multinomial_naive_bayes() {
        let data = vec![
            vec![2.0, 1.0, 0.0],
            vec![1.0, 2.0, 1.0],
            vec![0.0, 1.0, 2.0],
            vec![1.0, 0.0, 2.0],
        ];
        let labels = vec![0, 0, 1, 1];

        let mut mnb = MultinomialNaiveBayes::new();
        let result = mnb.train(&data, &labels);
        assert!(result.is_ok());

        let prediction = mnb.predict(&vec![1.0, 1.0, 0.0]).unwrap();
        assert!(prediction == 0 || prediction == 1);
    }

    #[test]
    fn test_naive_bayes_empty_data() {
        let data = vec![];
        let labels = vec![];
        let mut nb = NaiveBayesClassifier::new();
        let result = nb.train(&data, &labels);
        assert!(result.is_err());
    }

    #[tokio::test]
    async fn test_naive_bayes_async() {
        let data = vec![
            vec![1.0, 1.0],
            vec![2.0, 2.0],
            vec![5.0, 5.0],
            vec![6.0, 6.0],
        ];
        let labels = vec![0, 0, 1, 1];

        let result = naive_bayes_fit_async(data.clone(), labels, Some(0.5)).await;
        assert!(result.is_ok());

        let nb = result.unwrap();
        let prediction = nb.predict(&vec![1.5, 1.5]).unwrap();
        assert_eq!(prediction, 0);
    }
}
