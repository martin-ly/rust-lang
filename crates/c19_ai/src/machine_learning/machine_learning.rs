// 机器学习模块
// Machine Learning Module

use serde::{Deserialize, Serialize};
// use std::collections::HashMap;

/// 机器学习算法类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum MLAlgorithm {
    LinearRegression,
    LogisticRegression,
    DecisionTree,
    RandomForest,
    KMeans,
    SVM,
}

/// 训练数据点
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DataPoint {
    pub features: Vec<f64>,
    pub label: Option<f64>, // None for unsupervised learning
}

/// 训练数据集
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Dataset {
    pub data: Vec<DataPoint>,
    pub feature_names: Vec<String>,
}

impl Dataset {
    /// 创建新的数据集
    pub fn new(feature_names: Vec<String>) -> Self {
        Self {
            data: Vec::new(),
            feature_names,
        }
    }

    /// 添加数据点
    pub fn add_point(&mut self, features: Vec<f64>, label: Option<f64>) {
        self.data.push(DataPoint { features, label });
    }

    /// 获取特征数量
    pub fn feature_count(&self) -> usize {
        self.feature_names.len()
    }

    /// 获取数据点数量
    pub fn size(&self) -> usize {
        self.data.len()
    }
}

/// 线性回归模型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LinearRegression {
    pub weights: Vec<f64>,
    pub bias: f64,
    pub learning_rate: f64,
}

impl LinearRegression {
    /// 创建新的线性回归模型
    pub fn new(feature_count: usize, learning_rate: f64) -> Self {
        Self {
            weights: vec![0.0; feature_count],
            bias: 0.0,
            learning_rate,
        }
    }

    /// 预测
    pub fn predict(&self, features: &[f64]) -> f64 {
        let mut prediction = self.bias;
        for (i, &feature) in features.iter().enumerate() {
            prediction += self.weights[i] * feature;
        }
        prediction
    }

    /// 训练模型
    pub fn train(&mut self, dataset: &Dataset, epochs: usize) {
        for _ in 0..epochs {
            for point in &dataset.data {
                if let Some(label) = point.label {
                    let prediction = self.predict(&point.features);
                    let error = label - prediction;

                    // 更新权重
                    for (i, &feature) in point.features.iter().enumerate() {
                        self.weights[i] += self.learning_rate * error * feature;
                    }

                    // 更新偏置
                    self.bias += self.learning_rate * error;
                }
            }
        }
    }
}

/// K-means聚类
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct KMeans {
    pub centroids: Vec<Vec<f64>>,
    pub k: usize,
}

impl KMeans {
    /// 创建新的K-means模型
    pub fn new(k: usize) -> Self {
        Self {
            centroids: Vec::new(),
            k,
        }
    }

    /// 训练模型
    pub fn fit(&mut self, dataset: &Dataset) {
        if dataset.data.is_empty() {
            return;
        }

        let feature_count = dataset.feature_count();

        // 随机初始化质心
        self.centroids.clear();
        for _ in 0..self.k {
            let mut centroid = Vec::new();
            for _ in 0..feature_count {
                centroid.push(rand::random::<f64>());
            }
            self.centroids.push(centroid);
        }

        // 迭代优化
        for _ in 0..100 {
            let mut clusters: Vec<Vec<usize>> = vec![Vec::new(); self.k];

            // 分配数据点到最近的质心
            for (i, point) in dataset.data.iter().enumerate() {
                let mut min_distance = f64::INFINITY;
                let mut closest_centroid = 0;

                for (j, centroid) in self.centroids.iter().enumerate() {
                    let distance = self.euclidean_distance(&point.features, centroid);
                    if distance < min_distance {
                        min_distance = distance;
                        closest_centroid = j;
                    }
                }

                clusters[closest_centroid].push(i);
            }

            // 更新质心
            for (i, cluster) in clusters.iter().enumerate() {
                if !cluster.is_empty() {
                    for j in 0..feature_count {
                        let sum: f64 = cluster
                            .iter()
                            .map(|&idx| dataset.data[idx].features[j])
                            .sum();
                        self.centroids[i][j] = sum / cluster.len() as f64;
                    }
                }
            }
        }
    }

    /// 预测数据点属于哪个聚类
    pub fn predict(&self, features: &[f64]) -> usize {
        let mut min_distance = f64::INFINITY;
        let mut closest_centroid = 0;

        for (i, centroid) in self.centroids.iter().enumerate() {
            let distance = self.euclidean_distance(features, centroid);
            if distance < min_distance {
                min_distance = distance;
                closest_centroid = i;
            }
        }

        closest_centroid
    }

    /// 计算欧几里得距离
    fn euclidean_distance(&self, a: &[f64], b: &[f64]) -> f64 {
        a.iter()
            .zip(b.iter())
            .map(|(x, y)| (x - y).powi(2))
            .sum::<f64>()
            .sqrt()
    }
}

/// 机器学习模型训练器
pub struct MLTrainer {
    pub algorithm: MLAlgorithm,
}

impl MLTrainer {
    /// 创建新的训练器
    pub fn new(algorithm: MLAlgorithm) -> Self {
        Self { algorithm }
    }

    /// 训练模型
    pub fn train(&self, dataset: &Dataset) -> String {
        match &self.algorithm {
            MLAlgorithm::LinearRegression => {
                let mut model = LinearRegression::new(dataset.feature_count(), 0.01);
                model.train(dataset, 1000);
                "线性回归模型训练完成".to_string()
            }
            MLAlgorithm::KMeans => {
                let mut model = KMeans::new(3);
                model.fit(dataset);
                "K-means聚类模型训练完成".to_string()
            }
            _ => "算法暂未实现".to_string(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dataset_creation() {
        let mut dataset = Dataset::new(vec!["feature1".to_string(), "feature2".to_string()]);
        dataset.add_point(vec![1.0, 2.0], Some(3.0));
        dataset.add_point(vec![2.0, 3.0], Some(5.0));

        assert_eq!(dataset.size(), 2);
        assert_eq!(dataset.feature_count(), 2);
    }

    #[test]
    fn test_linear_regression() {
        let mut dataset = Dataset::new(vec!["x".to_string()]);
        dataset.add_point(vec![1.0], Some(2.0));
        dataset.add_point(vec![2.0], Some(4.0));
        dataset.add_point(vec![3.0], Some(6.0));

        let mut model = LinearRegression::new(1, 0.01);
        model.train(&dataset, 100);

        let prediction = model.predict(&[4.0]);
        assert!(prediction > 7.0 && prediction < 9.0);
    }

    #[test]
    fn test_kmeans() {
        let mut dataset = Dataset::new(vec!["x".to_string(), "y".to_string()]);
        dataset.add_point(vec![1.0, 1.0], None);
        dataset.add_point(vec![1.1, 1.1], None);
        dataset.add_point(vec![5.0, 5.0], None);
        dataset.add_point(vec![5.1, 5.1], None);

        let mut model = KMeans::new(2);
        model.fit(&dataset);

        let cluster = model.predict(&[1.0, 1.0]);
        assert!(cluster < 2);
    }
}
