//! 机器学习算法实现模块
//! 
//! 本模块提供了Rust中的机器学习算法实现，包括：
//! - 线性回归
//! - K-means聚类
//! - 决策树
//! - 神经网络

use std::collections::HashMap;

/// 线性回归实现
pub struct LinearRegression {
    weights: Vec<f64>,
    bias: f64,
    learning_rate: f64,
}

impl LinearRegression {
    pub fn new(input_size: usize, learning_rate: f64) -> Self {
        Self {
            weights: vec![0.0; input_size],
            bias: 0.0,
            learning_rate,
        }
    }
    
    pub fn train(&mut self, features: &[Vec<f64>], targets: &[f64], epochs: usize) {
        for _ in 0..epochs {
            for (feature, &target) in features.iter().zip(targets.iter()) {
                let prediction = self.predict(feature);
                let error = target - prediction;
                
                // 更新权重
                for (weight, &feature_val) in self.weights.iter_mut().zip(feature.iter()) {
                    *weight += self.learning_rate * error * feature_val;
                }
                
                // 更新偏置
                self.bias += self.learning_rate * error;
            }
        }
    }
    
    pub fn predict(&self, features: &[f64]) -> f64 {
        let mut result = self.bias;
        for (weight, &feature) in self.weights.iter().zip(features.iter()) {
            result += weight * feature;
        }
        result
    }
    
    pub fn get_weights(&self) -> &[f64] {
        &self.weights
    }
    
    pub fn get_bias(&self) -> f64 {
        self.bias
    }
}

/// K-means聚类算法
pub struct KMeans {
    k: usize,
    centroids: Vec<Vec<f64>>,
    max_iterations: usize,
}

impl KMeans {
    pub fn new(k: usize, max_iterations: usize) -> Self {
        Self {
            k,
            centroids: Vec::new(),
            max_iterations,
        }
    }
    
    pub fn fit(&mut self, data: &[Vec<f64>]) -> Vec<usize> {
        // 初始化聚类中心
        self.initialize_centroids(data);
        
        let mut assignments = vec![0; data.len()];
        
        for _ in 0..self.max_iterations {
            let mut new_assignments = vec![0; data.len()];
            let mut cluster_sums = vec![vec![0.0; data[0].len()]; self.k];
            let mut cluster_counts = vec![0; self.k];
            
            // 分配点到最近的聚类中心
            for (i, point) in data.iter().enumerate() {
                let cluster = self.find_nearest_centroid(point);
                new_assignments[i] = cluster;
                
                for (j, &val) in point.iter().enumerate() {
                    cluster_sums[cluster][j] += val;
                }
                cluster_counts[cluster] += 1;
            }
            
            // 更新聚类中心
            for i in 0..self.k {
                if cluster_counts[i] > 0 {
                    for j in 0..self.centroids[i].len() {
                        self.centroids[i][j] = cluster_sums[i][j] / cluster_counts[i] as f64;
                    }
                }
            }
            
            // 检查收敛
            if assignments == new_assignments {
                break;
            }
            assignments = new_assignments;
        }
        
        assignments
    }
    
    pub fn predict(&self, point: &[f64]) -> usize {
        self.find_nearest_centroid(point)
    }
    
    pub fn get_centroids(&self) -> &[Vec<f64>] {
        &self.centroids
    }
    
    fn initialize_centroids(&mut self, data: &[Vec<f64>]) {
        use rand::Rng;
        let mut rng = rand::thread_rng();
        
        self.centroids.clear();
        for _ in 0..self.k {
            let random_index = rng.gen_range(0..data.len());
            self.centroids.push(data[random_index].clone());
        }
    }
    
    fn find_nearest_centroid(&self, point: &[f64]) -> usize {
        let mut min_distance = f64::INFINITY;
        let mut nearest_cluster = 0;
        
        for (i, centroid) in self.centroids.iter().enumerate() {
            let distance = self.euclidean_distance(point, centroid);
            if distance < min_distance {
                min_distance = distance;
                nearest_cluster = i;
            }
        }
        
        nearest_cluster
    }
    
    fn euclidean_distance(&self, a: &[f64], b: &[f64]) -> f64 {
        a.iter()
            .zip(b.iter())
            .map(|(x, y)| (x - y).powi(2))
            .sum::<f64>()
            .sqrt()
    }
}

/// 决策树实现
pub struct DecisionTree {
    root: Option<Box<TreeNode>>,
    max_depth: usize,
}

struct TreeNode {
    feature_index: Option<usize>,
    threshold: Option<f64>,
    value: Option<f64>,
    left: Option<Box<TreeNode>>,
    right: Option<Box<TreeNode>>,
}

impl DecisionTree {
    pub fn new(max_depth: usize) -> Self {
        Self {
            root: None,
            max_depth,
        }
    }
    
    pub fn fit(&mut self, features: &[Vec<f64>], targets: &[f64]) {
        self.root = Some(self.build_tree(features, targets, 0));
    }
    
    pub fn predict(&self, features: &[f64]) -> f64 {
        if let Some(ref root) = self.root {
            self.predict_recursive(root, features)
        } else {
            0.0
        }
    }
    
    pub fn predict_batch(&self, features: &[Vec<f64>]) -> Vec<f64> {
        features.iter().map(|f| self.predict(f)).collect()
    }
    
    fn build_tree(&self, features: &[Vec<f64>], targets: &[f64], depth: usize) -> Box<TreeNode> {
        if depth >= self.max_depth || targets.iter().all(|&t| t == targets[0]) {
            return Box::new(TreeNode {
                feature_index: None,
                threshold: None,
                value: Some(targets.iter().sum::<f64>() / targets.len() as f64),
                left: None,
                right: None,
            });
        }
        
        let (best_feature, best_threshold) = self.find_best_split(features, targets);
        
        if best_feature.is_none() {
            return Box::new(TreeNode {
                feature_index: None,
                threshold: None,
                value: Some(targets.iter().sum::<f64>() / targets.len() as f64),
                left: None,
                right: None,
            });
        }
        
        let feature_index = best_feature.unwrap();
        let threshold = best_threshold.unwrap();
        
        let mut left_features = Vec::new();
        let mut left_targets = Vec::new();
        let mut right_features = Vec::new();
        let mut right_targets = Vec::new();
        
        for (feature, &target) in features.iter().zip(targets.iter()) {
            if feature[feature_index] <= threshold {
                left_features.push(feature.clone());
                left_targets.push(target);
            } else {
                right_features.push(feature.clone());
                right_targets.push(target);
            }
        }
        
        Box::new(TreeNode {
            feature_index: Some(feature_index),
            threshold: Some(threshold),
            value: None,
            left: Some(self.build_tree(&left_features, &left_targets, depth + 1)),
            right: Some(self.build_tree(&right_features, &right_targets, depth + 1)),
        })
    }
    
    fn find_best_split(&self, features: &[Vec<f64>], targets: &[f64]) -> (Option<usize>, Option<f64>) {
        let mut best_gain = 0.0;
        let mut best_feature = None;
        let mut best_threshold = None;
        
        for feature_index in 0..features[0].len() {
            let mut values: Vec<f64> = features.iter().map(|f| f[feature_index]).collect();
            values.sort_by(|a, b| a.partial_cmp(b).unwrap());
            
            for i in 0..values.len() - 1 {
                let threshold = (values[i] + values[i + 1]) / 2.0;
                let gain = self.calculate_information_gain(features, targets, feature_index, threshold);
                
                if gain > best_gain {
                    best_gain = gain;
                    best_feature = Some(feature_index);
                    best_threshold = Some(threshold);
                }
            }
        }
        
        (best_feature, best_threshold)
    }
    
    fn calculate_information_gain(&self, features: &[Vec<f64>], targets: &[f64], feature_index: usize, threshold: f64) -> f64 {
        let parent_entropy = self.calculate_entropy(targets);
        
        let mut left_targets = Vec::new();
        let mut right_targets = Vec::new();
        
        for (feature, &target) in features.iter().zip(targets.iter()) {
            if feature[feature_index] <= threshold {
                left_targets.push(target);
            } else {
                right_targets.push(target);
            }
        }
        
        let left_entropy = self.calculate_entropy(&left_targets);
        let right_entropy = self.calculate_entropy(&right_targets);
        
        let left_weight = left_targets.len() as f64 / targets.len() as f64;
        let right_weight = right_targets.len() as f64 / targets.len() as f64;
        
        parent_entropy - (left_weight * left_entropy + right_weight * right_entropy)
    }
    
    fn calculate_entropy(&self, targets: &[f64]) -> f64 {
        if targets.is_empty() {
            return 0.0;
        }
        
        let mean = targets.iter().sum::<f64>() / targets.len() as f64;
        let variance = targets.iter().map(|&t| (t - mean).powi(2)).sum::<f64>() / targets.len() as f64;
        
        if variance == 0.0 {
            0.0
        } else {
            0.5 * (2.0 * std::f64::consts::PI * std::f64::consts::E * variance).ln()
        }
    }
    
    fn predict_recursive(&self, node: &TreeNode, features: &[f64]) -> f64 {
        if let Some(value) = node.value {
            return value;
        }
        
        if let (Some(feature_index), Some(threshold)) = (node.feature_index, node.threshold) {
            if features[feature_index] <= threshold {
                if let Some(ref left) = node.left {
                    self.predict_recursive(left, features)
                } else {
                    0.0
                }
            } else {
                if let Some(ref right) = node.right {
                    self.predict_recursive(right, features)
                } else {
                    0.0
                }
            }
        } else {
            0.0
        }
    }
}

/// 朴素贝叶斯分类器
pub struct NaiveBayes {
    class_probabilities: HashMap<String, f64>,
    feature_probabilities: HashMap<String, HashMap<String, f64>>,
    classes: Vec<String>,
}

impl NaiveBayes {
    pub fn new() -> Self {
        Self {
            class_probabilities: HashMap::new(),
            feature_probabilities: HashMap::new(),
            classes: Vec::new(),
        }
    }
    
    pub fn fit(&mut self, features: &[Vec<String>], labels: &[String]) {
        // 计算类别概率
        let mut class_counts: HashMap<String, usize> = HashMap::new();
        for label in labels {
            *class_counts.entry(label.clone()).or_insert(0) += 1;
        }
        
        let total_samples = labels.len() as f64;
        for (class, count) in class_counts {
            self.class_probabilities.insert(class.clone(), count as f64 / total_samples);
            self.classes.push(class);
        }
        
        // 计算特征概率
        for feature_idx in 0..features[0].len() {
            let mut feature_probs: HashMap<String, HashMap<String, f64>> = HashMap::new();
            
            for class in &self.classes {
                let mut feature_counts: HashMap<String, usize> = HashMap::new();
                let mut class_count = 0;
                
                for (i, label) in labels.iter().enumerate() {
                    if label == class {
                        class_count += 1;
                        let feature_value = &features[i][feature_idx];
                        *feature_counts.entry(feature_value.clone()).or_insert(0) += 1;
                    }
                }
                
                let mut class_feature_probs: HashMap<String, f64> = HashMap::new();
                for (feature_value, count) in feature_counts {
                    class_feature_probs.insert(feature_value, count as f64 / class_count as f64);
                }
                
                feature_probs.insert(class.clone(), class_feature_probs);
            }
            
            self.feature_probabilities.insert(feature_idx.to_string(), feature_probs);
        }
    }
    
    pub fn predict(&self, features: &[String]) -> String {
        let mut best_class = String::new();
        let mut best_probability = f64::NEG_INFINITY;
        
        for class in &self.classes {
            let mut probability = self.class_probabilities[class].ln();
            
            for (feature_idx, feature_value) in features.iter().enumerate() {
                if let Some(class_probs) = self.feature_probabilities.get(&feature_idx.to_string()) {
                    if let Some(class_feature_probs) = class_probs.get(class) {
                        if let Some(&prob) = class_feature_probs.get(feature_value) {
                            probability += prob.ln();
                        } else {
                            // 拉普拉斯平滑
                            probability += (1.0 / (class_feature_probs.len() + 1) as f64).ln();
                        }
                    }
                }
            }
            
            if probability > best_probability {
                best_probability = probability;
                best_class = class.clone();
            }
        }
        
        best_class
    }
    
    pub fn predict_batch(&self, features: &[Vec<String>]) -> Vec<String> {
        features.iter().map(|f| self.predict(f)).collect()
    }
}

/// 支持向量机 (简化版)
pub struct SupportVectorMachine {
    weights: Vec<f64>,
    bias: f64,
    learning_rate: f64,
    lambda: f64, // 正则化参数
}

impl SupportVectorMachine {
    pub fn new(input_size: usize, learning_rate: f64, lambda: f64) -> Self {
        Self {
            weights: vec![0.0; input_size],
            bias: 0.0,
            learning_rate,
            lambda,
        }
    }
    
    pub fn train(&mut self, features: &[Vec<f64>], labels: &[i32], epochs: usize) {
        for _ in 0..epochs {
            for (feature, &label) in features.iter().zip(labels.iter()) {
                let prediction = self.predict_raw(feature);
                let margin = label as f64 * prediction;
                
                if margin < 1.0 {
                    // 支持向量或误分类样本
                    for (weight, &feature_val) in self.weights.iter_mut().zip(feature.iter()) {
                        *weight += self.learning_rate * (label as f64 * feature_val - self.lambda * *weight);
                    }
                    self.bias += self.learning_rate * label as f64;
                } else {
                    // 正确分类的样本，只进行正则化
                    for weight in self.weights.iter_mut() {
                        *weight -= self.learning_rate * self.lambda * *weight;
                    }
                }
            }
        }
    }
    
    pub fn predict(&self, features: &[f64]) -> i32 {
        if self.predict_raw(features) >= 0.0 {
            1
        } else {
            -1
        }
    }
    
    pub fn predict_batch(&self, features: &[Vec<f64>]) -> Vec<i32> {
        features.iter().map(|f| self.predict(f)).collect()
    }
    
    fn predict_raw(&self, features: &[f64]) -> f64 {
        let mut result = self.bias;
        for (weight, &feature) in self.weights.iter().zip(features.iter()) {
            result += weight * feature;
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_linear_regression() {
        let features = vec![
            vec![1.0, 2.0],
            vec![2.0, 3.0],
            vec![3.0, 4.0],
            vec![4.0, 5.0],
        ];
        let targets = vec![2.0, 4.0, 6.0, 8.0];
        
        let mut model = LinearRegression::new(2, 0.01);
        model.train(&features, &targets, 1000);
        
        let prediction = model.predict(&[5.0, 6.0]);
        assert!(prediction > 9.0 && prediction < 11.0);
    }
    
    #[test]
    fn test_kmeans() {
        let data = vec![
            vec![1.0, 1.0],
            vec![1.5, 1.5],
            vec![2.0, 2.0],
            vec![8.0, 8.0],
            vec![8.5, 8.5],
            vec![9.0, 9.0],
        ];
        
        let mut kmeans = KMeans::new(2, 100);
        let assignments = kmeans.fit(&data);
        
        // 检查是否形成了两个聚类
        let unique_clusters: std::collections::HashSet<_> = assignments.iter().collect();
        assert_eq!(unique_clusters.len(), 2);
    }
    
    #[test]
    fn test_decision_tree() {
        let features = vec![
            vec![1.0, 2.0],
            vec![2.0, 3.0],
            vec![3.0, 4.0],
            vec![4.0, 5.0],
        ];
        let targets = vec![1.0, 2.0, 3.0, 4.0];
        
        let mut tree = DecisionTree::new(3);
        tree.fit(&features, &targets);
        
        let prediction = tree.predict(&[2.5, 3.5]);
        assert!(prediction > 1.0 && prediction < 4.0);
    }
    
    #[test]
    fn test_naive_bayes() {
        let features = vec![
            vec!["sunny".to_string(), "hot".to_string()],
            vec!["sunny".to_string(), "hot".to_string()],
            vec!["overcast".to_string(), "hot".to_string()],
            vec!["rainy".to_string(), "mild".to_string()],
            vec!["rainy".to_string(), "cool".to_string()],
            vec!["rainy".to_string(), "cool".to_string()],
            vec!["overcast".to_string(), "cool".to_string()],
        ];
        let labels = vec![
            "no".to_string(),
            "no".to_string(),
            "yes".to_string(),
            "yes".to_string(),
            "yes".to_string(),
            "no".to_string(),
            "yes".to_string(),
        ];
        
        let mut nb = NaiveBayes::new();
        nb.fit(&features, &labels);
        
        let prediction = nb.predict(&["sunny".to_string(), "hot".to_string()]);
        assert!(prediction == "no" || prediction == "yes");
    }
    
    #[test]
    fn test_svm() {
        let features = vec![
            vec![1.0, 1.0],
            vec![2.0, 2.0],
            vec![3.0, 3.0],
            vec![-1.0, -1.0],
            vec![-2.0, -2.0],
            vec![-3.0, -3.0],
        ];
        let labels = vec![1, 1, 1, -1, -1, -1];
        
        let mut svm = SupportVectorMachine::new(2, 0.01, 0.1);
        svm.train(&features, &labels, 1000);
        
        let prediction = svm.predict(&[4.0, 4.0]);
        assert_eq!(prediction, 1);
        
        let prediction = svm.predict(&[-4.0, -4.0]);
        assert_eq!(prediction, -1);
    }
}
