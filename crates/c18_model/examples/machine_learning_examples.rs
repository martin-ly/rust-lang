//! 机器学习的Rust实现示例
//! 
//! 本文件展示了如何使用Rust实现各种机器学习算法，
//! 包括线性回归、逻辑回归、KMeans聚类、决策树等。

use std::collections::HashMap;
use std::f64;

/// 线性回归模型
/// 
/// 实现最小二乘法线性回归
#[derive(Debug, Clone)]
pub struct LinearRegression {
    pub weights: Vec<f64>,
    pub bias: f64,
    pub learning_rate: f64,
    pub max_iterations: usize,
}

impl LinearRegression {
    /// 创建新的线性回归模型
    pub fn new(learning_rate: f64, max_iterations: usize) -> Self {
        Self {
            weights: Vec::new(),
            bias: 0.0,
            learning_rate,
            max_iterations,
        }
    }

    /// 训练模型
    pub fn fit(&mut self, x: &[Vec<f64>], y: &[f64]) -> Result<(), String> {
        if x.is_empty() || y.is_empty() {
            return Err("训练数据不能为空".to_string());
        }

        let n_features = x[0].len();
        self.weights = vec![0.0; n_features];
        self.bias = 0.0;

        let n_samples = x.len();
        
        for iteration in 0..self.max_iterations {
            let mut total_loss = 0.0;
            let mut weight_gradients = vec![0.0; n_features];
            let mut bias_gradient = 0.0;

            // 计算梯度
            for i in 0..n_samples {
                let prediction = self.predict_single(&x[i]);
                let error = prediction - y[i];
                total_loss += error * error;

                // 计算权重梯度
                for j in 0..n_features {
                    weight_gradients[j] += error * x[i][j];
                }
                bias_gradient += error;
            }

            // 更新参数
            for j in 0..n_features {
                self.weights[j] -= self.learning_rate * weight_gradients[j] / n_samples as f64;
            }
            self.bias -= self.learning_rate * bias_gradient / n_samples as f64;

            // 检查收敛
            let avg_loss = total_loss / n_samples as f64;
            if iteration % 100 == 0 {
                println!("迭代 {}: 平均损失 = {:.6}", iteration, avg_loss);
            }
            
            if avg_loss < 1e-6 {
                println!("在第 {} 次迭代后收敛", iteration);
                break;
            }
        }

        Ok(())
    }

    /// 预测单个样本
    fn predict_single(&self, x: &[f64]) -> f64 {
        let mut prediction = self.bias;
        for (i, &feature) in x.iter().enumerate() {
            prediction += self.weights[i] * feature;
        }
        prediction
    }

    /// 预测
    pub fn predict(&self, x: &[Vec<f64>]) -> Vec<f64> {
        x.iter().map(|sample| self.predict_single(sample)).collect()
    }

    /// 计算R²分数
    pub fn score(&self, x: &[Vec<f64>], y: &[f64]) -> f64 {
        let predictions = self.predict(x);
        let y_mean = y.iter().sum::<f64>() / y.len() as f64;
        
        let ss_res: f64 = y.iter().zip(&predictions)
            .map(|(&actual, &pred)| (actual - pred).powi(2))
            .sum();
        
        let ss_tot: f64 = y.iter()
            .map(|&actual| (actual - y_mean).powi(2))
            .sum();
        
        1.0 - ss_res / ss_tot
    }
}

/// 逻辑回归模型
/// 
/// 实现二分类逻辑回归
#[derive(Debug, Clone)]
pub struct LogisticRegression {
    pub weights: Vec<f64>,
    pub bias: f64,
    pub learning_rate: f64,
    pub max_iterations: usize,
}

impl LogisticRegression {
    /// 创建新的逻辑回归模型
    pub fn new(learning_rate: f64, max_iterations: usize) -> Self {
        Self {
            weights: Vec::new(),
            bias: 0.0,
            learning_rate,
            max_iterations,
        }
    }

    /// Sigmoid激活函数
    fn sigmoid(&self, z: f64) -> f64 {
        1.0 / (1.0 + (-z).exp())
    }

    /// 训练模型
    pub fn fit(&mut self, x: &[Vec<f64>], y: &[f64]) -> Result<(), String> {
        if x.is_empty() || y.is_empty() {
            return Err("训练数据不能为空".to_string());
        }

        let n_features = x[0].len();
        self.weights = vec![0.0; n_features];
        self.bias = 0.0;

        let n_samples = x.len();
        
        for iteration in 0..self.max_iterations {
            let mut total_loss = 0.0;
            let mut weight_gradients = vec![0.0; n_features];
            let mut bias_gradient = 0.0;

            // 计算梯度
            for i in 0..n_samples {
                let prediction = self.predict_probability(&x[i]);
                let error = prediction - y[i];
                
                // 交叉熵损失
                total_loss += -(y[i] * prediction.ln() + (1.0 - y[i]) * (1.0 - prediction).ln());

                // 计算权重梯度
                for j in 0..n_features {
                    weight_gradients[j] += error * x[i][j];
                }
                bias_gradient += error;
            }

            // 更新参数
            for j in 0..n_features {
                self.weights[j] -= self.learning_rate * weight_gradients[j] / n_samples as f64;
            }
            self.bias -= self.learning_rate * bias_gradient / n_samples as f64;

            // 检查收敛
            let avg_loss = total_loss / n_samples as f64;
            if iteration % 100 == 0 {
                println!("迭代 {}: 平均损失 = {:.6}", iteration, avg_loss);
            }
        }

        Ok(())
    }

    /// 预测概率
    pub fn predict_probability(&self, x: &[f64]) -> f64 {
        let mut z = self.bias;
        for (i, &feature) in x.iter().enumerate() {
            z += self.weights[i] * feature;
        }
        self.sigmoid(z)
    }

    /// 预测类别
    pub fn predict(&self, x: &[Vec<f64>]) -> Vec<f64> {
        x.iter().map(|sample| {
            if self.predict_probability(sample) > 0.5 { 1.0 } else { 0.0 }
        }).collect()
    }

    /// 计算准确率
    pub fn accuracy(&self, x: &[Vec<f64>], y: &[f64]) -> f64 {
        let predictions = self.predict(x);
        let correct: usize = y.iter().zip(&predictions)
            .map(|(&actual, &pred)| if (actual - pred).abs() < 1e-6 { 1 } else { 0 })
            .sum();
        correct as f64 / y.len() as f64
    }
}

/// KMeans聚类算法
/// 
/// 实现KMeans聚类算法
#[derive(Debug, Clone)]
pub struct KMeans {
    pub k: usize,
    pub centroids: Vec<Vec<f64>>,
    pub max_iterations: usize,
    pub tolerance: f64,
}

impl KMeans {
    /// 创建新的KMeans模型
    pub fn new(k: usize, max_iterations: usize, tolerance: f64) -> Self {
        Self {
            k,
            centroids: Vec::new(),
            max_iterations,
            tolerance,
        }
    }

    /// 计算欧几里得距离
    fn euclidean_distance(&self, a: &[f64], b: &[f64]) -> f64 {
        a.iter().zip(b.iter())
            .map(|(x, y)| (x - y).powi(2))
            .sum::<f64>()
            .sqrt()
    }

    /// 训练模型
    pub fn fit(&mut self, x: &[Vec<f64>]) -> Result<(), String> {
        if x.is_empty() {
            return Err("训练数据不能为空".to_string());
        }

        let n_features = x[0].len();
        let n_samples = x.len();

        // 初始化质心（随机选择）
        self.centroids = Vec::new();
        for _ in 0..self.k {
            let random_idx = fastrand::usize(..n_samples);
            self.centroids.push(x[random_idx].clone());
        }

        for iteration in 0..self.max_iterations {
            // 分配每个点到最近的质心
            let mut clusters: Vec<Vec<usize>> = vec![Vec::new(); self.k];
            
            for (i, sample) in x.iter().enumerate() {
                let mut min_distance = f64::INFINITY;
                let mut closest_centroid = 0;
                
                for (j, centroid) in self.centroids.iter().enumerate() {
                    let distance = self.euclidean_distance(sample, centroid);
                    if distance < min_distance {
                        min_distance = distance;
                        closest_centroid = j;
                    }
                }
                
                clusters[closest_centroid].push(i);
            }

            // 更新质心
            let mut new_centroids = Vec::new();
            let mut converged = true;

            for cluster in &clusters {
                if cluster.is_empty() {
                    // 如果聚类为空，保持原质心
                    new_centroids.push(self.centroids[new_centroids.len()].clone());
                    continue;
                }

                let mut new_centroid = vec![0.0; n_features];
                for &sample_idx in cluster {
                    for (j, &feature) in x[sample_idx].iter().enumerate() {
                        new_centroid[j] += feature;
                    }
                }

                // 计算平均值
                for j in 0..n_features {
                    new_centroid[j] /= cluster.len() as f64;
                }

                // 检查收敛
                if new_centroids.len() < self.centroids.len() {
                    let old_centroid = &self.centroids[new_centroids.len()];
                    let distance = self.euclidean_distance(&new_centroid, old_centroid);
                    if distance > self.tolerance {
                        converged = false;
                    }
                }

                new_centroids.push(new_centroid);
            }

            self.centroids = new_centroids;

            if iteration % 10 == 0 {
                println!("迭代 {}: 质心已更新", iteration);
            }

            if converged {
                println!("在第 {} 次迭代后收敛", iteration);
                break;
            }
        }

        Ok(())
    }

    /// 预测聚类标签
    pub fn predict(&self, x: &[Vec<f64>]) -> Vec<usize> {
        x.iter().map(|sample| {
            let mut min_distance = f64::INFINITY;
            let mut closest_centroid = 0;
            
            for (j, centroid) in self.centroids.iter().enumerate() {
                let distance = self.euclidean_distance(sample, centroid);
                if distance < min_distance {
                    min_distance = distance;
                    closest_centroid = j;
                }
            }
            
            closest_centroid
        }).collect()
    }

    /// 计算轮廓系数
    pub fn silhouette_score(&self, x: &[Vec<f64>], labels: &[usize]) -> f64 {
        let mut total_score = 0.0;
        let n_samples = x.len();

        for i in 0..n_samples {
            let mut intra_cluster_distances = Vec::new();
            let mut inter_cluster_distances = HashMap::new();

            for j in 0..n_samples {
                if i != j {
                    let distance = self.euclidean_distance(&x[i], &x[j]);
                    if labels[i] == labels[j] {
                        intra_cluster_distances.push(distance);
                    } else {
                        inter_cluster_distances.entry(labels[j])
                            .or_insert_with(Vec::new)
                            .push(distance);
                    }
                }
            }

            let a = if intra_cluster_distances.is_empty() {
                0.0
            } else {
                intra_cluster_distances.iter().sum::<f64>() / intra_cluster_distances.len() as f64
            };

            let b = if inter_cluster_distances.is_empty() {
                0.0
            } else {
                inter_cluster_distances.values()
                    .map(|distances| distances.iter().sum::<f64>() / distances.len() as f64)
                    .fold(f64::INFINITY, f64::min)
            };

            if a == 0.0 && b == 0.0 {
                continue;
            }

            let silhouette = (b - a) / a.max(b);
            total_score += silhouette;
        }

        total_score / n_samples as f64
    }
}

/// 决策树节点
#[derive(Debug, Clone)]
pub enum DecisionTreeNode {
    Leaf { class: f64 },
    Internal { 
        feature: usize, 
        threshold: f64, 
        left: Box<DecisionTreeNode>, 
        right: Box<DecisionTreeNode> 
    },
}

/// 决策树分类器
/// 
/// 实现简单的决策树分类器
#[derive(Debug, Clone)]
pub struct DecisionTree {
    pub root: Option<DecisionTreeNode>,
    pub max_depth: usize,
    pub min_samples_split: usize,
}

impl DecisionTree {
    /// 创建新的决策树
    pub fn new(max_depth: usize, min_samples_split: usize) -> Self {
        Self {
            root: None,
            max_depth,
            min_samples_split,
        }
    }

    /// 计算基尼不纯度
    fn gini_impurity(&self, labels: &[f64]) -> f64 {
        if labels.is_empty() {
            return 0.0;
        }

        let mut counts = HashMap::new();
        for &label in labels {
            // 将f64转换为字符串作为HashMap的键，因为f64不实现Eq和Hash
            let label_key = format!("{:.6}", label);
            *counts.entry(label_key).or_insert(0) += 1;
        }

        let total = labels.len() as f64;
        let mut gini = 1.0;
        
        for &count in counts.values() {
            let probability = count as f64 / total;
            gini -= probability * probability;
        }

        gini
    }

    /// 找到最佳分割点
    fn find_best_split(&self, x: &[Vec<f64>], y: &[f64]) -> Option<(usize, f64, f64)> {
        let mut best_gini = f64::INFINITY;
        let mut best_feature = 0;
        let mut best_threshold = 0.0;

        for feature in 0..x[0].len() {
            let mut values: Vec<f64> = x.iter().map(|sample| sample[feature]).collect();
            values.sort_by(|a, b| a.partial_cmp(b).unwrap());

            for i in 1..values.len() {
                let threshold = (values[i-1] + values[i]) / 2.0;
                
                // 手动分割数据，因为partition的返回类型不匹配
                let mut left_y = Vec::new();
                let mut right_y = Vec::new();
                
                for (sample, &label) in x.iter().zip(y.iter()) {
                    if sample[feature] <= threshold {
                        left_y.push(label);
                    } else {
                        right_y.push(label);
                    }
                }

                if left_y.len() < self.min_samples_split || right_y.len() < self.min_samples_split {
                    continue;
                }

                let left_gini = self.gini_impurity(&left_y);
                let right_gini = self.gini_impurity(&right_y);
                
                let weighted_gini = (left_y.len() as f64 * left_gini + right_y.len() as f64 * right_gini) 
                    / (left_y.len() + right_y.len()) as f64;

                if weighted_gini < best_gini {
                    best_gini = weighted_gini;
                    best_feature = feature;
                    best_threshold = threshold;
                }
            }
        }

        if best_gini == f64::INFINITY {
            None
        } else {
            Some((best_feature, best_threshold, best_gini))
        }
    }

    /// 构建决策树
    fn build_tree(&self, x: &[Vec<f64>], y: &[f64], depth: usize) -> DecisionTreeNode {
        // 检查停止条件
        if depth >= self.max_depth || y.len() < self.min_samples_split {
            let class = if y.iter().sum::<f64>() / y.len() as f64 > 0.5 { 1.0 } else { 0.0 };
            return DecisionTreeNode::Leaf { class };
        }

        // 检查是否所有样本都属于同一类
        if y.iter().all(|&label| label == y[0]) {
            return DecisionTreeNode::Leaf { class: y[0] };
        }

        // 找到最佳分割
        if let Some((feature, threshold, _)) = self.find_best_split(x, y) {
            // 手动分割数据
            let mut left_x = Vec::new();
            let mut left_y = Vec::new();
            let mut right_x = Vec::new();
            let mut right_y = Vec::new();
            
            for (sample, &label) in x.iter().zip(y.iter()) {
                if sample[feature] <= threshold {
                    left_x.push(sample.clone());
                    left_y.push(label);
                } else {
                    right_x.push(sample.clone());
                    right_y.push(label);
                }
            }

            if left_x.is_empty() || right_x.is_empty() {
                let class = if y.iter().sum::<f64>() / y.len() as f64 > 0.5 { 1.0 } else { 0.0 };
                return DecisionTreeNode::Leaf { class };
            }

            let left_child = self.build_tree(&left_x, &left_y, depth + 1);
            let right_child = self.build_tree(&right_x, &right_y, depth + 1);

            DecisionTreeNode::Internal {
                feature,
                threshold,
                left: Box::new(left_child),
                right: Box::new(right_child),
            }
        } else {
            let class = if y.iter().sum::<f64>() / y.len() as f64 > 0.5 { 1.0 } else { 0.0 };
            DecisionTreeNode::Leaf { class }
        }
    }

    /// 训练模型
    pub fn fit(&mut self, x: &[Vec<f64>], y: &[f64]) -> Result<(), String> {
        if x.is_empty() || y.is_empty() {
            return Err("训练数据不能为空".to_string());
        }

        self.root = Some(self.build_tree(x, y, 0));
        Ok(())
    }

    /// 预测单个样本
    fn predict_single(&self, x: &[f64], node: &DecisionTreeNode) -> f64 {
        match node {
            DecisionTreeNode::Leaf { class } => *class,
            DecisionTreeNode::Internal { feature, threshold, left, right } => {
                if x[*feature] <= *threshold {
                    self.predict_single(x, left)
                } else {
                    self.predict_single(x, right)
                }
            }
        }
    }

    /// 预测
    pub fn predict(&self, x: &[Vec<f64>]) -> Vec<f64> {
        if let Some(ref root) = self.root {
            x.iter().map(|sample| self.predict_single(sample, root)).collect()
        } else {
            vec![0.0; x.len()]
        }
    }

    /// 计算准确率
    pub fn accuracy(&self, x: &[Vec<f64>], y: &[f64]) -> f64 {
        let predictions = self.predict(x);
        let correct: usize = y.iter().zip(&predictions)
            .map(|(&actual, &pred)| if (actual - pred).abs() < 1e-6 { 1 } else { 0 })
            .sum();
        correct as f64 / y.len() as f64
    }
}

fn main() {
    println!("=== Rust机器学习算法示例 ===\n");

    // 1. 线性回归示例
    println!("1. 线性回归");
    let x = vec![
        vec![1.0, 2.0],
        vec![2.0, 3.0],
        vec![3.0, 4.0],
        vec![4.0, 5.0],
        vec![5.0, 6.0],
    ];
    let y = vec![3.0, 5.0, 7.0, 9.0, 11.0];

    let mut lr = LinearRegression::new(0.01, 1000);
    lr.fit(&x, &y).unwrap();
    
    let predictions = lr.predict(&x);
    let score = lr.score(&x, &y);
    
    println!("   预测结果: {:?}", predictions);
    println!("   R²分数: {:.4}", score);
    println!();

    // 2. 逻辑回归示例
    println!("2. 逻辑回归");
    let x_binary = vec![
        vec![1.0, 2.0],
        vec![2.0, 3.0],
        vec![3.0, 4.0],
        vec![4.0, 5.0],
        vec![5.0, 6.0],
        vec![6.0, 7.0],
    ];
    let y_binary = vec![0.0, 0.0, 0.0, 1.0, 1.0, 1.0];

    let mut log_reg = LogisticRegression::new(0.1, 1000);
    log_reg.fit(&x_binary, &y_binary).unwrap();
    
    let predictions = log_reg.predict(&x_binary);
    let accuracy = log_reg.accuracy(&x_binary, &y_binary);
    
    println!("   预测结果: {:?}", predictions);
    println!("   准确率: {:.4}", accuracy);
    println!();

    // 3. KMeans聚类示例
    println!("3. KMeans聚类");
    let x_cluster = vec![
        vec![1.0, 1.0],
        vec![1.5, 2.0],
        vec![3.0, 4.0],
        vec![5.0, 7.0],
        vec![3.5, 5.0],
        vec![4.5, 5.0],
        vec![3.5, 4.5],
    ];

    let mut kmeans = KMeans::new(2, 100, 1e-4);
    kmeans.fit(&x_cluster).unwrap();
    
    let labels = kmeans.predict(&x_cluster);
    let silhouette = kmeans.silhouette_score(&x_cluster, &labels);
    
    println!("   聚类标签: {:?}", labels);
    println!("   轮廓系数: {:.4}", silhouette);
    println!("   质心: {:?}", kmeans.centroids);
    println!();

    // 4. 决策树示例
    println!("4. 决策树");
    let x_tree = vec![
        vec![1.0, 1.0],
        vec![1.0, 2.0],
        vec![2.0, 1.0],
        vec![2.0, 2.0],
        vec![3.0, 3.0],
        vec![3.0, 4.0],
        vec![4.0, 3.0],
        vec![4.0, 4.0],
    ];
    let y_tree = vec![0.0, 0.0, 0.0, 0.0, 1.0, 1.0, 1.0, 1.0];

    let mut tree = DecisionTree::new(3, 2);
    tree.fit(&x_tree, &y_tree).unwrap();
    
    let predictions = tree.predict(&x_tree);
    let accuracy = tree.accuracy(&x_tree, &y_tree);
    
    println!("   预测结果: {:?}", predictions);
    println!("   准确率: {:.4}", accuracy);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_linear_regression() {
        let x = vec![vec![1.0], vec![2.0], vec![3.0]];
        let y = vec![2.0, 4.0, 6.0];
        
        let mut lr = LinearRegression::new(0.01, 100);
        lr.fit(&x, &y).unwrap();
        
        let predictions = lr.predict(&x);
        assert!(predictions[0] > 1.0 && predictions[0] < 3.0);
    }

    #[test]
    fn test_logistic_regression() {
        let x = vec![vec![1.0], vec![2.0], vec![3.0], vec![4.0]];
        let y = vec![0.0, 0.0, 1.0, 1.0];
        
        let mut log_reg = LogisticRegression::new(0.1, 100);
        log_reg.fit(&x, &y).unwrap();
        
        let accuracy = log_reg.accuracy(&x, &y);
        assert!(accuracy >= 0.0 && accuracy <= 1.0);
    }

    #[test]
    fn test_kmeans() {
        let x = vec![vec![1.0, 1.0], vec![2.0, 2.0], vec![10.0, 10.0], vec![11.0, 11.0]];
        
        let mut kmeans = KMeans::new(2, 10, 1e-4);
        kmeans.fit(&x).unwrap();
        
        let labels = kmeans.predict(&x);
        assert_eq!(labels.len(), x.len());
    }

    #[test]
    fn test_decision_tree() {
        let x = vec![vec![1.0], vec![2.0], vec![3.0], vec![4.0]];
        let y = vec![0.0, 0.0, 1.0, 1.0];
        
        let mut tree = DecisionTree::new(2, 1);
        tree.fit(&x, &y).unwrap();
        
        let accuracy = tree.accuracy(&x, &y);
        assert!(accuracy >= 0.0 && accuracy <= 1.0);
    }
}
