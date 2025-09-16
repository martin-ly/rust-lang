//! 机器学习模型实现
//!
//! 本模块实现了各种机器学习算法，包括监督学习、无监督学习和强化学习算法。
//! 使用Rust的类型安全特性确保算法的正确性和性能。

use std::collections::HashMap;
use std::f64;

/// 线性回归模型
///
/// 实现最小二乘法线性回归，使用梯度下降算法进行训练。
///
/// # 数学公式
/// - 预测函数: ŷ = w₀ + w₁x₁ + w₂x₂ + ... + wₙxₙ
/// - 损失函数: MSE = (1/n) * Σ(yᵢ - ŷᵢ)²
/// - 梯度: ∂MSE/∂wⱼ = (2/n) * Σ(yᵢ - ŷᵢ) * xᵢⱼ
#[derive(Debug, Clone)]
pub struct LinearRegression {
    /// 权重向量
    pub weights: Vec<f64>,
    /// 偏置项
    pub bias: f64,
    /// 学习率
    pub learning_rate: f64,
    /// 最大迭代次数
    pub max_iterations: usize,
    /// 收敛阈值
    pub convergence_threshold: f64,
}

impl LinearRegression {
    /// 创建新的线性回归模型
    pub fn new(learning_rate: f64, max_iterations: usize) -> Self {
        Self {
            weights: Vec::new(),
            bias: 0.0,
            learning_rate,
            max_iterations,
            convergence_threshold: 1e-6,
        }
    }

    /// 训练模型
    pub fn fit(&mut self, x: &[Vec<f64>], y: &[f64]) -> Result<(), String> {
        if x.is_empty() || y.is_empty() {
            return Err("训练数据不能为空".to_string());
        }

        if x.len() != y.len() {
            return Err("特征和标签数量不匹配".to_string());
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

            if avg_loss < self.convergence_threshold {
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

        let ss_res: f64 = y
            .iter()
            .zip(predictions.iter())
            .map(|(&y_true, &y_pred)| (y_true - y_pred).powi(2))
            .sum();

        let ss_tot: f64 = y.iter().map(|&y_true| (y_true - y_mean).powi(2)).sum();

        1.0 - (ss_res / ss_tot)
    }
}

/// 逻辑回归模型
///
/// 实现二分类逻辑回归，使用Sigmoid激活函数。
///
/// # 数学公式
/// - 预测函数: ŷ = σ(w₀ + w₁x₁ + w₂x₂ + ... + wₙxₙ)
/// - Sigmoid函数: σ(z) = 1 / (1 + e^(-z))
/// - 损失函数: BCE = -Σ[yᵢlog(ŷᵢ) + (1-yᵢ)log(1-ŷᵢ)]
#[derive(Debug, Clone)]
pub struct LogisticRegression {
    /// 权重向量
    pub weights: Vec<f64>,
    /// 偏置项
    pub bias: f64,
    /// 学习率
    pub learning_rate: f64,
    /// 最大迭代次数
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

                // 二元交叉熵损失
                if y[i] > 0.0 {
                    total_loss -= y[i] * prediction.ln();
                }
                if y[i] < 1.0 {
                    total_loss -= (1.0 - y[i]) * (1.0 - prediction).ln();
                }

                // 计算梯度
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

            if iteration % 100 == 0 {
                println!(
                    "迭代 {}: 平均损失 = {:.6}",
                    iteration,
                    total_loss / n_samples as f64
                );
            }
        }

        Ok(())
    }

    /// 预测单个样本
    fn predict_single(&self, x: &[f64]) -> f64 {
        let mut z = self.bias;
        for (i, &feature) in x.iter().enumerate() {
            z += self.weights[i] * feature;
        }
        self.sigmoid(z)
    }

    /// Sigmoid激活函数
    fn sigmoid(&self, z: f64) -> f64 {
        1.0 / (1.0 + (-z).exp())
    }

    /// 预测概率
    pub fn predict_proba(&self, x: &[Vec<f64>]) -> Vec<f64> {
        x.iter().map(|sample| self.predict_single(sample)).collect()
    }

    /// 预测类别
    pub fn predict(&self, x: &[Vec<f64>]) -> Vec<f64> {
        self.predict_proba(x)
            .iter()
            .map(|&prob| if prob > 0.5 { 1.0 } else { 0.0 })
            .collect()
    }

    /// 计算准确率
    pub fn accuracy(&self, x: &[Vec<f64>], y: &[f64]) -> f64 {
        let predictions = self.predict(x);
        let correct: usize = y
            .iter()
            .zip(predictions.iter())
            .map(|(&y_true, &y_pred)| if (y_true - y_pred).abs() < 1e-6 { 1 } else { 0 })
            .sum();
        correct as f64 / y.len() as f64
    }
}

/// KMeans聚类算法
///
/// 实现K均值聚类算法，用于无监督学习。
///
/// # 算法步骤
/// 1. 随机初始化K个质心
/// 2. 将每个数据点分配到最近的质心
/// 3. 更新质心位置
/// 4. 重复步骤2-3直到收敛
#[derive(Debug, Clone)]
pub struct KMeans {
    /// 聚类数量
    pub k: usize,
    /// 质心
    pub centroids: Vec<Vec<f64>>,
    /// 最大迭代次数
    pub max_iterations: usize,
    /// 收敛阈值
    pub convergence_threshold: f64,
}

impl KMeans {
    /// 创建新的KMeans模型
    pub fn new(k: usize, max_iterations: usize) -> Self {
        Self {
            k,
            centroids: Vec::new(),
            max_iterations,
            convergence_threshold: 1e-4,
        }
    }

    /// 训练模型
    pub fn fit(&mut self, x: &[Vec<f64>]) -> Result<(), String> {
        if x.is_empty() {
            return Err("训练数据不能为空".to_string());
        }

        let n_features = x[0].len();

        // 随机初始化质心
        self.centroids = (0..self.k)
            .map(|_| {
                (0..n_features)
                    .map(|_| fastrand::f64() * 10.0 - 5.0)
                    .collect()
            })
            .collect();

        for iteration in 0..self.max_iterations {
            let old_centroids = self.centroids.clone();

            // 分配数据点到最近的质心
            let assignments = self.assign_clusters(x);

            // 更新质心
            self.update_centroids(x, &assignments);

            // 检查收敛
            let max_change = self
                .centroids
                .iter()
                .zip(old_centroids.iter())
                .map(|(new, old)| {
                    new.iter()
                        .zip(old.iter())
                        .map(|(&n, &o)| (n - o).abs())
                        .fold(0.0, f64::max)
                })
                .fold(0.0, f64::max);

            if iteration % 10 == 0 {
                println!("迭代 {}: 质心已更新", iteration);
            }

            if max_change < self.convergence_threshold {
                println!("在第 {} 次迭代后收敛", iteration);
                break;
            }
        }

        Ok(())
    }

    /// 分配数据点到最近的质心
    fn assign_clusters(&self, x: &[Vec<f64>]) -> Vec<usize> {
        x.iter()
            .map(|point| {
                let mut min_distance = f64::INFINITY;
                let mut closest_centroid = 0;

                for (i, centroid) in self.centroids.iter().enumerate() {
                    let distance = self.euclidean_distance(point, centroid);
                    if distance < min_distance {
                        min_distance = distance;
                        closest_centroid = i;
                    }
                }

                closest_centroid
            })
            .collect()
    }

    /// 更新质心
    fn update_centroids(&mut self, x: &[Vec<f64>], assignments: &[usize]) {
        let mut cluster_sums = vec![vec![0.0; x[0].len()]; self.k];
        let mut cluster_counts = vec![0; self.k];

        for (point, &assignment) in x.iter().zip(assignments.iter()) {
            for (j, &feature) in point.iter().enumerate() {
                cluster_sums[assignment][j] += feature;
            }
            cluster_counts[assignment] += 1;
        }

        for i in 0..self.k {
            if cluster_counts[i] > 0 {
                for j in 0..x[0].len() {
                    self.centroids[i][j] = cluster_sums[i][j] / cluster_counts[i] as f64;
                }
            }
        }
    }

    /// 计算欧几里得距离
    fn euclidean_distance(&self, a: &[f64], b: &[f64]) -> f64 {
        a.iter()
            .zip(b.iter())
            .map(|(&x, &y)| (x - y).powi(2))
            .sum::<f64>()
            .sqrt()
    }

    /// 预测聚类标签
    pub fn predict(&self, x: &[Vec<f64>]) -> Vec<usize> {
        self.assign_clusters(x)
    }

    /// 计算轮廓系数
    pub fn silhouette_score(&self, x: &[Vec<f64>]) -> f64 {
        let assignments = self.assign_clusters(x);
        let mut total_silhouette = 0.0;

        for (i, point) in x.iter().enumerate() {
            let cluster = assignments[i];

            // 计算簇内平均距离
            let mut intra_cluster_distances = Vec::new();
            for (j, other_point) in x.iter().enumerate() {
                if assignments[j] == cluster && i != j {
                    intra_cluster_distances.push(self.euclidean_distance(point, other_point));
                }
            }
            let a = if intra_cluster_distances.is_empty() {
                0.0
            } else {
                intra_cluster_distances.iter().sum::<f64>() / intra_cluster_distances.len() as f64
            };

            // 计算最近簇的平均距离
            let mut min_inter_cluster_distance = f64::INFINITY;
            for other_cluster in 0..self.k {
                if other_cluster != cluster {
                    let mut inter_cluster_distances = Vec::new();
                    for (j, other_point) in x.iter().enumerate() {
                        if assignments[j] == other_cluster {
                            inter_cluster_distances
                                .push(self.euclidean_distance(point, other_point));
                        }
                    }
                    if !inter_cluster_distances.is_empty() {
                        let avg_distance = inter_cluster_distances.iter().sum::<f64>()
                            / inter_cluster_distances.len() as f64;
                        min_inter_cluster_distance = min_inter_cluster_distance.min(avg_distance);
                    }
                }
            }
            let b = min_inter_cluster_distance;

            // 计算轮廓系数
            if a == 0.0 && b == 0.0 {
                total_silhouette += 0.0;
            } else {
                total_silhouette += (b - a) / a.max(b);
            }
        }

        total_silhouette / x.len() as f64
    }
}

/// 决策树节点
#[derive(Debug, Clone)]
pub enum DecisionTreeNode {
    /// 内部节点
    Internal {
        feature: usize,
        threshold: f64,
        left: Box<DecisionTreeNode>,
        right: Box<DecisionTreeNode>,
    },
    /// 叶子节点
    Leaf { class: f64 },
}

/// 决策树模型
///
/// 实现分类决策树，使用基尼不纯度作为分割标准。
#[derive(Debug, Clone)]
pub struct DecisionTree {
    /// 根节点
    pub root: Option<DecisionTreeNode>,
    /// 最大深度
    pub max_depth: usize,
    /// 最小分割样本数
    pub min_samples_split: usize,
    /// 最小叶子样本数
    pub min_samples_leaf: usize,
}

impl DecisionTree {
    /// 创建新的决策树模型
    pub fn new(max_depth: usize, min_samples_split: usize, min_samples_leaf: usize) -> Self {
        Self {
            root: None,
            max_depth,
            min_samples_split,
            min_samples_leaf,
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

    /// 构建决策树
    fn build_tree(&self, x: &[Vec<f64>], y: &[f64], depth: usize) -> DecisionTreeNode {
        // 检查停止条件
        if depth >= self.max_depth || y.len() < self.min_samples_split {
            let class = if y.iter().sum::<f64>() / y.len() as f64 > 0.5 {
                1.0
            } else {
                0.0
            };
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
                let class = if y.iter().sum::<f64>() / y.len() as f64 > 0.5 {
                    1.0
                } else {
                    0.0
                };
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
            let class = if y.iter().sum::<f64>() / y.len() as f64 > 0.5 {
                1.0
            } else {
                0.0
            };
            DecisionTreeNode::Leaf { class }
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
                let threshold = (values[i - 1] + values[i]) / 2.0;

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

                let weighted_gini = (left_y.len() as f64 * left_gini
                    + right_y.len() as f64 * right_gini)
                    / (left_y.len() + right_y.len()) as f64;

                if weighted_gini < best_gini {
                    best_gini = weighted_gini;
                    best_feature = feature;
                    best_threshold = threshold;
                }
            }
        }

        if best_gini < f64::INFINITY {
            Some((best_feature, best_threshold, best_gini))
        } else {
            None
        }
    }

    /// 预测单个样本
    fn predict_single(&self, x: &[f64], node: &DecisionTreeNode) -> f64 {
        match node {
            DecisionTreeNode::Leaf { class } => *class,
            DecisionTreeNode::Internal {
                feature,
                threshold,
                left,
                right,
            } => {
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
            x.iter()
                .map(|sample| self.predict_single(sample, root))
                .collect()
        } else {
            vec![0.0; x.len()]
        }
    }

    /// 计算准确率
    pub fn accuracy(&self, x: &[Vec<f64>], y: &[f64]) -> f64 {
        let predictions = self.predict(x);
        let correct: usize = y
            .iter()
            .zip(predictions.iter())
            .map(|(&y_true, &y_pred)| if (y_true - y_pred).abs() < 1e-6 { 1 } else { 0 })
            .sum();
        correct as f64 / y.len() as f64
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_linear_regression() {
        let mut model = LinearRegression::new(0.01, 1000);
        let x = vec![vec![1.0], vec![2.0], vec![3.0], vec![4.0], vec![5.0]];
        let y = vec![2.0, 4.0, 6.0, 8.0, 10.0];

        assert!(model.fit(&x, &y).is_ok());
        let predictions = model.predict(&x);
        assert_eq!(predictions.len(), 5);
    }

    #[test]
    fn test_logistic_regression() {
        let mut model = LogisticRegression::new(0.01, 1000);
        let x = vec![vec![1.0], vec![2.0], vec![3.0], vec![4.0], vec![5.0]];
        let y = vec![0.0, 0.0, 1.0, 1.0, 1.0];

        assert!(model.fit(&x, &y).is_ok());
        let predictions = model.predict(&x);
        assert_eq!(predictions.len(), 5);
    }

    #[test]
    fn test_kmeans() {
        let mut model = KMeans::new(2, 100);
        let x = vec![
            vec![1.0, 1.0],
            vec![1.5, 2.0],
            vec![3.0, 4.0],
            vec![5.0, 7.0],
            vec![3.5, 5.0],
            vec![4.5, 5.0],
            vec![3.5, 4.5],
        ];

        assert!(model.fit(&x).is_ok());
        let predictions = model.predict(&x);
        assert_eq!(predictions.len(), 7);
    }

    #[test]
    fn test_decision_tree() {
        let mut model = DecisionTree::new(10, 2, 1);
        let x = vec![
            vec![1.0, 1.0],
            vec![2.0, 2.0],
            vec![3.0, 3.0],
            vec![4.0, 4.0],
            vec![5.0, 5.0],
            vec![6.0, 6.0],
            vec![7.0, 7.0],
            vec![8.0, 8.0],
        ];
        let y = vec![0.0, 0.0, 0.0, 0.0, 1.0, 1.0, 1.0, 1.0];

        assert!(model.fit(&x, &y).is_ok());
        let predictions = model.predict(&x);
        assert_eq!(predictions.len(), 8);
    }
}
