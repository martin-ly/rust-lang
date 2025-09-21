//! # 机器学习算法模块
//! 
//! 本模块实现了各种机器学习算法。

//use serde::{Serialize, Deserialize};

/// 机器学习算法实现
pub struct MachineLearningAlgorithms;

impl MachineLearningAlgorithms {
    /// K-Means 聚类
    pub fn kmeans(data: &[Vec<f64>], k: usize, max_iterations: usize) -> Vec<usize> {
        if data.is_empty() || k == 0 {
            return vec![];
        }
        
        let n = data.len();
        let dim = data[0].len();
        
        // 初始化聚类中心
        let mut centroids = vec![vec![0.0; dim]; k];
        for i in 0..k {
            if i < n {
                centroids[i] = data[i].clone();
            }
        }
        
        let mut assignments = vec![0; n];
        
        for _ in 0..max_iterations {
            let mut changed = false;
            
            // 分配点到最近的聚类中心
            for (i, point) in data.iter().enumerate() {
                let mut min_dist = f64::INFINITY;
                let mut best_cluster = 0;
                
                for (j, centroid) in centroids.iter().enumerate() {
                    let dist = Self::euclidean_distance(point, centroid);
                    if dist < min_dist {
                        min_dist = dist;
                        best_cluster = j;
                    }
                }
                
                if assignments[i] != best_cluster {
                    assignments[i] = best_cluster;
                    changed = true;
                }
            }
            
            if !changed {
                break;
            }
            
            // 更新聚类中心
            let mut cluster_sums = vec![vec![0.0; dim]; k];
            let mut cluster_counts = vec![0; k];
            
            for (i, &cluster) in assignments.iter().enumerate() {
                for j in 0..dim {
                    cluster_sums[cluster][j] += data[i][j];
                }
                cluster_counts[cluster] += 1;
            }
            
            for i in 0..k {
                if cluster_counts[i] > 0 {
                    for j in 0..dim {
                        centroids[i][j] = cluster_sums[i][j] / cluster_counts[i] as f64;
                    }
                }
            }
        }
        
        assignments
    }
    
    /// 计算欧几里得距离
    fn euclidean_distance(p1: &[f64], p2: &[f64]) -> f64 {
        p1.iter()
            .zip(p2.iter())
            .map(|(a, b)| (a - b).powi(2))
            .sum::<f64>()
            .sqrt()
    }

    /// 线性回归
    pub fn linear_regression(x: &[f64], y: &[f64]) -> (f64, f64) {
        let n = x.len() as f64;
        let sum_x: f64 = x.iter().sum();
        let sum_y: f64 = y.iter().sum();
        let sum_xy: f64 = x.iter().zip(y.iter()).map(|(a, b)| a * b).sum();
        let sum_x_sq: f64 = x.iter().map(|a| a * a).sum();
        
        let slope = (n * sum_xy - sum_x * sum_y) / (n * sum_x_sq - sum_x * sum_x);
        let intercept = (sum_y - slope * sum_x) / n;
        
        (slope, intercept)
    }
}
