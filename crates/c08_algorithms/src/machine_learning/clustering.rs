//! 聚类算法实现
//! 
//! 本模块提供了常用的聚类算法，包括：
//! - K-means 聚类
//! - DBSCAN 聚类

use super::*;
use std::collections::HashMap;

/// K-means 聚类算法
#[derive(Debug, Clone)]
pub struct KMeans {
    /// 聚类数量
    k: usize,
    /// 最大迭代次数
    max_iterations: usize,
    /// 收敛阈值
    tolerance: f64,
    /// 聚类中心
    centroids: Option<Dataset>,
    /// 是否已训练
    is_fitted: bool,
}

impl KMeans {
    /// 创建新的 K-means 实例
    pub fn new(k: usize) -> Self {
        Self {
            k,
            max_iterations: 100,
            tolerance: 1e-6,
            centroids: None,
            is_fitted: false,
        }
    }
    
    /// 设置最大迭代次数
    pub fn with_max_iterations(mut self, max_iterations: usize) -> Self {
        self.max_iterations = max_iterations;
        self
    }
    
    /// 设置收敛阈值
    pub fn with_tolerance(mut self, tolerance: f64) -> Self {
        self.tolerance = tolerance;
        self
    }
    
    /// 初始化聚类中心
    fn initialize_centroids(&self, data: &Dataset) -> MLResult<Dataset> {
        if data.is_empty() {
            return Err(MLError::InvalidInput("数据集为空".to_string()));
        }
        
        if self.k > data.len() {
            return Err(MLError::InvalidInput(
                format!("聚类数量 {} 大于样本数量 {}", self.k, data.len())
            ));
        }
        
        use rand::seq::SliceRandom;
        
        let mut indices: Vec<usize> = (0..data.len()).collect();
        use rand::rngs::ThreadRng;
        indices.shuffle(&mut ThreadRng::default());
        
        let centroids = indices[..self.k]
            .iter()
            .map(|&i| data[i].clone())
            .collect();
            
        Ok(centroids)
    }
    
    /// 计算点到聚类中心的距离
    fn euclidean_distance(&self, point1: &DataPoint, point2: &DataPoint) -> f64 {
        point1
            .iter()
            .zip(point2.iter())
            .map(|(a, b)| (a - b).powi(2))
            .sum::<f64>()
            .sqrt()
    }
    
    /// 分配样本到最近的聚类中心
    fn assign_clusters(&self, data: &Dataset, centroids: &Dataset) -> Labels {
        data.iter()
            .map(|point| {
                centroids
                    .iter()
                    .enumerate()
                    .map(|(i, centroid)| (i, self.euclidean_distance(point, centroid)))
                    .min_by(|a, b| a.1.partial_cmp(&b.1).unwrap())
                    .map(|(i, _)| i as Label)
                    .unwrap_or(0)
            })
            .collect()
    }
    
    /// 更新聚类中心
    fn update_centroids(&self, data: &Dataset, labels: &Labels) -> MLResult<Dataset> {
        let n_features = data[0].len();
        let mut new_centroids = vec![vec![0.0; n_features]; self.k];
        let mut cluster_sizes = vec![0; self.k];
        
        // 计算每个聚类的样本和
        for (point, &label) in data.iter().zip(labels.iter()) {
            let cluster_id = label as usize;
            if cluster_id < self.k {
                for (i, &value) in point.iter().enumerate() {
                    new_centroids[cluster_id][i] += value;
                }
                cluster_sizes[cluster_id] += 1;
            }
        }
        
        // 计算平均值
        for (cluster_id, centroid) in new_centroids.iter_mut().enumerate() {
            if cluster_sizes[cluster_id] > 0 {
                for value in centroid.iter_mut() {
                    *value /= cluster_sizes[cluster_id] as f64;
                }
            }
        }
        
        Ok(new_centroids)
    }
    
    /// 检查收敛性
    fn has_converged(&self, old_centroids: &Dataset, new_centroids: &Dataset) -> bool {
        old_centroids
            .iter()
            .zip(new_centroids.iter())
            .all(|(old, new)| self.euclidean_distance(old, new) < self.tolerance)
    }
    
    /// 计算惯性（簇内平方和）
    pub fn inertia(&self, data: &Dataset) -> MLResult<f64> {
        if !self.is_fitted {
            return Err(MLError::ModelNotTrained);
        }
        
        let centroids = self.centroids.as_ref().unwrap();
        let labels = self.assign_clusters(data, centroids);
        
        let mut inertia = 0.0;
        for (point, &label) in data.iter().zip(labels.iter()) {
            let centroid = &centroids[label as usize];
            inertia += self.euclidean_distance(point, centroid).powi(2);
        }
        
        Ok(inertia)
    }
}

impl UnsupervisedLearning for KMeans {
    fn fit(&mut self, data: &Dataset) -> MLResult<()> {
        if data.is_empty() {
            return Err(MLError::InvalidInput("数据集为空".to_string()));
        }
        
        // 初始化聚类中心
        let mut centroids = self.initialize_centroids(data)?;
        
        for iteration in 0..self.max_iterations {
            // 分配样本到聚类
            let labels = self.assign_clusters(data, &centroids);
            
            // 更新聚类中心
            let new_centroids = self.update_centroids(data, &labels)?;
            
            // 检查收敛性
            if self.has_converged(&centroids, &new_centroids) {
                tracing::info!("K-means 在第 {} 次迭代收敛", iteration + 1);
                centroids = new_centroids;
                break;
            }
            
            centroids = new_centroids;
        }
        
        self.centroids = Some(centroids);
        self.is_fitted = true;
        
        Ok(())
    }
    
    fn predict(&self, data: &Dataset) -> MLResult<Labels> {
        if !self.is_fitted {
            return Err(MLError::ModelNotTrained);
        }
        
        let centroids = self.centroids.as_ref().unwrap();
        Ok(self.assign_clusters(data, centroids))
    }
    
    fn cluster_centers(&self) -> Option<Dataset> {
        self.centroids.clone()
    }
}

/// DBSCAN 聚类算法
#[derive(Debug, Clone)]
pub struct DBSCAN {
    /// 邻域半径
    eps: f64,
    /// 最小样本数
    min_samples: usize,
    /// 是否已训练
    is_fitted: bool,
}

impl DBSCAN {
    /// 创建新的 DBSCAN 实例
    pub fn new(eps: f64, min_samples: usize) -> Self {
        Self {
            eps,
            min_samples,
            is_fitted: false,
        }
    }
    
    /// 计算欧几里得距离
    fn euclidean_distance(&self, point1: &DataPoint, point2: &DataPoint) -> f64 {
        point1
            .iter()
            .zip(point2.iter())
            .map(|(a, b)| (a - b).powi(2))
            .sum::<f64>()
            .sqrt()
    }
    
    /// 找到点的邻域
    fn range_query(&self, data: &Dataset, point_idx: usize) -> Vec<usize> {
        let point = &data[point_idx];
        data.iter()
            .enumerate()
            .filter(|(_, other_point)| {
                self.euclidean_distance(point, other_point) <= self.eps
            })
            .map(|(idx, _)| idx)
            .collect()
    }
}

impl UnsupervisedLearning for DBSCAN {
    fn fit(&mut self, data: &Dataset) -> MLResult<()> {
        if data.is_empty() {
            return Err(MLError::InvalidInput("数据集为空".to_string()));
        }
        
        self.is_fitted = true;
        Ok(())
    }
    
    fn predict(&self, data: &Dataset) -> MLResult<Labels> {
        if !self.is_fitted {
            return Err(MLError::ModelNotTrained);
        }
        
        let n = data.len();
        let mut labels = vec![-1; n]; // -1 表示噪声点
        let mut cluster_id = 0;
        let mut visited = vec![false; n];
        
        for i in 0..n {
            if visited[i] {
                continue;
            }
            visited[i] = true;
            
            let neighbors = self.range_query(data, i);
            
            if neighbors.len() < self.min_samples {
                labels[i] = -1; // 噪声点
            } else {
                // 开始新的聚类
                self.expand_cluster(data, i, &neighbors, cluster_id, &mut labels, &mut visited)?;
                cluster_id += 1;
            }
        }
        
        Ok(labels)
    }
}

impl DBSCAN {
    /// 扩展聚类
    fn expand_cluster(
        &self,
        data: &Dataset,
        point_idx: usize,
        neighbors: &[usize],
        cluster_id: i32,
        labels: &mut [i32],
        visited: &mut [bool],
    ) -> MLResult<()> {
        labels[point_idx] = cluster_id;
        let mut seeds = neighbors.to_vec();
        let mut i = 0;
        
        while i < seeds.len() {
            let q = seeds[i];
            
            if !visited[q] {
                visited[q] = true;
                let q_neighbors = self.range_query(data, q);
                
                if q_neighbors.len() >= self.min_samples {
                    for &neighbor in &q_neighbors {
                        if !seeds.contains(&neighbor) {
                            seeds.push(neighbor);
                        }
                    }
                }
            }
            
            if labels[q] == -1 {
                labels[q] = cluster_id;
            }
            
            i += 1;
        }
        
        Ok(())
    }
}

/// 聚类评估指标
pub struct ClusteringMetrics;

impl ClusteringMetrics {
    /// 计算轮廓系数
    pub fn silhouette_score(data: &Dataset, labels: &Labels) -> MLResult<f64> {
        if data.len() != labels.len() {
            return Err(MLError::DimensionMismatch {
                expected: data.len(),
                actual: labels.len(),
            });
        }
        
        let n = data.len();
        let mut silhouette_scores = vec![0.0; n];
        
        // 按聚类分组
        let mut clusters: HashMap<i32, Vec<usize>> = HashMap::new();
        for (idx, &label) in labels.iter().enumerate() {
            if label >= 0 {
                clusters.entry(label).or_insert_with(Vec::new).push(idx);
            }
        }
        
        for (i, &label) in labels.iter().enumerate() {
            if label < 0 {
                silhouette_scores[i] = 0.0; // 噪声点轮廓系数为0
                continue;
            }
            
            let same_cluster = clusters.get(&label).unwrap();
            
            // 计算 a(i) - 同一聚类内的平均距离
            let a_i = if same_cluster.len() == 1 {
                0.0
            } else {
                same_cluster
                    .iter()
                    .filter(|&&j| j != i)
                    .map(|&j| Self::euclidean_distance(&data[i], &data[j]))
                    .sum::<f64>() / (same_cluster.len() - 1) as f64
            };
            
            // 计算 b(i) - 到最近其他聚类的平均距离
            let mut min_b_i = f64::INFINITY;
            for (&other_label, other_cluster) in &clusters {
                if other_label != label {
                    let avg_dist = other_cluster
                        .iter()
                        .map(|&j| Self::euclidean_distance(&data[i], &data[j]))
                        .sum::<f64>() / other_cluster.len() as f64;
                    min_b_i = min_b_i.min(avg_dist);
                }
            }
            
            // 计算轮廓系数
            silhouette_scores[i] = if a_i < min_b_i {
                (min_b_i - a_i) / min_b_i
            } else if a_i > min_b_i {
                (min_b_i - a_i) / a_i
            } else {
                0.0
            };
        }
        
        Ok(silhouette_scores.iter().sum::<f64>() / n as f64)
    }
    
    /// 计算 Davies-Bouldin 指数
    pub fn davies_bouldin_score(data: &Dataset, labels: &Labels) -> MLResult<f64> {
        if data.len() != labels.len() {
            return Err(MLError::DimensionMismatch {
                expected: data.len(),
                actual: labels.len(),
            });
        }
        
        // 按聚类分组
        let mut clusters: HashMap<i32, Vec<usize>> = HashMap::new();
        for (idx, &label) in labels.iter().enumerate() {
            if label >= 0 {
                clusters.entry(label).or_insert_with(Vec::new).push(idx);
            }
        }
        
        if clusters.len() < 2 {
            return Ok(0.0);
        }
        
        // 计算每个聚类的中心和内部距离
        let mut centroids = HashMap::new();
        let mut intra_cluster_distances = HashMap::new();
        
        for (&label, indices) in &clusters {
            // 计算聚类中心
            let n_features = data[0].len();
            let mut centroid = vec![0.0; n_features];
            for &idx in indices {
                for (j, &value) in data[idx].iter().enumerate() {
                    centroid[j] += value;
                }
            }
            for value in centroid.iter_mut() {
                *value /= indices.len() as f64;
            }
            
            // 计算平均内部距离
            let avg_intra_dist = indices
                .iter()
                .map(|&idx| Self::euclidean_distance(&data[idx], &centroid))
                .sum::<f64>() / indices.len() as f64;
            
            centroids.insert(label, centroid);
            intra_cluster_distances.insert(label, avg_intra_dist);
        }
        
        // 计算 Davies-Bouldin 指数
        let mut total_db = 0.0;
        for (&label_i, centroid_i) in &centroids {
            let mut max_ratio: f64 = 0.0;
            for (&label_j, centroid_j) in &centroids {
                if label_i != label_j {
                    let inter_dist = Self::euclidean_distance(centroid_i, centroid_j);
                    let ratio = (intra_cluster_distances[&label_i] + intra_cluster_distances[&label_j]) / inter_dist;
                    max_ratio = max_ratio.max(ratio);
                }
            }
            total_db += max_ratio;
        }
        
        Ok(total_db / clusters.len() as f64)
    }
    
    /// 计算欧几里得距离
    fn euclidean_distance(point1: &DataPoint, point2: &DataPoint) -> f64 {
        point1
            .iter()
            .zip(point2.iter())
            .map(|(a, b)| (a - b).powi(2))
            .sum::<f64>()
            .sqrt()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_kmeans_clustering() {
        let data = vec![
            vec![1.0, 1.0],
            vec![1.5, 2.0],
            vec![3.0, 4.0],
            vec![5.0, 7.0],
            vec![3.5, 5.0],
            vec![4.5, 5.0],
            vec![3.5, 4.5],
        ];
        
        let mut kmeans = KMeans::new(2);
        let result = kmeans.fit(&data);
        assert!(result.is_ok());
        
        let labels = kmeans.predict(&data).unwrap();
        assert_eq!(labels.len(), data.len());
        
        let centroids = kmeans.cluster_centers().unwrap();
        assert_eq!(centroids.len(), 2);
        
        let inertia = kmeans.inertia(&data).unwrap();
        assert!(inertia > 0.0);
    }
    
    #[test]
    fn test_dbscan_clustering() {
        let data = vec![
            vec![1.0, 1.0],
            vec![1.5, 2.0],
            vec![3.0, 4.0],
            vec![5.0, 7.0],
            vec![3.5, 5.0],
            vec![4.5, 5.0],
            vec![3.5, 4.5],
        ];
        
        let mut dbscan = DBSCAN::new(2.0, 2);
        let result = dbscan.fit(&data);
        assert!(result.is_ok());
        
        let labels = dbscan.predict(&data).unwrap();
        assert_eq!(labels.len(), data.len());
    }
    
    #[test]
    fn test_silhouette_score() {
        let data = vec![
            vec![1.0, 1.0],
            vec![1.5, 2.0],
            vec![3.0, 4.0],
            vec![5.0, 7.0],
        ];
        let labels = vec![0, 0, 1, 1];
        
        let score = ClusteringMetrics::silhouette_score(&data, &labels).unwrap();
        assert!(score >= -1.0 && score <= 1.0);
    }
    
    #[test]
    fn test_davies_bouldin_score() {
        let data = vec![
            vec![1.0, 1.0],
            vec![1.5, 2.0],
            vec![3.0, 4.0],
            vec![5.0, 7.0],
        ];
        let labels = vec![0, 0, 1, 1];
        
        let score = ClusteringMetrics::davies_bouldin_score(&data, &labels).unwrap();
        assert!(score >= 0.0);
    }
}
