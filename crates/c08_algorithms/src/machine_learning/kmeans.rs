//! K-means 聚类算法实现
//!
//! 本模块提供了 K-means 聚类算法的基础实现

use super::*;
use rand::Rng;

/// K-means 聚类器
#[derive(Debug, Clone)]
pub struct KMeans {
    /// 聚类数量
    k: usize,
    /// 聚类中心
    centers: Option<Dataset>,
    /// 最大迭代次数
    max_iterations: usize,
    /// 收敛阈值
    tolerance: f64,
    /// 是否已训练
    is_fitted: bool,
}

impl KMeans {
    /// 创建新的 K-means 聚类器
    pub fn new(k: usize) -> Self {
        Self {
            k,
            centers: None,
            max_iterations: 100,
            tolerance: 1e-4,
            is_fitted: false,
        }
    }

    /// 设置最大迭代次数
    pub fn max_iterations(mut self, max_iter: usize) -> Self {
        self.max_iterations = max_iter;
        self
    }

    /// 设置收敛阈值
    pub fn tolerance(mut self, tol: f64) -> Self {
        self.tolerance = tol;
        self
    }

    /// 计算欧几里得距离
    fn euclidean_distance(a: &DataPoint, b: &DataPoint) -> f64 {
        a.iter()
            .zip(b.iter())
            .map(|(x, y)| (x - y).powi(2))
            .sum::<f64>()
            .sqrt()
    }

    /// 找到最近的聚类中心
    fn find_closest_center_in<'a>(point: &DataPoint, centers: &'a [DataPoint]) -> usize {
        let mut min_distance = f64::INFINITY;
        let mut closest_center = 0;

        for (i, center) in centers.iter().enumerate() {
            let distance = Self::euclidean_distance(point, center);
            if distance < min_distance {
                min_distance = distance;
                closest_center = i;
            }
        }

        closest_center
    }

    /// 初始化聚类中心（K-means++ 方法）
    fn initialize_centers(&self, data: &Dataset) -> Dataset {
        let mut centers = Vec::with_capacity(self.k);
        use rand::rngs::ThreadRng;
        let mut rng = ThreadRng::default();

        // 随机选择第一个中心
        if !data.is_empty() {
            let first_idx = rng.random_range(0..data.len());
            centers.push(data[first_idx].clone());
        }

        // 使用 K-means++ 选择剩余中心
        for _ in 1..self.k {
            let mut distances = Vec::with_capacity(data.len());
            let mut total_distance = 0.0;

            for point in data.iter() {
                let min_distance = centers
                    .iter()
                    .map(|center| Self::euclidean_distance(point, center))
                    .fold(f64::INFINITY, f64::min);

                distances.push(min_distance);
                total_distance += min_distance;
            }

            // 根据距离概率选择下一个中心
            let mut cumulative = 0.0;
            let random_value: f64 = rng.random_range(0.0..total_distance);

            for (i, &distance) in distances.iter().enumerate() {
                cumulative += distance;
                if cumulative >= random_value {
                    centers.push(data[i].clone());
                    break;
                }
            }
        }

        centers
    }
}

impl UnsupervisedLearning for KMeans {
    fn fit(&mut self, data: &Dataset) -> MLResult<()> {
        if data.is_empty() {
            return Err(MLError::InvalidInput("数据集不能为空".to_string()));
        }

        if self.k == 0 {
            return Err(MLError::InvalidInput("聚类数量必须大于 0".to_string()));
        }

        if self.k > data.len() {
            return Err(MLError::InvalidInput(
                "聚类数量不能大于数据点数量".to_string(),
            ));
        }

        // 初始化聚类中心
        let mut centers = self.initialize_centers(data);

        // K-means 迭代
        for _iteration in 0..self.max_iterations {
            let mut clusters: Vec<Vec<usize>> = vec![Vec::new(); self.k];

            // 分配每个点到最近的聚类中心
            for (i, point) in data.iter().enumerate() {
                let closest_center = Self::find_closest_center_in(point, &centers);
                clusters[closest_center].push(i);
            }

            // 更新聚类中心
            let mut new_centers = Vec::with_capacity(self.k);
            let mut converged = true;

            for (i, cluster) in clusters.iter().enumerate() {
                if cluster.is_empty() {
                    // 如果聚类为空，保持原中心
                    new_centers.push(centers[i].clone());
                    continue;
                }

                let n_features = data[0].len();
                let mut new_center = vec![0.0; n_features];

                // 计算新中心（均值）
                for &point_idx in cluster.iter() {
                    for (j, &value) in data[point_idx].iter().enumerate() {
                        new_center[j] += value;
                    }
                }

                for value in new_center.iter_mut() {
                    *value /= cluster.len() as f64;
                }

                // 检查是否收敛
                let distance = Self::euclidean_distance(&centers[i], &new_center);
                if distance > self.tolerance {
                    converged = false;
                }

                new_centers.push(new_center);
            }

            centers = new_centers;

            if converged {
                break;
            }
        }

        self.centers = Some(centers);
        self.is_fitted = true;
        Ok(())
    }

    fn predict(&self, data: &Dataset) -> MLResult<Labels> {
        if !self.is_fitted {
            return Err(MLError::ModelNotTrained);
        }

        let mut labels = Vec::with_capacity(data.len());
        let centers = self.centers.as_ref().ok_or(MLError::ModelNotTrained)?;
        for point in data.iter() {
            let cluster = Self::find_closest_center_in(point, centers);
            labels.push(cluster as i32);
        }

        Ok(labels)
    }

    fn cluster_centers(&self) -> Option<Dataset> {
        self.centers.clone()
    }
}

/// 异步版本的 K-means 训练
pub async fn kmeans_fit_async(
    k: usize,
    data: Dataset,
    max_iterations: Option<usize>,
    tolerance: Option<f64>,
) -> MLResult<KMeans> {
    tokio::task::spawn_blocking(move || {
        let mut kmeans = KMeans::new(k);
        if let Some(max_iter) = max_iterations {
            kmeans = kmeans.max_iterations(max_iter);
        }
        if let Some(tol) = tolerance {
            kmeans = kmeans.tolerance(tol);
        }

        kmeans.fit(&data)?;
        Ok(kmeans)
    })
    .await
    .map_err(|e| MLError::TrainingFailed(format!("异步训练失败: {}", e)))?
}

/// 并行版本的 K-means 训练（使用 rayon）
#[cfg(feature = "with-petgraph")]
pub fn kmeans_fit_parallel(
    k: usize,
    data: &Dataset,
    max_iterations: Option<usize>,
    tolerance: Option<f64>,
) -> MLResult<KMeans> {
    use rayon::prelude::*;

    if data.is_empty() {
        return Err(MLError::InvalidInput("数据集不能为空".to_string()));
    }

    if k == 0 {
        return Err(MLError::InvalidInput("聚类数量必须大于 0".to_string()));
    }

    if k > data.len() {
        return Err(MLError::InvalidInput(
            "聚类数量不能大于数据点数量".to_string(),
        ));
    }

    let mut kmeans = KMeans::new(k);
    if let Some(max_iter) = max_iterations {
        kmeans = kmeans.max_iterations(max_iter);
    }
    if let Some(tol) = tolerance {
        kmeans = kmeans.tolerance(tol);
    }

    // 初始化聚类中心
    let mut centers = kmeans.initialize_centers(data);

    // K-means 迭代
    for iteration in 0..kmeans.max_iterations {
        // 并行分配每个点到最近的聚类中心
        let cluster_assignments: Vec<usize> = data
            .par_iter()
            .map(|point| {
                let mut min_distance = f64::INFINITY;
                let mut closest_center = 0;

                for (i, center) in centers.iter().enumerate() {
                    let distance = KMeans::euclidean_distance(point, center);
                    if distance < min_distance {
                        min_distance = distance;
                        closest_center = i;
                    }
                }

                closest_center
            })
            .collect();

        // 更新聚类中心
        let mut new_centers = Vec::with_capacity(k);
        let mut converged = true;

        for i in 0..k {
            let cluster_points: Vec<&DataPoint> = cluster_assignments
                .iter()
                .enumerate()
                .filter(|(_, &cluster)| cluster == i)
                .map(|(idx, _)| &data[idx])
                .collect();

            if cluster_points.is_empty() {
                new_centers.push(centers[i].clone());
                continue;
            }

            let n_features = data[0].len();
            let mut new_center = vec![0.0; n_features];

            // 计算新中心（均值）
            for point in cluster_points.iter() {
                for (j, &value) in point.iter().enumerate() {
                    new_center[j] += value;
                }
            }

            for value in new_center.iter_mut() {
                *value /= cluster_points.len() as f64;
            }

            // 检查是否收敛
            let distance = KMeans::euclidean_distance(&centers[i], &new_center);
            if distance > kmeans.tolerance {
                converged = false;
            }

            new_centers.push(new_center);
        }

        centers = new_centers;

        if converged {
            break;
        }
    }

    kmeans.centers = Some(centers);
    kmeans.is_fitted = true;
    Ok(kmeans)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_kmeans_basic() {
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

        let predictions = kmeans.predict(&data).unwrap();
        assert_eq!(predictions.len(), data.len());

        // 检查聚类中心
        let centers = kmeans.cluster_centers().unwrap();
        assert_eq!(centers.len(), 2);
    }

    #[test]
    fn test_kmeans_empty_data() {
        let data = vec![];
        let mut kmeans = KMeans::new(2);
        let result = kmeans.fit(&data);
        assert!(result.is_err());
    }

    #[test]
    fn test_kmeans_invalid_k() {
        let data = vec![vec![1.0, 2.0], vec![3.0, 4.0]];
        let mut kmeans = KMeans::new(0);
        let result = kmeans.fit(&data);
        assert!(result.is_err());
    }

    #[tokio::test]
    async fn test_kmeans_async() {
        let data = vec![
            vec![1.0, 1.0],
            vec![1.5, 2.0],
            vec![3.0, 4.0],
            vec![5.0, 7.0],
        ];

        let result = kmeans_fit_async(2, data.clone(), Some(50), Some(1e-3)).await;
        assert!(result.is_ok());

        let kmeans = result.unwrap();
        let predictions = kmeans.predict(&data).unwrap();
        assert_eq!(predictions.len(), data.len());
    }
}
