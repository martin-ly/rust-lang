//! 向量数据库
//! 
//! 提供向量存储、索引和检索功能

use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// 向量数据库
#[derive(Debug, Clone)]
pub struct VectorDatabase {
    pub name: String,
    pub collections: HashMap<String, VectorCollection>,
    pub config: DatabaseConfig,
}

/// 向量集合
#[derive(Debug, Clone)]
pub struct VectorCollection {
    pub name: String,
    pub vectors: Vec<Vector>,
    pub metadata: HashMap<String, String>,
    pub index: Option<VectorIndex>,
}

/// 向量
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Vector {
    pub id: String,
    pub data: Vec<f64>,
    pub metadata: HashMap<String, serde_json::Value>,
}

/// 向量索引
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum VectorIndex {
    /// 暴力搜索
    BruteForce,
    /// 近似最近邻
    ApproximateNearestNeighbor {
        algorithm: ANNAlgorithm,
        parameters: HashMap<String, f64>,
    },
}

/// ANN 算法
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ANNAlgorithm {
    /// HNSW (Hierarchical Navigable Small World)
    HNSW,
    /// IVF (Inverted File)
    IVF,
    /// LSH (Locality Sensitive Hashing)
    LSH,
}

/// 数据库配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DatabaseConfig {
    pub max_vectors_per_collection: usize,
    pub vector_dimension: usize,
    pub distance_metric: DistanceMetric,
    pub enable_persistence: bool,
    pub cache_size: usize,
}

/// 距离度量
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum DistanceMetric {
    /// 欧几里得距离
    Euclidean,
    /// 余弦相似度
    Cosine,
    /// 曼哈顿距离
    Manhattan,
    /// 点积
    DotProduct,
}

impl VectorDatabase {
    /// 创建新的向量数据库
    pub fn new(name: String, config: DatabaseConfig) -> Self {
        Self {
            name,
            collections: HashMap::new(),
            config,
        }
    }
    
    /// 创建集合
    pub fn create_collection(&mut self, name: String) -> Result<(), String> {
        if self.collections.contains_key(&name) {
            return Err(format!("集合 '{}' 已存在", name));
        }
        
        let collection = VectorCollection {
            name: name.clone(),
            vectors: Vec::new(),
            metadata: HashMap::new(),
            index: None,
        };
        
        self.collections.insert(name, collection);
        Ok(())
    }
    
    /// 插入向量
    pub fn insert_vector(&mut self, collection_name: &str, vector: Vector) -> Result<(), String> {
        let collection = self.collections.get_mut(collection_name)
            .ok_or_else(|| format!("集合 '{}' 不存在", collection_name))?;
        
        if vector.data.len() != self.config.vector_dimension {
            return Err(format!("向量维度 {} 与配置维度 {} 不匹配", 
                vector.data.len(), self.config.vector_dimension));
        }
        
        if collection.vectors.len() >= self.config.max_vectors_per_collection {
            return Err(format!("集合 '{}' 已达到最大向量数量限制", collection_name));
        }
        
        collection.vectors.push(vector);
        Ok(())
    }
    
    /// 搜索相似向量
    pub fn search(&self, collection_name: &str, query_vector: &[f64], top_k: usize) -> Result<Vec<SearchResult>, String> {
        let collection = self.collections.get(collection_name)
            .ok_or_else(|| format!("集合 '{}' 不存在", collection_name))?;
        
        if query_vector.len() != self.config.vector_dimension {
            return Err(format!("查询向量维度 {} 与配置维度 {} 不匹配", 
                query_vector.len(), self.config.vector_dimension));
        }
        
        let mut results = Vec::new();
        
        for vector in &collection.vectors {
            let distance = self.calculate_distance(query_vector, &vector.data);
            results.push(SearchResult {
                vector: vector.clone(),
                distance,
                score: self.distance_to_score(distance),
            });
        }
        
        // 根据距离排序（距离越小越相似）
        results.sort_by(|a, b| a.distance.partial_cmp(&b.distance).unwrap());
        
        // 返回前 k 个结果
        results.truncate(top_k);
        Ok(results)
    }
    
    /// 计算距离
    fn calculate_distance(&self, a: &[f64], b: &[f64]) -> f64 {
        match self.config.distance_metric {
            DistanceMetric::Euclidean => {
                a.iter().zip(b.iter())
                    .map(|(x, y)| (x - y).powi(2))
                    .sum::<f64>()
                    .sqrt()
            }
            DistanceMetric::Cosine => {
                let dot_product: f64 = a.iter().zip(b.iter()).map(|(x, y)| x * y).sum();
                let norm_a: f64 = a.iter().map(|x| x * x).sum::<f64>().sqrt();
                let norm_b: f64 = b.iter().map(|x| x * x).sum::<f64>().sqrt();
                
                if norm_a == 0.0 || norm_b == 0.0 {
                    1.0 // 最大距离
                } else {
                    1.0 - (dot_product / (norm_a * norm_b))
                }
            }
            DistanceMetric::Manhattan => {
                a.iter().zip(b.iter())
                    .map(|(x, y)| (x - y).abs())
                    .sum()
            }
            DistanceMetric::DotProduct => {
                -a.iter().zip(b.iter()).map(|(x, y)| x * y).sum::<f64>()
            }
        }
    }
    
    /// 将距离转换为相似度分数
    fn distance_to_score(&self, distance: f64) -> f64 {
        match self.config.distance_metric {
            DistanceMetric::Euclidean | DistanceMetric::Manhattan => {
                1.0 / (1.0 + distance)
            }
            DistanceMetric::Cosine => {
                1.0 - distance
            }
            DistanceMetric::DotProduct => {
                -distance
            }
        }
    }
    
    /// 获取集合信息
    pub fn get_collection_info(&self, collection_name: &str) -> Result<CollectionInfo, String> {
        let collection = self.collections.get(collection_name)
            .ok_or_else(|| format!("集合 '{}' 不存在", collection_name))?;
        
        Ok(CollectionInfo {
            name: collection.name.clone(),
            vector_count: collection.vectors.len(),
            dimension: self.config.vector_dimension,
            distance_metric: self.config.distance_metric.clone(),
            has_index: collection.index.is_some(),
        })
    }
    
    /// 删除向量
    pub fn delete_vector(&mut self, collection_name: &str, vector_id: &str) -> Result<(), String> {
        let collection = self.collections.get_mut(collection_name)
            .ok_or_else(|| format!("集合 '{}' 不存在", collection_name))?;
        
        let initial_len = collection.vectors.len();
        collection.vectors.retain(|v| v.id != vector_id);
        
        if collection.vectors.len() == initial_len {
            return Err(format!("向量 '{}' 不存在", vector_id));
        }
        
        Ok(())
    }
    
    /// 清空集合
    pub fn clear_collection(&mut self, collection_name: &str) -> Result<(), String> {
        let collection = self.collections.get_mut(collection_name)
            .ok_or_else(|| format!("集合 '{}' 不存在", collection_name))?;
        
        collection.vectors.clear();
        Ok(())
    }
}

/// 搜索结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SearchResult {
    pub vector: Vector,
    pub distance: f64,
    pub score: f64,
}

/// 集合信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CollectionInfo {
    pub name: String,
    pub vector_count: usize,
    pub dimension: usize,
    pub distance_metric: DistanceMetric,
    pub has_index: bool,
}

impl Default for DatabaseConfig {
    fn default() -> Self {
        Self {
            max_vectors_per_collection: 10000,
            vector_dimension: 128,
            distance_metric: DistanceMetric::Cosine,
            enable_persistence: false,
            cache_size: 1000,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_vector_database_creation() {
        let config = DatabaseConfig::default();
        let db = VectorDatabase::new("test_db".to_string(), config);
        
        assert_eq!(db.name, "test_db");
        assert_eq!(db.collections.len(), 0);
    }
    
    #[test]
    fn test_create_collection() {
        let mut db = VectorDatabase::new("test_db".to_string(), DatabaseConfig::default());
        
        db.create_collection("test_collection".to_string()).unwrap();
        assert_eq!(db.collections.len(), 1);
        assert!(db.collections.contains_key("test_collection"));
    }
    
    #[test]
    fn test_insert_and_search_vector() {
        let mut db = VectorDatabase::new("test_db".to_string(), DatabaseConfig::default());
        db.create_collection("test_collection".to_string()).unwrap();
        
        let vector = Vector {
            id: "vec1".to_string(),
            data: vec![1.0, 2.0, 3.0, 4.0],
            metadata: HashMap::new(),
        };
        
        db.insert_vector("test_collection", vector).unwrap();
        
        let query = vec![1.1, 2.1, 3.1, 4.1];
        let results = db.search("test_collection", &query, 1).unwrap();
        
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].vector.id, "vec1");
    }
    
    #[test]
    fn test_euclidean_distance() {
        let config = DatabaseConfig {
            distance_metric: DistanceMetric::Euclidean,
            ..Default::default()
        };
        let db = VectorDatabase::new("test_db".to_string(), config);
        
        let a = vec![0.0, 0.0];
        let b = vec![3.0, 4.0];
        let distance = db.calculate_distance(&a, &b);
        
        assert!((distance - 5.0).abs() < 1e-10); // 3-4-5 直角三角形
    }
    
    #[test]
    fn test_cosine_similarity() {
        let config = DatabaseConfig {
            distance_metric: DistanceMetric::Cosine,
            ..Default::default()
        };
        let db = VectorDatabase::new("test_db".to_string(), config);
        
        let a = vec![1.0, 0.0];
        let b = vec![1.0, 0.0];
        let distance = db.calculate_distance(&a, &b);
        
        assert!(distance.abs() < 1e-10); // 相同向量，余弦距离为 0
    }
}
