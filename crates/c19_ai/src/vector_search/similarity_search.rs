//! 相似性搜索
//!
//! 提供高效的相似性搜索算法和优化

use crate::vector_search::VectorDatabase;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// 相似性搜索引擎
#[derive(Debug, Clone)]
pub struct SimilaritySearchEngine {
    pub name: String,
    pub database: VectorDatabase,
    pub search_config: SearchConfig,
}

/// 搜索配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SearchConfig {
    pub default_top_k: usize,
    pub similarity_threshold: f64,
    pub enable_filtering: bool,
    pub max_search_time_ms: u64,
    pub cache_results: bool,
}

/// 搜索查询
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SearchQuery {
    pub vector: Vec<f64>,
    pub top_k: Option<usize>,
    pub threshold: Option<f64>,
    pub filters: Option<HashMap<String, serde_json::Value>>,
    pub include_metadata: bool,
}

/// 搜索结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SearchResponse {
    pub results: Vec<SearchResult>,
    pub total_found: usize,
    pub search_time_ms: u64,
    pub query_info: QueryInfo,
}

/// 搜索结果项
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SearchResult {
    pub id: String,
    pub score: f64,
    pub distance: f64,
    pub metadata: Option<HashMap<String, serde_json::Value>>,
}

/// 查询信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct QueryInfo {
    pub collection_name: String,
    pub vector_dimension: usize,
    pub distance_metric: String,
    pub algorithm_used: String,
}

/// 批量搜索请求
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BatchSearchRequest {
    pub queries: Vec<SearchQuery>,
    pub collection_name: String,
}

/// 批量搜索结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BatchSearchResponse {
    pub responses: Vec<SearchResponse>,
    pub total_queries: usize,
    pub total_time_ms: u64,
}

impl SimilaritySearchEngine {
    /// 创建新的相似性搜索引擎
    pub fn new(name: String, database: VectorDatabase, config: SearchConfig) -> Self {
        Self {
            name,
            database,
            search_config: config,
        }
    }

    /// 执行相似性搜索
    pub fn search(
        &self,
        collection_name: &str,
        query: SearchQuery,
    ) -> Result<SearchResponse, String> {
        let start_time = std::time::Instant::now();

        // 验证查询
        self.validate_query(&query)?;

        // 执行搜索
        let top_k = query.top_k.unwrap_or(self.search_config.default_top_k);
        let threshold = query
            .threshold
            .unwrap_or(self.search_config.similarity_threshold);

        let raw_results = self
            .database
            .search(collection_name, &query.vector, top_k)?;

        // 应用阈值过滤
        let filtered_results: Vec<SearchResult> = raw_results
            .into_iter()
            .filter(|result| result.score >= threshold)
            .map(|result| SearchResult {
                id: result.vector.id,
                score: result.score,
                distance: result.distance,
                metadata: if query.include_metadata {
                    Some(result.vector.metadata)
                } else {
                    None
                },
            })
            .collect();

        let search_time = start_time.elapsed().as_millis() as u64;

        // 获取查询信息
        let collection_info = self.database.get_collection_info(collection_name)?;
        let query_info = QueryInfo {
            collection_name: collection_name.to_string(),
            vector_dimension: collection_info.dimension,
            distance_metric: format!("{:?}", collection_info.distance_metric),
            algorithm_used: "brute_force".to_string(), // 简化实现
        };

        Ok(SearchResponse {
            results: filtered_results,
            total_found: filtered_results.len(),
            search_time_ms: search_time,
            query_info,
        })
    }

    /// 批量搜索
    pub fn batch_search(&self, request: BatchSearchRequest) -> Result<BatchSearchResponse, String> {
        let start_time = std::time::Instant::now();
        let mut responses = Vec::new();

        for query in request.queries {
            let response = self.search(&request.collection_name, query)?;
            responses.push(response);
        }

        let total_time = start_time.elapsed().as_millis() as u64;

        Ok(BatchSearchResponse {
            responses,
            total_queries: request.queries.len(),
            total_time_ms: total_time,
        })
    }

    /// 验证搜索查询
    fn validate_query(&self, query: &SearchQuery) -> Result<(), String> {
        if query.vector.is_empty() {
            return Err("查询向量不能为空".to_string());
        }

        if let Some(top_k) = query.top_k {
            if top_k == 0 {
                return Err("top_k 必须大于 0".to_string());
            }
        }

        if let Some(threshold) = query.threshold {
            if threshold < 0.0 || threshold > 1.0 {
                return Err("相似度阈值必须在 [0, 1] 范围内".to_string());
            }
        }

        Ok(())
    }

    /// 获取搜索统计信息
    pub fn get_search_stats(&self) -> SearchStats {
        let total_collections = self.database.collections.len();
        let total_vectors: usize = self
            .database
            .collections
            .values()
            .map(|c| c.vectors.len())
            .sum();

        SearchStats {
            total_collections,
            total_vectors,
            average_vectors_per_collection: if total_collections > 0 {
                total_vectors as f64 / total_collections as f64
            } else {
                0.0
            },
            search_config: self.search_config.clone(),
        }
    }

    /// 优化搜索性能
    pub fn optimize_search(&mut self) -> Result<OptimizationReport, String> {
        let mut report = OptimizationReport::new();

        // 为每个集合构建索引
        for (collection_name, collection) in &mut self.database.collections {
            if collection.index.is_none() {
                // 简化实现：为大型集合添加索引
                if collection.vectors.len() > 1000 {
                    collection.index = Some(
                        crate::vector_search::VectorIndex::ApproximateNearestNeighbor {
                            algorithm: crate::vector_search::ANNAlgorithm::HNSW,
                            parameters: HashMap::new(),
                        },
                    );
                    report.indexes_created += 1;
                }
            }
        }

        // 优化搜索配置
        if self.search_config.default_top_k > 100 {
            self.search_config.default_top_k = 100;
            report.config_optimizations += 1;
        }

        report.optimization_complete = true;
        Ok(report)
    }
}

/// 搜索统计信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SearchStats {
    pub total_collections: usize,
    pub total_vectors: usize,
    pub average_vectors_per_collection: f64,
    pub search_config: SearchConfig,
}

/// 优化报告
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OptimizationReport {
    pub indexes_created: usize,
    pub config_optimizations: usize,
    pub optimization_complete: bool,
    pub recommendations: Vec<String>,
}

impl OptimizationReport {
    pub fn new() -> Self {
        Self {
            indexes_created: 0,
            config_optimizations: 0,
            optimization_complete: false,
            recommendations: Vec::new(),
        }
    }

    pub fn add_recommendation(&mut self, recommendation: String) {
        self.recommendations.push(recommendation);
    }
}

impl Default for SearchConfig {
    fn default() -> Self {
        Self {
            default_top_k: 10,
            similarity_threshold: 0.7,
            enable_filtering: true,
            max_search_time_ms: 1000,
            cache_results: true,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vector_search::{DatabaseConfig, DistanceMetric, VectorDatabase};

    #[test]
    fn test_search_engine_creation() {
        let config = DatabaseConfig::default();
        let db = VectorDatabase::new("test_db".to_string(), config);
        let search_config = SearchConfig::default();

        let engine = SimilaritySearchEngine::new("test_engine".to_string(), db, search_config);

        assert_eq!(engine.name, "test_engine");
    }

    #[test]
    fn test_similarity_search() {
        let mut config = DatabaseConfig::default();
        config.vector_dimension = 3;
        let mut db = VectorDatabase::new("test_db".to_string(), config);

        db.create_collection("test_collection".to_string()).unwrap();

        // 插入测试向量
        let vectors = vec![
            ("vec1", vec![1.0, 0.0, 0.0]),
            ("vec2", vec![0.0, 1.0, 0.0]),
            ("vec3", vec![0.0, 0.0, 1.0]),
        ];

        for (id, data) in vectors {
            let vector = crate::vector_search::Vector {
                id: id.to_string(),
                data,
                metadata: HashMap::new(),
            };
            db.insert_vector("test_collection", vector).unwrap();
        }

        let search_config = SearchConfig::default();
        let engine = SimilaritySearchEngine::new("test_engine".to_string(), db, search_config);

        let query = SearchQuery {
            vector: vec![1.0, 0.0, 0.0],
            top_k: Some(2),
            threshold: Some(0.5),
            filters: None,
            include_metadata: false,
        };

        let response = engine.search("test_collection", query).unwrap();

        assert_eq!(response.results.len(), 1); // 应该找到 vec1
        assert_eq!(response.results[0].id, "vec1");
    }

    #[test]
    fn test_batch_search() {
        let mut config = DatabaseConfig::default();
        config.vector_dimension = 2;
        let mut db = VectorDatabase::new("test_db".to_string(), config);

        db.create_collection("test_collection".to_string()).unwrap();

        // 插入测试向量
        let vector = crate::vector_search::Vector {
            id: "vec1".to_string(),
            data: vec![1.0, 0.0],
            metadata: HashMap::new(),
        };
        db.insert_vector("test_collection", vector).unwrap();

        let search_config = SearchConfig::default();
        let engine = SimilaritySearchEngine::new("test_engine".to_string(), db, search_config);

        let request = BatchSearchRequest {
            queries: vec![
                SearchQuery {
                    vector: vec![1.0, 0.0],
                    top_k: Some(1),
                    threshold: Some(0.5),
                    filters: None,
                    include_metadata: false,
                },
                SearchQuery {
                    vector: vec![0.0, 1.0],
                    top_k: Some(1),
                    threshold: Some(0.5),
                    filters: None,
                    include_metadata: false,
                },
            ],
            collection_name: "test_collection".to_string(),
        };

        let response = engine.batch_search(request).unwrap();

        assert_eq!(response.total_queries, 2);
        assert_eq!(response.responses.len(), 2);
    }

    #[test]
    fn test_query_validation() {
        let config = DatabaseConfig::default();
        let db = VectorDatabase::new("test_db".to_string(), config);
        let search_config = SearchConfig::default();
        let engine = SimilaritySearchEngine::new("test_engine".to_string(), db, search_config);

        // 测试空向量
        let invalid_query = SearchQuery {
            vector: vec![],
            top_k: Some(1),
            threshold: Some(0.5),
            filters: None,
            include_metadata: false,
        };

        assert!(engine.validate_query(&invalid_query).is_err());

        // 测试无效阈值
        let invalid_threshold_query = SearchQuery {
            vector: vec![1.0, 2.0],
            top_k: Some(1),
            threshold: Some(1.5),
            filters: None,
            include_metadata: false,
        };

        assert!(engine.validate_query(&invalid_threshold_query).is_err());
    }
}
