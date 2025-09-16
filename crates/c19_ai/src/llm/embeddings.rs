//! 嵌入向量功能
//!
//! 提供文本嵌入向量生成和相似度计算

use anyhow::Result;
use ndarray::Array1;
use rand::Rng;
use serde::{Deserialize, Serialize};

/// 嵌入向量
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Embedding {
    /// 向量数据
    pub vector: Vec<f32>,
    /// 原始文本
    pub text: String,
    /// 元数据
    pub metadata: Option<serde_json::Value>,
}

/// 嵌入配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EmbeddingConfig {
    /// 模型名称
    pub model: String,
    /// 向量维度
    pub dimensions: Option<usize>,
    /// 批处理大小
    pub batch_size: Option<usize>,
    /// 是否标准化
    pub normalize: bool,
}

/// 嵌入客户端 trait
pub trait EmbeddingClient {
    /// 生成单个文本的嵌入向量
    async fn embed(&self, text: &str) -> Result<Embedding>;

    /// 批量生成嵌入向量
    async fn embed_batch(&self, texts: &[String]) -> Result<Vec<Embedding>>;

    /// 获取支持的模型列表
    async fn list_models(&self) -> Result<Vec<String>>;
}

/// 嵌入向量工具
pub struct EmbeddingUtils;

impl EmbeddingUtils {
    /// 计算余弦相似度
    pub fn cosine_similarity(a: &[f32], b: &[f32]) -> Result<f32> {
        if a.len() != b.len() {
            return Err(anyhow::anyhow!("向量维度不匹配"));
        }

        let dot_product: f32 = a.iter().zip(b.iter()).map(|(x, y)| x * y).sum();
        let norm_a: f32 = a.iter().map(|x| x * x).sum::<f32>().sqrt();
        let norm_b: f32 = b.iter().map(|x| x * x).sum::<f32>().sqrt();

        if norm_a == 0.0 || norm_b == 0.0 {
            return Ok(0.0);
        }

        Ok(dot_product / (norm_a * norm_b))
    }

    /// 计算欧几里得距离
    pub fn euclidean_distance(a: &[f32], b: &[f32]) -> Result<f32> {
        if a.len() != b.len() {
            return Err(anyhow::anyhow!("向量维度不匹配"));
        }

        let distance: f32 = a
            .iter()
            .zip(b.iter())
            .map(|(x, y)| (x - y).powi(2))
            .sum::<f32>()
            .sqrt();

        Ok(distance)
    }

    /// 标准化向量
    pub fn normalize(vector: &[f32]) -> Vec<f32> {
        let norm: f32 = vector.iter().map(|x| x * x).sum::<f32>().sqrt();
        if norm == 0.0 {
            return vector.to_vec();
        }
        vector.iter().map(|x| x / norm).collect()
    }

    /// 查找最相似的嵌入向量
    pub fn find_most_similar(
        query: &Embedding,
        candidates: &[Embedding],
        top_k: usize,
    ) -> Result<Vec<(Embedding, f32)>> {
        let mut similarities: Vec<(Embedding, f32)> = candidates
            .iter()
            .map(|candidate| {
                let similarity =
                    Self::cosine_similarity(&query.vector, &candidate.vector).unwrap_or(0.0);
                (candidate.clone(), similarity)
            })
            .collect();

        similarities.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal));
        similarities.truncate(top_k);

        Ok(similarities)
    }
}

/// 嵌入向量数据库
pub struct EmbeddingDatabase {
    embeddings: Vec<Embedding>,
    index: Option<tantivy::Index>,
}

impl EmbeddingDatabase {
    /// 创建新的嵌入向量数据库
    pub fn new() -> Self {
        Self {
            embeddings: Vec::new(),
            index: None,
        }
    }

    /// 添加嵌入向量
    pub fn add_embedding(&mut self, embedding: Embedding) {
        self.embeddings.push(embedding);
    }

    /// 批量添加嵌入向量
    pub fn add_embeddings(&mut self, embeddings: Vec<Embedding>) {
        self.embeddings.extend(embeddings);
    }

    /// 搜索相似向量
    pub fn search(&self, query: &Embedding, top_k: usize) -> Result<Vec<(Embedding, f32)>> {
        EmbeddingUtils::find_most_similar(query, &self.embeddings, top_k)
    }

    /// 获取数据库大小
    pub fn size(&self) -> usize {
        self.embeddings.len()
    }

    /// 清空数据库
    pub fn clear(&mut self) {
        self.embeddings.clear();
    }
}

impl Default for EmbeddingConfig {
    fn default() -> Self {
        Self {
            model: "text-embedding-ada-002".to_string(),
            dimensions: None,
            batch_size: Some(100),
            normalize: true,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cosine_similarity() {
        let a = vec![1.0, 0.0, 0.0];
        let b = vec![0.0, 1.0, 0.0];
        let c = vec![1.0, 0.0, 0.0];

        assert_eq!(EmbeddingUtils::cosine_similarity(&a, &b).unwrap(), 0.0);
        assert_eq!(EmbeddingUtils::cosine_similarity(&a, &c).unwrap(), 1.0);
    }

    #[test]
    fn test_euclidean_distance() {
        let a = vec![0.0, 0.0];
        let b = vec![3.0, 4.0];

        assert_eq!(EmbeddingUtils::euclidean_distance(&a, &b).unwrap(), 5.0);
    }

    #[test]
    fn test_normalize() {
        let vector = vec![3.0, 4.0];
        let normalized = EmbeddingUtils::normalize(&vector);

        let norm: f32 = normalized.iter().map(|x| x * x).sum::<f32>().sqrt();
        assert!((norm - 1.0).abs() < 1e-6);
    }

    #[test]
    fn test_embedding_database() {
        let mut db = EmbeddingDatabase::new();

        let embedding1 = Embedding {
            vector: vec![1.0, 0.0, 0.0],
            text: "hello".to_string(),
            metadata: None,
        };

        let embedding2 = Embedding {
            vector: vec![0.0, 1.0, 0.0],
            text: "world".to_string(),
            metadata: None,
        };

        db.add_embedding(embedding1.clone());
        db.add_embedding(embedding2);

        let query = Embedding {
            vector: vec![1.0, 0.0, 0.0],
            text: "query".to_string(),
            metadata: None,
        };

        let results = db.search(&query, 1).unwrap();
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].0.text, "hello");
    }
}
