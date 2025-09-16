//! 向量嵌入模块
//!
//! 提供文本、图像等数据的向量化功能

use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// 嵌入模型
#[derive(Debug, Clone)]
pub struct EmbeddingModel {
    pub name: String,
    pub model_type: EmbeddingModelType,
    pub dimension: usize,
    pub max_input_length: usize,
    pub config: EmbeddingConfig,
}

/// 嵌入模型类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum EmbeddingModelType {
    /// 文本嵌入
    TextEmbedding,
    /// 图像嵌入
    ImageEmbedding,
    /// 多模态嵌入
    MultimodalEmbedding,
    /// 句子嵌入
    SentenceEmbedding,
}

/// 嵌入配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EmbeddingConfig {
    pub normalize: bool,
    pub batch_size: usize,
    pub device: String,
    pub precision: Precision,
}

/// 精度类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Precision {
    /// 32位浮点
    Float32,
    /// 16位浮点
    Float16,
    /// 8位整数
    Int8,
}

/// 嵌入结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EmbeddingResult {
    pub embeddings: Vec<Vec<f64>>,
    pub input_tokens: Option<Vec<usize>>,
    pub metadata: HashMap<String, serde_json::Value>,
}

/// 文本嵌入器
#[derive(Debug, Clone)]
pub struct TextEmbedder {
    pub model: EmbeddingModel,
    pub tokenizer: Option<Tokenizer>,
}

/// 分词器
#[derive(Debug, Clone)]
pub struct Tokenizer {
    pub name: String,
    pub vocab_size: usize,
    pub special_tokens: HashMap<String, usize>,
}

/// 批量嵌入请求
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BatchEmbeddingRequest {
    pub texts: Vec<String>,
    pub model_name: String,
    pub normalize: Option<bool>,
    pub batch_size: Option<usize>,
}

/// 批量嵌入响应
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BatchEmbeddingResponse {
    pub embeddings: Vec<Vec<f64>>,
    pub total_tokens: usize,
    pub processing_time_ms: u64,
    pub model_info: EmbeddingModel,
}

impl EmbeddingModel {
    /// 创建新的嵌入模型
    pub fn new(name: String, model_type: EmbeddingModelType, dimension: usize) -> Self {
        Self {
            name,
            model_type,
            dimension,
            max_input_length: 512,
            config: EmbeddingConfig::default(),
        }
    }

    /// 获取模型信息
    pub fn get_info(&self) -> ModelInfo {
        ModelInfo {
            name: self.name.clone(),
            model_type: self.model_type.clone(),
            dimension: self.dimension,
            max_input_length: self.max_input_length,
            config: self.config.clone(),
        }
    }
}

impl TextEmbedder {
    /// 创建新的文本嵌入器
    pub fn new(model: EmbeddingModel) -> Self {
        Self {
            model,
            tokenizer: None,
        }
    }

    /// 设置分词器
    pub fn set_tokenizer(&mut self, tokenizer: Tokenizer) {
        self.tokenizer = Some(tokenizer);
    }

    /// 嵌入单个文本
    pub fn embed_text(&self, text: &str) -> Result<EmbeddingResult, String> {
        // 验证输入长度
        if text.len() > self.model.max_input_length {
            return Err(format!(
                "文本长度 {} 超过最大长度 {}",
                text.len(),
                self.model.max_input_length
            ));
        }

        // 简化的嵌入实现
        let tokens = self.tokenize(text)?;
        let embedding = self.generate_embedding(&tokens)?;

        Ok(EmbeddingResult {
            embeddings: vec![embedding],
            input_tokens: Some(tokens),
            metadata: HashMap::new(),
        })
    }

    /// 批量嵌入文本
    pub fn embed_batch(&self, texts: &[String]) -> Result<BatchEmbeddingResponse, String> {
        let start_time = std::time::Instant::now();
        let mut embeddings = Vec::new();
        let mut total_tokens = 0;

        for text in texts {
            let result = self.embed_text(text)?;
            embeddings.extend(result.embeddings);
            if let Some(tokens) = result.input_tokens {
                total_tokens += tokens.len();
            }
        }

        let processing_time = start_time.elapsed().as_millis() as u64;

        Ok(BatchEmbeddingResponse {
            embeddings,
            total_tokens,
            processing_time_ms: processing_time,
            model_info: self.model.clone(),
        })
    }

    /// 计算文本相似度
    pub fn compute_similarity(&self, text1: &str, text2: &str) -> Result<f64, String> {
        let result1 = self.embed_text(text1)?;
        let result2 = self.embed_text(text2)?;

        if result1.embeddings.is_empty() || result2.embeddings.is_empty() {
            return Err("嵌入结果为空".to_string());
        }

        let embedding1 = &result1.embeddings[0];
        let embedding2 = &result2.embeddings[0];

        if embedding1.len() != embedding2.len() {
            return Err("嵌入维度不匹配".to_string());
        }

        // 计算余弦相似度
        let dot_product: f64 = embedding1
            .iter()
            .zip(embedding2.iter())
            .map(|(a, b)| a * b)
            .sum();

        let norm1: f64 = embedding1.iter().map(|x| x * x).sum::<f64>().sqrt();
        let norm2: f64 = embedding2.iter().map(|x| x * x).sum::<f64>().sqrt();

        if norm1 == 0.0 || norm2 == 0.0 {
            return Ok(0.0);
        }

        Ok(dot_product / (norm1 * norm2))
    }

    /// 分词
    fn tokenize(&self, text: &str) -> Result<Vec<usize>, String> {
        if let Some(tokenizer) = &self.tokenizer {
            // 简化的分词实现
            let words: Vec<&str> = text.split_whitespace().collect();
            let tokens: Vec<usize> = words
                .iter()
                .map(|word| {
                    // 简单的哈希函数作为 token ID
                    word.len() % tokenizer.vocab_size
                })
                .collect();
            Ok(tokens)
        } else {
            // 如果没有分词器，使用字符级别的简单编码
            let tokens: Vec<usize> = text
                .chars()
                .map(|c| c as usize % 1000) // 简化的字符编码
                .collect();
            Ok(tokens)
        }
    }

    /// 生成嵌入
    fn generate_embedding(&self, tokens: &[usize]) -> Result<Vec<f64>, String> {
        // 简化的嵌入生成：基于 token 的统计特征
        let mut embedding = vec![0.0; self.model.dimension];

        for (i, &token) in tokens.iter().enumerate() {
            let idx = i % self.model.dimension;
            embedding[idx] += (token as f64) / (tokens.len() as f64);
        }

        // 归一化
        if self.model.config.normalize {
            let norm: f64 = embedding.iter().map(|x| x * x).sum::<f64>().sqrt();
            if norm > 0.0 {
                for val in &mut embedding {
                    *val /= norm;
                }
            }
        }

        Ok(embedding)
    }
}

/// 模型信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ModelInfo {
    pub name: String,
    pub model_type: EmbeddingModelType,
    pub dimension: usize,
    pub max_input_length: usize,
    pub config: EmbeddingConfig,
}

impl Default for EmbeddingConfig {
    fn default() -> Self {
        Self {
            normalize: true,
            batch_size: 32,
            device: "cpu".to_string(),
            precision: Precision::Float32,
        }
    }
}

/// 预定义的嵌入模型
pub mod models {
    use super::*;

    /// 创建 BERT 风格的文本嵌入模型
    pub fn create_bert_model() -> EmbeddingModel {
        EmbeddingModel::new(
            "bert-base".to_string(),
            EmbeddingModelType::TextEmbedding,
            768,
        )
    }

    /// 创建句子嵌入模型
    pub fn create_sentence_model() -> EmbeddingModel {
        EmbeddingModel::new(
            "sentence-transformers".to_string(),
            EmbeddingModelType::SentenceEmbedding,
            384,
        )
    }

    /// 创建图像嵌入模型
    pub fn create_image_model() -> EmbeddingModel {
        EmbeddingModel::new(
            "resnet-embedding".to_string(),
            EmbeddingModelType::ImageEmbedding,
            2048,
        )
    }

    /// 创建多模态嵌入模型
    pub fn create_multimodal_model() -> EmbeddingModel {
        EmbeddingModel::new(
            "clip-model".to_string(),
            EmbeddingModelType::MultimodalEmbedding,
            512,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_embedding_model_creation() {
        let model = EmbeddingModel::new(
            "test-model".to_string(),
            EmbeddingModelType::TextEmbedding,
            128,
        );

        assert_eq!(model.name, "test-model");
        assert_eq!(model.dimension, 128);
        assert_eq!(model.model_type, EmbeddingModelType::TextEmbedding);
    }

    #[test]
    fn test_text_embedder() {
        let model = EmbeddingModel::new(
            "test-model".to_string(),
            EmbeddingModelType::TextEmbedding,
            10,
        );
        let embedder = TextEmbedder::new(model);

        let result = embedder.embed_text("Hello world").unwrap();
        assert_eq!(result.embeddings.len(), 1);
        assert_eq!(result.embeddings[0].len(), 10);
    }

    #[test]
    fn test_batch_embedding() {
        let model = EmbeddingModel::new(
            "test-model".to_string(),
            EmbeddingModelType::TextEmbedding,
            5,
        );
        let embedder = TextEmbedder::new(model);

        let texts = vec!["Hello".to_string(), "World".to_string()];
        let response = embedder.embed_batch(&texts).unwrap();

        assert_eq!(response.embeddings.len(), 2);
        assert_eq!(response.total_queries, 2);
    }

    #[test]
    fn test_text_similarity() {
        let model = EmbeddingModel::new(
            "test-model".to_string(),
            EmbeddingModelType::TextEmbedding,
            5,
        );
        let embedder = TextEmbedder::new(model);

        let similarity = embedder.compute_similarity("Hello", "Hello").unwrap();
        assert!(similarity > 0.0);

        let similarity2 = embedder.compute_similarity("Hello", "World").unwrap();
        assert!(similarity2 >= 0.0 && similarity2 <= 1.0);
    }

    #[test]
    fn test_tokenizer() {
        let model = EmbeddingModel::new(
            "test-model".to_string(),
            EmbeddingModelType::TextEmbedding,
            10,
        );
        let mut embedder = TextEmbedder::new(model);

        let tokenizer = Tokenizer {
            name: "simple".to_string(),
            vocab_size: 1000,
            special_tokens: HashMap::new(),
        };
        embedder.set_tokenizer(tokenizer);

        let result = embedder.embed_text("Hello world").unwrap();
        assert!(result.input_tokens.is_some());
    }
}
