//! # C19 AI - 人工智能与机器学习
//! 
//! 这是一个基于 Rust 1.89 的现代化 AI 和机器学习库，集成了最新的开源 AI 框架和工具。
//! 
//! ## 主要特性
//! 
//! - 🤖 **机器学习**: 支持监督学习、无监督学习和强化学习
//! - 🧠 **深度学习**: 集成 Candle、Burn、Tch 等现代深度学习框架
//! - 🗣️ **自然语言处理**: 支持 BERT、GPT 等预训练模型
//! - 👁️ **计算机视觉**: OpenCV 集成和图像处理功能
//! - 📊 **数据处理**: 高性能的 DataFrame 和数据处理管道
//! - 🔍 **向量搜索**: 支持向量数据库和语义搜索
//! - 🚀 **高性能**: 利用 Rust 的零成本抽象和内存安全
//! 
//! ## 快速开始
//! 
//! ```rust
//! use c19_ai::prelude::*;
//! 
//! #[tokio::main]
//! async fn main() -> Result<(), Box<dyn std::error::Error>> {
//!     // 创建 AI 引擎
//!     let mut ai_engine = AIEngine::new();
//!     
//!     // 加载预训练模型
//!     ai_engine.load_model("bert-base-chinese").await?;
//!     
//!     // 进行推理
//!     let result = ai_engine.predict("你好，世界！").await?;
//!     println!("预测结果: {:?}", result);
//!     
//!     Ok(())
//! }
//! ```

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use thiserror::Error;

// 核心模块
pub mod neural_networks;
pub mod machine_learning;
pub mod deep_learning;
pub mod nlp;
pub mod computer_vision;
pub mod data_processing;
pub mod vector_search;
pub mod model_management;
pub mod pipelines;

// 新增模块 - Rust 1.89 和最新 AI 功能
pub mod llm;
pub mod diffusion;
pub mod reinforcement_learning;
pub mod graph_neural_networks;
pub mod time_series;
pub mod monitoring;

// 预导入模块
pub mod prelude {
    pub use crate::{
        AIEngine, AIModule, ModelType, ModelConfig, 
        PredictionResult, TrainingConfig, Error,
        neural_networks::*, machine_learning::*, 
        deep_learning::*, nlp::*, computer_vision::*,
        data_processing::*, vector_search::*,
        model_management::*, pipelines::*,
        // 新增模块的预导入
        llm::*, diffusion::*, reinforcement_learning::*,
        graph_neural_networks::*, time_series::*, monitoring::*
    };
}

/// AI 引擎错误类型
#[derive(Error, Debug)]
pub enum Error {
    #[error("模型加载失败: {0}")]
    ModelLoadError(String),
    
    #[error("推理失败: {0}")]
    InferenceError(String),
    
    #[error("训练失败: {0}")]
    TrainingError(String),
    
    #[error("数据处理错误: {0}")]
    DataProcessingError(String),
    
    #[error("配置错误: {0}")]
    ConfigError(String),
    
    #[error("IO 错误: {0}")]
    IoError(#[from] std::io::Error),
    
    #[error("序列化错误: {0}")]
    SerializationError(#[from] serde_json::Error),
}

/// 模型类型枚举
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ModelType {
    /// 机器学习模型
    MachineLearning,
    /// 深度学习模型
    DeepLearning,
    /// 自然语言处理模型
    NLP,
    /// 计算机视觉模型
    ComputerVision,
    /// 多模态模型
    Multimodal,
}

/// 模型配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ModelConfig {
    pub name: String,
    pub model_type: ModelType,
    pub version: String,
    pub path: Option<String>,
    pub parameters: HashMap<String, serde_json::Value>,
}

/// 预测结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PredictionResult {
    pub predictions: Vec<f64>,
    pub confidence: f64,
    pub metadata: HashMap<String, serde_json::Value>,
}

/// 训练配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TrainingConfig {
    pub epochs: usize,
    pub batch_size: usize,
    pub learning_rate: f64,
    pub validation_split: f64,
    pub early_stopping: bool,
    pub metrics: Vec<String>,
}

/// AI 模块
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AIModule {
    pub name: String,
    pub version: String,
    pub description: String,
    pub capabilities: Vec<String>,
}

impl AIModule {
    /// 创建新的 AI 模块
    pub fn new(name: String, description: String) -> Self {
        Self {
            name,
            version: "0.1.0".to_string(),
            description,
            capabilities: Vec::new(),
        }
    }
    
    /// 添加能力
    pub fn add_capability(&mut self, capability: String) {
        self.capabilities.push(capability);
    }
    
    /// 获取模块信息
    pub fn get_info(&self) -> String {
        format!("AI模块: {} v{} - {}", self.name, self.version, self.description)
    }
    
    /// 获取能力列表
    pub fn get_capabilities(&self) -> &[String] {
        &self.capabilities
    }
}

/// AI 引擎 - 主要的 AI 系统接口
pub struct AIEngine {
    modules: HashMap<String, AIModule>,
    models: HashMap<String, ModelConfig>,
    config: EngineConfig,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EngineConfig {
    pub max_models: usize,
    pub cache_size: usize,
    pub enable_gpu: bool,
    pub log_level: String,
}

impl Default for EngineConfig {
    fn default() -> Self {
        Self {
            max_models: 10,
            cache_size: 1000,
            enable_gpu: false,
            log_level: "info".to_string(),
        }
    }
}

impl AIEngine {
    /// 创建新的 AI 引擎
    pub fn new() -> Self {
        Self {
            modules: HashMap::new(),
            models: HashMap::new(),
            config: EngineConfig::default(),
        }
    }
    
    /// 使用配置创建 AI 引擎
    pub fn with_config(config: EngineConfig) -> Self {
        Self {
            modules: HashMap::new(),
            models: HashMap::new(),
            config,
        }
    }
    
    /// 注册 AI 模块
    pub fn register_module(&mut self, module: AIModule) {
        self.modules.insert(module.name.clone(), module);
    }
    
    /// 加载模型
    pub async fn load_model(&mut self, model_name: &str) -> Result<(), Error> {
        // 这里将集成实际的模型加载逻辑
        tracing::info!("加载模型: {}", model_name);
        Ok(())
    }
    
    /// 进行预测
    pub async fn predict(&self, input: &str) -> Result<PredictionResult, Error> {
        // 这里将集成实际的预测逻辑
        tracing::info!("进行预测: {}", input);
        
        Ok(PredictionResult {
            predictions: vec![0.8, 0.2],
            confidence: 0.85,
            metadata: HashMap::new(),
        })
    }
    
    /// 训练模型
    pub async fn train(&mut self, config: TrainingConfig) -> Result<(), Error> {
        tracing::info!("开始训练模型，配置: {:?}", config);
        // 这里将集成实际的训练逻辑
        Ok(())
    }
    
    /// 获取已注册的模块
    pub fn get_modules(&self) -> &HashMap<String, AIModule> {
        &self.modules
    }
    
    /// 获取已加载的模型
    pub fn get_models(&self) -> &HashMap<String, ModelConfig> {
        &self.models
    }
}

impl Default for AIEngine {
    fn default() -> Self {
        Self::new()
    }
}

/// 创建默认的 AI 模块集合
pub fn create_default_modules() -> Vec<AIModule> {
    vec![
        {
            let mut ml_module = AIModule::new(
                "机器学习".to_string(),
                "支持各种机器学习算法".to_string(),
            );
            ml_module.add_capability("分类".to_string());
            ml_module.add_capability("回归".to_string());
            ml_module.add_capability("聚类".to_string());
            ml_module
        },
        {
            let mut dl_module = AIModule::new(
                "深度学习".to_string(),
                "支持神经网络和深度学习模型".to_string(),
            );
            dl_module.add_capability("CNN".to_string());
            dl_module.add_capability("RNN".to_string());
            dl_module.add_capability("Transformer".to_string());
            dl_module
        },
        {
            let mut nlp_module = AIModule::new(
                "自然语言处理".to_string(),
                "支持文本分析和语言模型".to_string(),
            );
            nlp_module.add_capability("文本分类".to_string());
            nlp_module.add_capability("情感分析".to_string());
            nlp_module.add_capability("机器翻译".to_string());
            nlp_module
        },
        {
            let mut cv_module = AIModule::new(
                "计算机视觉".to_string(),
                "支持图像处理和计算机视觉任务".to_string(),
            );
            cv_module.add_capability("图像分类".to_string());
            cv_module.add_capability("目标检测".to_string());
            cv_module.add_capability("图像分割".to_string());
            cv_module
        },
    ]
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_ai_module() {
        let mut ai = AIModule::new("测试模块".to_string(), "测试描述".to_string());
        ai.add_capability("测试能力".to_string());
        
        assert_eq!(ai.get_info(), "AI模块: 测试模块 v0.1.0 - 测试描述");
        assert_eq!(ai.get_capabilities(), &["测试能力"]);
    }
    
    #[test]
    fn test_ai_engine() {
        let mut engine = AIEngine::new();
        let module = AIModule::new("测试模块".to_string(), "测试描述".to_string());
        
        engine.register_module(module);
        assert_eq!(engine.get_modules().len(), 1);
    }
    
    #[test]
    fn test_default_modules() {
        let modules = create_default_modules();
        assert_eq!(modules.len(), 4);
        
        let ml_module = &modules[0];
        assert_eq!(ml_module.name, "机器学习");
        assert!(ml_module.capabilities.contains(&"分类".to_string()));
    }
    
    #[tokio::test]
    async fn test_ai_engine_async() {
        let engine = AIEngine::new();
        let result = engine.predict("测试输入").await.unwrap();
        
        assert_eq!(result.predictions.len(), 2);
        assert!(result.confidence > 0.0);
    }
}
