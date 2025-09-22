//! 模型管理
//! 
//! 提供大语言模型的注册、管理和查询功能

use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use uuid::Uuid;
use chrono::{DateTime, Utc};

/// 模型信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Model {
    pub id: String,
    pub name: String,
    pub provider: String,
    pub description: Option<String>,
    pub version: String,
    pub model_type: ModelType,
    pub capabilities: Vec<ModelCapability>,
    pub parameters: ModelParameters,
    pub pricing: Option<PricingInfo>,
    pub status: ModelStatus,
    pub metadata: HashMap<String, serde_json::Value>,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

/// 模型类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ModelType {
    Chat,
    Completion,
    Embedding,
    Multimodal,
    Code,
    Custom(String),
}

/// 模型能力
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ModelCapability {
    Chat,
    Completion,
    Embedding,
    FunctionCalling,
    Vision,
    CodeGeneration,
    Reasoning,
    Multimodal,
    Custom(String),
}

/// 模型参数
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ModelParameters {
    pub max_tokens: Option<usize>,
    pub context_length: Option<usize>,
    pub dimensions: Option<usize>,
    pub temperature_range: Option<(f64, f64)>,
    pub top_p_range: Option<(f64, f64)>,
    pub top_k_range: Option<(usize, usize)>,
    pub frequency_penalty_range: Option<(f64, f64)>,
    pub presence_penalty_range: Option<(f64, f64)>,
    pub stop_sequences: Vec<String>,
    pub supported_languages: Vec<String>,
    pub supported_formats: Vec<String>,
}

/// 定价信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PricingInfo {
    pub input_price_per_1k_tokens: f64,
    pub output_price_per_1k_tokens: f64,
    pub currency: String,
    pub billing_unit: BillingUnit,
    pub free_tier: Option<FreeTier>,
}

/// 计费单位
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum BillingUnit {
    Tokens,
    Requests,
    Characters,
    Images,
    Custom(String),
}

/// 免费额度
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FreeTier {
    pub monthly_limit: Option<usize>,
    pub daily_limit: Option<usize>,
    pub hourly_limit: Option<usize>,
    pub unit: BillingUnit,
}

/// 模型状态
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ModelStatus {
    Active,
    Inactive,
    Deprecated,
    Beta,
    Alpha,
    Custom(String),
}

/// 模型注册表
#[derive(Debug)]
pub struct ModelRegistry {
    models: HashMap<String, Model>,
    providers: HashMap<String, Vec<String>>,
    categories: HashMap<String, Vec<String>>,
    search_index: HashMap<String, Vec<String>>,
}

impl ModelRegistry {
    /// 创建新的模型注册表
    pub fn new() -> Self {
        Self {
            models: HashMap::new(),
            providers: HashMap::new(),
            categories: HashMap::new(),
            search_index: HashMap::new(),
        }
    }

    /// 注册模型
    pub fn register_model(&mut self, model: Model) -> Result<()> {
        let model_id = model.id.clone();
        
        // 添加到模型映射
        self.models.insert(model_id.clone(), model.clone());
        
        // 添加到提供商映射
        self.providers
            .entry(model.provider.clone())
            .or_insert_with(Vec::new)
            .push(model_id.clone());
        
        // 添加到类别映射
        let category = format!("{:?}", model.model_type);
        self.categories
            .entry(category)
            .or_insert_with(Vec::new)
            .push(model_id.clone());
        
        // 添加到搜索索引
        self.add_to_search_index(&model_id, &model);
        
        Ok(())
    }

    /// 获取模型
    pub fn get_model(&self, model_id: &str) -> Option<&Model> {
        self.models.get(model_id)
    }

    /// 获取所有模型
    pub fn get_all_models(&self) -> Vec<&Model> {
        self.models.values().collect()
    }

    /// 按提供商获取模型
    pub fn get_models_by_provider(&self, provider: &str) -> Vec<&Model> {
        if let Some(model_ids) = self.providers.get(provider) {
            model_ids.iter()
                .filter_map(|id| self.models.get(id))
                .collect()
        } else {
            Vec::new()
        }
    }

    /// 按类型获取模型
    pub fn get_models_by_type(&self, model_type: &ModelType) -> Vec<&Model> {
        let category = format!("{:?}", model_type);
        if let Some(model_ids) = self.categories.get(&category) {
            model_ids.iter()
                .filter_map(|id| self.models.get(id))
                .collect()
        } else {
            Vec::new()
        }
    }

    /// 添加到搜索索引
    fn add_to_search_index(&mut self, model_id: &str, model: &Model) {
        let terms = vec![
            model.name.to_lowercase(),
            model.id.to_lowercase(),
            model.provider.to_lowercase(),
            format!("{:?}", model.model_type).to_lowercase(),
        ];
        
        for term in terms {
            self.search_index
                .entry(term)
                .or_insert_with(Vec::new)
                .push(model_id.to_string());
        }
    }

    /// 从搜索索引中移除
    fn remove_from_search_index(&mut self, model_id: &str) {
        self.search_index.retain(|_, model_ids| {
            model_ids.retain(|id| id != model_id);
            !model_ids.is_empty()
        });
    }

    /// 获取提供商列表
    pub fn get_providers(&self) -> Vec<String> {
        self.providers.keys().cloned().collect()
    }

    /// 获取类别列表
    pub fn get_categories(&self) -> Vec<String> {
        self.categories.keys().cloned().collect()
    }

    /// 获取模型数量
    pub fn model_count(&self) -> usize {
        self.models.len()
    }
}

impl Default for ModelRegistry {
    fn default() -> Self {
        Self::new()
    }
}