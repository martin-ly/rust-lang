//! 模型管理
//!
//! 提供 LLM 模型的管理功能

use anyhow::Result;
use serde::{Deserialize, Serialize};

/// 模型信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ModelInfo {
    pub name: String,
    pub version: String,
    pub description: String,
    pub capabilities: Vec<String>,
}

/// 模型管理器
pub struct ModelManager {
    models: std::collections::HashMap<String, ModelInfo>,
}

impl ModelManager {
    pub fn new() -> Self {
        Self {
            models: std::collections::HashMap::new(),
        }
    }

    pub fn register_model(&mut self, model: ModelInfo) {
        self.models.insert(model.name.clone(), model);
    }

    pub fn get_model(&self, name: &str) -> Option<&ModelInfo> {
        self.models.get(name)
    }
}
