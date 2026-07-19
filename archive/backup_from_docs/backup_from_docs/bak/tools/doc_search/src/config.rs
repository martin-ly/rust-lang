// 配置管理模块

use serde::{Deserialize, Serialize};
use std::fs;
use std::path::{Path, PathBuf};

/// 搜索配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Config {
    /// 项目根目录
    pub root_path: Option<PathBuf>,
    
    /// 默认最大搜索结果数
    pub default_max_results: usize,
    
    /// 默认最小相关性分数
    pub default_min_score: f64,
    
    /// 索引缓存路径
    pub cache_path: Option<PathBuf>,
    
    /// 启用增量索引
    pub incremental_index: bool,
    
    /// 搜索历史文件路径
    pub history_path: Option<PathBuf>,
    
    /// 启用搜索历史
    pub enable_history: bool,
    
    /// 最大历史记录数
    pub max_history: usize,
    
    /// 导出格式
    pub export_format: ExportFormat,
    
    /// 高级搜索选项
    pub advanced: AdvancedOptions,
}

/// 高级搜索选项
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AdvancedOptions {
    /// 启用正则表达式搜索
    pub enable_regex: bool,
    
    /// 启用模糊搜索
    pub enable_fuzzy: bool,
    
    /// 模糊搜索阈值 (0.0-1.0)
    pub fuzzy_threshold: f64,
    
    /// 上下文行数
    pub context_lines: usize,
}

/// 导出格式
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
pub enum ExportFormat {
    Json,
    Csv,
    Markdown,
}

impl Default for Config {
    fn default() -> Self {
        Self {
            root_path: None,
            default_max_results: 20,
            default_min_score: 1.0,
            cache_path: None,
            incremental_index: true,
            history_path: None,
            enable_history: true,
            max_history: 100,
            export_format: ExportFormat::Json,
            advanced: AdvancedOptions::default(),
        }
    }
}

impl Default for AdvancedOptions {
    fn default() -> Self {
        Self {
            enable_regex: true,
            enable_fuzzy: true,
            fuzzy_threshold: 0.7,
            context_lines: 2,
        }
    }
}

impl Config {
    /// 从文件加载配置
    pub fn load_from_file<P: AsRef<Path>>(path: P) -> Result<Self, Box<dyn std::error::Error>> {
        let content = fs::read_to_string(path)?;
        let config: Config = toml::from_str(&content)?;
        Ok(config)
    }
    
    /// 保存配置到文件
    pub fn save_to_file<P: AsRef<Path>>(&self, path: P) -> Result<(), Box<dyn std::error::Error>> {
        let content = toml::to_string_pretty(self)?;
        fs::write(path, content)?;
        Ok(())
    }
    
    /// 获取默认配置文件路径
    pub fn default_config_path() -> Option<PathBuf> {
        dirs::config_dir().map(|mut p| {
            p.push("rust-doc-search");
            p.push("config.toml");
            p
        })
    }
    
    /// 加载或创建默认配置
    pub fn load_or_default() -> Self {
        if let Some(config_path) = Self::default_config_path() {
            if config_path.exists() {
                if let Ok(config) = Self::load_from_file(&config_path) {
                    return config;
                }
            }
        }
        Self::default()
    }
    
    /// 保存到默认位置
    pub fn save_default(&self) -> Result<(), Box<dyn std::error::Error>> {
        if let Some(config_path) = Self::default_config_path() {
            // 确保目录存在
            if let Some(parent) = config_path.parent() {
                fs::create_dir_all(parent)?;
            }
            self.save_to_file(config_path)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_config_serialization() {
        let config = Config::default();
        let toml_str = toml::to_string(&config).unwrap();
        let deserialized: Config = toml::from_str(&toml_str).unwrap();
        
        assert_eq!(config.default_max_results, deserialized.default_max_results);
        assert_eq!(config.default_min_score, deserialized.default_min_score);
    }
}

