//! 配置管理模块
//!
//! 本模块提供了统一的配置管理功能，包括默认配置、配置验证、
//! 配置序列化等。使用Rust的类型安全特性确保配置的正确性。

use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// 日志级别
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[derive(Default)]
pub enum LogLevel {
    /// 错误级别
    Error,
    /// 警告级别
    Warn,
    /// 信息级别
    #[default]
    Info,
    /// 调试级别
    Debug,
    /// 跟踪级别
    Trace,
}


impl std::fmt::Display for LogLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LogLevel::Error => write!(f, "ERROR"),
            LogLevel::Warn => write!(f, "WARN"),
            LogLevel::Info => write!(f, "INFO"),
            LogLevel::Debug => write!(f, "DEBUG"),
            LogLevel::Trace => write!(f, "TRACE"),
        }
    }
}

/// 数值精度配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PrecisionConfig {
    /// 默认精度
    pub default_precision: f64,
    /// 收敛阈值
    pub convergence_threshold: f64,
    /// 最大迭代次数
    pub max_iterations: usize,
    /// 数值稳定性阈值
    pub stability_threshold: f64,
}

impl Default for PrecisionConfig {
    fn default() -> Self {
        Self {
            default_precision: 1e-6,
            convergence_threshold: 1e-6,
            max_iterations: 1000,
            stability_threshold: 1e-12,
        }
    }
}

/// 性能配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PerformanceConfig {
    /// 是否启用并行计算
    pub enable_parallel: bool,
    /// 并行线程数（0表示自动）
    pub thread_count: usize,
    /// 是否启用缓存
    pub enable_cache: bool,
    /// 缓存大小限制
    pub cache_size_limit: usize,
    /// 是否启用性能监控
    pub enable_profiling: bool,
}

impl Default for PerformanceConfig {
    fn default() -> Self {
        Self {
            enable_parallel: true,
            thread_count: 0, // 自动检测
            enable_cache: true,
            cache_size_limit: 1000,
            enable_profiling: false,
        }
    }
}

/// 可视化配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VisualizationConfig {
    /// 默认图表宽度
    pub default_width: u32,
    /// 默认图表高度
    pub default_height: u32,
    /// 默认颜色主题
    pub color_theme: String,
    /// 是否启用动画
    pub enable_animation: bool,
    /// 导出格式
    pub export_formats: Vec<String>,
}

impl Default for VisualizationConfig {
    fn default() -> Self {
        Self {
            default_width: 800,
            default_height: 600,
            color_theme: "default".to_string(),
            enable_animation: false,
            export_formats: vec!["svg".to_string(), "png".to_string()],
        }
    }
}

/// 模型配置
#[derive(Debug, Clone, Serialize, Deserialize)]
#[derive(Default)]
pub struct ModelConfig {
    /// 数值精度配置
    pub precision: PrecisionConfig,
    /// 性能配置
    pub performance: PerformanceConfig,
    /// 可视化配置
    pub visualization: VisualizationConfig,
    /// 日志配置
    pub log_level: LogLevel,
    /// 是否启用日志
    pub enable_logging: bool,
    /// 自定义配置
    pub custom: HashMap<String, serde_json::Value>,
}


impl ModelConfig {
    /// 创建新的配置
    pub fn new() -> Self {
        Self::default()
    }

    /// 从JSON字符串加载配置
    pub fn from_json(json: &str) -> Result<Self, String> {
        serde_json::from_str(json).map_err(|e| format!("配置解析错误: {}", e))
    }

    /// 将配置保存为JSON字符串
    pub fn to_json(&self) -> Result<String, String> {
        serde_json::to_string_pretty(self).map_err(|e| format!("配置序列化错误: {}", e))
    }

    /// 验证配置
    pub fn validate(&self) -> Result<(), String> {
        // 验证精度配置
        if self.precision.default_precision <= 0.0 {
            return Err("默认精度必须大于0".to_string());
        }
        if self.precision.convergence_threshold <= 0.0 {
            return Err("收敛阈值必须大于0".to_string());
        }
        if self.precision.max_iterations == 0 {
            return Err("最大迭代次数必须大于0".to_string());
        }

        // 验证性能配置
        if self.performance.cache_size_limit == 0 {
            return Err("缓存大小限制必须大于0".to_string());
        }

        // 验证可视化配置
        if self.visualization.default_width == 0 {
            return Err("默认宽度必须大于0".to_string());
        }
        if self.visualization.default_height == 0 {
            return Err("默认高度必须大于0".to_string());
        }

        Ok(())
    }

    /// 设置自定义配置
    pub fn set_custom(&mut self, key: String, value: serde_json::Value) {
        self.custom.insert(key, value);
    }

    /// 获取自定义配置
    pub fn get_custom(&self, key: &str) -> Option<&serde_json::Value> {
        self.custom.get(key)
    }

    /// 更新精度配置
    pub fn with_precision(mut self, precision: PrecisionConfig) -> Self {
        self.precision = precision;
        self
    }

    /// 更新性能配置
    pub fn with_performance(mut self, performance: PerformanceConfig) -> Self {
        self.performance = performance;
        self
    }

    /// 更新可视化配置
    pub fn with_visualization(mut self, visualization: VisualizationConfig) -> Self {
        self.visualization = visualization;
        self
    }

    /// 设置日志级别
    pub fn with_log_level(mut self, log_level: LogLevel) -> Self {
        self.log_level = log_level;
        self
    }

    /// 启用或禁用日志
    pub fn with_logging(mut self, enable: bool) -> Self {
        self.enable_logging = enable;
        self
    }
}

/// 配置管理器
#[derive(Debug, Clone)]
pub struct ConfigManager {
    config: ModelConfig,
}

impl ConfigManager {
    /// 创建新的配置管理器
    pub fn new() -> Self {
        Self {
            config: ModelConfig::default(),
        }
    }

    /// 从配置创建管理器
    pub fn from_config(config: ModelConfig) -> Result<Self, String> {
        config.validate()?;
        Ok(Self { config })
    }

    /// 获取当前配置
    pub fn get_config(&self) -> &ModelConfig {
        &self.config
    }

    /// 更新配置
    pub fn update_config(&mut self, config: ModelConfig) -> Result<(), String> {
        config.validate()?;
        self.config = config;
        Ok(())
    }

    /// 获取精度配置
    pub fn get_precision_config(&self) -> &PrecisionConfig {
        &self.config.precision
    }

    /// 获取性能配置
    pub fn get_performance_config(&self) -> &PerformanceConfig {
        &self.config.performance
    }

    /// 获取可视化配置
    pub fn get_visualization_config(&self) -> &VisualizationConfig {
        &self.config.visualization
    }

    /// 获取日志级别
    pub fn get_log_level(&self) -> &LogLevel {
        &self.config.log_level
    }

    /// 是否启用日志
    pub fn is_logging_enabled(&self) -> bool {
        self.config.enable_logging
    }

    /// 从文件加载配置
    pub fn load_from_file(&mut self, path: &str) -> Result<(), String> {
        let content =
            std::fs::read_to_string(path).map_err(|e| format!("读取配置文件失败: {}", e))?;
        let config = ModelConfig::from_json(&content)?;
        self.update_config(config)
    }

    /// 保存配置到文件
    pub fn save_to_file(&self, path: &str) -> Result<(), String> {
        let content = self.config.to_json()?;
        std::fs::write(path, content).map_err(|e| format!("保存配置文件失败: {}", e))
    }

    /// 重置为默认配置
    pub fn reset_to_default(&mut self) {
        self.config = ModelConfig::default();
    }

    /// 获取配置摘要
    pub fn get_summary(&self) -> String {
        format!(
            "配置摘要:\n\
            - 默认精度: {}\n\
            - 收敛阈值: {}\n\
            - 最大迭代次数: {}\n\
            - 并行计算: {}\n\
            - 缓存: {}\n\
            - 日志级别: {}\n\
            - 日志启用: {}",
            self.config.precision.default_precision,
            self.config.precision.convergence_threshold,
            self.config.precision.max_iterations,
            self.config.performance.enable_parallel,
            self.config.performance.enable_cache,
            self.config.log_level,
            self.config.enable_logging
        )
    }
}

impl Default for ConfigManager {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_model_config_default() {
        let config = ModelConfig::default();
        assert_eq!(config.precision.default_precision, 1e-6);
        assert_eq!(config.precision.max_iterations, 1000);
        assert!(config.performance.enable_parallel);
        assert_eq!(config.log_level, LogLevel::Info);
        assert!(!config.enable_logging);
    }

    #[test]
    fn test_model_config_validation() {
        let mut config = ModelConfig::default();
        assert!(config.validate().is_ok());

        // 测试无效配置
        config.precision.default_precision = -1.0;
        assert!(config.validate().is_err());

        config.precision.default_precision = 1e-6;
        config.precision.max_iterations = 0;
        assert!(config.validate().is_err());
    }

    #[test]
    fn test_model_config_json() {
        let config = ModelConfig::default();
        let json = config.to_json().unwrap();
        let parsed_config = ModelConfig::from_json(&json).unwrap();

        assert_eq!(
            config.precision.default_precision,
            parsed_config.precision.default_precision
        );
        assert_eq!(config.log_level, parsed_config.log_level);
    }

    #[test]
    fn test_config_manager() {
        let manager = ConfigManager::new();
        assert!(manager.get_config().validate().is_ok());

        let summary = manager.get_summary();
        assert!(summary.contains("配置摘要"));
        assert!(summary.contains("默认精度"));
    }

    #[test]
    fn test_custom_config() {
        let mut config = ModelConfig::default();
        config.set_custom("test_key".to_string(), serde_json::json!("test_value"));

        let value = config.get_custom("test_key");
        assert!(value.is_some());
        assert_eq!(value.unwrap(), &serde_json::json!("test_value"));
    }

    #[test]
    fn test_log_level_display() {
        assert_eq!(LogLevel::Error.to_string(), "ERROR");
        assert_eq!(LogLevel::Warn.to_string(), "WARN");
        assert_eq!(LogLevel::Info.to_string(), "INFO");
        assert_eq!(LogLevel::Debug.to_string(), "DEBUG");
        assert_eq!(LogLevel::Trace.to_string(), "TRACE");
    }

    #[test]
    fn test_config_builder_pattern() {
        let config = ModelConfig::new()
            .with_log_level(LogLevel::Debug)
            .with_logging(true);

        assert_eq!(config.log_level, LogLevel::Debug);
        assert!(config.enable_logging);
    }
}
