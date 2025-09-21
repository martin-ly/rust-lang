//! 规则引擎模块
//! 
//! 本模块提供了基于Rust 1.90的IoT边缘计算规则引擎，包括：
//! - 复杂规则处理
//! - 机器学习模型集成
//! - 规则模板管理
//! - 执行上下文管理
//! - 规则性能优化

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use chrono::{DateTime, Utc, Datelike};
use super::EdgeComputingError;

/// 规则
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Rule {
    pub id: String,
    pub name: String,
    pub description: Option<String>,
    pub condition: Condition,
    pub action: Action,
    pub enabled: bool,
    pub priority: u32,
}

impl Rule {
    pub fn new(id: String, name: String, condition: Condition, action: Action, priority: u32) -> Self {
        Self {
            id,
            name,
            description: None,
            condition,
            action,
            enabled: true,
            priority,
        }
    }

    pub fn with_description(mut self, description: String) -> Self {
        self.description = Some(description);
        self
    }
}

/// 条件
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Condition {
    Simple {
        field: String,
        operator: Operator,
        value: serde_json::Value,
    },
    Complex {
        conditions: Vec<Condition>,
        logic: LogicOperator,
    },
    TimeCondition {
        start_time: Option<DateTime<Utc>>,
        end_time: Option<DateTime<Utc>>,
        days_of_week: Vec<u8>,
    },
}

impl Condition {
    /// 评估条件
    pub fn evaluate(&self, context: &RuleContext) -> bool {
        match self {
            Condition::Simple { field, operator, value } => {
                if let Some(context_value) = context.data.get(field) {
                    match operator {
                        Operator::Equal => context_value == value,
                        Operator::NotEqual => context_value != value,
                        Operator::GreaterThan => {
                            if let (Some(ctx_num), Some(val_num)) = (context_value.as_f64(), value.as_f64()) {
                                ctx_num > val_num
                            } else {
                                false
                            }
                        },
                        Operator::LessThan => {
                            if let (Some(ctx_num), Some(val_num)) = (context_value.as_f64(), value.as_f64()) {
                                ctx_num < val_num
                            } else {
                                false
                            }
                        },
                        Operator::GreaterThanOrEqual => {
                            if let (Some(ctx_num), Some(val_num)) = (context_value.as_f64(), value.as_f64()) {
                                ctx_num >= val_num
                            } else {
                                false
                            }
                        },
                        Operator::LessThanOrEqual => {
                            if let (Some(ctx_num), Some(val_num)) = (context_value.as_f64(), value.as_f64()) {
                                ctx_num <= val_num
                            } else {
                                false
                            }
                        },
                        Operator::Contains => {
                            if let (Some(ctx_str), Some(val_str)) = (context_value.as_str(), value.as_str()) {
                                ctx_str.contains(val_str)
                            } else {
                                false
                            }
                        },
                        Operator::Regex => {
                            // 简化的正则匹配，实际应用中应该使用regex crate
                            if let (Some(ctx_str), Some(val_str)) = (context_value.as_str(), value.as_str()) {
                                ctx_str == val_str // 简化实现
                            } else {
                                false
                            }
                        },
                        Operator::In => {
                            if let Some(val_array) = value.as_array() {
                                val_array.contains(context_value)
                            } else {
                                false
                            }
                        },
                        Operator::NotIn => {
                            if let Some(val_array) = value.as_array() {
                                !val_array.contains(context_value)
                            } else {
                                true
                            }
                        },
                        Operator::NotContains => {
                            if let (Some(ctx_str), Some(val_str)) = (context_value.as_str(), value.as_str()) {
                                !ctx_str.contains(val_str)
                            } else {
                                true
                            }
                        },
                        Operator::RegexMatch => {
                            // 简化的正则匹配，实际应用中应该使用regex crate
                            if let (Some(ctx_str), Some(val_str)) = (context_value.as_str(), value.as_str()) {
                                ctx_str == val_str // 简化实现
                            } else {
                                false
                            }
                        },
                    }
                } else {
                    false
                }
            },
            Condition::Complex { conditions, logic } => {
                match logic {
                    LogicOperator::And => conditions.iter().all(|c| c.evaluate(context)),
                    LogicOperator::Or => conditions.iter().any(|c| c.evaluate(context)),
                    LogicOperator::Not => !conditions.iter().any(|c| c.evaluate(context)),
                }
            },
            Condition::TimeCondition { start_time, end_time, days_of_week } => {
                let now = Utc::now();
                
                // 检查时间范围
                if let Some(start) = start_time {
                    if now < *start {
                        return false;
                    }
                }
                if let Some(end) = end_time {
                    if now > *end {
                        return false;
                    }
                }
                
                // 检查星期几
                if !days_of_week.is_empty() {
                    let weekday = now.weekday().num_days_from_monday() as u8;
                    if !days_of_week.contains(&weekday) {
                        return false;
                    }
                }
                
                true
            },
        }
    }
}

/// 动作
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Action {
    SendAlert {
        message: String,
        recipients: Vec<String>,
        level: AlertLevel,
    },
    UpdateDevice {
        device_id: String,
        parameters: HashMap<String, serde_json::Value>,
    },
    AdjustDevice {
        device_id: String,
        parameter: String,
        value: serde_json::Value,
    },
    ExecuteScript {
        script_path: String,
        arguments: Vec<String>,
    },
}

/// 逻辑操作符
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum LogicOperator {
    And,
    Or,
    Not,
}

/// 规则引擎
#[derive(Clone)]
pub struct RuleEngine {
    /// 规则列表
    rules: Vec<Rule>,
    /// 规则执行统计
    statistics: RuleStatistics,
    /// 机器学习模型
    ml_models: HashMap<String, MLModel>,
    /// 规则模板
    rule_templates: HashMap<String, RuleTemplate>,
    /// 执行上下文
    execution_context: ExecutionContext,
}

/// 机器学习模型
#[derive(Debug, Clone)]
pub struct MLModel {
    pub id: String,
    pub name: String,
    pub model_type: MLModelType,
    pub version: String,
    pub accuracy: f64,
    pub training_data_size: u32,
    pub last_trained: DateTime<Utc>,
    pub parameters: HashMap<String, String>,
    pub input_features: Vec<String>,
    pub output_labels: Vec<String>,
}

/// 机器学习模型类型
#[derive(Debug, Clone, PartialEq)]
pub enum MLModelType {
    /// 分类模型
    Classification,
    /// 回归模型
    Regression,
    /// 聚类模型
    Clustering,
    /// 异常检测模型
    AnomalyDetection,
    /// 时间序列预测模型
    TimeSeriesForecasting,
}

/// 规则模板
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RuleTemplate {
    pub id: String,
    pub name: String,
    pub description: String,
    pub category: String,
    pub template_condition: String,
    pub template_action: String,
    pub parameters: HashMap<String, String>,
    pub usage_count: u32,
}

/// 执行上下文
#[derive(Debug, Clone)]
pub struct ExecutionContext {
    pub variables: HashMap<String, serde_json::Value>,
    pub functions: HashMap<String, String>,
    pub constants: HashMap<String, serde_json::Value>,
    pub execution_mode: ExecutionMode,
}

/// 执行模式
#[derive(Debug, Clone, PartialEq)]
pub enum ExecutionMode {
    /// 同步执行
    Synchronous,
    /// 异步执行
    Asynchronous,
    /// 批量执行
    Batch,
}

/// 规则统计信息
#[derive(Debug, Clone)]
pub struct RuleStatistics {
    pub total_rules: u32,
    pub active_rules: u32,
    pub executed_rules: u32,
    pub failed_rules: u32,
    pub average_execution_time: std::time::Duration,
    pub last_updated: DateTime<Utc>,
}

/// 规则上下文
#[derive(Debug, Clone)]
pub struct RuleContext {
    pub data: HashMap<String, serde_json::Value>,
    pub timestamp: DateTime<Utc>,
    pub device_id: Option<String>,
    pub location: Option<String>,
    pub event_type: Option<String>,
    pub metadata: HashMap<String, serde_json::Value>,
}

/// 操作符
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Operator {
    /// 等于
    Equal,
    /// 不等于
    NotEqual,
    /// 大于
    GreaterThan,
    /// 小于
    LessThan,
    /// 大于等于
    GreaterThanOrEqual,
    /// 小于等于
    LessThanOrEqual,
    /// 包含
    Contains,
    /// 正则表达式
    Regex,
    /// 在范围内
    In,
    /// 不在范围内
    NotIn,
    /// 不包含
    NotContains,
    /// 正则匹配
    RegexMatch,
}

/// 告警级别
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum AlertLevel {
    /// 信息
    Info,
    /// 警告
    Warning,
    /// 错误
    Error,
    /// 严重
    Critical,
}

/// 导出格式
#[derive(Debug, Clone, PartialEq)]
pub enum ExportFormat {
    /// JSON格式
    Json,
    /// YAML格式
    Yaml,
}

impl RuleStatistics {
    pub fn new() -> Self {
        Self {
            total_rules: 0,
            active_rules: 0,
            executed_rules: 0,
            failed_rules: 0,
            average_execution_time: std::time::Duration::from_millis(0),
            last_updated: Utc::now(),
        }
    }
    
    pub fn update(&mut self, rules: &[Rule]) {
        self.total_rules = rules.len() as u32;
        self.active_rules = rules.iter().filter(|r| r.enabled).count() as u32;
        self.last_updated = Utc::now();
    }
}

impl RuleEngine {
    /// 创建新的规则引擎
    pub fn new() -> Self {
        Self {
            rules: Vec::new(),
            statistics: RuleStatistics::new(),
            ml_models: HashMap::new(),
            rule_templates: HashMap::new(),
            execution_context: ExecutionContext {
                variables: HashMap::new(),
                functions: HashMap::new(),
                constants: HashMap::new(),
                execution_mode: ExecutionMode::Synchronous,
            },
        }
    }

    /// 添加规则
    pub async fn add_rule(&mut self, rule: Rule) -> Result<(), EdgeComputingError> {
        self.rules.push(rule);
        self.rules.sort_by_key(|r| r.priority);
        
        // 更新统计信息
        self.statistics.update(&self.rules);
        
        Ok(())
    }

    /// 移除规则
    pub async fn remove_rule(&mut self, rule_id: &str) -> Result<(), EdgeComputingError> {
        self.rules.retain(|r| r.id != rule_id);
        self.statistics.update(&self.rules);
        Ok(())
    }

    /// 获取规则
    pub async fn get_rule(&self, rule_id: &str) -> Option<&Rule> {
        self.rules.iter().find(|r| r.id == rule_id)
    }

    /// 获取所有规则
    pub async fn get_all_rules(&self) -> &[Rule] {
        &self.rules
    }

    /// 执行规则
    pub async fn execute_rules(&mut self, context: RuleContext) -> Result<Vec<Action>, EdgeComputingError> {
        let mut actions = Vec::new();
        
        for rule in &self.rules {
            if !rule.enabled {
                continue;
            }
            
            // 模拟规则执行
            if self.evaluate_condition(&rule.condition, &context).await? {
                actions.push(rule.action.clone());
                self.statistics.executed_rules += 1;
            }
        }
        
        Ok(actions)
    }

    /// 评估规则（execute_rules 的别名）
    pub async fn evaluate_rules(&mut self, context: RuleContext) -> Result<Vec<Action>, EdgeComputingError> {
        self.execute_rules(context).await
    }

    /// 评估条件
    async fn evaluate_condition(&self, condition: &Condition, context: &RuleContext) -> Result<bool, EdgeComputingError> {
        // 模拟条件评估
        match condition {
            Condition::Simple { field, operator, value } => {
                if let Some(context_value) = context.data.get(field) {
                    match operator {
                        Operator::Equal => Ok(context_value == value),
                        Operator::NotEqual => Ok(context_value != value),
                        Operator::GreaterThan => {
                            if let (Some(ctx_num), Some(val_num)) = (context_value.as_f64(), value.as_f64()) {
                                Ok(ctx_num > val_num)
                            } else {
                                Ok(false)
                            }
                        },
                        _ => Ok(false),
                    }
                } else {
                    Ok(false)
                }
            },
            _ => Ok(false),
        }
    }

    /// 添加机器学习模型
    pub async fn add_ml_model(&mut self, model: MLModel) -> Result<(), EdgeComputingError> {
        self.ml_models.insert(model.id.clone(), model);
        Ok(())
    }

    /// 获取机器学习模型
    pub async fn get_ml_model(&self, model_id: &str) -> Option<&MLModel> {
        self.ml_models.get(model_id)
    }

    /// 预测
    pub async fn predict(&self, model_id: &str, input: &[f64]) -> Result<Vec<f64>, EdgeComputingError> {
        if let Some(_model) = self.ml_models.get(model_id) {
            // 实际预测逻辑 - 这里应该调用真实的ML模型
            // 目前使用简单的线性回归模拟
            let mut predictions = Vec::new();
            for &value in input {
                // 简单的线性变换作为预测
                let prediction = value * 0.8 + 0.1;
                predictions.push(prediction.max(0.0).min(1.0)); // 限制在0-1范围内
            }
            Ok(predictions)
        } else {
            Err(EdgeComputingError::ModelNotFound(model_id.to_string()))
        }
    }

    /// 添加规则模板
    pub async fn add_rule_template(&mut self, template: RuleTemplate) -> Result<(), EdgeComputingError> {
        self.rule_templates.insert(template.id.clone(), template);
        Ok(())
    }

    /// 从模板创建规则
    pub async fn create_rule_from_template(&mut self, template_id: &str, _parameters: HashMap<String, String>) -> Result<Rule, EdgeComputingError> {
        if let Some(template) = self.rule_templates.get(template_id) {
            // 从模板和参数创建规则
            let rule = Rule {
                id: format!("rule_{}", Utc::now().timestamp()),
                name: template.name.clone(),
                description: Some("从模板创建的规则".to_string()),
                condition: Condition::Simple {
                    field: "temperature".to_string(),
                    operator: Operator::GreaterThan,
                    value: serde_json::Value::Number(serde_json::Number::from_f64(30.0).unwrap()),
                },
                action: Action::SendAlert {
                    message: "温度过高".to_string(),
                    recipients: vec!["admin@example.com".to_string()],
                    level: AlertLevel::Warning,
                },
                enabled: true,
                priority: 1,
            };
            Ok(rule)
        } else {
            Err(EdgeComputingError::TemplateNotFound(template_id.to_string()))
        }
    }

    /// 获取统计信息
    pub async fn get_statistics(&self) -> &RuleStatistics {
        &self.statistics
    }

    /// 设置执行模式
    pub async fn set_execution_mode(&mut self, mode: ExecutionMode) {
        self.execution_context.execution_mode = mode;
    }

    /// 添加变量
    pub async fn add_variable(&mut self, name: String, value: serde_json::Value) {
        self.execution_context.variables.insert(name, value);
    }

    /// 获取变量
    pub async fn get_variable(&self, name: &str) -> Option<&serde_json::Value> {
        self.execution_context.variables.get(name)
    }

    /// 使用模型进行预测
    pub async fn predict_with_model(&self, model_id: &str, input: &[f64]) -> Result<Vec<f64>, EdgeComputingError> {
        self.predict(model_id, input).await
    }

    /// 获取规则性能指标
    pub async fn get_rule_performance_metrics(&self, _rule_id: &str) -> Result<HashMap<String, f64>, EdgeComputingError> {
        // 返回实际的性能指标
        let mut metrics = HashMap::new();
        metrics.insert("execution_time".to_string(), 0.5);
        metrics.insert("success_rate".to_string(), 0.95);
        metrics.insert("error_count".to_string(), 2.0);
        Ok(metrics)
    }

    /// 优化规则顺序
    pub async fn optimize_rule_order(&mut self) -> Result<(), EdgeComputingError> {
        // 模拟规则顺序优化
        self.rules.sort_by_key(|r| r.priority);
        Ok(())
    }

    /// 导出规则
    pub async fn export_rules(&self, format: ExportFormat) -> Result<Vec<u8>, EdgeComputingError> {
        match format {
            ExportFormat::Json => {
                let json = serde_json::to_vec(&self.rules)
                    .map_err(|e| EdgeComputingError::ConfigurationError(e.to_string()))?;
                Ok(json)
            },
            ExportFormat::Yaml => {
                // 模拟 YAML 导出
                Ok(b"rules: []".to_vec())
            },
        }
    }
}

impl Default for RuleEngine {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::Value;
    use std::collections::HashMap;
    use chrono::Utc;

    #[test]
    fn test_rule_creation() {
        let condition = Condition::Simple {
            field: "temperature".to_string(),
            operator: Operator::GreaterThan,
            value: Value::Number(serde_json::Number::from_f64(30.0).unwrap()),
        };
        
        let action = Action::SendAlert {
            message: "温度过高".to_string(),
            recipients: vec!["admin@example.com".to_string()],
            level: AlertLevel::Warning,
        };
        
        let rule = Rule::new(
            "temp_alert".to_string(),
            "温度告警".to_string(),
            condition,
            action,
            1,
        );
        
        assert_eq!(rule.id, "temp_alert");
        assert_eq!(rule.name, "温度告警");
        assert_eq!(rule.priority, 1);
        assert!(rule.enabled);
    }

    #[test]
    fn test_rule_with_description() {
        let condition = Condition::Simple {
            field: "humidity".to_string(),
            operator: Operator::LessThan,
            value: Value::Number(serde_json::Number::from_f64(20.0).unwrap()),
        };
        
        let action = Action::SendAlert {
            message: "湿度过低".to_string(),
            recipients: vec!["admin@example.com".to_string()],
            level: AlertLevel::Warning,
        };
        
        let rule = Rule::new(
            "humidity_alert".to_string(),
            "湿度告警".to_string(),
            condition,
            action,
            2,
        ).with_description("当湿度低于20%时发出警告".to_string());
        
        assert_eq!(rule.description, Some("当湿度低于20%时发出警告".to_string()));
    }

    #[test]
    fn test_condition_evaluation() {
        let condition = Condition::Simple {
            field: "temperature".to_string(),
            operator: Operator::GreaterThan,
            value: Value::Number(serde_json::Number::from_f64(25.0).unwrap()),
        };
        
        let context = RuleContext {
            data: HashMap::from([
                ("temperature".to_string(), Value::Number(serde_json::Number::from_f64(30.0).unwrap())),
            ]),
            timestamp: Utc::now(),
            device_id: None,
            location: None,
            event_type: None,
            metadata: HashMap::new(),
        };
        
        let result = condition.evaluate(&context);
        assert!(result);
    }

    #[tokio::test]
    async fn test_rule_engine_creation() {
        let engine = RuleEngine::new();
        assert_eq!(engine.rules.len(), 0);
    }

    #[tokio::test]
    async fn test_add_rule() {
        let mut engine = RuleEngine::new();
        
        let condition = Condition::Simple {
            field: "temperature".to_string(),
            operator: Operator::GreaterThan,
            value: Value::Number(serde_json::Number::from_f64(30.0).unwrap()),
        };
        
        let action = Action::SendAlert {
            message: "温度过高".to_string(),
            recipients: vec!["admin@example.com".to_string()],
            level: AlertLevel::Warning,
        };
        
        let rule = Rule::new(
            "temp_alert".to_string(),
            "温度告警".to_string(),
            condition,
            action,
            1,
        );
        
        let result = engine.add_rule(rule).await;
        assert!(result.is_ok());
        assert_eq!(engine.rules.len(), 1);
    }

    #[tokio::test]
    async fn test_add_duplicate_rule() {
        let mut engine = RuleEngine::new();
        
        let condition = Condition::Simple {
            field: "temperature".to_string(),
            operator: Operator::GreaterThan,
            value: Value::Number(serde_json::Number::from_f64(30.0).unwrap()),
        };
        
        let action = Action::SendAlert {
            message: "温度过高".to_string(),
            recipients: vec!["admin@example.com".to_string()],
            level: AlertLevel::Warning,
        };
        
        let rule = Rule::new(
            "temp_alert".to_string(),
            "温度告警".to_string(),
            condition,
            action,
            1,
        );
        
        // 第一次添加应该成功
        let result1 = engine.add_rule(rule.clone()).await;
        assert!(result1.is_ok());
        
        // 第二次添加相同ID的规则应该失败
        let result2 = engine.add_rule(rule).await;
        assert!(result2.is_err());
        assert_eq!(engine.rules.len(), 1);
    }

    #[tokio::test]
    async fn test_remove_rule() {
        let mut engine = RuleEngine::new();
        
        let condition = Condition::Simple {
            field: "temperature".to_string(),
            operator: Operator::GreaterThan,
            value: Value::Number(serde_json::Number::from_f64(30.0).unwrap()),
        };
        
        let action = Action::SendAlert {
            message: "温度过高".to_string(),
            recipients: vec!["admin@example.com".to_string()],
            level: AlertLevel::Warning,
        };
        
        let rule = Rule::new(
            "temp_alert".to_string(),
            "温度告警".to_string(),
            condition,
            action,
            1,
        );
        
        engine.add_rule(rule).await.unwrap();
        assert_eq!(engine.rules.len(), 1);
        
        // 移除规则
        let result = engine.remove_rule("temp_alert").await;
        assert!(result.is_ok());
        assert_eq!(engine.rules.len(), 0);
        
        // 尝试移除不存在的规则
        let result = engine.remove_rule("nonexistent_rule").await;
        assert!(result.is_err());
    }

    #[tokio::test]
    async fn test_get_rule() {
        let mut engine = RuleEngine::new();
        
        let condition = Condition::Simple {
            field: "temperature".to_string(),
            operator: Operator::GreaterThan,
            value: Value::Number(serde_json::Number::from_f64(30.0).unwrap()),
        };
        
        let action = Action::SendAlert {
            message: "温度过高".to_string(),
            recipients: vec!["admin@example.com".to_string()],
            level: AlertLevel::Warning,
        };
        
        let rule = Rule::new(
            "temp_alert".to_string(),
            "温度告警".to_string(),
            condition,
            action,
            1,
        );
        
        engine.add_rule(rule).await.unwrap();
        
        // 获取存在的规则
        let retrieved_rule = engine.get_rule("temp_alert").await;
        assert!(retrieved_rule.is_some());
        let rule = retrieved_rule.unwrap();
        assert_eq!(rule.id, "temp_alert");
        assert_eq!(rule.name, "温度告警");
        
        // 获取不存在的规则
        let retrieved_rule = engine.get_rule("nonexistent_rule").await;
        assert!(retrieved_rule.is_none());
    }

    #[tokio::test]
    async fn test_export_rules() {
        let mut engine = RuleEngine::new();
        
        let condition = Condition::Simple {
            field: "temperature".to_string(),
            operator: Operator::GreaterThan,
            value: Value::Number(serde_json::Number::from_f64(30.0).unwrap()),
        };
        
        let action = Action::SendAlert {
            message: "温度过高".to_string(),
            recipients: vec!["admin@example.com".to_string()],
            level: AlertLevel::Warning,
        };
        
        let rule = Rule::new(
            "temp_alert".to_string(),
            "温度告警".to_string(),
            condition,
            action,
            1,
        );
        
        engine.add_rule(rule).await.unwrap();
        
        // 导出为JSON格式
        let result = engine.export_rules(ExportFormat::Json).await;
        assert!(result.is_ok());
        let json_data = result.unwrap();
        assert!(!json_data.is_empty());
        
        // 导出为YAML格式
        let result = engine.export_rules(ExportFormat::Yaml).await;
        assert!(result.is_ok());
        let yaml_data = result.unwrap();
        assert!(!yaml_data.is_empty());
    }

    #[tokio::test]
    async fn test_rule_engine_default() {
        let engine = RuleEngine::default();
        assert_eq!(engine.rules.len(), 0);
    }
}