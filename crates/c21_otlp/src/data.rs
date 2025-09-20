//! # OTLP数据模型模块
//! 
//! 定义OTLP协议的数据结构，支持Rust 1.90的类型系统特性。

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::time::{SystemTime, UNIX_EPOCH};
//use opentelemetry::trace::{SpanId, TraceId};
//use opentelemetry::KeyValue;

/// 遥测数据类型
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum TelemetryDataType {
    /// 追踪数据
    Trace,
    /// 指标数据
    Metric,
    /// 日志数据
    Log,
}

/// 遥测数据基类
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TelemetryData {
    /// 数据类型
    pub data_type: TelemetryDataType,
    /// 时间戳
    pub timestamp: u64,
    /// 资源属性
    pub resource_attributes: HashMap<String, String>,
    /// 作用域属性
    pub scope_attributes: HashMap<String, String>,
    /// 数据内容
    pub content: TelemetryContent,
}

/// 遥测数据内容
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TelemetryContent {
    /// 追踪数据
    Trace(TraceData),
    /// 指标数据
    Metric(MetricData),
    /// 日志数据
    Log(LogData),
}

/// 追踪数据
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraceData {
    /// 追踪ID
    pub trace_id: String,
    /// 跨度ID
    pub span_id: String,
    /// 父跨度ID
    pub parent_span_id: Option<String>,
    /// 操作名称
    pub name: String,
    /// 跨度类型
    pub span_kind: SpanKind,
    /// 开始时间
    pub start_time: u64,
    /// 结束时间
    pub end_time: u64,
    /// 状态
    pub status: SpanStatus,
    /// 属性
    pub attributes: HashMap<String, AttributeValue>,
    /// 事件
    pub events: Vec<SpanEvent>,
    /// 链接
    pub links: Vec<SpanLink>,
}

/// 跨度类型
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum SpanKind {
    /// 内部跨度
    Internal,
    /// 服务器跨度
    Server,
    /// 客户端跨度
    Client,
    /// 生产者跨度
    Producer,
    /// 消费者跨度
    Consumer,
}

impl Default for SpanKind {
    fn default() -> Self {
        Self::Internal
    }
}

/// 跨度状态
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SpanStatus {
    /// 状态代码
    pub code: StatusCode,
    /// 状态消息
    pub message: Option<String>,
}

impl Default for SpanStatus {
    fn default() -> Self {
        Self {
            code: StatusCode::Ok,
            message: None,
        }
    }
}

/// 状态代码
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum StatusCode {
    /// 未设置
    Unset,
    /// 成功
    Ok,
    /// 错误
    Error,
}

/// 属性值
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum AttributeValue {
    /// 字符串值
    String(String),
    /// 布尔值
    Bool(bool),
    /// 整数
    Int(i64),
    /// 浮点数
    Double(f64),
    /// 字符串数组
    StringArray(Vec<String>),
    /// 布尔数组
    BoolArray(Vec<bool>),
    /// 整数数组
    IntArray(Vec<i64>),
    /// 浮点数数组
    DoubleArray(Vec<f64>),
}

/// 跨度事件
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SpanEvent {
    /// 时间戳
    pub timestamp: u64,
    /// 名称
    pub name: String,
    /// 属性
    pub attributes: HashMap<String, AttributeValue>,
}

/// 跨度链接
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SpanLink {
    /// 追踪ID
    pub trace_id: String,
    /// 跨度ID
    pub span_id: String,
    /// 属性
    pub attributes: HashMap<String, AttributeValue>,
}

/// 指标数据
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MetricData {
    /// 指标名称
    pub name: String,
    /// 指标描述
    pub description: String,
    /// 指标单位
    pub unit: String,
    /// 指标类型
    pub metric_type: MetricType,
    /// 数据点
    pub data_points: Vec<DataPoint>,
}

/// 指标类型
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum MetricType {
    /// 计数器
    Counter,
    /// 仪表
    Gauge,
    /// 直方图
    Histogram,
    /// 摘要
    Summary,
}

/// 数据点
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DataPoint {
    /// 时间戳
    pub timestamp: u64,
    /// 属性
    pub attributes: HashMap<String, AttributeValue>,
    /// 值
    pub value: DataPointValue,
}

/// 数据点值
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum DataPointValue {
    /// 数值
    Number(f64),
    /// 直方图
    Histogram(HistogramData),
    /// 摘要
    Summary(SummaryData),
}

/// 直方图数据
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HistogramData {
    /// 计数
    pub count: u64,
    /// 总和
    pub sum: f64,
    /// 桶
    pub buckets: Vec<HistogramBucket>,
}

/// 直方图桶
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HistogramBucket {
    /// 计数
    pub count: u64,
    /// 上限
    pub upper_bound: f64,
}

/// 摘要数据
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SummaryData {
    /// 计数
    pub count: u64,
    /// 总和
    pub sum: f64,
    /// 分位数
    pub quantiles: Vec<Quantile>,
}

/// 分位数
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Quantile {
    /// 分位数
    pub quantile: f64,
    /// 值
    pub value: f64,
}

/// 日志数据
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LogData {
    /// 时间戳
    pub timestamp: u64,
    /// 严重程度
    pub severity: LogSeverity,
    /// 严重程度文本
    pub severity_text: String,
    /// 消息
    pub message: String,
    /// 属性
    pub attributes: HashMap<String, AttributeValue>,
    /// 资源属性
    pub resource_attributes: HashMap<String, AttributeValue>,
    /// 追踪ID
    pub trace_id: Option<String>,
    /// 跨度ID
    pub span_id: Option<String>,
}

/// 日志严重程度
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum LogSeverity {
    /// 跟踪
    Trace = 1,
    /// 调试
    Debug = 5,
    /// 信息
    Info = 9,
    /// 警告
    Warn = 13,
    /// 错误
    Error = 17,
    /// 致命
    Fatal = 21,
}

impl Default for LogSeverity {
    fn default() -> Self {
        Self::Info
    }
}

impl TelemetryData {
    /// 创建新的遥测数据
    pub fn new(data_type: TelemetryDataType, content: TelemetryContent) -> Self {
        Self {
            data_type,
            timestamp: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap_or_default()
                .as_nanos() as u64,
            resource_attributes: HashMap::new(),
            scope_attributes: HashMap::new(),
            content,
        }
    }

    /// 创建追踪数据
    pub fn trace(name: impl Into<String>) -> Self {
        let trace_id = format!("{:032x}", rand::random::<u128>());
        let span_id = format!("{:016x}", rand::random::<u64>());
        
        let trace_data = TraceData {
            trace_id: trace_id.clone(),
            span_id: span_id.clone(),
            parent_span_id: None,
            name: name.into(),
            span_kind: SpanKind::Internal,
            start_time: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap_or_default()
                .as_nanos() as u64,
            end_time: 0,
            status: SpanStatus::default(),
            attributes: HashMap::new(),
            events: Vec::new(),
            links: Vec::new(),
        };

        Self::new(TelemetryDataType::Trace, TelemetryContent::Trace(trace_data))
    }

    /// 创建指标数据
    pub fn metric(name: impl Into<String>, metric_type: MetricType) -> Self {
        let metric_data = MetricData {
            name: name.into(),
            description: String::new(),
            unit: String::new(),
            metric_type,
            data_points: Vec::new(),
        };

        Self::new(TelemetryDataType::Metric, TelemetryContent::Metric(metric_data))
    }

    /// 创建日志数据
    pub fn log(message: impl Into<String>, severity: LogSeverity) -> Self {
        let log_data = LogData {
            timestamp: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap_or_default()
                .as_nanos() as u64,
            severity,
            severity_text: format!("{:?}", severity),
            message: message.into(),
            attributes: HashMap::new(),
            resource_attributes: HashMap::new(),
            trace_id: None,
            span_id: None,
        };

        Self::new(TelemetryDataType::Log, TelemetryContent::Log(log_data))
    }

    /// 添加资源属性
    pub fn with_resource_attribute(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.resource_attributes.insert(key.into(), value.into());
        self
    }

    /// 添加作用域属性
    pub fn with_scope_attribute(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.scope_attributes.insert(key.into(), value.into());
        self
    }

    /// 添加属性（针对追踪数据）
    pub fn with_attribute(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        if let TelemetryContent::Trace(ref mut trace_data) = self.content {
            trace_data.attributes.insert(
                key.into(),
                AttributeValue::String(value.into()),
            );
        }
        self
    }

    /// 添加数值属性
    pub fn with_numeric_attribute(mut self, key: impl Into<String>, value: f64) -> Self {
        if let TelemetryContent::Trace(ref mut trace_data) = self.content {
            trace_data.attributes.insert(
                key.into(),
                AttributeValue::Double(value),
            );
        }
        self
    }

    /// 添加布尔属性
    pub fn with_bool_attribute(mut self, key: impl Into<String>, value: bool) -> Self {
        if let TelemetryContent::Trace(ref mut trace_data) = self.content {
            trace_data.attributes.insert(
                key.into(),
                AttributeValue::Bool(value),
            );
        }
        self
    }

    /// 设置跨度状态
    pub fn with_status(mut self, code: StatusCode, message: Option<String>) -> Self {
        if let TelemetryContent::Trace(ref mut trace_data) = self.content {
            trace_data.status = SpanStatus { code, message };
        }
        self
    }

    /// 添加事件
    pub fn with_event(mut self, name: impl Into<String>, attributes: HashMap<String, AttributeValue>) -> Self {
        if let TelemetryContent::Trace(ref mut trace_data) = self.content {
            let event = SpanEvent {
                timestamp: SystemTime::now()
                    .duration_since(UNIX_EPOCH)
                    .unwrap_or_default()
                    .as_nanos() as u64,
                name: name.into(),
                attributes,
            };
            trace_data.events.push(event);
        }
        self
    }

    /// 完成追踪（设置结束时间）
    pub fn finish(mut self) -> Self {
        if let TelemetryContent::Trace(ref mut trace_data) = self.content {
            trace_data.end_time = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap_or_default()
                .as_nanos() as u64;
        }
        self
    }

    /// 获取数据大小（字节）
    pub fn size(&self) -> usize {
        // 简化的大小计算，实际实现中可能需要更精确的计算
        let mut size = 0;
        
        // 基础字段
        size += 8; // timestamp
        size += self.resource_attributes.len() * 32; // 估算
        size += self.scope_attributes.len() * 32; // 估算
        
        // 内容大小
        match &self.content {
            TelemetryContent::Trace(trace) => {
                size += trace.trace_id.len();
                size += trace.span_id.len();
                size += trace.name.len();
                size += trace.attributes.len() * 32;
                size += trace.events.len() * 64;
                size += trace.links.len() * 64;
            }
            TelemetryContent::Metric(metric) => {
                size += metric.name.len();
                size += metric.description.len();
                size += metric.unit.len();
                size += metric.data_points.len() * 64;
            }
            TelemetryContent::Log(log) => {
                size += log.message.len();
                size += log.severity_text.len();
                size += log.attributes.len() * 32;
                size += log.resource_attributes.len() * 32;
            }
        }
        
        size
    }

    /// 检查数据是否有效
    pub fn is_valid(&self) -> bool {
        match &self.content {
            TelemetryContent::Trace(trace) => {
                !trace.trace_id.is_empty() && !trace.span_id.is_empty() && !trace.name.is_empty()
            }
            TelemetryContent::Metric(metric) => {
                !metric.name.is_empty() && !metric.data_points.is_empty()
            }
            TelemetryContent::Log(log) => {
                !log.message.is_empty()
            }
        }
    }
}

impl AttributeValue {
    /// 转换为字符串
    pub fn to_string(&self) -> String {
        match self {
            AttributeValue::String(s) => s.clone(),
            AttributeValue::Bool(b) => b.to_string(),
            AttributeValue::Int(i) => i.to_string(),
            AttributeValue::Double(d) => d.to_string(),
            AttributeValue::StringArray(arr) => format!("{:?}", arr),
            AttributeValue::BoolArray(arr) => format!("{:?}", arr),
            AttributeValue::IntArray(arr) => format!("{:?}", arr),
            AttributeValue::DoubleArray(arr) => format!("{:?}", arr),
        }
    }

    /// 获取类型名称
    pub fn type_name(&self) -> &'static str {
        match self {
            AttributeValue::String(_) => "string",
            AttributeValue::Bool(_) => "bool",
            AttributeValue::Int(_) => "int",
            AttributeValue::Double(_) => "double",
            AttributeValue::StringArray(_) => "string_array",
            AttributeValue::BoolArray(_) => "bool_array",
            AttributeValue::IntArray(_) => "int_array",
            AttributeValue::DoubleArray(_) => "double_array",
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_telemetry_data_creation() {
        let trace_data = TelemetryData::trace("test-operation");
        assert_eq!(trace_data.data_type, TelemetryDataType::Trace);
        assert!(trace_data.is_valid());
        
        let metric_data = TelemetryData::metric("test-metric", MetricType::Counter);
        assert_eq!(metric_data.data_type, TelemetryDataType::Metric);
        
        let log_data = TelemetryData::log("test message", LogSeverity::Info);
        assert_eq!(log_data.data_type, TelemetryDataType::Log);
    }

    #[test]
    fn test_trace_data_attributes() {
        let trace_data = TelemetryData::trace("test-operation")
            .with_attribute("service.name", "test-service")
            .with_numeric_attribute("duration", 100.0)
            .with_bool_attribute("success", true)
            .with_status(StatusCode::Ok, Some("success".to_string()));
        
        if let TelemetryContent::Trace(trace) = &trace_data.content {
            assert_eq!(trace.name, "test-operation");
            assert!(trace.attributes.contains_key("service.name"));
            assert!(trace.attributes.contains_key("duration"));
            assert!(trace.attributes.contains_key("success"));
            assert_eq!(trace.status.code, StatusCode::Ok);
        }
    }

    #[test]
    fn test_attribute_value_conversion() {
        let string_attr = AttributeValue::String("test".to_string());
        assert_eq!(string_attr.to_string(), "test");
        assert_eq!(string_attr.type_name(), "string");
        
        let bool_attr = AttributeValue::Bool(true);
        assert_eq!(bool_attr.to_string(), "true");
        assert_eq!(bool_attr.type_name(), "bool");
        
        let int_attr = AttributeValue::Int(42);
        assert_eq!(int_attr.to_string(), "42");
        assert_eq!(int_attr.type_name(), "int");
        
        let double_attr = AttributeValue::Double(3.14);
        assert_eq!(double_attr.to_string(), "3.14");
        assert_eq!(double_attr.type_name(), "double");
    }

    #[test]
    fn test_data_size_calculation() {
        let trace_data = TelemetryData::trace("test-operation")
            .with_attribute("key", "value");
        
        let size = trace_data.size();
        assert!(size > 0);
    }
}
