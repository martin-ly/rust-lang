//! # 分布式追踪（Distributed Tracing）
//!
//! 提供调用链追踪和性能分析功能，兼容OpenTelemetry。

use crate::prelude::*;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, Instant, SystemTime};
use tokio::sync::RwLock;

/// Trace ID
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct TraceId(pub String);

/// Span ID
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct SpanId(pub String);

/// Span状态
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum SpanStatus {
    /// 未设置
    Unset,
    /// 正常
    Ok,
    /// 错误
    Error,
}

/// Span类型
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum SpanKind {
    /// 内部Span
    Internal,
    /// 服务端Span
    Server,
    /// 客户端Span
    Client,
    /// 生产者Span
    Producer,
    /// 消费者Span
    Consumer,
}

/// Span属性
pub type SpanAttributes = HashMap<String, String>;

/// Span事件
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SpanEvent {
    pub name: String,
    pub timestamp: SystemTime,
    pub attributes: SpanAttributes,
}

/// Span上下文
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SpanContext {
    pub trace_id: TraceId,
    pub span_id: SpanId,
    pub parent_span_id: Option<SpanId>,
    pub trace_flags: u8,
    pub trace_state: String,
}

/// Span
#[derive(Debug, Clone)]
pub struct Span {
    pub context: SpanContext,
    pub operation_name: String,
    pub kind: SpanKind,
    pub start_time: Instant,
    pub end_time: Option<Instant>,
    pub status: SpanStatus,
    pub attributes: SpanAttributes,
    pub events: Vec<SpanEvent>,
    pub links: Vec<SpanContext>,
}

impl Span {
    pub fn new(operation_name: String, context: SpanContext, kind: SpanKind) -> Self {
        Self {
            context,
            operation_name,
            kind,
            start_time: Instant::now(),
            end_time: None,
            status: SpanStatus::Unset,
            attributes: HashMap::new(),
            events: Vec::new(),
            links: Vec::new(),
        }
    }

    /// 设置属性
    pub fn set_attribute(&mut self, key: String, value: String) {
        self.attributes.insert(key, value);
    }

    /// 添加事件
    pub fn add_event(&mut self, name: String, attributes: SpanAttributes) {
        self.events.push(SpanEvent {
            name,
            timestamp: SystemTime::now(),
            attributes,
        });
    }

    /// 设置状态
    pub fn set_status(&mut self, status: SpanStatus) {
        self.status = status;
    }

    /// 添加链接
    pub fn add_link(&mut self, context: SpanContext) {
        self.links.push(context);
    }

    /// 结束Span
    pub fn finish(&mut self) {
        self.end_time = Some(Instant::now());
    }

    /// 获取持续时间
    pub fn duration(&self) -> Option<Duration> {
        self.end_time.map(|end| end - self.start_time)
    }
}

/// 追踪配置
#[derive(Debug, Clone)]
pub struct TracingConfig {
    pub service_name: String,
    pub service_version: String,
    pub sampling_rate: f64,
    pub max_attributes_per_span: usize,
    pub max_events_per_span: usize,
    pub max_links_per_span: usize,
}

impl Default for TracingConfig {
    fn default() -> Self {
        Self {
            service_name: "unnamed-service".to_string(),
            service_version: "0.1.0".to_string(),
            sampling_rate: 1.0,
            max_attributes_per_span: 128,
            max_events_per_span: 128,
            max_links_per_span: 128,
        }
    }
}

/// 采样决策
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SamplingDecision {
    /// 不记录
    Drop,
    /// 记录但不采样
    RecordOnly,
    /// 记录并采样
    RecordAndSample,
}

/// 采样器trait
#[async_trait::async_trait]
pub trait Sampler: Send + Sync {
    async fn should_sample(&self, context: &SpanContext) -> SamplingDecision;
}

/// 始终采样
pub struct AlwaysOnSampler;

#[async_trait::async_trait]
impl Sampler for AlwaysOnSampler {
    async fn should_sample(&self, _context: &SpanContext) -> SamplingDecision {
        SamplingDecision::RecordAndSample
    }
}

/// 始终不采样
pub struct AlwaysOffSampler;

#[async_trait::async_trait]
impl Sampler for AlwaysOffSampler {
    async fn should_sample(&self, _context: &SpanContext) -> SamplingDecision {
        SamplingDecision::Drop
    }
}

/// 比率采样
pub struct RatioSampler {
    ratio: f64,
}

impl RatioSampler {
    pub fn new(ratio: f64) -> Self {
        Self {
            ratio: ratio.clamp(0.0, 1.0),
        }
    }
}

#[async_trait::async_trait]
impl Sampler for RatioSampler {
    async fn should_sample(&self, context: &SpanContext) -> SamplingDecision {
        // 使用trace_id的哈希值来决定是否采样
        let hash = context.trace_id.0.bytes().map(|b| b as u64).sum::<u64>();
        let threshold = (self.ratio * u64::MAX as f64) as u64;

        if hash < threshold {
            SamplingDecision::RecordAndSample
        } else {
            SamplingDecision::Drop
        }
    }
}

/// Span导出器trait
#[async_trait::async_trait]
pub trait SpanExporter: Send + Sync {
    async fn export(&self, spans: Vec<Span>) -> Result<()>;
    async fn shutdown(&self) -> Result<()>;
}

/// 控制台导出器（用于调试）
pub struct ConsoleExporter;

#[async_trait::async_trait]
impl SpanExporter for ConsoleExporter {
    async fn export(&self, spans: Vec<Span>) -> Result<()> {
        for span in spans {
            println!(
                "[TRACE] {} ({:?}) - {:?}",
                span.operation_name,
                span.kind,
                span.duration()
            );
        }
        Ok(())
    }

    async fn shutdown(&self) -> Result<()> {
        Ok(())
    }
}

/// 追踪提供者
#[async_trait::async_trait]
pub trait TracingProvider: Send + Sync {
    async fn start_span(&self, operation_name: &str, kind: SpanKind) -> Span;
    async fn start_child_span(&self, operation_name: &str, parent: &SpanContext) -> Span;
    async fn finish_span(&self, span: Span);
}

/// 追踪器
pub struct Tracer {
    config: TracingConfig,
    sampler: Arc<dyn Sampler>,
    exporter: Arc<dyn SpanExporter>,
    active_spans: Arc<RwLock<HashMap<SpanId, Span>>>,
    completed_spans: Arc<RwLock<Vec<Span>>>,
}

impl Tracer {
    pub fn new(
        config: TracingConfig,
        sampler: Arc<dyn Sampler>,
        exporter: Arc<dyn SpanExporter>,
    ) -> Self {
        Self {
            config,
            sampler,
            exporter,
            active_spans: Arc::new(RwLock::new(HashMap::new())),
            completed_spans: Arc::new(RwLock::new(Vec::new())),
        }
    }

    /// 创建默认追踪器
    pub fn default_tracer(service_name: String) -> Self {
        let config = TracingConfig {
            service_name,
            ..Default::default()
        };
        Self::new(
            config,
            Arc::new(AlwaysOnSampler),
            Arc::new(ConsoleExporter),
        )
    }

    /// 导出已完成的spans
    pub async fn flush(&self) -> Result<()> {
        let mut completed = self.completed_spans.write().await;
        if !completed.is_empty() {
            let spans = completed.drain(..).collect();
            self.exporter.export(spans).await?;
        }
        Ok(())
    }

    /// 获取活跃span数量
    pub async fn active_span_count(&self) -> usize {
        self.active_spans.read().await.len()
    }

    /// 获取完成span数量
    pub async fn completed_span_count(&self) -> usize {
        self.completed_spans.read().await.len()
    }
}

#[async_trait::async_trait]
impl TracingProvider for Tracer {
    async fn start_span(&self, operation_name: &str, kind: SpanKind) -> Span {
        let context = SpanContext {
            trace_id: TraceId(uuid::Uuid::new_v4().to_string()),
            span_id: SpanId(uuid::Uuid::new_v4().to_string()),
            parent_span_id: None,
            trace_flags: 1, // 采样标志
            trace_state: String::new(),
        };

        let mut span = Span::new(operation_name.to_string(), context.clone(), kind);
        span.set_attribute("service.name".to_string(), self.config.service_name.clone());
        span.set_attribute(
            "service.version".to_string(),
            self.config.service_version.clone(),
        );

        // 添加到活跃spans
        self.active_spans
            .write()
            .await
            .insert(context.span_id.clone(), span.clone());

        span
    }

    async fn start_child_span(&self, operation_name: &str, parent: &SpanContext) -> Span {
        let context = SpanContext {
            trace_id: parent.trace_id.clone(),
            span_id: SpanId(uuid::Uuid::new_v4().to_string()),
            parent_span_id: Some(parent.span_id.clone()),
            trace_flags: parent.trace_flags,
            trace_state: parent.trace_state.clone(),
        };

        let mut span = Span::new(operation_name.to_string(), context.clone(), SpanKind::Internal);
        span.set_attribute("service.name".to_string(), self.config.service_name.clone());

        self.active_spans
            .write()
            .await
            .insert(context.span_id.clone(), span.clone());

        span
    }

    async fn finish_span(&self, mut span: Span) {
        span.finish();

        // 从活跃spans移除
        self.active_spans
            .write()
            .await
            .remove(&span.context.span_id);

        // 检查是否应该采样
        let decision = self.sampler.should_sample(&span.context).await;
        if decision != SamplingDecision::Drop {
            self.completed_spans.write().await.push(span);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_span_lifecycle() {
        let context = SpanContext {
            trace_id: TraceId("test-trace".to_string()),
            span_id: SpanId("test-span".to_string()),
            parent_span_id: None,
            trace_flags: 1,
            trace_state: String::new(),
        };

        let mut span = Span::new("test-operation".to_string(), context, SpanKind::Internal);
        span.set_attribute("key".to_string(), "value".to_string());
        span.add_event("event".to_string(), HashMap::new());
        span.set_status(SpanStatus::Ok);
        span.finish();

        assert!(span.end_time.is_some());
        assert!(span.duration().is_some());
        assert_eq!(span.attributes.get("key"), Some(&"value".to_string()));
        assert_eq!(span.events.len(), 1);
    }

    #[tokio::test]
    async fn test_tracer() {
        let tracer = Tracer::default_tracer("test-service".to_string());

        let span = tracer
            .start_span("test-operation", SpanKind::Server)
            .await;
        assert_eq!(tracer.active_span_count().await, 1);

        tracer.finish_span(span).await;
        assert_eq!(tracer.active_span_count().await, 0);
        assert_eq!(tracer.completed_span_count().await, 1);
    }

    #[tokio::test]
    async fn test_child_span() {
        let tracer = Tracer::default_tracer("test-service".to_string());

        let parent = tracer.start_span("parent", SpanKind::Server).await;
        let child = tracer
            .start_child_span("child", &parent.context)
            .await;

        assert_eq!(child.context.trace_id, parent.context.trace_id);
        assert_eq!(
            child.context.parent_span_id,
            Some(parent.context.span_id.clone())
        );

        tracer.finish_span(child).await;
        tracer.finish_span(parent).await;
    }

    #[tokio::test]
    async fn test_ratio_sampler() {
        let sampler = RatioSampler::new(0.5);
        let context = SpanContext {
            trace_id: TraceId("test".to_string()),
            span_id: SpanId("span".to_string()),
            parent_span_id: None,
            trace_flags: 1,
            trace_state: String::new(),
        };

        let decision = sampler.should_sample(&context).await;
        assert!(matches!(
            decision,
            SamplingDecision::RecordAndSample | SamplingDecision::Drop
        ));
    }
}
