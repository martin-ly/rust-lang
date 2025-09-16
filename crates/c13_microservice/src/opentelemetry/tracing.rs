//! 分布式追踪模块

use anyhow::Result;
use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::{Arc, Mutex, RwLock};
use std::thread_local;
use std::time::{Duration, SystemTime};
use tracing::info;

use super::config::OpenTelemetryConfig;

/// 采样策略
#[derive(Debug, Clone)]
pub enum SamplingStrategy {
    Always,
    Never,
    Probability(f64),  // 0.0 - 1.0
    RateLimiting(u32), // 每秒最大采样数
}

impl SamplingStrategy {
    pub fn should_sample(&self, trace_id: &str) -> bool {
        match self {
            SamplingStrategy::Always => true,
            SamplingStrategy::Never => false,
            SamplingStrategy::Probability(prob) => {
                // 使用trace_id的哈希值来决定是否采样
                let hash = trace_id
                    .chars()
                    .fold(0u64, |acc, c| acc.wrapping_mul(31).wrapping_add(c as u64));
                (hash % 1000) < (*prob * 1000.0) as u64
            }
            SamplingStrategy::RateLimiting(_) => {
                // 简化实现，实际应该使用令牌桶算法
                true
            }
        }
    }
}

/// 追踪上下文（增强版本）
#[derive(Debug, Clone)]
pub struct TraceContext {
    pub trace_id: String,
    pub span_id: String,
    pub parent_span_id: Option<String>,
    pub baggage: HashMap<String, String>,
    pub flags: u8, // 追踪标志位
    pub sampled: bool,
    pub debug: bool,
}

/// 追踪上下文传播器
#[derive(Debug)]
pub struct TraceContextPropagator {
    #[allow(dead_code)]
    headers: HashMap<String, String>,
}

impl TraceContextPropagator {
    pub fn new() -> Self {
        Self {
            headers: HashMap::new(),
        }
    }

    /// 从HTTP头部提取追踪上下文
    pub fn extract_from_headers(
        &mut self,
        headers: &HashMap<String, String>,
    ) -> Option<TraceContext> {
        let trace_id = headers.get("x-trace-id")?.clone();
        let span_id = headers.get("x-span-id")?.clone();
        let parent_span_id = headers.get("x-parent-span-id").cloned();
        let flags = headers
            .get("x-trace-flags")
            .and_then(|f| f.parse::<u8>().ok())
            .unwrap_or(0);

        let mut baggage = HashMap::new();
        for (key, value) in headers {
            if key.starts_with("x-baggage-") {
                let baggage_key = key.strip_prefix("x-baggage-")?.to_string();
                baggage.insert(baggage_key, value.clone());
            }
        }

        Some(TraceContext {
            trace_id,
            span_id,
            parent_span_id,
            baggage,
            flags,
            sampled: (flags & 1) != 0,
            debug: (flags & 2) != 0,
        })
    }

    /// 将追踪上下文注入到HTTP头部
    pub fn inject_to_headers(&self, context: &TraceContext) -> HashMap<String, String> {
        let mut headers = HashMap::new();
        headers.insert("x-trace-id".to_string(), context.trace_id.clone());
        headers.insert("x-span-id".to_string(), context.span_id.clone());

        if let Some(parent_span_id) = &context.parent_span_id {
            headers.insert("x-parent-span-id".to_string(), parent_span_id.clone());
        }

        headers.insert("x-trace-flags".to_string(), context.flags.to_string());

        for (key, value) in &context.baggage {
            headers.insert(format!("x-baggage-{}", key), value.clone());
        }

        headers
    }
}

// 线程本地追踪上下文存储
thread_local! {
    static CURRENT_CONTEXT: RefCell<Option<TraceContext>> = RefCell::new(None);
}

/// 追踪上下文管理器
#[derive(Debug)]
pub struct TraceContextManager;

impl TraceContextManager {
    /// 设置当前线程的追踪上下文
    pub fn set_current_context(context: TraceContext) {
        CURRENT_CONTEXT.with(|ctx| {
            *ctx.borrow_mut() = Some(context);
        });
    }

    /// 获取当前线程的追踪上下文
    pub fn get_current_context() -> Option<TraceContext> {
        CURRENT_CONTEXT.with(|ctx| ctx.borrow().clone())
    }

    /// 清除当前线程的追踪上下文
    pub fn clear_current_context() {
        CURRENT_CONTEXT.with(|ctx| {
            *ctx.borrow_mut() = None;
        });
    }

    /// 在当前上下文中执行函数
    pub fn with_context<F, R>(context: TraceContext, f: F) -> R
    where
        F: FnOnce() -> R,
    {
        let old_context = Self::get_current_context();
        Self::set_current_context(context);
        let result = f();
        if let Some(old) = old_context {
            Self::set_current_context(old);
        } else {
            Self::clear_current_context();
        }
        result
    }
}

impl TraceContext {
    pub fn new() -> Self {
        Self {
            trace_id: generate_id(),
            span_id: generate_id(),
            parent_span_id: None,
            baggage: HashMap::new(),
            flags: 1, // 默认采样
            sampled: true,
            debug: false,
        }
    }

    pub fn with_parent(parent: &TraceContext) -> Self {
        Self {
            trace_id: parent.trace_id.clone(),
            span_id: generate_id(),
            parent_span_id: Some(parent.span_id.clone()),
            baggage: parent.baggage.clone(),
            flags: parent.flags,
            sampled: parent.sampled,
            debug: parent.debug,
        }
    }

    pub fn add_baggage(&mut self, key: String, value: String) {
        self.baggage.insert(key, value);
    }

    pub fn get_baggage(&self, key: &str) -> Option<&String> {
        self.baggage.get(key)
    }

    pub fn set_sampled(&mut self, sampled: bool) {
        self.sampled = sampled;
        if sampled {
            self.flags |= 1;
        } else {
            self.flags &= !1;
        }
    }

    pub fn set_debug(&mut self, debug: bool) {
        self.debug = debug;
        if debug {
            self.flags |= 2;
        } else {
            self.flags &= !2;
        }
    }

    pub fn is_sampled(&self) -> bool {
        self.sampled
    }

    pub fn is_debug(&self) -> bool {
        self.debug
    }
}

/// 跨度（Span）
#[derive(Debug, Clone)]
pub struct Span {
    pub context: TraceContext,
    pub name: String,
    pub start_time: SystemTime,
    pub end_time: Option<SystemTime>,
    pub attributes: HashMap<String, String>,
    pub events: Vec<SpanEvent>,
    pub status: SpanStatus,
}

#[derive(Debug, Clone)]
pub struct SpanEvent {
    pub name: String,
    pub timestamp: SystemTime,
    pub attributes: HashMap<String, String>,
}

#[derive(Debug, Clone)]
pub enum SpanStatus {
    Ok,
    Error(String),
}

impl Span {
    pub fn new(name: String, context: TraceContext) -> Self {
        Self {
            context,
            name,
            start_time: SystemTime::now(),
            end_time: None,
            attributes: HashMap::new(),
            events: Vec::new(),
            status: SpanStatus::Ok,
        }
    }

    pub fn add_attribute(&mut self, key: String, value: String) {
        self.attributes.insert(key, value);
    }

    pub fn add_event(&mut self, name: String, attributes: HashMap<String, String>) {
        self.events.push(SpanEvent {
            name,
            timestamp: SystemTime::now(),
            attributes,
        });
    }

    pub fn set_status(&mut self, status: SpanStatus) {
        self.status = status;
    }

    pub fn finish(&mut self) {
        self.end_time = Some(SystemTime::now());
        let duration = self
            .end_time
            .unwrap()
            .duration_since(self.start_time)
            .unwrap();
        info!("Span '{}' finished in {:?}", self.name, duration);
    }

    pub fn duration(&self) -> Option<Duration> {
        self.end_time?.duration_since(self.start_time).ok()
    }
}

/// 追踪器（增强版本）
#[derive(Debug)]
pub struct Tracer {
    #[allow(dead_code)]
    config: OpenTelemetryConfig,
    spans: Arc<RwLock<HashMap<String, Span>>>,
    active_spans: Arc<RwLock<HashMap<String, String>>>, // span_id -> trace_id
    span_counter: Arc<Mutex<u64>>,
    sampling_strategy: SamplingStrategy,
    propagator: TraceContextPropagator,
}

impl Tracer {
    pub fn new(config: OpenTelemetryConfig) -> Self {
        let sampling_strategy = SamplingStrategy::Probability(config.sampling_ratio);
        Self {
            config,
            spans: Arc::new(RwLock::new(HashMap::new())),
            active_spans: Arc::new(RwLock::new(HashMap::new())),
            span_counter: Arc::new(Mutex::new(0)),
            sampling_strategy,
            propagator: TraceContextPropagator::new(),
        }
    }

    /// 设置采样策略
    pub fn set_sampling_strategy(&mut self, strategy: SamplingStrategy) {
        self.sampling_strategy = strategy;
    }

    /// 从HTTP头部提取追踪上下文
    pub fn extract_context_from_headers(
        &self,
        headers: &HashMap<String, String>,
    ) -> Option<TraceContext> {
        let mut propagator = TraceContextPropagator::new();
        propagator.extract_from_headers(headers)
    }

    /// 将追踪上下文注入到HTTP头部
    pub fn inject_context_to_headers(&self, context: &TraceContext) -> HashMap<String, String> {
        self.propagator.inject_to_headers(context)
    }

    /// 创建根span
    pub fn start_root_span(&self, name: String) -> Option<Span> {
        let context = TraceContext::new();

        // 应用采样策略
        if !self.sampling_strategy.should_sample(&context.trace_id) {
            return None;
        }

        let mut span = Span::new(name, context);

        // 增加span计数器
        if let Ok(mut counter) = self.span_counter.lock() {
            *counter += 1;
            span.add_attribute("span.sequence".to_string(), counter.to_string());
        }

        // 记录活跃span
        if let Ok(mut active_spans) = self.active_spans.write() {
            active_spans.insert(span.context.span_id.clone(), span.context.trace_id.clone());
        }

        // 存储span
        if let Ok(mut spans) = self.spans.write() {
            spans.insert(span.context.span_id.clone(), span.clone());
        }

        // 设置当前线程的追踪上下文
        TraceContextManager::set_current_context(span.context.clone());

        info!(
            "Started root span: {} (trace_id: {}, span_id: {})",
            span.name, span.context.trace_id, span.context.span_id
        );
        Some(span)
    }

    pub fn start_span(&self, name: String) -> Option<Span> {
        // 尝试从当前上下文获取父span
        let parent_context = TraceContextManager::get_current_context();
        let context = if let Some(parent) = parent_context {
            TraceContext::with_parent(&parent)
        } else {
            TraceContext::new()
        };

        // 应用采样策略
        if !self.sampling_strategy.should_sample(&context.trace_id) {
            return None;
        }

        let mut span = Span::new(name, context);

        // 增加span计数器
        if let Ok(mut counter) = self.span_counter.lock() {
            *counter += 1;
            span.add_attribute("span.sequence".to_string(), counter.to_string());
        }

        // 记录活跃span
        if let Ok(mut active_spans) = self.active_spans.write() {
            active_spans.insert(span.context.span_id.clone(), span.context.trace_id.clone());
        }

        // 存储span
        if let Ok(mut spans) = self.spans.write() {
            spans.insert(span.context.span_id.clone(), span.clone());
        }

        // 设置当前线程的追踪上下文
        TraceContextManager::set_current_context(span.context.clone());

        info!(
            "Started span: {} (trace_id: {}, span_id: {})",
            span.name, span.context.trace_id, span.context.span_id
        );
        Some(span)
    }

    pub fn start_child_span(&self, name: String, parent: &TraceContext) -> Span {
        let context = TraceContext::with_parent(parent);
        let mut span = Span::new(name, context);

        // 增加span计数器
        if let Ok(mut counter) = self.span_counter.lock() {
            *counter += 1;
            span.add_attribute("span.sequence".to_string(), counter.to_string());
        }

        // 记录活跃span
        if let Ok(mut active_spans) = self.active_spans.write() {
            active_spans.insert(span.context.span_id.clone(), span.context.trace_id.clone());
        }

        // 存储span
        if let Ok(mut spans) = self.spans.write() {
            spans.insert(span.context.span_id.clone(), span.clone());
        }

        info!(
            "Started child span: {} (trace_id: {}, span_id: {}, parent: {})",
            span.name, span.context.trace_id, span.context.span_id, parent.span_id
        );
        span
    }

    pub fn finish_span(&self, mut span: Span) {
        span.finish();

        // 从活跃span中移除
        if let Ok(mut active_spans) = self.active_spans.write() {
            active_spans.remove(&span.context.span_id);
        }

        // 更新存储的span
        if let Ok(mut spans) = self.spans.write() {
            spans.insert(span.context.span_id.clone(), span.clone());
        }

        // 清除当前线程的追踪上下文
        TraceContextManager::clear_current_context();

        info!(
            "Finished span: {} with status: {:?} (duration: {:?})",
            span.name,
            span.status,
            span.duration().unwrap_or_default()
        );
    }

    /// 获取活跃span数量
    pub fn get_active_span_count(&self) -> usize {
        if let Ok(active_spans) = self.active_spans.read() {
            active_spans.len()
        } else {
            0
        }
    }

    /// 获取总span数量
    pub fn get_total_span_count(&self) -> usize {
        if let Ok(spans) = self.spans.read() {
            spans.len()
        } else {
            0
        }
    }

    /// 获取指定trace的所有span
    pub fn get_trace_spans(&self, trace_id: &str) -> Vec<Span> {
        if let Ok(spans) = self.spans.read() {
            spans
                .values()
                .filter(|span| span.context.trace_id == trace_id)
                .cloned()
                .collect()
        } else {
            Vec::new()
        }
    }

    /// 导出追踪数据
    pub fn export_traces(&self) -> Result<String, Box<dyn std::error::Error>> {
        if let Ok(spans) = self.spans.read() {
            let mut traces: HashMap<String, Vec<serde_json::Value>> = HashMap::new();

            for span in spans.values() {
                let span_json = serde_json::json!({
                    "span_id": span.context.span_id,
                    "trace_id": span.context.trace_id,
                    "parent_span_id": span.context.parent_span_id,
                    "name": span.name,
                    "start_time": span.start_time.duration_since(std::time::UNIX_EPOCH)?.as_millis(),
                    "end_time": span.end_time.map(|t| t.duration_since(std::time::UNIX_EPOCH).unwrap().as_millis()),
                    "attributes": span.attributes,
                    "status": format!("{:?}", span.status)
                });

                traces
                    .entry(span.context.trace_id.clone())
                    .or_insert_with(Vec::new)
                    .push(span_json);
            }

            Ok(serde_json::to_string_pretty(&traces)?)
        } else {
            Ok("{}".to_string())
        }
    }

    /// 清理旧的span数据
    pub fn cleanup_old_spans(
        &self,
        max_age: Duration,
    ) -> Result<usize, Box<dyn std::error::Error>> {
        let cutoff_time = SystemTime::now() - max_age;
        let mut removed_count = 0;

        if let Ok(mut spans) = self.spans.write() {
            let keys_to_remove: Vec<String> = spans
                .iter()
                .filter(|(_, span)| span.start_time < cutoff_time)
                .map(|(key, _)| key.clone())
                .collect();

            for key in keys_to_remove {
                spans.remove(&key);
                removed_count += 1;
            }
        }

        info!("Cleaned up {} old spans", removed_count);
        Ok(removed_count)
    }
}

/// 初始化OpenTelemetry追踪
pub fn init_tracing(config: OpenTelemetryConfig) -> Result<()> {
    if config.tracing_enabled {
        info!(
            "Initializing OpenTelemetry tracing with Jaeger endpoint: {}",
            config.jaeger_endpoint
        );
    }
    info!("OpenTelemetry tracing initialized successfully");
    Ok(())
}

/// 生成唯一ID
fn generate_id() -> String {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    let mut hasher = DefaultHasher::new();
    SystemTime::now().hash(&mut hasher);
    format!("{:x}", hasher.finish())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_trace_context() {
        let context = TraceContext::new();
        assert!(!context.trace_id.is_empty());
        assert!(!context.span_id.is_empty());
        assert!(context.parent_span_id.is_none());

        let child_context = TraceContext::with_parent(&context);
        assert_eq!(child_context.trace_id, context.trace_id);
        assert_ne!(child_context.span_id, context.span_id);
        assert_eq!(child_context.parent_span_id, Some(context.span_id));
    }

    #[test]
    fn test_span_operations() {
        let context = TraceContext::new();
        let mut span = Span::new("test_span".to_string(), context);

        span.add_attribute("key".to_string(), "value".to_string());
        span.add_event("test_event".to_string(), HashMap::new());
        span.set_status(SpanStatus::Ok);
        span.finish();

        assert_eq!(span.name, "test_span");
        assert!(span.end_time.is_some());
        assert!(span.duration().is_some());
    }

    #[test]
    fn test_tracer() {
        let config = OpenTelemetryConfig::default();
        let tracer = Tracer::new(config);

        if let Some(span) = tracer.start_span("test_span".to_string()) {
            assert_eq!(span.name, "test_span");
            tracer.finish_span(span);
        }
    }
}
