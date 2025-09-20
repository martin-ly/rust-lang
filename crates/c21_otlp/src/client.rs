//! # OTLP客户端模块
//! 
//! 提供OTLP客户端的高级接口，整合处理器、导出器和传输层，
//! 利用Rust 1.90的异步特性实现完整的OTLP功能。
#[allow(unused_imports)]
use std::sync::Arc;
use std::time::Duration;
use tokio::sync::RwLock;
use tokio::time::{
    interval, 
    //sleep,
};
//use futures::stream::{StreamExt, FuturesUnordered};
//use futures::FutureExt;
use crate::config::OtlpConfig;
use crate::data::{
    TelemetryData, 
    //TelemetryDataType,
};
use crate::error::{Result, OtlpError};
use crate::exporter::{OtlpExporter, ExportResult, ExporterMetrics};
use crate::processor::{OtlpProcessor, ProcessingConfig, ProcessorMetrics};
use crate::config::TransportProtocol;

/// OTLP客户端
pub struct OtlpClient {
    config: OtlpConfig,
    exporter: Arc<OtlpExporter>,
    processor: Arc<RwLock<Option<OtlpProcessor>>>,
    is_initialized: Arc<RwLock<bool>>,
    is_shutdown: Arc<RwLock<bool>>,
    metrics: Arc<RwLock<ClientMetrics>>,
}

/// 客户端指标
#[derive(Debug, Default, Clone)]
pub struct ClientMetrics {
    /// 总发送数据量
    pub total_data_sent: u64,
    /// 总接收数据量
    pub total_data_received: u64,
    /// 活跃连接数
    pub active_connections: usize,
    /// 客户端启动时间
    pub start_time: Option<std::time::Instant>,
    /// 运行时间
    pub uptime: Duration,
    /// 导出器指标
    pub exporter_metrics: ExporterMetrics,
    /// 处理器指标
    pub processor_metrics: ProcessorMetrics,
}

impl OtlpClient {
    /// 创建新的OTLP客户端
    pub async fn new(config: OtlpConfig) -> Result<Self> {
        // 验证配置
        config.validate()?;

        let exporter = Arc::new(OtlpExporter::new(config.clone()));

        Ok(Self {
            config,
            exporter,
            processor: Arc::new(RwLock::new(None)),
            is_initialized: Arc::new(RwLock::new(false)),
            is_shutdown: Arc::new(RwLock::new(false)),
            metrics: Arc::new(RwLock::new(ClientMetrics::default())),
        })
    }

    /// 初始化客户端
    pub async fn initialize(&self) -> Result<()> {
        let mut is_initialized = self.is_initialized.write().await;
        if *is_initialized {
            return Ok(());
        }

        // 初始化导出器
        self.exporter.initialize().await?;

        // 初始化处理器
        let processing_config = ProcessingConfig {
            batch_size: self.config.batch_config.max_export_batch_size,
            batch_timeout: self.config.batch_config.export_timeout,
            max_queue_size: self.config.batch_config.max_queue_size,
            enable_filtering: true,
            enable_aggregation: self.config.enable_metrics,
            enable_compression: self.config.is_compression_enabled(),
            worker_threads: num_cpus::get(),
        };

        let processor = OtlpProcessor::new(processing_config);
        processor.start().await?;

        let mut processor_guard = self.processor.write().await;
        *processor_guard = Some(processor);
        drop(processor_guard);

        // 更新指标
        let mut metrics = self.metrics.write().await;
        metrics.start_time = Some(std::time::Instant::now());
        metrics.uptime = Duration::ZERO;

        *is_initialized = true;

        // 启动指标更新任务
        self.start_metrics_update_task().await;

        Ok(())
    }

    /// 发送遥测数据
    pub async fn send(&self, data: TelemetryData) -> Result<ExportResult> {
        self.check_initialized().await?;
        self.check_shutdown().await?;

        // 更新指标
        self.update_send_metrics(1).await;

        // 处理数据
        if let Some(processor) = self.processor.read().await.as_ref() {
            processor.process(data.clone()).await?;
        }

        // 导出数据
        let result = self.exporter.export_single(data).await?;

        // 更新指标
        self.update_export_metrics(&result).await;

        Ok(result)
    }

    /// 批量发送遥测数据
    pub async fn send_batch(&self, data: Vec<TelemetryData>) -> Result<ExportResult> {
        if data.is_empty() {
            return Ok(ExportResult::success(0, Duration::ZERO));
        }

        self.check_initialized().await?;
        self.check_shutdown().await?;

        // 更新指标
        self.update_send_metrics(data.len()).await;

        // 处理数据
        if let Some(processor) = self.processor.read().await.as_ref() {
            for item in &data {
                processor.process(item.clone()).await?;
            }
        }

        // 导出数据
        let result = self.exporter.export(data).await?;

        // 更新指标
        self.update_export_metrics(&result).await;

        Ok(result)
    }

    /// 发送追踪数据
    pub async fn send_trace(&self, name: impl Into<String>) -> Result<TraceBuilder> {
        let data = TelemetryData::trace(name);
        Ok(TraceBuilder::new(self.clone(), data))
    }

    /// 发送指标数据
    pub async fn send_metric(&self, name: impl Into<String>, value: f64) -> Result<MetricBuilder> {
        let data = TelemetryData::metric(name, crate::data::MetricType::Gauge);
        Ok(MetricBuilder::new(self.clone(), data, value))
    }

    /// 发送日志数据
    pub async fn send_log(&self, message: impl Into<String>, severity: crate::data::LogSeverity) -> Result<LogBuilder> {
        let data = TelemetryData::log(message, severity);
        Ok(LogBuilder::new(self.clone(), data))
    }

    /// 获取客户端指标
    pub async fn get_metrics(&self) -> ClientMetrics {
        let mut metrics = self.metrics.read().await.clone();
        
        // 更新运行时间
        if let Some(start_time) = metrics.start_time {
            metrics.uptime = start_time.elapsed();
        }

        // 获取导出器指标
        metrics.exporter_metrics = self.exporter.get_metrics().await;

        // 获取处理器指标
        if let Some(processor) = self.processor.read().await.as_ref() {
            metrics.processor_metrics = processor.get_metrics().await;
        }

        metrics
    }

    /// 关闭客户端
    pub async fn shutdown(&self) -> Result<()> {
        let mut is_shutdown = self.is_shutdown.write().await;
        if *is_shutdown {
            return Ok(());
        }

        // 停止处理器
        if let Some(processor) = self.processor.read().await.as_ref() {
            processor.stop().await?;
        }

        // 关闭导出器
        self.exporter.shutdown().await?;

        *is_shutdown = true;

        Ok(())
    }

    /// 检查是否已初始化
    async fn check_initialized(&self) -> Result<()> {
        let is_initialized = self.is_initialized.read().await;
        if !*is_initialized {
            return Err(OtlpError::concurrency("Client not initialized"));
        }
        Ok(())
    }

    /// 检查是否已关闭
    async fn check_shutdown(&self) -> Result<()> {
        let is_shutdown = self.is_shutdown.read().await;
        if *is_shutdown {
            return Err(OtlpError::concurrency("Client is shutdown"));
        }
        Ok(())
    }

    /// 更新发送指标
    async fn update_send_metrics(&self, count: usize) {
        let mut metrics = self.metrics.write().await;
        metrics.total_data_sent += count as u64;
    }

    /// 更新导出指标
    async fn update_export_metrics(&self, result: &ExportResult) {
        let mut metrics = self.metrics.write().await;
        metrics.total_data_received += result.success_count as u64;
    }

    /// 启动指标更新任务
    async fn start_metrics_update_task(&self) {
        let metrics = self.metrics.clone();
        let is_shutdown = self.is_shutdown.clone();

        tokio::spawn(async move {
            let mut interval = interval(Duration::from_secs(1));

            loop {
                interval.tick().await;

                // 检查是否应该停止
                {
                    let shutdown = is_shutdown.read().await;
                    if *shutdown {
                        break;
                    }
                }

                // 更新运行时间
                {
                    let mut metrics_guard = metrics.write().await;
                    if let Some(start_time) = metrics_guard.start_time {
                        metrics_guard.uptime = start_time.elapsed();
                    }
                }
            }
        });
    }
}

impl Clone for OtlpClient {
    fn clone(&self) -> Self {
        Self {
            config: self.config.clone(),
            exporter: self.exporter.clone(),
            processor: self.processor.clone(),
            is_initialized: self.is_initialized.clone(),
            is_shutdown: self.is_shutdown.clone(),
            metrics: self.metrics.clone(),
        }
    }
}

/// 追踪构建器
pub struct TraceBuilder {
    client: OtlpClient,
    data: TelemetryData,
}

impl TraceBuilder {
    /// 创建新的追踪构建器
    pub fn new(client: OtlpClient, data: TelemetryData) -> Self {
        Self { client, data }
    }

    /// 添加属性
    pub fn with_attribute(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.data = self.data.with_attribute(key, value);
        self
    }

    /// 添加数值属性
    pub fn with_numeric_attribute(mut self, key: impl Into<String>, value: f64) -> Self {
        self.data = self.data.with_numeric_attribute(key, value);
        self
    }

    /// 添加布尔属性
    pub fn with_bool_attribute(mut self, key: impl Into<String>, value: bool) -> Self {
        self.data = self.data.with_bool_attribute(key, value);
        self
    }

    /// 设置状态
    pub fn with_status(mut self, code: crate::data::StatusCode, message: Option<String>) -> Self {
        self.data = self.data.with_status(code, message);
        self
    }

    /// 添加事件
    pub fn with_event(mut self, name: impl Into<String>, attributes: std::collections::HashMap<String, crate::data::AttributeValue>) -> Self {
        self.data = self.data.with_event(name, attributes);
        self
    }

    /// 完成并发送追踪
    pub async fn finish(self) -> Result<ExportResult> {
        let data = self.data.finish();
        self.client.send(data).await
    }
}

/// 指标构建器
pub struct MetricBuilder {
    client: OtlpClient,
    data: TelemetryData,
    value: f64,
}

impl MetricBuilder {
    /// 创建新的指标构建器
    pub fn new(client: OtlpClient, data: TelemetryData, value: f64) -> Self {
        Self { client, data, value }
    }

    /// 添加标签
    pub fn with_label(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.data = self.data.with_attribute(key, value);
        self
    }

    /// 设置描述
    pub fn with_description(mut self, description: impl Into<String>) -> Self {
        if let crate::data::TelemetryContent::Metric(ref mut metric_data) = self.data.content {
            metric_data.description = description.into();
        }
        self
    }

    /// 设置单位
    pub fn with_unit(mut self, unit: impl Into<String>) -> Self {
        if let crate::data::TelemetryContent::Metric(ref mut metric_data) = self.data.content {
            metric_data.unit = unit.into();
        }
        self
    }

    /// 发送指标
    pub async fn send(mut self) -> Result<ExportResult> {
        // 添加数据点
        if let crate::data::TelemetryContent::Metric(ref mut metric_data) = self.data.content {
            let data_point = crate::data::DataPoint {
                timestamp: crate::utils::TimeUtils::current_timestamp_nanos(),
                attributes: std::collections::HashMap::new(),
                value: crate::data::DataPointValue::Number(self.value),
            };
            metric_data.data_points.push(data_point);
        }

        self.client.send(self.data).await
    }
}

/// 日志构建器
pub struct LogBuilder {
    client: OtlpClient,
    data: TelemetryData,
}

impl LogBuilder {
    /// 创建新的日志构建器
    pub fn new(client: OtlpClient, data: TelemetryData) -> Self {
        Self { client, data }
    }

    /// 添加属性
    pub fn with_attribute(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        if let crate::data::TelemetryContent::Log(ref mut log_data) = self.data.content {
            log_data.attributes.insert(
                key.into(),
                crate::data::AttributeValue::String(value.into()),
            );
        }
        self
    }

    /// 添加数值属性
    pub fn with_numeric_attribute(mut self, key: impl Into<String>, value: f64) -> Self {
        if let crate::data::TelemetryContent::Log(ref mut log_data) = self.data.content {
            log_data.attributes.insert(
                key.into(),
                crate::data::AttributeValue::Double(value),
            );
        }
        self
    }

    /// 添加布尔属性
    pub fn with_bool_attribute(mut self, key: impl Into<String>, value: bool) -> Self {
        if let crate::data::TelemetryContent::Log(ref mut log_data) = self.data.content {
            log_data.attributes.insert(
                key.into(),
                crate::data::AttributeValue::Bool(value),
            );
        }
        self
    }

    /// 设置追踪上下文
    pub fn with_trace_context(mut self, trace_id: impl Into<String>, span_id: impl Into<String>) -> Self {
        if let crate::data::TelemetryContent::Log(ref mut log_data) = self.data.content {
            log_data.trace_id = Some(trace_id.into());
            log_data.span_id = Some(span_id.into());
        }
        self
    }

    /// 发送日志
    pub async fn send(self) -> Result<ExportResult> {
        self.client.send(self.data).await
    }
}

/// 客户端构建器
pub struct OtlpClientBuilder {
    config: OtlpConfig,
}

impl OtlpClientBuilder {
    /// 创建新的客户端构建器
    pub fn new() -> Self {
        Self {
            config: OtlpConfig::default(),
        }
    }

    /// 设置端点
    pub fn endpoint(mut self, endpoint: impl Into<String>) -> Self {
        self.config = self.config.with_endpoint(endpoint);
        self
    }

    /// 设置协议
    pub fn protocol(mut self, protocol: TransportProtocol) -> Self {
        self.config = self.config.with_protocol(protocol);
        self
    }

    /// 设置服务信息
    pub fn service(mut self, name: impl Into<String>, version: impl Into<String>) -> Self {
        self.config = self.config.with_service(name, version);
        self
    }

    /// 设置认证
    pub fn auth(mut self, api_key: impl Into<String>) -> Self {
        self.config = self.config.with_api_key(api_key);
        self
    }

    /// 设置超时
    pub fn timeout(mut self, timeout: Duration) -> Self {
        self.config = self.config.with_request_timeout(timeout);
        self
    }

    /// 构建客户端
    pub async fn build(self) -> Result<OtlpClient> {
        OtlpClient::new(self.config).await
    }
}

impl Default for OtlpClientBuilder {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::data::{
        //TelemetryData, 
        LogSeverity,
    };

    #[tokio::test]
    async fn test_client_creation() {
        let config = OtlpConfig::default();
        let client = OtlpClient::new(config).await;
        assert!(client.is_ok());
    }

    #[tokio::test]
    async fn test_client_builder() {
        let client = OtlpClientBuilder::new()
            .endpoint("http://localhost:4317")
            .protocol(TransportProtocol::Grpc)
            .service("test-service", "1.0.0")
            .timeout(Duration::from_secs(5))
            .build()
            .await;
        
        assert!(client.is_ok());
    }

    #[tokio::test]
    async fn test_trace_builder() {
        let config = OtlpConfig::default();
        let client = OtlpClient::new(config).await.unwrap();
        
        let trace_builder = client.send_trace("test-operation").await.unwrap();
        let _result = trace_builder
            .with_attribute("service.name", "test-service")
            .with_numeric_attribute("duration", 100.0)
            .with_status(crate::data::StatusCode::Ok, Some("success".to_string()))
            .finish()
            .await;
        
        // 注意：这个测试可能会失败，因为需要实际的网络连接
        // 在实际测试中，应该使用mock或测试服务器
    }

    #[tokio::test]
    async fn test_metric_builder() {
        let config = OtlpConfig::default();
        let client = OtlpClient::new(config).await.unwrap();
        
        let metric_builder = client.send_metric("test-metric", 42.0).await.unwrap();
        let _result = metric_builder
            .with_label("environment", "test")
            .with_description("Test metric")
            .with_unit("count")
            .send()
            .await;
        
        // 注意：这个测试可能会失败，因为需要实际的网络连接
    }

    #[tokio::test]
    async fn test_log_builder() {
        let config = OtlpConfig::default();
        let client = OtlpClient::new(config).await.unwrap();
        
        let log_builder = client.send_log("Test log message", LogSeverity::Info).await.unwrap();
        let _result = log_builder
            .with_attribute("logger", "test")
            .with_numeric_attribute("line", 42.0)
            .with_trace_context("trace-id", "span-id")
            .send()
            .await;
        
        // 注意：这个测试可能会失败，因为需要实际的网络连接
    }
}
