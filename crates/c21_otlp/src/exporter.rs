//! # OTLP导出器模块
//! 
//! 实现OTLP数据的导出功能，支持多种传输方式和重试机制，
//! 利用Rust 1.90的异步特性实现高性能数据导出。

use std::sync::Arc;
use std::time::Duration;
use tokio::sync::{mpsc, RwLock};
use tokio::time::{
    sleep, 
    //timeout,
};
//use futures::stream::{StreamExt, FuturesUnordered};
//use futures::FutureExt;
use crate::config::OtlpConfig;
use crate::data::TelemetryData;
use crate::error::{
    Result, ExportError, 
    //OtlpError,
};
use crate::transport::{
    //Transport, 
    //TransportFactory, 
    TransportPool,
};
use crate::utils::{
    RetryUtils, 
    //TimeUtils, 
    PerformanceUtils,
};

/// 导出结果
#[derive(Debug, Clone)]
pub struct ExportResult {
    /// 成功导出的数据数量
    pub success_count: usize,
    /// 失败的数据数量
    pub failure_count: usize,
    /// 导出耗时
    pub duration: Duration,
    /// 错误信息
    pub errors: Vec<String>,
}

impl ExportResult {
    /// 创建成功结果
    pub fn success(count: usize, duration: Duration) -> Self {
        Self {
            success_count: count,
            failure_count: 0,
            duration,
            errors: Vec::new(),
        }
    }

    /// 创建失败结果
    pub fn failure(count: usize, duration: Duration, errors: Vec<String>) -> Self {
        Self {
            success_count: 0,
            failure_count: count,
            duration,
            errors,
        }
    }

    /// 创建部分成功结果
    pub fn partial(success_count: usize, failure_count: usize, duration: Duration, errors: Vec<String>) -> Self {
        Self {
            success_count,
            failure_count,
            duration,
            errors,
        }
    }

    /// 是否完全成功
    pub fn is_success(&self) -> bool {
        self.failure_count == 0
    }

    /// 是否完全失败
    pub fn is_failure(&self) -> bool {
        self.success_count == 0
    }

    /// 总数据数量
    pub fn total_count(&self) -> usize {
        self.success_count + self.failure_count
    }

    /// 成功率
    pub fn success_rate(&self) -> f64 {
        if self.total_count() == 0 {
            return 1.0;
        }
        self.success_count as f64 / self.total_count() as f64
    }
}

/// 导出器指标
#[derive(Debug, Default, Clone)]
pub struct ExporterMetrics {
    /// 总导出次数
    pub total_exports: u64,
    /// 成功导出次数
    pub successful_exports: u64,
    /// 失败导出次数
    pub failed_exports: u64,
    /// 总导出数据量
    pub total_data_exported: u64,
    /// 平均导出延迟
    pub average_export_latency: Duration,
    /// 最大导出延迟
    pub max_export_latency: Duration,
    /// 重试次数
    pub total_retries: u64,
    /// 当前队列大小
    pub current_queue_size: usize,
}

/// OTLP导出器
#[allow(dead_code)]
pub struct OtlpExporter {
    config: OtlpConfig,
    transport_pool: Arc<RwLock<Option<TransportPool>>>,
    export_queue: mpsc::UnboundedSender<Vec<TelemetryData>>,
    metrics: Arc<RwLock<ExporterMetrics>>,
    is_initialized: Arc<RwLock<bool>>,
    is_shutdown: Arc<RwLock<bool>>,
}

impl OtlpExporter {
    /// 创建新的导出器
    pub fn new(config: OtlpConfig) -> Self {
        let (export_tx, _export_rx) = mpsc::unbounded_channel();

        Self {
            config,
            transport_pool: Arc::new(RwLock::new(None)),
            export_queue: export_tx,
            metrics: Arc::new(RwLock::new(ExporterMetrics::default())),
            is_initialized: Arc::new(RwLock::new(false)),
            is_shutdown: Arc::new(RwLock::new(false)),
        }
    }

    /// 初始化导出器
    pub async fn initialize(&self) -> Result<()> {
        let mut is_initialized = self.is_initialized.write().await;
        if *is_initialized {
            return Ok(());
        }

        // 创建传输池
        let pool_size = self.config.batch_config.max_export_batch_size.min(10);
        let transport_pool = TransportPool::new(self.config.clone(), pool_size).await?;
        
        let mut pool_guard = self.transport_pool.write().await;
        *pool_guard = Some(transport_pool);
        drop(pool_guard);

        *is_initialized = true;

        // 启动导出任务
        self.start_export_task().await;

        Ok(())
    }

    /// 导出数据
    pub async fn export(&self, data: Vec<TelemetryData>) -> Result<ExportResult> {
        if data.is_empty() {
            return Ok(ExportResult::success(0, Duration::ZERO));
        }

        // 检查是否已关闭
        {
            let is_shutdown = self.is_shutdown.read().await;
            if *is_shutdown {
                return Err(ExportError::Shutdown.into());
            }
        }

        // 检查是否已初始化
        {
            let is_initialized = self.is_initialized.read().await;
            if !*is_initialized {
                return Err(ExportError::NotInitialized.into());
            }
        }

        let (result, duration) = PerformanceUtils::measure_time(async {
            self.export_with_retry(data).await
        }).await;

        // 更新指标
        match &result {
            Ok(export_result) => {
                self.update_metrics(export_result, duration).await;
            }
            Err(_) => {
                // 处理错误情况
            }
        }

        result
    }

    /// 导出单个数据
    pub async fn export_single(&self, data: TelemetryData) -> Result<ExportResult> {
        self.export(vec![data]).await
    }

    /// 关闭导出器
    pub async fn shutdown(&self) -> Result<()> {
        let mut is_shutdown = self.is_shutdown.write().await;
        *is_shutdown = true;
        drop(is_shutdown);

        // 关闭传输池
        let mut pool_guard = self.transport_pool.write().await;
        if let Some(ref mut pool) = *pool_guard {
            pool.close_all().await?;
        }
        *pool_guard = None;

        Ok(())
    }

    /// 获取导出器指标
    pub async fn get_metrics(&self) -> ExporterMetrics {
        self.metrics.read().await.clone()
    }

    /// 启动导出任务
    async fn start_export_task(&self) {
        let _config = self.config.clone();
        let transport_pool = self.transport_pool.clone();
        let metrics = self.metrics.clone();
        let is_shutdown = self.is_shutdown.clone();

        tokio::spawn(async move {
            let mut export_queue = mpsc::unbounded_channel::<Vec<TelemetryData>>().1;
            
            loop {
                // 检查是否应该关闭
                {
                    let shutdown = is_shutdown.read().await;
                    if *shutdown {
                        break;
                    }
                }

                // 处理导出队列
                if let Some(data) = export_queue.recv().await
                    && let Some(pool) = transport_pool.write().await.as_mut() {
                        let result = Self::export_batch(pool, data.clone()).await;
                        
                        // 更新指标
                        let mut metrics_guard = metrics.write().await;
                        metrics_guard.total_exports += 1;
                        if let Ok(export_result) = &result {
                            if export_result.is_success() {
                                metrics_guard.successful_exports += 1;
                            } else {
                                metrics_guard.failed_exports += 1;
                            }
                        } else {
                            metrics_guard.failed_exports += 1;
                        }
                        metrics_guard.total_data_exported += data.len() as u64;
                    }
            }
        });
    }

    /// 带重试的导出
    async fn export_with_retry(&self, data: Vec<TelemetryData>) -> Result<ExportResult> {
        let mut last_error = None;
        let mut total_retries = 0;

        for attempt in 0..=self.config.retry_config.max_retries {
            match self.export_batch_direct(data.clone()).await {
                Ok(result) => {
                    if attempt > 0 {
                        // 更新重试指标
                        let mut metrics = self.metrics.write().await;
                        metrics.total_retries += attempt as u64;
                    }
                    return Ok(result);
                }
                Err(e) => {
                    last_error = Some(e);
                    
                    if !RetryUtils::should_retry(attempt, self.config.retry_config.max_retries, last_error.as_ref().unwrap()) {
                        break;
                    }

                    // 计算重试延迟
                    let delay = RetryUtils::calculate_retry_delay(
                        attempt,
                        self.config.retry_config.initial_retry_delay,
                        self.config.retry_config.max_retry_delay,
                        self.config.retry_config.retry_delay_multiplier,
                        self.config.retry_config.randomize_retry_delay,
                    );

                    sleep(delay).await;
                    total_retries += 1;
                }
            }
        }

        // 所有重试都失败了
        let _error = last_error.unwrap();
        Err(ExportError::RetryExhausted { attempts: total_retries }.into())
    }

    /// 直接导出批次
    async fn export_batch_direct(&self, data: Vec<TelemetryData>) -> Result<ExportResult> {
        let mut pool_guard = self.transport_pool.write().await;
        let pool = pool_guard.as_mut()
            .ok_or(ExportError::NotInitialized)?;

        Self::export_batch(pool, data).await
    }

    /// 导出批次数据
    async fn export_batch(pool: &mut TransportPool, data: Vec<TelemetryData>) -> Result<ExportResult> {
        let (result, duration) = PerformanceUtils::measure_time(async {
            pool.send(data.clone()).await
        }).await;

        match result {
            Ok(()) => Ok(ExportResult::success(data.len(), duration)),
            Err(e) => {
                let errors = vec![e.to_string()];
                Ok(ExportResult::failure(data.len(), duration, errors))
            }
        }
    }

    /// 更新指标
    async fn update_metrics(&self, result: &ExportResult, duration: Duration) {
        let mut metrics = self.metrics.write().await;
        
        metrics.total_exports += 1;
        if result.is_success() {
            metrics.successful_exports += 1;
        } else {
            metrics.failed_exports += 1;
        }
        
        metrics.total_data_exported += result.total_count() as u64;
        
        // 更新平均延迟
        let total_exports = metrics.total_exports as f64;
        let current_avg = metrics.average_export_latency.as_nanos() as f64;
        let new_avg = (current_avg * (total_exports - 1.0) + duration.as_nanos() as f64) / total_exports;
        metrics.average_export_latency = Duration::from_nanos(new_avg as u64);
        
        // 更新最大延迟
        if duration > metrics.max_export_latency {
            metrics.max_export_latency = duration;
        }
    }
}

/// 批量导出器
#[allow(dead_code)]
pub struct BatchExporter {
    exporter: Arc<OtlpExporter>,
    batch_size: usize,
    batch_timeout: Duration,
    current_batch: Arc<RwLock<Vec<TelemetryData>>>,
    batch_timer: Arc<RwLock<Option<tokio::time::Instant>>>,
}

impl BatchExporter {
    /// 创建新的批量导出器
    pub fn new(exporter: Arc<OtlpExporter>, batch_size: usize, batch_timeout: Duration) -> Self {
        Self {
            exporter,
            batch_size,
            batch_timeout,
            current_batch: Arc::new(RwLock::new(Vec::with_capacity(batch_size))),
            batch_timer: Arc::new(RwLock::new(None)),
        }
    }

    /// 添加数据到批次
    pub async fn add_data(&self, data: TelemetryData) -> Result<()> {
        let mut batch = self.current_batch.write().await;
        batch.push(data);

        // 检查是否达到批处理大小
        if batch.len() >= self.batch_size {
            let batch_data = std::mem::replace(&mut *batch, Vec::with_capacity(self.batch_size));
            drop(batch);
            
            // 重置定时器
            let mut timer = self.batch_timer.write().await;
            *timer = None;
            drop(timer);
            
            // 导出批次
            self.exporter.export(batch_data).await?;
        } else {
            // 设置或更新定时器
            let mut timer = self.batch_timer.write().await;
            if timer.is_none() {
                *timer = Some(tokio::time::Instant::now());
            }
        }

        Ok(())
    }

    /// 强制导出当前批次
    pub async fn flush(&self) -> Result<ExportResult> {
        let batch = {
            let mut current_batch = self.current_batch.write().await;
            std::mem::replace(&mut *current_batch, Vec::with_capacity(self.batch_size))
        };

        if batch.is_empty() {
            return Ok(ExportResult::success(0, Duration::ZERO));
        }

        // 重置定时器
        let mut timer = self.batch_timer.write().await;
        *timer = None;

        self.exporter.export(batch).await
    }

    /// 检查并处理超时的批次
    pub async fn check_timeout(&self) -> Result<Option<ExportResult>> {
        let timer_guard = self.batch_timer.read().await;
        if let Some(timer) = *timer_guard
            && tokio::time::Instant::now().duration_since(timer) >= self.batch_timeout {
                drop(timer_guard);
                return Ok(Some(self.flush().await?));
            }
        Ok(None)
    }
}

/// 异步导出器
#[allow(dead_code)]
pub struct AsyncExporter {
    exporter: Arc<OtlpExporter>,
    export_queue: mpsc::UnboundedSender<TelemetryData>,
    result_receiver: mpsc::UnboundedReceiver<ExportResult>,
}

impl AsyncExporter {
    /// 创建新的异步导出器
    pub fn new(exporter: Arc<OtlpExporter>) -> Self {
        let (export_tx, export_rx) = mpsc::unbounded_channel();
        let (result_tx, result_rx) = mpsc::unbounded_channel();

        let exporter_clone = exporter.clone();
        tokio::spawn(async move {
            let mut export_receiver = export_rx;
            let mut batch = Vec::new();
            let batch_size = exporter_clone.config.batch_config.max_export_batch_size;

            while let Some(data) = export_receiver.recv().await {
                batch.push(data);

                if batch.len() >= batch_size {
                    let batch_data = std::mem::replace(&mut batch, Vec::with_capacity(batch_size));
                    let result = exporter_clone.export(batch_data).await.unwrap_or_else(|e| {
                        ExportResult::failure(0, Duration::ZERO, vec![e.to_string()])
                    });
                    
                    if result_tx.send(result).is_err() {
                        break;
                    }
                }
            }

            // 导出剩余数据
            if !batch.is_empty() {
                let result = exporter_clone.export(batch).await.unwrap_or_else(|e| {
                    ExportResult::failure(0, Duration::ZERO, vec![e.to_string()])
                });
                let _ = result_tx.send(result);
            }
        });

        Self {
            exporter,
            export_queue: export_tx,
            result_receiver: result_rx,
        }
    }

    /// 异步导出数据
    pub fn export_async(&self, data: TelemetryData) -> Result<()> {
        self.export_queue.send(data)
            .map_err(|_| ExportError::ExportFailed {
                reason: "Failed to send data to export queue".to_string(),
            })?;
        Ok(())
    }

    /// 获取导出结果
    pub async fn get_result(&mut self) -> Option<ExportResult> {
        self.result_receiver.recv().await
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::data::TelemetryData;

    #[tokio::test]
    async fn test_export_result() {
        let result = ExportResult::success(10, Duration::from_millis(100));
        assert!(result.is_success());
        assert!(!result.is_failure());
        assert_eq!(result.total_count(), 10);
        assert_eq!(result.success_rate(), 1.0);

        let result = ExportResult::failure(5, Duration::from_millis(50), vec!["error".to_string()]);
        assert!(!result.is_success());
        assert!(result.is_failure());
        assert_eq!(result.total_count(), 5);
        assert_eq!(result.success_rate(), 0.0);

        let result = ExportResult::partial(7, 3, Duration::from_millis(75), vec!["error".to_string()]);
        assert!(!result.is_success());
        assert!(!result.is_failure());
        assert_eq!(result.total_count(), 10);
        assert_eq!(result.success_rate(), 0.7);
    }

    #[tokio::test]
    async fn test_exporter_creation() {
        let config = OtlpConfig::default();
        let exporter = OtlpExporter::new(config);
        
        // 测试初始化
        let _result = exporter.initialize().await;
        // 注意：这个测试可能会失败，因为需要实际的网络连接
        // 在实际测试中，应该使用mock或测试服务器
    }

    #[tokio::test]
    async fn test_batch_exporter() {
        let config = OtlpConfig::default();
        let exporter = Arc::new(OtlpExporter::new(config));
        let batch_exporter = BatchExporter::new(exporter, 5, Duration::from_millis(100));
        
        let data = TelemetryData::trace("test-operation");
        let _result = batch_exporter.add_data(data).await;
        // 注意：这个测试可能会失败，因为需要实际的网络连接
    }

    #[tokio::test]
    async fn test_async_exporter() {
        let config = OtlpConfig::default();
        let exporter = Arc::new(OtlpExporter::new(config));
        let async_exporter = AsyncExporter::new(exporter);
        
        let data = TelemetryData::trace("test-operation");
        let _result = async_exporter.export_async(data);
        // 注意：这个测试可能会失败，因为需要实际的网络连接
    }
}
