# OTLP 详细分类和组合方式

本文档详细介绍了 OTLP 实现中的各种分类方式和组合策略。

## 📋 目录

- [OTLP 详细分类和组合方式](#otlp-详细分类和组合方式)

## 📊 数据类型分类

### 1. 遥测数据类型

```rust
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TelemetryDataType {
    /// 追踪数据 - 用于分布式追踪
    Trace,
    /// 指标数据 - 用于性能监控
    Metric,
    /// 日志数据 - 用于日志记录
    Log,
}
```

#### 追踪数据分类

```rust
#[derive(Debug, Clone)]
pub struct TraceData {
    /// 追踪ID - 全局唯一标识
    pub trace_id: String,
    /// 跨度ID - 操作唯一标识
    pub span_id: String,
    /// 父跨度ID - 用于构建调用链
    pub parent_span_id: Option<String>,
    /// 操作名称
    pub name: String,
    /// 跨度类型
    pub span_kind: SpanKind,
    /// 开始时间
    pub start_time: u64,
    /// 结束时间
    pub end_time: u64,
    /// 状态信息
    pub status: SpanStatus,
    /// 属性集合
    pub attributes: HashMap<String, AttributeValue>,
    /// 事件列表
    pub events: Vec<SpanEvent>,
    /// 链接列表
    pub links: Vec<SpanLink>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpanKind {
    /// 内部跨度 - 服务内部操作
    Internal,
    /// 服务器跨度 - 接收请求
    Server,
    /// 客户端跨度 - 发送请求
    Client,
    /// 生产者跨度 - 消息生产
    Producer,
    /// 消费者跨度 - 消息消费
    Consumer,
}
```

#### 指标数据分类

```rust
#[derive(Debug, Clone)]
pub struct MetricData {
    /// 指标名称
    pub name: String,
    /// 指标描述
    pub description: String,
    /// 指标单位
    pub unit: String,
    /// 指标类型
    pub metric_type: MetricType,
    /// 数据点集合
    pub data_points: Vec<DataPoint>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MetricType {
    /// 计数器 - 单调递增的数值
    Counter,
    /// 仪表 - 可增可减的数值
    Gauge,
    /// 直方图 - 数值分布统计
    Histogram,
    /// 摘要 - 分位数统计
    Summary,
}
```

#### 日志数据分类

```rust
#[derive(Debug, Clone)]
pub struct LogData {
    /// 时间戳
    pub timestamp: u64,
    /// 严重程度
    pub severity: LogSeverity,
    /// 严重程度文本
    pub severity_text: String,
    /// 日志消息
    pub message: String,
    /// 属性集合
    pub attributes: HashMap<String, AttributeValue>,
    /// 资源属性
    pub resource_attributes: HashMap<String, AttributeValue>,
    /// 关联的追踪ID
    pub trace_id: Option<String>,
    /// 关联的跨度ID
    pub span_id: Option<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum LogSeverity {
    /// 跟踪级别
    Trace = 1,
    /// 调试级别
    Debug = 5,
    /// 信息级别
    Info = 9,
    /// 警告级别
    Warn = 13,
    /// 错误级别
    Error = 17,
    /// 致命级别
    Fatal = 21,
}
```

### 2. 属性值类型分类

```rust
#[derive(Debug, Clone, PartialEq)]
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
```

## 🌐 传输协议分类

### 1. 协议类型

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TransportProtocol {
    /// gRPC协议 - 高性能二进制协议
    Grpc,
    /// HTTP/JSON协议 - 通用Web协议
    Http,
    /// HTTP/Protobuf协议 - HTTP + 二进制序列化
    HttpProtobuf,
}

impl TransportProtocol {
    /// 获取默认端口
    pub fn default_port(&self) -> u16 {
        match self {
            TransportProtocol::Grpc => 4317,
            TransportProtocol::Http => 4318,
            TransportProtocol::HttpProtobuf => 4318,
        }
    }
    
    /// 获取内容类型
    pub fn content_type(&self) -> &'static str {
        match self {
            TransportProtocol::Grpc => "application/grpc",
            TransportProtocol::Http => "application/json",
            TransportProtocol::HttpProtobuf => "application/x-protobuf",
        }
    }
}
```

### 2. 压缩算法分类

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompressionAlgorithm {
    /// 无压缩
    None,
    /// Gzip压缩 - 通用压缩算法
    Gzip,
    /// Brotli压缩 - 高效压缩算法
    Brotli,
    /// Zstd压缩 - 快速压缩算法
    Zstd,
}

impl CompressionAlgorithm {
    /// 压缩数据
    pub fn compress(&self, data: &[u8]) -> Result<Vec<u8>> {
        match self {
            CompressionAlgorithm::None => Ok(data.to_vec()),
            CompressionAlgorithm::Gzip => {
                use flate2::write::GzEncoder;
                use flate2::Compression;
                let mut encoder = GzEncoder::new(Vec::new(), Compression::default());
                encoder.write_all(data)?;
                Ok(encoder.finish()?)
            }
            CompressionAlgorithm::Brotli => {
                use brotli::enc::BrotliEncoderParams;
                let params = BrotliEncoderParams::default();
                Ok(brotli::enc::BrotliCompress(data, &params)?)
            }
            CompressionAlgorithm::Zstd => {
                Ok(zstd::encode_all(data, 0)?)
            }
        }
    }
}
```

## ⚙️ 配置分类

### 1. 基础配置

```rust
#[derive(Debug, Clone)]
pub struct BasicConfig {
    /// 服务端点
    pub endpoint: String,
    /// 传输协议
    pub protocol: TransportProtocol,
    /// 连接超时
    pub timeout: Duration,
    /// 重试次数
    pub retry_count: usize,
}

impl BasicConfig {
    /// 开发环境配置
    pub fn for_development() -> Self {
        Self {
            endpoint: "http://localhost:4317".to_string(),
            protocol: TransportProtocol::Grpc,
            timeout: Duration::from_secs(5),
            retry_count: 3,
        }
    }
    
    /// 生产环境配置
    pub fn for_production() -> Self {
        Self {
            endpoint: "https://otlp-collector.company.com".to_string(),
            protocol: TransportProtocol::Grpc,
            timeout: Duration::from_secs(30),
            retry_count: 5,
        }
    }
}
```

### 2. 高级配置

```rust
#[derive(Debug, Clone)]
pub struct AdvancedConfig {
    /// 基础配置
    pub basic: BasicConfig,
    /// 批处理配置
    pub batch_config: BatchConfig,
    /// 压缩配置
    pub compression: CompressionAlgorithm,
    /// 认证配置
    pub auth: AuthConfig,
    /// TLS配置
    pub tls: TlsConfig,
    /// 采样配置
    pub sampling: SamplingConfig,
}

impl AdvancedConfig {
    /// 高吞吐量配置
    pub fn for_high_throughput() -> Self {
        Self {
            basic: BasicConfig::for_production(),
            batch_config: BatchConfig {
                max_batch_size: 1000,
                batch_timeout: Duration::from_millis(100),
                max_queue_size: 10000,
            },
            compression: CompressionAlgorithm::Zstd,
            auth: AuthConfig::with_api_key("production-key"),
            tls: TlsConfig::enabled(),
            sampling: SamplingConfig::adaptive(0.1),
        }
    }
}
```

### 3. 环境特定配置

```rust
pub struct EnvironmentConfig {
    /// 开发环境
    pub development: OtlpConfig,
    /// 测试环境
    pub testing: OtlpConfig,
    /// 预生产环境
    pub staging: OtlpConfig,
    /// 生产环境
    pub production: OtlpConfig,
}

impl EnvironmentConfig {
    pub fn get_config(&self, env: &str) -> &OtlpConfig {
        match env {
            "development" => &self.development,
            "testing" => &self.testing,
            "staging" => &self.staging,
            "production" => &self.production,
            _ => &self.development,
        }
    }
}
```

## 🚀 性能分类

### 1. 性能等级

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PerformanceLevel {
    /// 低延迟 - 优先考虑延迟
    LowLatency,
    /// 高吞吐量 - 优先考虑吞吐量
    HighThroughput,
    /// 平衡模式 - 平衡延迟和吞吐量
    Balanced,
    /// 资源优化 - 优先考虑资源使用
    ResourceOptimized,
}

impl PerformanceLevel {
    pub fn get_config(&self) -> OtlpConfig {
        match self {
            PerformanceLevel::LowLatency => OtlpConfig::default()
                .with_batch_config(BatchConfig {
                    max_export_batch_size: 10,
                    export_timeout: Duration::from_millis(10),
                    max_queue_size: 100,
                    scheduled_delay: Duration::from_millis(1),
                }),
            PerformanceLevel::HighThroughput => OtlpConfig::default()
                .with_batch_config(BatchConfig {
                    max_export_batch_size: 10000,
                    export_timeout: Duration::from_secs(10),
                    max_queue_size: 100000,
                    scheduled_delay: Duration::from_secs(1),
                }),
            PerformanceLevel::Balanced => OtlpConfig::default()
                .with_batch_config(BatchConfig {
                    max_export_batch_size: 1000,
                    export_timeout: Duration::from_millis(1000),
                    max_queue_size: 10000,
                    scheduled_delay: Duration::from_millis(100),
                }),
            PerformanceLevel::ResourceOptimized => OtlpConfig::default()
                .with_batch_config(BatchConfig {
                    max_export_batch_size: 100,
                    export_timeout: Duration::from_secs(5),
                    max_queue_size: 1000,
                    scheduled_delay: Duration::from_secs(1),
                }),
        }
    }
}
```

### 2. 资源使用分类

```rust
#[derive(Debug, Clone)]
pub struct ResourceUsage {
    /// CPU使用率
    pub cpu_usage: f64,
    /// 内存使用量
    pub memory_usage: usize,
    /// 网络带宽使用
    pub network_usage: usize,
    /// 磁盘I/O使用
    pub disk_io_usage: usize,
}

impl ResourceUsage {
    /// 获取资源使用等级
    pub fn get_usage_level(&self) -> UsageLevel {
        let total_score = self.cpu_usage + 
            (self.memory_usage as f64 / 1024.0 / 1024.0) + // MB
            (self.network_usage as f64 / 1024.0) + // KB
            (self.disk_io_usage as f64 / 1024.0); // KB
        
        match total_score {
            score if score < 10.0 => UsageLevel::Low,
            score if score < 50.0 => UsageLevel::Medium,
            score if score < 100.0 => UsageLevel::High,
            _ => UsageLevel::Critical,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UsageLevel {
    /// 低使用率
    Low,
    /// 中等使用率
    Medium,
    /// 高使用率
    High,
    /// 临界使用率
    Critical,
}
```

## 🎯 使用场景分类

### 1. 应用类型分类

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ApplicationType {
    /// Web应用
    WebApplication,
    /// 微服务
    Microservice,
    /// 批处理应用
    BatchApplication,
    /// 实时流处理
    StreamProcessing,
    /// 移动应用
    MobileApplication,
    /// 桌面应用
    DesktopApplication,
}

impl ApplicationType {
    pub fn get_recommended_config(&self) -> OtlpConfig {
        match self {
            ApplicationType::WebApplication => OtlpConfig::default()
                .with_batch_config(BatchConfig {
                    max_export_batch_size: 500,
                    export_timeout: Duration::from_millis(500),
                    max_queue_size: 5000,
                    scheduled_delay: Duration::from_millis(100),
                }),
            ApplicationType::Microservice => OtlpConfig::default()
                .with_batch_config(BatchConfig {
                    max_export_batch_size: 100,
                    export_timeout: Duration::from_millis(100),
                    max_queue_size: 1000,
                    scheduled_delay: Duration::from_millis(50),
                }),
            ApplicationType::BatchApplication => OtlpConfig::default()
                .with_batch_config(BatchConfig {
                    max_export_batch_size: 10000,
                    export_timeout: Duration::from_secs(30),
                    max_queue_size: 100000,
                    scheduled_delay: Duration::from_secs(5),
                }),
            ApplicationType::StreamProcessing => OtlpConfig::default()
                .with_batch_config(BatchConfig {
                    max_export_batch_size: 1000,
                    export_timeout: Duration::from_millis(100),
                    max_queue_size: 10000,
                    scheduled_delay: Duration::from_millis(10),
                }),
            ApplicationType::MobileApplication => OtlpConfig::default()
                .with_batch_config(BatchConfig {
                    max_export_batch_size: 50,
                    export_timeout: Duration::from_secs(10),
                    max_queue_size: 500,
                    scheduled_delay: Duration::from_secs(1),
                }),
            ApplicationType::DesktopApplication => OtlpConfig::default()
                .with_batch_config(BatchConfig {
                    max_export_batch_size: 200,
                    export_timeout: Duration::from_secs(5),
                    max_queue_size: 2000,
                    scheduled_delay: Duration::from_millis(500),
                }),
        }
    }
}
```

### 2. 部署环境分类

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DeploymentEnvironment {
    /// 本地开发
    Local,
    /// 开发环境
    Development,
    /// 测试环境
    Testing,
    /// 预生产环境
    Staging,
    /// 生产环境
    Production,
}

impl DeploymentEnvironment {
    pub fn get_config(&self) -> OtlpConfig {
        match self {
            DeploymentEnvironment::Local => OtlpConfig::default()
                .with_endpoint("http://localhost:4317")
                .with_debug(true)
                .with_sampling_ratio(1.0),
            DeploymentEnvironment::Development => OtlpConfig::default()
                .with_endpoint("http://dev-otlp-collector:4317")
                .with_debug(true)
                .with_sampling_ratio(0.5),
            DeploymentEnvironment::Testing => OtlpConfig::default()
                .with_endpoint("http://test-otlp-collector:4317")
                .with_debug(false)
                .with_sampling_ratio(0.1),
            DeploymentEnvironment::Staging => OtlpConfig::default()
                .with_endpoint("http://staging-otlp-collector:4317")
                .with_debug(false)
                .with_sampling_ratio(0.01),
            DeploymentEnvironment::Production => OtlpConfig::default()
                .with_endpoint("https://prod-otlp-collector.company.com")
                .with_debug(false)
                .with_sampling_ratio(0.001)
                .with_tls(true),
        }
    }
}
```

### 3. 数据量级分类

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DataVolume {
    /// 低数据量 - < 1K events/sec
    Low,
    /// 中等数据量 - 1K-10K events/sec
    Medium,
    /// 高数据量 - 10K-100K events/sec
    High,
    /// 超高数据量 - > 100K events/sec
    VeryHigh,
}

impl DataVolume {
    pub fn get_optimized_config(&self) -> OtlpConfig {
        match self {
            DataVolume::Low => OtlpConfig::default()
                .with_batch_config(BatchConfig {
                    max_export_batch_size: 100,
                    export_timeout: Duration::from_secs(5),
                    max_queue_size: 1000,
                    scheduled_delay: Duration::from_secs(1),
                }),
            DataVolume::Medium => OtlpConfig::default()
                .with_batch_config(BatchConfig {
                    max_export_batch_size: 1000,
                    export_timeout: Duration::from_millis(1000),
                    max_queue_size: 10000,
                    scheduled_delay: Duration::from_millis(100),
                }),
            DataVolume::High => OtlpConfig::default()
                .with_batch_config(BatchConfig {
                    max_export_batch_size: 5000,
                    export_timeout: Duration::from_millis(500),
                    max_queue_size: 50000,
                    scheduled_delay: Duration::from_millis(50),
                }),
            DataVolume::VeryHigh => OtlpConfig::default()
                .with_batch_config(BatchConfig {
                    max_export_batch_size: 10000,
                    export_timeout: Duration::from_millis(100),
                    max_queue_size: 100000,
                    scheduled_delay: Duration::from_millis(10),
                }),
        }
    }
}
```

## 🔄 组合策略

### 1. 智能配置组合

```rust
pub struct SmartConfigBuilder {
    application_type: ApplicationType,
    deployment_env: DeploymentEnvironment,
    data_volume: DataVolume,
    performance_level: PerformanceLevel,
}

impl SmartConfigBuilder {
    pub fn build(&self) -> OtlpConfig {
        let mut config = self.application_type.get_recommended_config();
        
        // 根据部署环境调整
        let env_config = self.deployment_env.get_config();
        config = config
            .with_endpoint(env_config.endpoint.clone())
            .with_debug(env_config.debug)
            .with_sampling_ratio(env_config.sampling_ratio);
        
        // 根据数据量级优化
        let volume_config = self.data_volume.get_optimized_config();
        config = config.with_batch_config(volume_config.batch_config);
        
        // 根据性能要求调整
        let perf_config = self.performance_level.get_config();
        config = config.with_batch_config(perf_config.batch_config);
        
        config
    }
}
```

### 2. 动态配置调整

```rust
pub struct DynamicConfigManager {
    current_config: Arc<RwLock<OtlpConfig>>,
    adjustment_strategies: Vec<Box<dyn ConfigAdjustmentStrategy>>,
}

impl DynamicConfigManager {
    pub async fn adjust_config(&self, metrics: &PerformanceMetrics) -> Result<()> {
        let mut config = self.current_config.read().await.clone();
        
        for strategy in &self.adjustment_strategies {
            config = strategy.adjust(config, metrics).await?;
        }
        
        let mut current = self.current_config.write().await;
        *current = config;
        
        Ok(())
    }
}

#[async_trait]
pub trait ConfigAdjustmentStrategy: Send + Sync {
    async fn adjust(&self, config: OtlpConfig, metrics: &PerformanceMetrics) -> Result<OtlpConfig>;
}
```

## 📚 参考资料

- [OpenTelemetry 数据模型规范](https://opentelemetry.io/docs/specs/otel/)
- [OTLP 协议规范](https://github.com/open-telemetry/opentelemetry-proto)
- [性能调优指南](https://opentelemetry.io/docs/collector/performance/)
- [配置最佳实践](https://opentelemetry.io/docs/collector/configuration/)
