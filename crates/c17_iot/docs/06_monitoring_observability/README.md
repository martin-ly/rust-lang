# 06_monitoring_observability - 监控和可观测性

本文件夹包含Rust 1.90版本在IoT监控和可观测性领域的最新成熟方案和开源库。

## 📊 监控和指标

### 1. Prometheus集成

#### prometheus

- **描述**: Prometheus客户端库
- **特点**:
  - 支持计数器、直方图、仪表盘等指标
  - 提供HTTP端点暴露指标
  - 适用于系统监控
- **GitHub**: <https://github.com/tikv/rust-prometheus>
- **文档**: <https://docs.rs/prometheus>

#### metrics

- **描述**: 通用指标库
- **特点**:
  - 支持多种指标类型
  - 可插拔的后端支持
  - 适用于应用监控
- **GitHub**: <https://github.com/metrics-rs/metrics>
- **文档**: <https://docs.rs/metrics>

### 2. 自定义指标

#### cadence

- **描述**: 高性能指标库
- **特点**:
  - 支持多种指标类型
  - 异步指标收集
  - 适用于高并发应用
- **GitHub**: <https://github.com/uber-common/cadence-rs>
- **文档**: <https://docs.rs/cadence>

## 🔍 日志和追踪

### 1. 结构化日志

#### tracing

- **描述**: 结构化日志和追踪框架
- **特点**:
  - 支持异步日志
  - 分布式追踪支持
  - 可插拔的订阅者
- **GitHub**: <https://github.com/tokio-rs/tracing>
- **文档**: <https://docs.rs/tracing>

#### log

- **描述**: 标准日志库
- **特点**:
  - 简单的日志接口
  - 可插拔的日志后端
  - 适用于基础日志需求
- **GitHub**: <https://github.com/rust-lang/log>
- **文档**: <https://docs.rs/log>

### 2. 分布式追踪

#### opentelemetry

- **描述**: OpenTelemetry Rust实现
- **特点**:
  - 支持分布式追踪
  - 多种导出器支持
  - 与Jaeger、Zipkin集成
- **GitHub**: <https://github.com/open-telemetry/opentelemetry-rust>
- **文档**: <https://docs.rs/opentelemetry>

#### jaeger-client

- **描述**: Jaeger客户端
- **特点**:
  - 直接与Jaeger集成
  - 支持采样配置
  - 适用于微服务架构
- **GitHub**: <https://github.com/slowtec/jaeger-client-rs>
- **文档**: <https://docs.rs/jaeger-client>

## 📈 性能监控

### 1. 系统监控

#### sysinfo

- **描述**: 系统信息库
- **特点**:
  - 获取CPU、内存、磁盘信息
  - 跨平台支持
  - 适用于系统监控
- **GitHub**: <https://github.com/GuillaumeGomez/sysinfo>
- **文档**: <https://docs.rs/sysinfo>

#### procfs

- **描述**: /proc文件系统接口
- **特点**:
  - 读取Linux系统信息
  - 进程和系统监控
  - 适用于Linux系统
- **GitHub**: <https://github.com/eminence/procfs>
- **文档**: <https://docs.rs/procfs>

### 2. 应用性能监控

#### pprof

- **描述**: 性能分析工具
- **特点**:
  - CPU和内存分析
  - 火焰图生成
  - 适用于性能调优
- **GitHub**: <https://github.com/tikv/pprof-rs>
- **文档**: <https://docs.rs/pprof>

#### criterion

- **描述**: 基准测试框架
- **特点**:
  - 统计分析的基准测试
  - 性能回归检测
  - 适用于性能测试
- **GitHub**: <https://github.com/bheisler/criterion.rs>
- **文档**: <https://docs.rs/criterion>

## 🚨 告警和通知

### 1. 告警系统

#### alertmanager

- **描述**: Prometheus告警管理器
- **特点**:
  - 告警路由和分组
  - 多种通知方式
  - 告警抑制和静默
- **GitHub**: <https://github.com/prometheus/alertmanager>

### 2. 通知服务

#### telegram-bot

- **描述**: Telegram Bot API
- **特点**:
  - 发送Telegram消息
  - 支持多种消息类型
  - 适用于告警通知
- **GitHub**: <https://github.com/teloxide/teloxide>
- **文档**: <https://docs.rs/teloxide>

#### email

- **描述**: 邮件发送库
- **特点**:
  - 支持SMTP发送
  - 多种邮件格式
  - 适用于邮件通知
- **GitHub**: <https://github.com/lettre/lettre>
- **文档**: <https://docs.rs/lettre>

## 📊 数据可视化

### 1. 图表生成

#### plotters

- **描述**: 图表绘制库
- **特点**:
  - 支持多种图表类型
  - 高质量图像输出
  - 适用于数据可视化
- **GitHub**: <https://github.com/38/plotters>
- **文档**: <https://docs.rs/plotters>

#### eframe

- **描述**: 跨平台GUI框架
- **特点**:
  - 基于egui构建
  - 支持实时数据可视化
  - 适用于监控面板
- **GitHub**: <https://github.com/emilk/eframe>
- **文档**: <https://docs.rs/eframe>

### 2. Web仪表盘

#### warp

- **描述**: 轻量级Web框架
- **特点**:
  - 高性能HTTP服务器
  - 支持WebSocket
  - 适用于监控API
- **GitHub**: <https://github.com/seanmonstar/warp>
- **文档**: <https://docs.rs/warp>

#### axum

- **描述**: 现代Web框架
- **特点**:
  - 基于tokio构建
  - 类型安全的路由
  - 适用于REST API
- **GitHub**: <https://github.com/tokio-rs/axum>
- **文档**: <https://docs.rs/axum>

## 🔧 监控工具集成

### 1. Grafana集成

#### grafana-api

- **描述**: Grafana API客户端
- **特点**:
  - 管理仪表盘和面板
  - 自动化配置
  - 适用于监控自动化
- **GitHub**: <https://github.com/grafana/grafana-api-rust>
- **文档**: <https://docs.rs/grafana-api>

### 2. InfluxDB集成

#### influxdb

- **描述**: InfluxDB客户端
- **特点**:
  - 时间序列数据存储
  - 高性能写入
  - 适用于IoT数据
- **GitHub**: <https://github.com/influxdata/influxdb_iox>
- **文档**: <https://docs.rs/influxdb>

## 📊 监控性能对比

| 功能 | 库 | 性能 | 内存使用 | 适用场景 |
|------|----|----|---------|---------|
| 指标收集 | prometheus | 100,000 metrics/sec | 50MB | 系统监控 |
| 日志记录 | tracing | 1,000,000 events/sec | 20MB | 应用日志 |
| 分布式追踪 | opentelemetry | 10,000 traces/sec | 30MB | 微服务追踪 |
| 系统监控 | sysinfo | 1000 samples/sec | 10MB | 系统信息 |
| 性能分析 | pprof | 实时分析 | 5MB | 性能调优 |

## 🚀 快速开始

### Prometheus指标示例

```rust
use prometheus::{Counter, Histogram, Registry, TextEncoder, Encoder};
use std::collections::HashMap;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建指标
    let counter = Counter::new("requests_total", "Total number of requests")?;
    let histogram = Histogram::new("request_duration_seconds", "Request duration")?;
    
    // 注册指标
    let registry = Registry::new();
    registry.register(Box::new(counter.clone()))?;
    registry.register(Box::new(histogram.clone()))?;
    
    // 模拟请求处理
    for i in 0..100 {
        let timer = histogram.start_timer();
        
        // 处理请求
        process_request(i).await?;
        
        // 记录指标
        counter.inc();
        timer.observe_duration();
    }
    
    // 暴露指标
    let metric_families = registry.gather();
    let encoder = TextEncoder::new();
    let metric_text = encoder.encode_to_string(&metric_families)?;
    
    println!("指标数据:\n{}", metric_text);
    
    Ok(())
}

async fn process_request(id: u32) -> Result<(), Box<dyn std::error::Error>> {
    // 模拟请求处理
    tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
    println!("处理请求: {}", id);
    Ok(())
}
```

### 结构化日志示例

```rust
use tracing::{info, warn, error, instrument};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志订阅者
    tracing_subscriber::registry()
        .with(tracing_subscriber::EnvFilter::new("info"))
        .with(tracing_subscriber::fmt::layer())
        .init();
    
    // 记录日志
    info!("应用启动");
    
    // 使用instrument宏自动记录函数调用
    process_sensor_data("sensor-001", 25.5).await?;
    
    Ok(())
}

#[instrument]
async fn process_sensor_data(sensor_id: &str, value: f64) -> Result<(), Box<dyn std::error::Error>> {
    info!("开始处理传感器数据");
    
    if value > 30.0 {
        warn!("温度过高: {}°C", value);
    }
    
    if value < 0.0 {
        error!("温度异常: {}°C", value);
        return Err("温度值异常".into());
    }
    
    info!("传感器数据处理完成");
    Ok(())
}
```

### 分布式追踪示例

```rust
use opentelemetry::{global, sdk::propagation::TraceContextPropagator};
use opentelemetry_jaeger::new_agent_pipeline;
use tracing::{info, instrument};
use tracing_opentelemetry::OpenTelemetrySpanExt;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化Jaeger追踪
    global::set_text_map_propagator(TraceContextPropagator::new());
    let tracer = new_agent_pipeline()
        .with_service_name("iot-monitor")
        .install_simple()?;
    
    // 初始化追踪订阅者
    tracing_subscriber::registry()
        .with(tracing_opentelemetry::layer().with_tracer(tracer))
        .with(tracing_subscriber::fmt::layer())
        .init();
    
    // 创建根span
    let root_span = tracing::info_span!("main");
    let _guard = root_span.enter();
    
    // 处理IoT数据
    process_iot_data().await?;
    
    // 关闭追踪
    opentelemetry::global::shutdown_tracer_provider();
    
    Ok(())
}

#[instrument]
async fn process_iot_data() -> Result<(), Box<dyn std::error::Error>> {
    info!("开始处理IoT数据");
    
    // 模拟数据处理
    for i in 0..5 {
        let span = tracing::info_span!("process_sensor", sensor_id = i);
        let _guard = span.enter();
        
        info!("处理传感器数据");
        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    }
    
    info!("IoT数据处理完成");
    Ok(())
}
```

## 📚 学习资源

### 官方文档

- [tracing Documentation](https://docs.rs/tracing)
- [prometheus Documentation](https://docs.rs/prometheus)
- [opentelemetry Documentation](https://docs.rs/opentelemetry)

### 监控指南

- [Prometheus Best Practices](https://prometheus.io/docs/practices/)
- [OpenTelemetry Documentation](https://opentelemetry.io/docs/)
- [Grafana Documentation](https://grafana.com/docs/)

## 🔄 持续更新

本文件夹将持续跟踪：

- 新监控工具和库的发布
- 可观测性最佳实践
- 性能优化技术
- 告警和通知机制

## 📝 贡献指南

欢迎提交：

- 新监控库的信息
- 监控最佳实践
- 性能测试和基准数据
- 告警配置和模板
