# Rust 微服务框架集合

> 导航：返回 [`rust-formal-engineering-system`](../../rust-formal-engineering-system/README.md) · 质量保障 [`10_quality_assurance/00_index.md`](../../rust-formal-engineering-system/10_quality_assurance/00_index.md) · 网络模块 [`crates/c10_networks`](../c10_networks/) · 异步范式 [`02_async/00_index.md`](../../rust-formal-engineering-system/02_programming_paradigms/02_async/00_index.md) · 事件驱动 [`08_event_driven/00_index.md`](../../rust-formal-engineering-system/02_programming_paradigms/08_event_driven/00_index.md) · Actor [`09_actor_model/00_index.md`](../../rust-formal-engineering-system/02_programming_paradigms/09_actor_model/00_index.md) · 基准指南 [`11_benchmark_minimal_guide.md`](../../rust-formal-engineering-system/02_programming_paradigms/11_benchmark_minimal_guide.md)

这是一个全面的Rust微服务框架集合，支持多种Web框架、gRPC、服务网格和云原生部署。结合Rust 1.89的最新语言特性，提供高性能、安全、可扩展的微服务解决方案。

## 🚀 主要特性

- **现代Web框架**: Axum, Actix-Web, Warp, Tide
- **gRPC支持**: Tonic, Volo (字节跳动开源)
- **服务网格**: 服务发现、负载均衡、熔断器
- **可观测性**: OpenTelemetry, Prometheus, Jaeger
- **数据库集成**: SQLx, Diesel, SeaORM
- **Kubernetes**: 部署和配置管理
- **安全特性**: JWT, OAuth2, HTTPS, CORS
- **异步模式**: Actor模型、消息队列、事件驱动

## 📦 支持的框架

### Web框架

- **Axum**: 现代、高性能的Web框架
- **Actix-Web**: 基于Actor模型的高性能Web框架
- **Warp**: 基于Filter的Web框架
- **Tide**: 异步Web框架

### RPC框架

- **Tonic**: 高性能gRPC框架
- **Volo**: 字节跳动开源的现代RPC框架

### 数据库

- **SQLx**: 异步SQL工具包
- **Diesel**: 类型安全的ORM
- **SeaORM**: 现代异步ORM

### 消息队列

- **RabbitMQ**: 通过lapin crate
- **Kafka**: 通过kafka crate
- **Redis**: 通过redis crate

## 🛠️ 快速开始

### 安装依赖

```bash
# 克隆项目
git clone <repository-url>
cd c13_microservice

# 构建项目
cargo build
```

### 运行示例

```bash
# 启动Axum Web服务
cargo run --bin microservice-server -- axum

# 启动Actix-Web服务
cargo run --bin microservice-server -- actix

# 启动gRPC服务
cargo run --bin microservice-server -- grpc

# 启动Volo RPC服务
cargo run --bin microservice-server -- volo

# 显示配置信息
cargo run --bin microservice-server -- config
```

### 运行示例程序

```bash
# 运行简化的Axum示例
cargo run --example simple_axum

# 运行gRPC服务示例
cargo run --example grpc_service

# 运行gRPC客户端示例
cargo run --example grpc_client_demo

# 运行Volo RPC服务示例
cargo run --example volo_rpc_service

# 运行高级消息队列示例
cargo run --example messaging_advanced_demo

# 运行可观测性示例
cargo run --example comprehensive_observability_demo
```

### 使用配置文件

```bash
# 使用自定义配置文件
cargo run --bin microservice-server -- axum --config config.toml
```

## 📝 配置

### 环境变量

```bash
export SERVICE_NAME="my-microservice"
export SERVICE_PORT="3000"
export SERVICE_HOST="0.0.0.0"
export DATABASE_URL="postgresql://localhost/microservice"
export LOG_LEVEL="info"
export JWT_SECRET="your-secret-key"
```

### 配置文件 (config.toml)

```toml
[service]
name = "microservice"
version = "1.0.0"
host = "0.0.0.0"
port = 3000
environment = "development"
health_check_path = "/health"
shutdown_timeout = 30

[database]
url = "postgresql://localhost/microservice"
max_connections = 10
connection_timeout = 30
idle_timeout = 600
enable_pool = true

[logging]
level = "info"
format = "pretty"
structured = true
output = "stdout"

[monitoring]
enable_metrics = true
metrics_port = 9090
metrics_path = "/metrics"
enable_tracing = true

[security]
jwt_secret = "your-secret-key"
jwt_expiry = 3600
enable_https = false

[service_mesh]
enable_discovery = false
discovery_type = "consul"
enable_load_balancer = false
load_balancer_strategy = "round_robin"
enable_circuit_breaker = false

[messaging]
queue_type = "rabbitmq"
queue_url = "amqp://localhost:5672"
enable_ack = true
retry_count = 3
message_ttl = 3600

[kubernetes]
in_cluster = false
namespace = "default"
enable_autoscaling = false
```

## 🆕 最新功能

### 增强的gRPC支持 ✅

- 完整的Protocol Buffers定义
- 自动代码生成（支持protoc编译器）
- 类型安全的客户端和服务器
- 健康检查支持
- 智能编译器检测和安装脚本

### 高级消息队列 ✅

- 统一的消息抽象
- 实际的消息队列连接（Redis、RabbitMQ）
- 消息处理器模式
- 事件驱动架构
- 条件编译支持

### 丰富的中间件功能 ✅

- 请求ID追踪
- 日志记录
- 限流控制
- 健康检查
- 错误处理
- CORS支持

### 性能测试和基准测试 ✅

- 全面的基准测试套件
- 使用Criterion框架
- 生成HTML格式的交互式报告
- 性能优化建议

### 改进的CLI工具

- 支持多种服务类型启动
- 统一的配置管理
- 更好的错误处理

## 🔧 API示例

### Axum REST API

```rust
use c13_microservice::{
    prelude::*,
    axum::AxumMicroservice,
    config::Config,
};

#[tokio::main]
async fn main() -> Result<()> {
    let config = Config::from_env()?;
    let microservice = AxumMicroservice::new(config);
    microservice.serve().await?;
    Ok(())
}
```

### gRPC服务

```rust
use c13_microservice::{
    prelude::*,
    grpc::GrpcMicroservice,
    config::Config,
};

#[tokio::main]
async fn main() -> Result<()> {
    let config = Config::from_env()?;
    let microservice = GrpcMicroservice::new(config);
    microservice.serve().await?;
    Ok(())
}
```

### gRPC客户端

```rust
use c13_microservice::grpc::GrpcClient;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut client = GrpcClient::new("http://[::1]:50051").await?;
    
    // 创建用户
    let user = client.create_user("张三".to_string(), "zhangsan@example.com".to_string()).await?;
    println!("创建用户: {:?}", user);
    
    // 获取用户
    let retrieved_user = client.get_user(user.id).await?;
    println!("获取用户: {:?}", retrieved_user);
    
    Ok(())
}
```

### Volo RPC服务

```rust
use c13_microservice::{
    prelude::*,
    volo::VoloMicroservice,
    config::Config,
};

#[tokio::main]
async fn main() -> Result<()> {
    let config = Config::from_env()?;
    let microservice = VoloMicroservice::new(config);
    microservice.serve().await?;
    Ok(())
}
```

### 消息队列1

```rust
use c13_microservice::messaging::{Message, MessageQueueManager};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut mq_manager = MessageQueueManager::new();
    
    // 添加消息队列
    mq_manager.add_redis("redis://localhost:6379".to_string());
    mq_manager.add_rabbitmq("amqp://localhost:5672".to_string());
    
    // 连接所有队列
    mq_manager.connect_all().await?;
    
    // 发布消息
    let message = Message::new("user_events".to_string(), b"Hello World".to_vec());
    mq_manager.publish_to_all(&message.topic, &message.payload).await?;
    
    Ok(())
}
```

## 🧪 测试

```bash
# 运行所有测试
cargo test

# 运行特定测试
cargo test test_axum_microservice

# 运行示例
cargo run --example axum_rest_api
cargo run --example grpc_service
cargo run --example volo_rpc_service
```

## 🔗 范式与示例对照

- 响应式：[`07_reactive/00_index.md`](../../rust-formal-engineering-system/02_programming_paradigms/07_reactive/00_index.md)
  - `examples/simple_observability_demo.rs`、`examples/comprehensive_observability_demo.rs`、`examples/axum_rest_api.rs`
- 事件驱动：[`08_event_driven/00_index.md`](../../rust-formal-engineering-system/02_programming_paradigms/08_event_driven/00_index.md)
  - `examples/simple_axum.rs`、`examples/grpc_service.rs`、`examples/grpc_client_demo.rs`、`examples/messaging_demo.rs`、`examples/messaging_advanced_demo.rs`
- Actor：[`09_actor_model/00_index.md`](../../rust-formal-engineering-system/02_programming_paradigms/09_actor_model/00_index.md)
  - `examples/volo_rpc_service.rs`、`examples/messaging_advanced_demo.rs`、`examples/advanced_grpc_demo.rs`

## 📦 构建说明（features 与独立模式）

- 本 crate 已合并为单一 `Cargo.toml`，通过 features 复刻“独立构建”能力：

```bash
# 最小构建（默认最小依赖）
cargo test -p c13_microservice

# 独立构建（启用重依赖：redis/sqlx/diesel）
cargo test -p c13_microservice --features standalone

# 精细启用
cargo test -p c13_microservice --features with-redis
cargo test -p c13_microservice --features with-sqlx
cargo test -p c13_microservice --features with-diesel
```

- 说明：`standalone = with-redis + with-sqlx + with-diesel`。若与工作区其它 crate 出现 `libsqlite3-sys` 冲突，可仅启用 `with-diesel` 或避免启用 sqlite 后端。

## 📊 监控和可观测性

### 健康检查

```bash
# 基本健康检查
curl http://localhost:3000/health

# 详细健康检查
curl http://localhost:3000/health/detailed
```

### 指标

```bash
# Prometheus指标
curl http://localhost:9090/metrics
```

### 追踪

支持OpenTelemetry和Jaeger追踪，可以通过环境变量配置：

```bash
export JAEGER_ENDPOINT="http://localhost:14268/api/traces"
```

## 🐳 Docker部署

```dockerfile
FROM rust:1.89-slim as builder

WORKDIR /app
COPY . .
RUN cargo build --release

FROM debian:bookworm-slim
RUN apt-get update && apt-get install -y ca-certificates && rm -rf /var/lib/apt/lists/*
COPY --from=builder /app/target/release/microservice-server /usr/local/bin/
EXPOSE 3000
CMD ["microservice-server", "axum"]
```

## ☸️ Kubernetes部署

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: microservice
spec:
  replicas: 3
  selector:
    matchLabels:
      app: microservice
  template:
    metadata:
      labels:
        app: microservice
    spec:
      containers:
      - name: microservice
        image: microservice:latest
        ports:
        - containerPort: 3000
        env:
        - name: SERVICE_NAME
          value: "microservice"
        - name: SERVICE_PORT
          value: "3000"
        - name: DATABASE_URL
          valueFrom:
            secretKeyRef:
              name: database-secret
              key: url
---
apiVersion: v1
kind: Service
metadata:
  name: microservice-service
spec:
  selector:
    app: microservice
  ports:
  - port: 3000
    targetPort: 3000
  type: ClusterIP
```

## 🔐 安全特性

- JWT认证
- OAuth2支持
- HTTPS/TLS
- CORS配置
- 请求限流
- 输入验证

## 📈 性能优化

- 异步处理
- 连接池
- 缓存策略
- 负载均衡
- 熔断器模式

## 🤝 贡献

欢迎贡献代码！请遵循以下步骤：

1. Fork项目
2. 创建特性分支
3. 提交更改
4. 推送到分支
5. 创建Pull Request

## 📄 许可证

本项目采用MIT许可证。详见[LICENSE](../../LICENSE)文件。

## 🙏 致谢

- [Axum](https://github.com/tokio-rs/axum) - 现代Web框架
- [Actix-Web](https://github.com/actix/actix-web) - 高性能Web框架
- [Tonic](https://github.com/hyperium/tonic) - gRPC框架
- [Volo](https://github.com/cloudwego/volo) - 字节跳动RPC框架
- [Tokio](https://github.com/tokio-rs/tokio) - 异步运行时

## 📚 相关资源

- [Rust官方文档](https://doc.rust-lang.org/)
- [Tokio文档](https://tokio.rs/)
- [Axum文档](https://docs.rs/axum/)
- [Actix-Web文档](https://actix.rs/)
- [Tonic文档](https://docs.rs/tonic/)
- [Volo文档](https://www.cloudwego.io/zh/docs/volo/)

---

**注意**: 这是一个示例项目，展示了如何使用Rust构建现代微服务。在生产环境中使用前，请确保进行充分的测试和安全审查。

## 📡 可观测性一键运行（OTLP）

- 启动观测性栈：`scripts/observability/start-stack.ps1`
- 环境变量：
  - `OTEL_EXPORTER_OTLP_ENDPOINT=http://localhost:4317`（gRPC）或 `http://localhost:4318`（HTTP）
  - `OTEL_TRACES_SAMPLER=parentbased_always_on`
  - `OTEL_SERVICE_NAME=c13-microservice`
- 运行可观测性示例：
  - `cargo run -p c13_microservice --example simple_observability_demo`
  - 或 `cargo run -p c13_microservice --example comprehensive_observability_demo`
- 验证：Grafana `http://localhost:3000`、Prometheus `http://localhost:9090`
