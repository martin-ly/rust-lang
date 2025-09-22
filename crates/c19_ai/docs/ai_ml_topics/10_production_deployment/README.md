# 生产部署 (Production Deployment)

## 概述

本文件夹包含Rust 1.90版本中AI/ML应用的生产部署策略、工具和最佳实践。

## 部署架构

### 1. 微服务架构

- **服务拆分**: 按功能模块拆分服务
- **API网关**: 统一入口和路由
- **服务发现**: 自动服务注册和发现
- **负载均衡**: 请求分发和故障转移
- **配置管理**: 集中化配置管理

### 2. 容器化部署

- **Docker**: 应用容器化
- **Kubernetes**: 容器编排
- **Helm**: 包管理
- **Istio**: 服务网格
- **监控**: 容器监控和日志

### 3. 云原生部署

- **AWS**: Amazon Web Services
- **Azure**: Microsoft Azure
- **GCP**: Google Cloud Platform
- **阿里云**: 阿里云服务
- **腾讯云**: 腾讯云服务

## 部署工具

### 1. 容器化

```dockerfile
# Dockerfile
FROM rust:1.90-slim as builder

WORKDIR /app
COPY Cargo.toml Cargo.lock ./
COPY src ./src

# 构建应用
RUN cargo build --release

# 运行时镜像
FROM debian:bookworm-slim

# 安装运行时依赖
RUN apt-get update && apt-get install -y \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

# 复制二进制文件
COPY --from=builder /app/target/release/ai-service /usr/local/bin/

# 设置用户
RUN useradd -r -s /bin/false appuser
USER appuser

# 暴露端口
EXPOSE 8080

# 启动命令
CMD ["ai-service"]
```

### 2. Kubernetes部署

```yaml
# deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: ai-service
  labels:
    app: ai-service
spec:
  replicas: 3
  selector:
    matchLabels:
      app: ai-service
  template:
    metadata:
      labels:
        app: ai-service
    spec:
      containers:
      - name: ai-service
        image: ai-service:latest
        ports:
        - containerPort: 8080
        env:
        - name: RUST_LOG
          value: "info"
        - name: DATABASE_URL
          valueFrom:
            secretKeyRef:
              name: ai-secrets
              key: database-url
        resources:
          requests:
            memory: "512Mi"
            cpu: "250m"
          limits:
            memory: "1Gi"
            cpu: "500m"
        livenessProbe:
          httpGet:
            path: /health
            port: 8080
          initialDelaySeconds: 30
          periodSeconds: 10
        readinessProbe:
          httpGet:
            path: /ready
            port: 8080
          initialDelaySeconds: 5
          periodSeconds: 5
---
apiVersion: v1
kind: Service
metadata:
  name: ai-service
spec:
  selector:
    app: ai-service
  ports:
  - port: 80
    targetPort: 8080
  type: LoadBalancer
```

### 3. 配置管理

```rust
use serde::{Deserialize, Serialize};
use std::env;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AppConfig {
    pub server: ServerConfig,
    pub database: DatabaseConfig,
    pub redis: RedisConfig,
    pub ai: AIConfig,
    pub monitoring: MonitoringConfig,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ServerConfig {
    pub host: String,
    pub port: u16,
    pub workers: usize,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DatabaseConfig {
    pub url: String,
    pub max_connections: u32,
    pub timeout: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RedisConfig {
    pub url: String,
    pub max_connections: u32,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AIConfig {
    pub model_path: String,
    pub batch_size: usize,
    pub max_concurrent_requests: usize,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MonitoringConfig {
    pub metrics_port: u16,
    pub log_level: String,
    pub enable_tracing: bool,
}

impl AppConfig {
    pub fn from_env() -> Result<Self, Box<dyn std::error::Error>> {
        let config = AppConfig {
            server: ServerConfig {
                host: env::var("SERVER_HOST").unwrap_or_else(|_| "0.0.0.0".to_string()),
                port: env::var("SERVER_PORT")?.parse()?,
                workers: env::var("SERVER_WORKERS")?.parse()?,
            },
            database: DatabaseConfig {
                url: env::var("DATABASE_URL")?,
                max_connections: env::var("DATABASE_MAX_CONNECTIONS")?.parse()?,
                timeout: env::var("DATABASE_TIMEOUT")?.parse()?,
            },
            redis: RedisConfig {
                url: env::var("REDIS_URL")?,
                max_connections: env::var("REDIS_MAX_CONNECTIONS")?.parse()?,
            },
            ai: AIConfig {
                model_path: env::var("AI_MODEL_PATH")?,
                batch_size: env::var("AI_BATCH_SIZE")?.parse()?,
                max_concurrent_requests: env::var("AI_MAX_CONCURRENT_REQUESTS")?.parse()?,
            },
            monitoring: MonitoringConfig {
                metrics_port: env::var("METRICS_PORT")?.parse()?,
                log_level: env::var("LOG_LEVEL").unwrap_or_else(|_| "info".to_string()),
                enable_tracing: env::var("ENABLE_TRACING")?.parse()?,
            },
        };
        Ok(config)
    }
}
```

## 监控和日志

### 1. 指标收集

```rust
use metrics::{counter, histogram, gauge};
use metrics_exporter_prometheus::PrometheusBuilder;
use std::time::Instant;

pub struct MetricsCollector {
    request_counter: counter!(),
    request_duration: histogram!(),
    active_connections: gauge!(),
}

impl MetricsCollector {
    pub fn new() -> Result<Self, Box<dyn std::error::Error>> {
        // 初始化Prometheus导出器
        let builder = PrometheusBuilder::new();
        builder.install()?;
        
        Ok(Self {
            request_counter: counter!("requests_total"),
            request_duration: histogram!("request_duration_seconds"),
            active_connections: gauge!("active_connections"),
        })
    }
    
    pub fn record_request(&self, duration: std::time::Duration) {
        self.request_counter.increment(1.0);
        self.request_duration.record(duration.as_secs_f64());
    }
    
    pub fn update_connections(&self, count: f64) {
        self.active_connections.set(count);
    }
}
```

### 2. 日志管理

```rust
use tracing::{info, warn, error, instrument};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

pub fn init_logging() -> Result<(), Box<dyn std::error::Error>> {
    tracing_subscriber::registry()
        .with(
            tracing_subscriber::EnvFilter::try_from_default_env()
                .unwrap_or_else(|_| "info".into()),
        )
        .with(tracing_subscriber::fmt::layer())
        .init();
    
    Ok(())
}

#[instrument]
pub async fn process_request(request_id: &str, data: &str) -> Result<String, Box<dyn std::error::Error>> {
    info!("开始处理请求: {}", request_id);
    
    // 处理逻辑
    let result = perform_ai_inference(data).await?;
    
    info!("请求处理完成: {}", request_id);
    Ok(result)
}

async fn perform_ai_inference(data: &str) -> Result<String, Box<dyn std::error::Error>> {
    // AI推理逻辑
    Ok("inference_result".to_string())
}
```

### 3. 健康检查

```rust
use axum::{
    extract::State,
    http::StatusCode,
    response::Json,
    routing::get,
    Router,
};
use serde_json::{json, Value};
use std::sync::Arc;

pub struct HealthChecker {
    database_healthy: bool,
    redis_healthy: bool,
    ai_model_loaded: bool,
}

impl HealthChecker {
    pub fn new() -> Self {
        Self {
            database_healthy: false,
            redis_healthy: false,
            ai_model_loaded: false,
        }
    }
    
    pub async fn check_database(&mut self) -> bool {
        // 检查数据库连接
        self.database_healthy = true; // 实际实现中检查数据库
        self.database_healthy
    }
    
    pub async fn check_redis(&mut self) -> bool {
        // 检查Redis连接
        self.redis_healthy = true; // 实际实现中检查Redis
        self.redis_healthy
    }
    
    pub async fn check_ai_model(&mut self) -> bool {
        // 检查AI模型是否加载
        self.ai_model_loaded = true; // 实际实现中检查模型
        self.ai_model_loaded
    }
    
    pub fn is_healthy(&self) -> bool {
        self.database_healthy && self.redis_healthy && self.ai_model_loaded
    }
}

pub async fn health_check(State(health_checker): State<Arc<HealthChecker>>) -> (StatusCode, Json<Value>) {
    let is_healthy = health_checker.is_healthy();
    let status = if is_healthy {
        StatusCode::OK
    } else {
        StatusCode::SERVICE_UNAVAILABLE
    };
    
    let response = json!({
        "status": if is_healthy { "healthy" } else { "unhealthy" },
        "database": health_checker.database_healthy,
        "redis": health_checker.redis_healthy,
        "ai_model": health_checker.ai_model_loaded,
        "timestamp": chrono::Utc::now().to_rfc3339(),
    });
    
    (status, Json(response))
}
```

## 部署策略

### 1. 蓝绿部署

```bash
#!/bin/bash
# 蓝绿部署脚本

# 部署新版本到绿色环境
echo "部署新版本到绿色环境..."
kubectl apply -f green-deployment.yaml

# 等待绿色环境就绪
echo "等待绿色环境就绪..."
kubectl wait --for=condition=available --timeout=300s deployment/ai-service-green

# 切换流量到绿色环境
echo "切换流量到绿色环境..."
kubectl patch service ai-service -p '{"spec":{"selector":{"version":"green"}}}'

# 验证新版本
echo "验证新版本..."
curl -f http://ai-service/health || exit 1

# 清理蓝色环境
echo "清理蓝色环境..."
kubectl delete deployment ai-service-blue

echo "蓝绿部署完成"
```

### 2. 滚动更新

```yaml
# rolling-update.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: ai-service
spec:
  strategy:
    type: RollingUpdate
    rollingUpdate:
      maxUnavailable: 1
      maxSurge: 1
  replicas: 3
  selector:
    matchLabels:
      app: ai-service
  template:
    metadata:
      labels:
        app: ai-service
    spec:
      containers:
      - name: ai-service
        image: ai-service:v2.0.0
        ports:
        - containerPort: 8080
```

### 3. 金丝雀部署

```yaml
# canary-deployment.yaml
apiVersion: argoproj.io/v1alpha1
kind: Rollout
metadata:
  name: ai-service
spec:
  replicas: 5
  strategy:
    canary:
      steps:
      - setWeight: 20
      - pause: {duration: 10m}
      - setWeight: 40
      - pause: {duration: 10m}
      - setWeight: 60
      - pause: {duration: 10m}
      - setWeight: 80
      - pause: {duration: 10m}
  selector:
    matchLabels:
      app: ai-service
  template:
    metadata:
      labels:
        app: ai-service
    spec:
      containers:
      - name: ai-service
        image: ai-service:v2.0.0
        ports:
        - containerPort: 8080
```

## 性能优化

### 1. 资源管理

```yaml
# resource-management.yaml
apiVersion: v1
kind: ResourceQuota
metadata:
  name: ai-service-quota
spec:
  hard:
    requests.cpu: "4"
    requests.memory: 8Gi
    limits.cpu: "8"
    limits.memory: 16Gi
    persistentvolumeclaims: "10"
---
apiVersion: v1
kind: LimitRange
metadata:
  name: ai-service-limits
spec:
  limits:
  - default:
      cpu: "500m"
      memory: "1Gi"
    defaultRequest:
      cpu: "250m"
      memory: "512Mi"
    type: Container
```

### 2. 自动扩缩容

```yaml
# hpa.yaml
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: ai-service-hpa
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: ai-service
  minReplicas: 2
  maxReplicas: 10
  metrics:
  - type: Resource
    resource:
      name: cpu
      target:
        type: Utilization
        averageUtilization: 70
  - type: Resource
    resource:
      name: memory
      target:
        type: Utilization
        averageUtilization: 80
```

## 最佳实践

### 1. 部署前检查

- 代码质量检查
- 安全漏洞扫描
- 性能测试
- 依赖更新检查
- 配置验证

### 2. 部署过程

- 使用版本控制
- 自动化部署
- 渐进式发布
- 回滚准备
- 监控告警

### 3. 部署后

- 健康检查
- 性能监控
- 日志分析
- 用户反馈
- 持续优化

## 相关资源

- [Rust生产部署指南](https://github.com/rust-ai/rust-production-guide)
- [Kubernetes部署最佳实践](https://github.com/rust-ai/k8s-deployment-guide)
- [监控和日志管理](https://github.com/rust-ai/monitoring-guide)
- [性能优化策略](https://github.com/rust-ai/production-optimization)
