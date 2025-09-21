# IoT部署和运维指南 - Rust 1.90

## 🎯 部署和运维概览

本文档详细介绍了基于Rust 1.90的IoT应用部署和运维策略，涵盖容器化、云平台部署、监控告警和故障排除等方面。

## 🐳 容器化部署

### 1. Docker配置优化

```dockerfile
# 多阶段构建优化
FROM rust:1.90-slim as builder

# 安装构建依赖
RUN apt-get update && apt-get install -y \
    pkg-config \
    libssl-dev \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /app

# 复制依赖文件
COPY Cargo.toml Cargo.lock ./

# 构建依赖（利用Docker缓存）
RUN cargo build --release --dependencies-only

# 复制源代码
COPY src ./src

# 构建应用
RUN cargo build --release

# 运行时镜像
FROM debian:bookworm-slim

# 安装运行时依赖
RUN apt-get update && apt-get install -y \
    ca-certificates \
    libssl3 \
    && rm -rf /var/lib/apt/lists/*

# 创建非root用户
RUN groupadd -r iot && useradd -r -g iot iot

# 复制二进制文件
COPY --from=builder /app/target/release/iot-app /usr/local/bin/iot-app

# 设置权限
RUN chown iot:iot /usr/local/bin/iot-app
USER iot

# 健康检查
HEALTHCHECK --interval=30s --timeout=3s --start-period=5s --retries=3 \
    CMD curl -f http://localhost:8080/health || exit 1

EXPOSE 8080

CMD ["iot-app"]
```

### 2. Docker Compose配置

```yaml
# docker-compose.yml
version: '3.8'

services:
  iot-app:
    build: .
    ports:
      - "8080:8080"
    environment:
      - RUST_LOG=info
      - DATABASE_URL=postgresql://user:pass@postgres:5432/iot_db
      - MQTT_BROKER=mqtt://mosquitto:1883
    depends_on:
      - postgres
      - mosquitto
      - redis
    volumes:
      - ./config:/app/config:ro
      - ./logs:/app/logs
    restart: unless-stopped
    deploy:
      resources:
        limits:
          memory: 512M
          cpus: '0.5'
        reservations:
          memory: 256M
          cpus: '0.25'

  postgres:
    image: postgres:15
    environment:
      - POSTGRES_DB=iot_db
      - POSTGRES_USER=user
      - POSTGRES_PASSWORD=pass
    volumes:
      - postgres_data:/var/lib/postgresql/data
      - ./init.sql:/docker-entrypoint-initdb.d/init.sql
    ports:
      - "5432:5432"
    restart: unless-stopped

  mosquitto:
    image: eclipse-mosquitto:2
    ports:
      - "1883:1883"
      - "9001:9001"
    volumes:
      - ./mosquitto.conf:/mosquitto/config/mosquitto.conf
      - mosquitto_data:/mosquitto/data
    restart: unless-stopped

  redis:
    image: redis:7-alpine
    ports:
      - "6379:6379"
    volumes:
      - redis_data:/data
    restart: unless-stopped

  prometheus:
    image: prom/prometheus:latest
    ports:
      - "9090:9090"
    volumes:
      - ./prometheus.yml:/etc/prometheus/prometheus.yml
      - prometheus_data:/prometheus
    command:
      - '--config.file=/etc/prometheus/prometheus.yml'
      - '--storage.tsdb.path=/prometheus'
      - '--web.console.libraries=/etc/prometheus/console_libraries'
      - '--web.console.templates=/etc/prometheus/consoles'
    restart: unless-stopped

  grafana:
    image: grafana/grafana:latest
    ports:
      - "3000:3000"
    environment:
      - GF_SECURITY_ADMIN_PASSWORD=admin
    volumes:
      - grafana_data:/var/lib/grafana
      - ./grafana/provisioning:/etc/grafana/provisioning
    restart: unless-stopped

volumes:
  postgres_data:
  mosquitto_data:
  redis_data:
  prometheus_data:
  grafana_data:
```

## ☁️ 云平台部署

### 1. Kubernetes部署

```yaml
# k8s-deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: iot-app
  labels:
    app: iot-app
spec:
  replicas: 3
  selector:
    matchLabels:
      app: iot-app
  template:
    metadata:
      labels:
        app: iot-app
    spec:
      containers:
      - name: iot-app
        image: iot-app:latest
        ports:
        - containerPort: 8080
        env:
        - name: RUST_LOG
          value: "info"
        - name: DATABASE_URL
          valueFrom:
            secretKeyRef:
              name: iot-secrets
              key: database-url
        - name: MQTT_BROKER
          valueFrom:
            configMapKeyRef:
              name: iot-config
              key: mqtt-broker
        resources:
          requests:
            memory: "256Mi"
            cpu: "250m"
          limits:
            memory: "512Mi"
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
        volumeMounts:
        - name: config-volume
          mountPath: /app/config
        - name: logs-volume
          mountPath: /app/logs
      volumes:
      - name: config-volume
        configMap:
          name: iot-config
      - name: logs-volume
        emptyDir: {}
      restartPolicy: Always

---
apiVersion: v1
kind: Service
metadata:
  name: iot-app-service
spec:
  selector:
    app: iot-app
  ports:
  - port: 80
    targetPort: 8080
  type: LoadBalancer

---
apiVersion: v1
kind: ConfigMap
metadata:
  name: iot-config
data:
  mqtt-broker: "mqtt://mqtt-broker:1883"
  redis-url: "redis://redis:6379"
  config.toml: |
    [device]
    id = "gateway_001"
    location = "cloud"
    
    [communication]
    keep_alive = 60
    qos = 1
    
    [storage]
    batch_size = 1000
    flush_interval = 30

---
apiVersion: v1
kind: Secret
metadata:
  name: iot-secrets
type: Opaque
data:
  database-url: cG9zdGdyZXNxbDovL3VzZXI6cGFzc0BkYjo1NDMyL2lvdF9kYg==
  api-key: YWJjZGVmZ2hpams=
```

### 2. Helm Chart配置

```yaml
# Chart.yaml
apiVersion: v2
name: iot-app
description: IoT Application Helm Chart
type: application
version: 0.1.0
appVersion: "1.0.0"

# values.yaml
replicaCount: 3

image:
  repository: iot-app
  tag: latest
  pullPolicy: IfNotPresent

service:
  type: LoadBalancer
  port: 80
  targetPort: 8080

ingress:
  enabled: true
  className: nginx
  annotations:
    nginx.ingress.kubernetes.io/rewrite-target: /
  hosts:
    - host: iot.example.com
      paths:
        - path: /
          pathType: Prefix

resources:
  limits:
    cpu: 500m
    memory: 512Mi
  requests:
    cpu: 250m
    memory: 256Mi

autoscaling:
  enabled: true
  minReplicas: 3
  maxReplicas: 10
  targetCPUUtilizationPercentage: 70
  targetMemoryUtilizationPercentage: 80

nodeSelector: {}

tolerations: []

affinity: {}

# templates/deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: {{ include "iot-app.fullname" . }}
  labels:
    {{- include "iot-app.labels" . | nindent 4 }}
spec:
  replicas: {{ .Values.replicaCount }}
  selector:
    matchLabels:
      {{- include "iot-app.selectorLabels" . | nindent 6 }}
  template:
    metadata:
      labels:
        {{- include "iot-app.selectorLabels" . | nindent 8 }}
    spec:
      containers:
        - name: {{ .Chart.Name }}
          image: "{{ .Values.image.repository }}:{{ .Values.image.tag }}"
          imagePullPolicy: {{ .Values.image.pullPolicy }}
          ports:
            - name: http
              containerPort: {{ .Values.service.targetPort }}
              protocol: TCP
          livenessProbe:
            httpGet:
              path: /health
              port: http
          readinessProbe:
            httpGet:
              path: /ready
              port: http
          resources:
            {{- toYaml .Values.resources | nindent 12 }}
```

## 📊 监控和告警

### 1. Prometheus配置

```yaml
# prometheus.yml
global:
  scrape_interval: 15s
  evaluation_interval: 15s

rule_files:
  - "iot-alerts.yml"

alerting:
  alertmanagers:
    - static_configs:
        - targets:
          - alertmanager:9093

scrape_configs:
  - job_name: 'iot-app'
    static_configs:
      - targets: ['iot-app:8080']
    metrics_path: /metrics
    scrape_interval: 5s

  - job_name: 'postgres'
    static_configs:
      - targets: ['postgres-exporter:9187']

  - job_name: 'redis'
    static_configs:
      - targets: ['redis-exporter:9121']

  - job_name: 'node'
    static_configs:
      - targets: ['node-exporter:9100']
```

### 2. 告警规则

```yaml
# iot-alerts.yml
groups:
- name: iot-alerts
  rules:
  - alert: HighTemperature
    expr: iot_temperature_celsius > 35
    for: 5m
    labels:
      severity: warning
    annotations:
      summary: "设备温度过高"
      description: "设备 {{ $labels.device_id }} 温度达到 {{ $value }}°C"

  - alert: DeviceOffline
    expr: up{job="iot-app"} == 0
    for: 1m
    labels:
      severity: critical
    annotations:
      summary: "设备离线"
      description: "设备 {{ $labels.device_id }} 已离线超过1分钟"

  - alert: HighErrorRate
    expr: rate(iot_errors_total[5m]) > 0.1
    for: 2m
    labels:
      severity: warning
    annotations:
      summary: "错误率过高"
      description: "设备 {{ $labels.device_id }} 错误率达到 {{ $value }}"

  - alert: HighMemoryUsage
    expr: (process_resident_memory_bytes / 1024 / 1024) > 400
    for: 5m
    labels:
      severity: warning
    annotations:
      summary: "内存使用过高"
      description: "应用内存使用达到 {{ $value }}MB"

  - alert: HighCPUUsage
    expr: rate(process_cpu_seconds_total[5m]) > 0.8
    for: 5m
    labels:
      severity: warning
    annotations:
      summary: "CPU使用过高"
      description: "应用CPU使用率达到 {{ $value }}"
```

### 3. Grafana仪表盘

```json
{
  "dashboard": {
    "title": "IoT应用监控",
    "panels": [
      {
        "title": "请求速率",
        "type": "graph",
        "targets": [
          {
            "expr": "rate(iot_requests_total[5m])",
            "legendFormat": "{{device_id}}"
          }
        ]
      },
      {
        "title": "响应时间",
        "type": "graph",
        "targets": [
          {
            "expr": "histogram_quantile(0.95, rate(iot_request_duration_seconds_bucket[5m]))",
            "legendFormat": "95th percentile"
          }
        ]
      },
      {
        "title": "设备状态",
        "type": "stat",
        "targets": [
          {
            "expr": "count(up{job=\"iot-app\"})",
            "legendFormat": "在线设备"
          }
        ]
      }
    ]
  }
}
```

## 🔧 运维自动化

### 1. 健康检查实现

```rust
use axum::{response::Json, routing::get, Router};
use serde_json::{json, Value};
use std::sync::Arc;
use tokio::sync::RwLock;

pub struct HealthChecker {
    database: Arc<DatabaseClient>,
    mqtt: Arc<MqttClient>,
    redis: Arc<RedisClient>,
    start_time: std::time::Instant,
}

impl HealthChecker {
    pub fn new(
        database: Arc<DatabaseClient>,
        mqtt: Arc<MqttClient>,
        redis: Arc<RedisClient>,
    ) -> Self {
        Self {
            database,
            mqtt,
            redis,
            start_time: std::time::Instant::now(),
        }
    }
    
    pub async fn health_check(&self) -> Json<Value> {
        let uptime = self.start_time.elapsed();
        
        Json(json!({
            "status": "healthy",
            "timestamp": chrono::Utc::now(),
            "uptime_seconds": uptime.as_secs(),
            "version": env!("CARGO_PKG_VERSION"),
            "components": {
                "database": self.check_database().await,
                "mqtt": self.check_mqtt().await,
                "redis": self.check_redis().await
            }
        }))
    }
    
    pub async fn readiness_check(&self) -> Json<Value> {
        let database_healthy = self.check_database().await;
        let mqtt_healthy = self.check_mqtt().await;
        let redis_healthy = self.check_redis().await;
        
        let all_healthy = database_healthy && mqtt_healthy && redis_healthy;
        
        Json(json!({
            "status": if all_healthy { "ready" } else { "not_ready" },
            "components": {
                "database": database_healthy,
                "mqtt": mqtt_healthy,
                "redis": redis_healthy
            }
        }))
    }
    
    async fn check_database(&self) -> bool {
        match self.database.ping().await {
            Ok(_) => true,
            Err(_) => false,
        }
    }
    
    async fn check_mqtt(&self) -> bool {
        match self.mqtt.is_connected().await {
            Ok(connected) => connected,
            Err(_) => false,
        }
    }
    
    async fn check_redis(&self) -> bool {
        match self.redis.ping().await {
            Ok(_) => true,
            Err(_) => false,
        }
    }
}

pub fn create_health_router(health_checker: Arc<HealthChecker>) -> Router {
    Router::new()
        .route("/health", get({
            let checker = Arc::clone(&health_checker);
            move || async move { checker.health_check().await }
        }))
        .route("/ready", get({
            let checker = Arc::clone(&health_checker);
            move || async move { checker.readiness_check().await }
        }))
}
```

### 2. 自动扩缩容

```rust
use std::sync::Arc;
use tokio::sync::RwLock;
use std::time::Duration;

pub struct AutoScaler {
    metrics: Arc<PerformanceMetrics>,
    current_replicas: Arc<RwLock<u32>>,
    min_replicas: u32,
    max_replicas: u32,
    scale_up_threshold: f64,
    scale_down_threshold: f64,
}

impl AutoScaler {
    pub fn new(
        min_replicas: u32,
        max_replicas: u32,
        scale_up_threshold: f64,
        scale_down_threshold: f64,
    ) -> Self {
        Self {
            metrics: Arc::new(PerformanceMetrics::new()),
            current_replicas: Arc::new(RwLock::new(min_replicas)),
            min_replicas,
            max_replicas,
            scale_up_threshold,
            scale_down_threshold,
        }
    }
    
    pub async fn start_scaling(&self) {
        let mut interval = tokio::time::interval(Duration::from_secs(30));
        
        loop {
            interval.tick().await;
            
            let metrics = self.metrics.get_current_metrics().await;
            let current_replicas = *self.current_replicas.read().await;
            
            let should_scale_up = metrics.cpu_usage > self.scale_up_threshold
                || metrics.memory_usage > 0.8
                || metrics.request_queue_length > 100;
            
            let should_scale_down = metrics.cpu_usage < self.scale_down_threshold
                && metrics.memory_usage < 0.5
                && metrics.request_queue_length < 10;
            
            if should_scale_up && current_replicas < self.max_replicas {
                self.scale_up().await;
            } else if should_scale_down && current_replicas > self.min_replicas {
                self.scale_down().await;
            }
        }
    }
    
    async fn scale_up(&self) {
        let mut replicas = self.current_replicas.write().await;
        *replicas += 1;
        
        println!("扩缩容: 增加到 {} 个副本", *replicas);
        
        // 通知Kubernetes或其他编排系统
        self.notify_scaling_change(*replicas).await;
    }
    
    async fn scale_down(&self) {
        let mut replicas = self.current_replicas.write().await;
        *replicas -= 1;
        
        println!("扩缩容: 减少到 {} 个副本", *replicas);
        
        // 通知Kubernetes或其他编排系统
        self.notify_scaling_change(*replicas).await;
    }
    
    async fn notify_scaling_change(&self, replicas: u32) {
        // 实现通知逻辑，例如调用Kubernetes API
        println!("通知编排系统: 副本数量变更为 {}", replicas);
    }
}
```

## 🚨 故障排除

### 1. 日志分析

```rust
use tracing::{info, warn, error, instrument};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

pub struct LogAnalyzer {
    log_patterns: Vec<LogPattern>,
}

#[derive(Debug, Clone)]
pub struct LogPattern {
    pub name: String,
    pub pattern: regex::Regex,
    pub severity: LogSeverity,
    pub action: LogAction,
}

#[derive(Debug, Clone)]
pub enum LogSeverity {
    Info,
    Warning,
    Error,
    Critical,
}

#[derive(Debug, Clone)]
pub enum LogAction {
    Alert,
    Restart,
    Scale,
    Ignore,
}

impl LogAnalyzer {
    pub fn new() -> Self {
        Self {
            log_patterns: vec![
                LogPattern {
                    name: "Connection Error".to_string(),
                    pattern: regex::Regex::new(r"connection.*failed").unwrap(),
                    severity: LogSeverity::Error,
                    action: LogAction::Alert,
                },
                LogPattern {
                    name: "Memory Leak".to_string(),
                    pattern: regex::Regex::new(r"memory.*leak").unwrap(),
                    severity: LogSeverity::Critical,
                    action: LogAction::Restart,
                },
                LogPattern {
                    name: "High Load".to_string(),
                    pattern: regex::Regex::new(r"high.*load").unwrap(),
                    severity: LogSeverity::Warning,
                    action: LogAction::Scale,
                },
            ],
        }
    }
    
    pub async fn analyze_log_line(&self, line: &str) -> Option<LogAnalysisResult> {
        for pattern in &self.log_patterns {
            if pattern.pattern.is_match(line) {
                return Some(LogAnalysisResult {
                    pattern: pattern.clone(),
                    line: line.to_string(),
                    timestamp: chrono::Utc::now(),
                });
            }
        }
        None
    }
    
    pub async fn handle_log_result(&self, result: LogAnalysisResult) {
        match result.pattern.action {
            LogAction::Alert => {
                error!("检测到问题: {} - {}", result.pattern.name, result.line);
                self.send_alert(&result).await;
            }
            LogAction::Restart => {
                error!("需要重启: {} - {}", result.pattern.name, result.line);
                self.restart_service().await;
            }
            LogAction::Scale => {
                warn!("需要扩缩容: {} - {}", result.pattern.name, result.line);
                self.trigger_scaling().await;
            }
            LogAction::Ignore => {
                info!("忽略日志: {} - {}", result.pattern.name, result.line);
            }
        }
    }
    
    async fn send_alert(&self, result: &LogAnalysisResult) {
        // 发送告警通知
        println!("发送告警: {}", result.pattern.name);
    }
    
    async fn restart_service(&self) {
        // 重启服务
        println!("重启服务");
    }
    
    async fn trigger_scaling(&self) {
        // 触发扩缩容
        println!("触发扩缩容");
    }
}

#[derive(Debug, Clone)]
pub struct LogAnalysisResult {
    pub pattern: LogPattern,
    pub line: String,
    pub timestamp: chrono::DateTime<chrono::Utc>,
}
```

### 2. 故障恢复

```rust
use std::sync::Arc;
use tokio::sync::RwLock;
use std::time::Duration;

pub struct FailureRecovery {
    failure_count: Arc<RwLock<u32>>,
    last_failure: Arc<RwLock<Option<std::time::Instant>>>,
    recovery_strategies: Vec<RecoveryStrategy>,
}

#[derive(Debug, Clone)]
pub enum RecoveryStrategy {
    Retry { max_attempts: u32, delay: Duration },
    CircuitBreaker { failure_threshold: u32, timeout: Duration },
    Fallback { fallback_service: String },
    Restart { delay: Duration },
}

impl FailureRecovery {
    pub fn new() -> Self {
        Self {
            failure_count: Arc::new(RwLock::new(0)),
            last_failure: Arc::new(RwLock::new(None)),
            recovery_strategies: vec![
                RecoveryStrategy::Retry {
                    max_attempts: 3,
                    delay: Duration::from_secs(1),
                },
                RecoveryStrategy::CircuitBreaker {
                    failure_threshold: 5,
                    timeout: Duration::from_secs(60),
                },
                RecoveryStrategy::Fallback {
                    fallback_service: "backup-service".to_string(),
                },
                RecoveryStrategy::Restart {
                    delay: Duration::from_secs(30),
                },
            ],
        }
    }
    
    pub async fn handle_failure(&self, error: &str) -> Result<(), Box<dyn std::error::Error>> {
        let mut count = self.failure_count.write().await;
        *count += 1;
        
        let mut last_failure = self.last_failure.write().await;
        *last_failure = Some(std::time::Instant::now());
        
        println!("处理故障: {} (第{}次)", error, *count);
        
        // 应用恢复策略
        for strategy in &self.recovery_strategies {
            match strategy {
                RecoveryStrategy::Retry { max_attempts, delay } => {
                    if *count <= *max_attempts {
                        tokio::time::sleep(*delay).await;
                        return Ok(());
                    }
                }
                RecoveryStrategy::CircuitBreaker { failure_threshold, timeout } => {
                    if *count >= *failure_threshold {
                        println!("熔断器开启，等待 {} 秒", timeout.as_secs());
                        tokio::time::sleep(*timeout).await;
                        *count = 0; // 重置计数
                        return Ok(());
                    }
                }
                RecoveryStrategy::Fallback { fallback_service } => {
                    println!("使用备用服务: {}", fallback_service);
                    return self.call_fallback_service(fallback_service).await;
                }
                RecoveryStrategy::Restart { delay } => {
                    println!("准备重启服务，等待 {} 秒", delay.as_secs());
                    tokio::time::sleep(*delay).await;
                    return self.restart_service().await;
                }
            }
        }
        
        Ok(())
    }
    
    async fn call_fallback_service(&self, service: &str) -> Result<(), Box<dyn std::error::Error>> {
        // 调用备用服务
        println!("调用备用服务: {}", service);
        Ok(())
    }
    
    async fn restart_service(&self) -> Result<(), Box<dyn std::error::Error>> {
        // 重启服务
        println!("重启服务");
        Ok(())
    }
    
    pub async fn reset_failure_count(&self) {
        let mut count = self.failure_count.write().await;
        *count = 0;
    }
}
```

## 📋 运维检查清单

### 1. 部署前检查

- [ ] 代码质量检查通过
- [ ] 单元测试和集成测试通过
- [ ] 性能测试满足要求
- [ ] 安全扫描无高危漏洞
- [ ] 配置文件正确
- [ ] 依赖版本兼容
- [ ] 资源需求评估
- [ ] 备份策略确认

### 2. 部署后检查

- [ ] 服务健康检查通过
- [ ] 监控指标正常
- [ ] 日志输出正常
- [ ] 数据库连接正常
- [ ] 外部服务连接正常
- [ ] 性能指标符合预期
- [ ] 告警规则生效
- [ ] 备份任务正常

### 3. 日常运维检查

- [ ] 系统资源使用情况
- [ ] 应用性能指标
- [ ] 错误日志分析
- [ ] 安全事件检查
- [ ] 备份任务状态
- [ ] 证书有效期检查
- [ ] 依赖更新检查
- [ ] 容量规划评估

## 🔄 持续改进

### 1. 性能监控

- 定期分析性能指标
- 识别性能瓶颈
- 优化热点代码
- 调整资源配置

### 2. 安全更新

- 定期更新依赖库
- 监控安全漏洞
- 实施安全补丁
- 加强访问控制

### 3. 容量规划

- 监控资源使用趋势
- 预测容量需求
- 规划扩容方案
- 优化资源利用率

---

**IoT部署和运维指南** - 基于Rust 1.90的完整部署和运维解决方案 🦀🚀
