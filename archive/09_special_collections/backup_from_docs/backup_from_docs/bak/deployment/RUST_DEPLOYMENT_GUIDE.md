# 🦀 Rust部署指南

**创建时间**: 2025年9月25日
**版本**: 1.0.0
**适用对象**: 所有Rust开发者

---

## 📋 目录

- [🦀 Rust部署指南](#-rust部署指南)
  - [📋 目录](#-目录)
  - [🎯 部署概述](#-部署概述)
  - [🐳 Docker部署](#-docker部署)
  - [☸️ Kubernetes部署](#️-kubernetes部署)
  - [🌐 云平台部署](#-云平台部署)
  - [📦 包管理部署](#-包管理部署)
  - [🔧 环境配置](#-环境配置)
  - [📊 部署监控](#-部署监控)
  - [📝 最佳实践](#-最佳实践)

---

## 🎯 部署概述

### 部署目标

1. **可靠性**: 确保部署的可靠性
2. **可扩展性**: 支持水平扩展
3. **安全性**: 保证部署安全
4. **可维护性**: 便于维护和更新
5. **监控性**: 提供完整的监控

### 部署策略

- **蓝绿部署**: 零停机部署
- **滚动部署**: 渐进式部署
- **金丝雀部署**: 风险控制部署
- **A/B测试**: 功能验证部署

---

## 🐳 Docker部署

### Dockerfile优化

```dockerfile
# 多阶段构建
FROM rust:1.70-slim as builder

# 设置工作目录
WORKDIR /app

# 安装系统依赖
RUN apt-get update && apt-get install -y \
    pkg-config \
    libssl-dev \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

# 复制Cargo文件
COPY Cargo.toml Cargo.lock ./

# 构建依赖
RUN cargo build --release

# 复制源代码
COPY src ./src

# 构建应用
RUN cargo build --release

# 运行时镜像
FROM debian:bookworm-slim

# 安装运行时依赖
RUN apt-get update && apt-get install -y \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

# 创建非root用户
RUN groupadd -r appuser && useradd -r -g appuser appuser

# 复制二进制文件
COPY --from=builder /app/target/release/my-app /usr/local/bin/my-app

# 设置权限
RUN chown appuser:appuser /usr/local/bin/my-app

# 切换到非root用户
USER appuser

# 暴露端口
EXPOSE 8080

# 健康检查
HEALTHCHECK --interval=30s --timeout=3s --start-period=5s --retries=3 \
    CMD curl -f http://localhost:8080/health || exit 1

# 启动命令
CMD ["my-app"]
```

### Docker Compose配置

```yaml
# docker-compose.yml
version: '3.8'

services:
  app:
    build: .
    ports:
      - "8080:8080"
    environment:
      - RUST_LOG=info
      - DATABASE_URL=postgresql://user:password@db:5432/mydb
    depends_on:
      - db
      - redis
    volumes:
      - ./config:/app/config:ro
    restart: unless-stopped
    healthcheck:
      test: ["CMD", "curl", "-f", "http://localhost:8080/health"]
      interval: 30s
      timeout: 10s
      retries: 3
      start_period: 40s

  db:
    image: postgres:15-alpine
    environment:
      - POSTGRES_DB=mydb
      - POSTGRES_USER=user
      - POSTGRES_PASSWORD=password
    volumes:
      - postgres_data:/var/lib/postgresql/data
    ports:
      - "5432:5432"
    restart: unless-stopped

  redis:
    image: redis:7-alpine
    ports:
      - "6379:6379"
    volumes:
      - redis_data:/data
    restart: unless-stopped

  nginx:
    image: nginx:alpine
    ports:
      - "80:80"
      - "443:443"
    volumes:
      - ./nginx.conf:/etc/nginx/nginx.conf:ro
      - ./ssl:/etc/nginx/ssl:ro
    depends_on:
      - app
    restart: unless-stopped

volumes:
  postgres_data:
  redis_data:
```

### Docker部署脚本

```bash
#!/bin/bash
# scripts/docker-deploy.sh

set -e

echo "Starting Docker deployment..."

# 配置变量
IMAGE_NAME="my-app"
IMAGE_TAG="latest"
REGISTRY_URL="registry.example.com"
NAMESPACE="production"

# 构建Docker镜像
build_image() {
    echo "Building Docker image..."
    docker build -t ${IMAGE_NAME}:${IMAGE_TAG} .
    echo "Docker image built successfully"
}

# 标记镜像
tag_image() {
    echo "Tagging Docker image..."
    docker tag ${IMAGE_NAME}:${IMAGE_TAG} ${REGISTRY_URL}/${NAMESPACE}/${IMAGE_NAME}:${IMAGE_TAG}
    echo "Docker image tagged successfully"
}

# 推送镜像
push_image() {
    echo "Pushing Docker image..."
    docker push ${REGISTRY_URL}/${NAMESPACE}/${IMAGE_NAME}:${IMAGE_TAG}
    echo "Docker image pushed successfully"
}

# 部署到Docker Compose
deploy_compose() {
    echo "Deploying with Docker Compose..."
    docker-compose down
    docker-compose pull
    docker-compose up -d
    echo "Docker Compose deployment completed"
}

# 健康检查
health_check() {
    echo "Performing health check..."

    # 等待服务启动
    sleep 30

    # 检查服务状态
    docker-compose ps

    # 检查应用健康状态
    curl -f http://localhost:8080/health || {
        echo "Health check failed"
        exit 1
    }

    echo "Health check passed"
}

# 清理旧镜像
cleanup() {
    echo "Cleaning up old images..."
    docker image prune -f
    echo "Cleanup completed"
}

# 主函数
main() {
    build_image
    tag_image
    push_image
    deploy_compose
    health_check
    cleanup

    echo "Docker deployment completed successfully!"
}

main "$@"
```

---

## ☸️ Kubernetes部署

### Kubernetes配置文件

```yaml
# k8s/namespace.yaml
apiVersion: v1
kind: Namespace
metadata:
  name: my-app
  labels:
    name: my-app
```

```yaml
# k8s/configmap.yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: my-app-config
  namespace: my-app
data:
  RUST_LOG: "info"
  DATABASE_URL: "postgresql://user:password@postgres:5432/mydb"
  REDIS_URL: "redis://redis:6379"
```

```yaml
# k8s/secret.yaml
apiVersion: v1
kind: Secret
metadata:
  name: my-app-secret
  namespace: my-app
type: Opaque
data:
  database-password: cGFzc3dvcmQ=  # base64 encoded
  api-key: YWJjZGVmZ2hpams=  # base64 encoded
```

```yaml
# k8s/deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: my-app
  namespace: my-app
  labels:
    app: my-app
spec:
  replicas: 3
  selector:
    matchLabels:
      app: my-app
  template:
    metadata:
      labels:
        app: my-app
    spec:
      containers:
      - name: my-app
        image: registry.example.com/production/my-app:latest
        ports:
        - containerPort: 8080
        env:
        - name: RUST_LOG
          valueFrom:
            configMapKeyRef:
              name: my-app-config
              key: RUST_LOG
        - name: DATABASE_URL
          valueFrom:
            configMapKeyRef:
              name: my-app-config
              key: DATABASE_URL
        - name: DATABASE_PASSWORD
          valueFrom:
            secretKeyRef:
              name: my-app-secret
              key: database-password
        resources:
          requests:
            memory: "128Mi"
            cpu: "100m"
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
        securityContext:
          runAsNonRoot: true
          runAsUser: 1000
          allowPrivilegeEscalation: false
          readOnlyRootFilesystem: true
          capabilities:
            drop:
            - ALL
```

```yaml
# k8s/service.yaml
apiVersion: v1
kind: Service
metadata:
  name: my-app-service
  namespace: my-app
  labels:
    app: my-app
spec:
  selector:
    app: my-app
  ports:
  - protocol: TCP
    port: 80
    targetPort: 8080
  type: ClusterIP
```

```yaml
# k8s/ingress.yaml
apiVersion: networking.k8s.io/v1
kind: Ingress
metadata:
  name: my-app-ingress
  namespace: my-app
  annotations:
    nginx.ingress.kubernetes.io/rewrite-target: /
    nginx.ingress.kubernetes.io/ssl-redirect: "true"
    cert-manager.io/cluster-issuer: "letsencrypt-prod"
spec:
  tls:
  - hosts:
    - my-app.example.com
    secretName: my-app-tls
  rules:
  - host: my-app.example.com
    http:
      paths:
      - path: /
        pathType: Prefix
        backend:
          service:
            name: my-app-service
            port:
              number: 80
```

### Kubernetes部署脚本

```bash
#!/bin/bash
# scripts/k8s-deploy.sh

set -e

echo "Starting Kubernetes deployment..."

# 配置变量
NAMESPACE="my-app"
IMAGE_NAME="my-app"
IMAGE_TAG="latest"
REGISTRY_URL="registry.example.com"

# 创建命名空间
create_namespace() {
    echo "Creating namespace..."
    kubectl apply -f k8s/namespace.yaml
    echo "Namespace created"
}

# 部署配置
deploy_config() {
    echo "Deploying configuration..."
    kubectl apply -f k8s/configmap.yaml
    kubectl apply -f k8s/secret.yaml
    echo "Configuration deployed"
}

# 部署应用
deploy_application() {
    echo "Deploying application..."

    # 更新镜像标签
    kubectl set image deployment/my-app my-app=${REGISTRY_URL}/${NAMESPACE}/${IMAGE_NAME}:${IMAGE_TAG} -n ${NAMESPACE}

    # 等待部署完成
    kubectl rollout status deployment/my-app -n ${NAMESPACE}

    echo "Application deployed"
}

# 部署服务
deploy_services() {
    echo "Deploying services..."
    kubectl apply -f k8s/service.yaml
    kubectl apply -f k8s/ingress.yaml
    echo "Services deployed"
}

# 健康检查
health_check() {
    echo "Performing health check..."

    # 等待Pod就绪
    kubectl wait --for=condition=ready pod -l app=my-app -n ${NAMESPACE} --timeout=300s

    # 检查Pod状态
    kubectl get pods -n ${NAMESPACE}

    # 检查服务状态
    kubectl get services -n ${NAMESPACE}

    echo "Health check completed"
}

# 滚动更新
rolling_update() {
    echo "Performing rolling update..."

    # 触发滚动更新
    kubectl rollout restart deployment/my-app -n ${NAMESPACE}

    # 等待更新完成
    kubectl rollout status deployment/my-app -n ${NAMESPACE}

    echo "Rolling update completed"
}

# 回滚
rollback() {
    echo "Performing rollback..."

    # 回滚到上一个版本
    kubectl rollout undo deployment/my-app -n ${NAMESPACE}

    # 等待回滚完成
    kubectl rollout status deployment/my-app -n ${NAMESPACE}

    echo "Rollback completed"
}

# 主函数
main() {
    create_namespace
    deploy_config
    deploy_application
    deploy_services
    health_check

    echo "Kubernetes deployment completed successfully!"
}

# 处理命令行参数
case "${1:-deploy}" in
    "deploy")
        main
        ;;
    "update")
        rolling_update
        ;;
    "rollback")
        rollback
        ;;
    *)
        echo "Usage: $0 {deploy|update|rollback}"
        exit 1
        ;;
esac
```

---

## 🌐 云平台部署

### AWS ECS部署

```yaml
# aws/ecs-task-definition.json
{
  "family": "my-app",
  "networkMode": "awsvpc",
  "requiresCompatibilities": ["FARGATE"],
  "cpu": "256",
  "memory": "512",
  "executionRoleArn": "arn:aws:iam::123456789012:role/ecsTaskExecutionRole",
  "taskRoleArn": "arn:aws:iam::123456789012:role/ecsTaskRole",
  "containerDefinitions": [
    {
      "name": "my-app",
      "image": "123456789012.dkr.ecr.us-west-2.amazonaws.com/my-app:latest",
      "portMappings": [
        {
          "containerPort": 8080,
          "protocol": "tcp"
        }
      ],
      "essential": true,
      "environment": [
        {
          "name": "RUST_LOG",
          "value": "info"
        }
      ],
      "secrets": [
        {
          "name": "DATABASE_PASSWORD",
          "valueFrom": "arn:aws:secretsmanager:us-west-2:123456789012:secret:my-app/db-password"
        }
      ],
      "logConfiguration": {
        "logDriver": "awslogs",
        "options": {
          "awslogs-group": "/ecs/my-app",
          "awslogs-region": "us-west-2",
          "awslogs-stream-prefix": "ecs"
        }
      },
      "healthCheck": {
        "command": ["CMD-SHELL", "curl -f http://localhost:8080/health || exit 1"],
        "interval": 30,
        "timeout": 5,
        "retries": 3,
        "startPeriod": 60
      }
    }
  ]
}
```

### Google Cloud Run部署

```yaml
# gcp/cloud-run.yaml
apiVersion: serving.knative.dev/v1
kind: Service
metadata:
  name: my-app
  annotations:
    run.googleapis.com/ingress: all
    run.googleapis.com/execution-environment: gen2
spec:
  template:
    metadata:
      annotations:
        autoscaling.knative.dev/maxScale: "10"
        autoscaling.knative.dev/minScale: "1"
        run.googleapis.com/cpu-throttling: "false"
        run.googleapis.com/memory: "512Mi"
        run.googleapis.com/cpu: "1"
    spec:
      containerConcurrency: 100
      containers:
      - image: gcr.io/my-project/my-app:latest
        ports:
        - containerPort: 8080
        env:
        - name: RUST_LOG
          value: "info"
        - name: DATABASE_URL
          value: "postgresql://user:password@/db?host=/cloudsql/my-project:us-central1:my-db"
        resources:
          limits:
            cpu: "1"
            memory: "512Mi"
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
```

### Azure Container Instances部署

```yaml
# azure/container-instance.yaml
apiVersion: 2021-09-01
location: eastus
name: my-app
properties:
  containers:
  - name: my-app
    properties:
      image: myregistry.azurecr.io/my-app:latest
      ports:
      - port: 8080
        protocol: TCP
      environmentVariables:
      - name: RUST_LOG
        value: info
      - name: DATABASE_URL
        secureValue: postgresql://user:password@server.database.windows.net:1433/database
      resources:
        requests:
          cpu: 1.0
          memoryInGb: 1.0
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
  osType: Linux
  ipAddress:
    type: Public
    ports:
    - protocol: TCP
      port: 8080
  restartPolicy: Always
type: Microsoft.ContainerInstance/containerGroups
```

---

## 📦 包管理部署

### Cargo发布

```toml
# Cargo.toml
[package]
name = "my-app"
version = "0.1.0"
edition = "2024"
description = "My awesome Rust application"
license = "MIT"
repository = "https://github.com/user/my-app"
homepage = "https://my-app.example.com"
keywords = ["rust", "web", "api"]
categories = ["web-programming", "api-bindings"]

# 发布配置
[publish]
registry = "crates-io"

# 二进制目标
[[bin]]
name = "my-app"
path = "src/main.rs"

# 库目标
[lib]
name = "my_app"
path = "src/lib.rs"
```

### 发布脚本

```bash
#!/bin/bash
# scripts/publish.sh

set -e

echo "Starting package publication..."

# 检查版本
check_version() {
    echo "Checking version..."

    # 检查是否有未提交的更改
    if ! git diff-index --quiet HEAD --; then
        echo "Error: Uncommitted changes detected"
        exit 1
    fi

    # 检查版本号格式
    version=$(grep '^version = ' Cargo.toml | cut -d'"' -f2)
    if [[ ! $version =~ ^[0-9]+\.[0-9]+\.[0-9]+$ ]]; then
        echo "Error: Invalid version format: $version"
        exit 1
    fi

    echo "Version check passed: $version"
}

# 运行测试
run_tests() {
    echo "Running tests..."
    cargo test --all
    cargo test --doc
    echo "Tests passed"
}

# 检查代码质量
check_quality() {
    echo "Checking code quality..."
    cargo fmt -- --check
    cargo clippy --all -- -D warnings
    cargo audit
    echo "Quality check passed"
}

# 构建发布版本
build_release() {
    echo "Building release version..."
    cargo build --release
    echo "Release build completed"
}

# 发布到crates.io
publish_crates() {
    echo "Publishing to crates.io..."
    cargo publish --dry-run
    read -p "Continue with publication? (y/N): " -n 1 -r
    echo
    if [[ $REPLY =~ ^[Yy]$ ]]; then
        cargo publish
        echo "Published to crates.io"
    else
        echo "Publication cancelled"
        exit 1
    fi
}

# 创建Git标签
create_tag() {
    echo "Creating Git tag..."
    version=$(grep '^version = ' Cargo.toml | cut -d'"' -f2)
    git tag -a "v$version" -m "Release version $version"
    git push origin "v$version"
    echo "Git tag created: v$version"
}

# 主函数
main() {
    check_version
    run_tests
    check_quality
    build_release
    publish_crates
    create_tag

    echo "Package publication completed successfully!"
}

main "$@"
```

---

## 🔧 环境配置

### 环境变量管理

```rust
// src/config.rs
use serde::{Deserialize, Serialize};
use std::env;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Config {
    pub server: ServerConfig,
    pub database: DatabaseConfig,
    pub redis: RedisConfig,
    pub logging: LoggingConfig,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ServerConfig {
    pub host: String,
    pub port: u16,
    pub workers: Option<usize>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DatabaseConfig {
    pub url: String,
    pub max_connections: u32,
    pub min_connections: u32,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RedisConfig {
    pub url: String,
    pub max_connections: u32,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LoggingConfig {
    pub level: String,
    pub format: String,
}

impl Config {
    pub fn from_env() -> Result<Self, Box<dyn std::error::Error>> {
        Ok(Config {
            server: ServerConfig {
                host: env::var("SERVER_HOST").unwrap_or_else(|_| "0.0.0.0".to_string()),
                port: env::var("SERVER_PORT")
                    .unwrap_or_else(|_| "8080".to_string())
                    .parse()?,
                workers: env::var("SERVER_WORKERS")
                    .ok()
                    .map(|w| w.parse())
                    .transpose()?,
            },
            database: DatabaseConfig {
                url: env::var("DATABASE_URL")?,
                max_connections: env::var("DATABASE_MAX_CONNECTIONS")
                    .unwrap_or_else(|_| "10".to_string())
                    .parse()?,
                min_connections: env::var("DATABASE_MIN_CONNECTIONS")
                    .unwrap_or_else(|_| "1".to_string())
                    .parse()?,
            },
            redis: RedisConfig {
                url: env::var("REDIS_URL").unwrap_or_else(|_| "redis://localhost:6379".to_string()),
                max_connections: env::var("REDIS_MAX_CONNECTIONS")
                    .unwrap_or_else(|_| "10".to_string())
                    .parse()?,
            },
            logging: LoggingConfig {
                level: env::var("RUST_LOG").unwrap_or_else(|_| "info".to_string()),
                format: env::var("LOG_FORMAT").unwrap_or_else(|_| "json".to_string()),
            },
        })
    }
}
```

### 配置验证

```rust
// src/config_validation.rs
use crate::config::Config;
use std::collections::HashMap;

pub struct ConfigValidator {
    errors: Vec<String>,
    warnings: Vec<String>,
}

impl ConfigValidator {
    pub fn new() -> Self {
        Self {
            errors: Vec::new(),
            warnings: Vec::new(),
        }
    }

    pub fn validate(&mut self, config: &Config) -> ValidationResult {
        self.errors.clear();
        self.warnings.clear();

        self.validate_server_config(&config.server);
        self.validate_database_config(&config.database);
        self.validate_redis_config(&config.redis);
        self.validate_logging_config(&config.logging);

        ValidationResult {
            is_valid: self.errors.is_empty(),
            errors: self.errors.clone(),
            warnings: self.warnings.clone(),
        }
    }

    fn validate_server_config(&mut self, server: &crate::config::ServerConfig) {
        if server.port == 0 {
            self.errors.push("Server port cannot be 0".to_string());
        }

        if server.port > 65535 {
            self.errors.push("Server port cannot be greater than 65535".to_string());
        }

        if let Some(workers) = server.workers {
            if workers == 0 {
                self.warnings.push("Server workers is 0, using default".to_string());
            }

            if workers > 100 {
                self.warnings.push("Server workers is very high, consider reducing".to_string());
            }
        }
    }

    fn validate_database_config(&mut self, database: &crate::config::DatabaseConfig) {
        if database.url.is_empty() {
            self.errors.push("Database URL cannot be empty".to_string());
        }

        if database.max_connections < database.min_connections {
            self.errors.push("Database max connections cannot be less than min connections".to_string());
        }

        if database.max_connections > 100 {
            self.warnings.push("Database max connections is very high".to_string());
        }
    }

    fn validate_redis_config(&mut self, redis: &crate::config::RedisConfig) {
        if redis.url.is_empty() {
            self.errors.push("Redis URL cannot be empty".to_string());
        }

        if redis.max_connections > 50 {
            self.warnings.push("Redis max connections is very high".to_string());
        }
    }

    fn validate_logging_config(&mut self, logging: &crate::config::LoggingConfig) {
        let valid_levels = ["error", "warn", "info", "debug", "trace"];
        if !valid_levels.contains(&logging.level.as_str()) {
            self.errors.push(format!("Invalid log level: {}", logging.level));
        }

        let valid_formats = ["json", "pretty", "compact"];
        if !valid_formats.contains(&logging.format.as_str()) {
            self.errors.push(format!("Invalid log format: {}", logging.format));
        }
    }
}

#[derive(Debug, Clone)]
pub struct ValidationResult {
    pub is_valid: bool,
    pub errors: Vec<String>,
    pub warnings: Vec<String>,
}

impl ValidationResult {
    pub fn print_summary(&self) {
        if !self.errors.is_empty() {
            println!("Configuration Errors:");
            for error in &self.errors {
                println!("  ❌ {}", error);
            }
        }

        if !self.warnings.is_empty() {
            println!("Configuration Warnings:");
            for warning in &self.warnings {
                println!("  ⚠️  {}", warning);
            }
        }

        if self.is_valid {
            println!("✅ Configuration is valid");
        } else {
            println!("❌ Configuration has errors");
        }
    }
}
```

---

## 📊 部署监控

### 部署状态监控

```rust
// src/deployment_monitor.rs
use std::time::{Duration, Instant};
use std::collections::HashMap;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeploymentStatus {
    pub version: String,
    pub status: DeploymentState,
    pub timestamp: chrono::DateTime<chrono::Utc>,
    pub health_checks: Vec<HealthCheck>,
    pub metrics: DeploymentMetrics,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum DeploymentState {
    Deploying,
    Healthy,
    Unhealthy,
    RollingBack,
    Failed,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HealthCheck {
    pub name: String,
    pub status: HealthStatus,
    pub response_time: Duration,
    pub last_check: chrono::DateTime<chrono::Utc>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum HealthStatus {
    Healthy,
    Unhealthy,
    Unknown,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeploymentMetrics {
    pub cpu_usage: f64,
    pub memory_usage: f64,
    pub request_count: u64,
    pub error_rate: f64,
    pub response_time: Duration,
}

pub struct DeploymentMonitor {
    status: DeploymentStatus,
    health_checkers: HashMap<String, Box<dyn HealthChecker>>,
}

pub trait HealthChecker: Send + Sync {
    fn check(&self) -> Result<HealthCheck, Box<dyn std::error::Error>>;
    fn name(&self) -> &str;
}

impl DeploymentMonitor {
    pub fn new(version: String) -> Self {
        Self {
            status: DeploymentStatus {
                version,
                status: DeploymentState::Deploying,
                timestamp: chrono::Utc::now(),
                health_checks: Vec::new(),
                metrics: DeploymentMetrics {
                    cpu_usage: 0.0,
                    memory_usage: 0.0,
                    request_count: 0,
                    error_rate: 0.0,
                    response_time: Duration::from_millis(0),
                },
            },
            health_checkers: HashMap::new(),
        }
    }

    pub fn add_health_checker(&mut self, name: String, checker: Box<dyn HealthChecker>) {
        self.health_checkers.insert(name, checker);
    }

    pub async fn run_health_checks(&mut self) {
        let mut health_checks = Vec::new();

        for (_, checker) in &self.health_checkers {
            match checker.check() {
                Ok(check) => health_checks.push(check),
                Err(e) => {
                    health_checks.push(HealthCheck {
                        name: checker.name().to_string(),
                        status: HealthStatus::Unknown,
                        response_time: Duration::from_millis(0),
                        last_check: chrono::Utc::now(),
                    });
                    eprintln!("Health check failed for {}: {}", checker.name(), e);
                }
            }
        }

        self.status.health_checks = health_checks;
        self.update_status();
    }

    fn update_status(&mut self) {
        let healthy_checks = self.status.health_checks
            .iter()
            .filter(|check| matches!(check.status, HealthStatus::Healthy))
            .count();

        let total_checks = self.status.health_checks.len();

        if total_checks == 0 {
            self.status.status = DeploymentState::Unknown;
        } else if healthy_checks == total_checks {
            self.status.status = DeploymentState::Healthy;
        } else {
            self.status.status = DeploymentState::Unhealthy;
        }

        self.status.timestamp = chrono::Utc::now();
    }

    pub fn get_status(&self) -> &DeploymentStatus {
        &self.status
    }

    pub fn update_metrics(&mut self, metrics: DeploymentMetrics) {
        self.status.metrics = metrics;
    }
}

// HTTP健康检查器
pub struct HttpHealthChecker {
    name: String,
    url: String,
    timeout: Duration,
}

impl HttpHealthChecker {
    pub fn new(name: String, url: String, timeout: Duration) -> Self {
        Self { name, url, timeout }
    }
}

impl HealthChecker for HttpHealthChecker {
    fn check(&self) -> Result<HealthCheck, Box<dyn std::error::Error>> {
        let start = Instant::now();

        let client = reqwest::Client::builder()
            .timeout(self.timeout)
            .build()?;

        let response = client.get(&self.url).send()?;
        let response_time = start.elapsed();

        let status = if response.status().is_success() {
            HealthStatus::Healthy
        } else {
            HealthStatus::Unhealthy
        };

        Ok(HealthCheck {
            name: self.name.clone(),
            status,
            response_time,
            last_check: chrono::Utc::now(),
        })
    }

    fn name(&self) -> &str {
        &self.name
    }
}
```

---

## 📝 最佳实践

### 部署原则

1. **可靠性**: 确保部署的可靠性
2. **可重复性**: 部署过程可重复
3. **可回滚性**: 支持快速回滚
4. **监控性**: 提供完整监控
5. **安全性**: 保证部署安全

### 部署检查清单

- [ ] 容器化配置
- [ ] 环境变量配置
- [ ] 健康检查配置
- [ ] 监控配置
- [ ] 日志配置
- [ ] 安全配置
- [ ] 扩展配置
- [ ] 备份配置

### 维护建议

1. **定期更新**: 定期更新部署配置
2. **监控部署**: 监控部署状态
3. **优化配置**: 优化部署配置
4. **备份策略**: 建立备份策略
5. **团队培训**: 定期进行部署培训

---

-**遵循这些部署指南，您将能够建立可靠、可扩展的Rust应用程序部署体系！🦀**-
