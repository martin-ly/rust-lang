# 🦀 部署自动化配置

**创建时间**: 2025年9月25日
**版本**: 1.0.0

---

## 📋 目录

- [🦀 部署自动化配置](#-部署自动化配置)
  - [📋 目录](#-目录)
  - [🎯 部署自动化概述](#-部署自动化概述)
  - [🚀 CI/CD集成](#-cicd集成)
  - [🐳 容器化部署](#-容器化部署)
  - [☸️ Kubernetes部署](#️-kubernetes部署)
  - [🌐 云平台部署](#-云平台部署)
  - [📊 部署监控](#-部署监控)
  - [📝 最佳实践](#-最佳实践)

---

## 🎯 部署自动化概述

### 自动化目标

1. **自动化部署**: 完全自动化的部署流程
2. **零停机部署**: 实现零停机时间部署
3. **快速回滚**: 支持快速回滚机制
4. **环境一致性**: 确保环境一致性
5. **部署监控**: 完整的部署监控

---

## 🚀 CI/CD集成

### GitHub Actions部署

```yaml
# .github/workflows/deploy.yml
name: Deploy to Production

on:
  push:
    branches: [ main ]
  workflow_dispatch:

env:
  REGISTRY: ghcr.io
  IMAGE_NAME: ${{ github.repository }}

jobs:
  build:
    runs-on: ubuntu-latest
    permissions:
      contents: read
      packages: write

    steps:
    - name: Checkout repository
      uses: actions/checkout@v3

    - name: Set up Docker Buildx
      uses: docker/setup-buildx-action@v2

    - name: Log in to Container Registry
      uses: docker/login-action@v2
      with:
        registry: ${{ env.REGISTRY }}
        username: ${{ github.actor }}
        password: ${{ secrets.GITHUB_TOKEN }}

    - name: Extract metadata
      id: meta
      uses: docker/metadata-action@v4
      with:
        images: ${{ env.REGISTRY }}/${{ env.IMAGE_NAME }}
        tags: |
          type=ref,event=branch
          type=ref,event=pr
          type=sha,prefix={{branch}}-
          type=raw,value=latest,enable={{is_default_branch}}

    - name: Build and push Docker image
      uses: docker/build-push-action@v4
      with:
        context: .
        push: true
        tags: ${{ steps.meta.outputs.tags }}
        labels: ${{ steps.meta.outputs.labels }}
        cache-from: type=gha
        cache-to: type=gha,mode=max

  deploy:
    needs: build
    runs-on: ubuntu-latest
    environment: production

    steps:
    - name: Checkout repository
      uses: actions/checkout@v3

    - name: Configure AWS credentials
      uses: aws-actions/configure-aws-credentials@v2
      with:
        aws-access-key-id: ${{ secrets.AWS_ACCESS_KEY_ID }}
        aws-secret-access-key: ${{ secrets.AWS_SECRET_ACCESS_KEY }}
        aws-region: us-west-2

    - name: Deploy to ECS
      run: |
        aws ecs update-service \
          --cluster my-cluster \
          --service my-service \
          --force-new-deployment

    - name: Wait for deployment
      run: |
        aws ecs wait services-stable \
          --cluster my-cluster \
          --services my-service

    - name: Verify deployment
      run: |
        # Health check
        curl -f https://my-app.example.com/health || exit 1
```

### GitLab CI/CD部署

```yaml
# .gitlab-ci.yml
stages:
  - test
  - build
  - deploy

variables:
  DOCKER_DRIVER: overlay2
  DOCKER_TLS_CERTDIR: "/certs"

test:
  stage: test
  image: rust:1.70
  script:
    - cargo test --all
    - cargo clippy --all -- -D warnings
    - cargo fmt -- --check
  artifacts:
    reports:
      junit: target/test-results/*.xml

build:
  stage: build
  image: docker:20.10.16
  services:
    - docker:20.10.16-dind
  script:
    - docker build -t $CI_REGISTRY_IMAGE:$CI_COMMIT_SHA .
    - docker push $CI_REGISTRY_IMAGE:$CI_COMMIT_SHA
  only:
    - main

deploy:
  stage: deploy
  image: bitnami/kubectl:latest
  script:
    - kubectl set image deployment/my-app my-app=$CI_REGISTRY_IMAGE:$CI_COMMIT_SHA
    - kubectl rollout status deployment/my-app
    - kubectl get pods -l app=my-app
  environment:
    name: production
    url: https://my-app.example.com
  only:
    - main
  when: manual
```

---

## 🐳 容器化部署

### Docker多阶段构建

```dockerfile
# Dockerfile.multi-stage
# 构建阶段
FROM rust:1.70-slim as builder

WORKDIR /app

# 安装系统依赖
RUN apt-get update && apt-get install -y \
    pkg-config \
    libssl-dev \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

# 复制Cargo文件
COPY Cargo.toml Cargo.lock ./

# 构建依赖（利用Docker缓存）
RUN mkdir src && \
    echo "fn main() {}" > src/main.rs && \
    cargo build --release && \
    rm -rf src

# 复制源代码
COPY src ./src

# 构建应用
RUN cargo build --release

# 运行时阶段
FROM debian:bookworm-slim

# 安装运行时依赖
RUN apt-get update && apt-get install -y \
    ca-certificates \
    curl \
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

### Docker Compose生产配置

```yaml
# docker-compose.prod.yml
version: '3.8'

services:
  app:
    build:
      context: .
      dockerfile: Dockerfile.multi-stage
    ports:
      - "8080:8080"
    environment:
      - RUST_LOG=info
      - DATABASE_URL=postgresql://user:${DB_PASSWORD}@db:5432/mydb
      - REDIS_URL=redis://redis:6379
    depends_on:
      db:
        condition: service_healthy
      redis:
        condition: service_started
    volumes:
      - ./config:/app/config:ro
    restart: unless-stopped
    healthcheck:
      test: ["CMD", "curl", "-f", "http://localhost:8080/health"]
      interval: 30s
      timeout: 10s
      retries: 3
      start_period: 40s
    deploy:
      replicas: 3
      resources:
        limits:
          cpus: '0.5'
          memory: 512M
        reservations:
          cpus: '0.25'
          memory: 256M
      restart_policy:
        condition: on-failure
        delay: 5s
        max_attempts: 3
        window: 120s

  db:
    image: postgres:15-alpine
    environment:
      - POSTGRES_DB=mydb
      - POSTGRES_USER=user
      - POSTGRES_PASSWORD=${DB_PASSWORD}
    volumes:
      - postgres_data:/var/lib/postgresql/data
      - ./init.sql:/docker-entrypoint-initdb.d/init.sql:ro
    ports:
      - "5432:5432"
    restart: unless-stopped
    healthcheck:
      test: ["CMD-SHELL", "pg_isready -U user -d mydb"]
      interval: 10s
      timeout: 5s
      retries: 5

  redis:
    image: redis:7-alpine
    ports:
      - "6379:6379"
    volumes:
      - redis_data:/data
    restart: unless-stopped
    healthcheck:
      test: ["CMD", "redis-cli", "ping"]
      interval: 10s
      timeout: 3s
      retries: 3

  nginx:
    image: nginx:alpine
    ports:
      - "80:80"
      - "443:443"
    volumes:
      - ./nginx/nginx.conf:/etc/nginx/nginx.conf:ro
      - ./nginx/ssl:/etc/nginx/ssl:ro
    depends_on:
      - app
    restart: unless-stopped

volumes:
  postgres_data:
  redis_data:
```

---

## ☸️ Kubernetes部署

### Helm Chart配置

```yaml
# helm/my-app/values.yaml
replicaCount: 3

image:
  repository: my-app
  pullPolicy: IfNotPresent
  tag: "latest"

service:
  type: ClusterIP
  port: 80
  targetPort: 8080

ingress:
  enabled: true
  className: "nginx"
  annotations:
    nginx.ingress.kubernetes.io/rewrite-target: /
    cert-manager.io/cluster-issuer: "letsencrypt-prod"
  hosts:
    - host: my-app.example.com
      paths:
        - path: /
          pathType: Prefix
  tls:
    - secretName: my-app-tls
      hosts:
        - my-app.example.com

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

env:
  - name: RUST_LOG
    value: "info"
  - name: DATABASE_URL
    valueFrom:
      secretKeyRef:
        name: my-app-secret
        key: database-url

configMap:
  data:
    app-config.yaml: |
      server:
        host: "0.0.0.0"
        port: 8080
      logging:
        level: "info"
        format: "json"
```

### Kubernetes部署脚本

```bash
#!/bin/bash
# scripts/k8s-deploy.sh

set -e

echo "Starting Kubernetes deployment..."

# 配置变量
NAMESPACE="my-app"
CHART_PATH="./helm/my-app"
RELEASE_NAME="my-app"
IMAGE_TAG="${1:-latest}"

# 创建命名空间
create_namespace() {
    echo "Creating namespace..."
    kubectl create namespace $NAMESPACE --dry-run=client -o yaml | kubectl apply -f -
    echo "Namespace created"
}

# 部署Secrets
deploy_secrets() {
    echo "Deploying secrets..."

    # 从环境变量创建secret
    kubectl create secret generic my-app-secret \
        --from-literal=database-url="$DATABASE_URL" \
        --from-literal=redis-url="$REDIS_URL" \
        --namespace=$NAMESPACE \
        --dry-run=client -o yaml | kubectl apply -f -

    echo "Secrets deployed"
}

# 部署ConfigMap
deploy_configmap() {
    echo "Deploying ConfigMap..."
    kubectl apply -f k8s/configmap.yaml
    echo "ConfigMap deployed"
}

# 使用Helm部署
deploy_with_helm() {
    echo "Deploying with Helm..."

    helm upgrade --install $RELEASE_NAME $CHART_PATH \
        --namespace $NAMESPACE \
        --set image.tag=$IMAGE_TAG \
        --set image.repository=$REGISTRY_URL/$NAMESPACE/my-app \
        --wait \
        --timeout=10m

    echo "Helm deployment completed"
}

# 等待部署完成
wait_for_deployment() {
    echo "Waiting for deployment to complete..."

    kubectl wait --for=condition=available \
        --timeout=300s \
        deployment/$RELEASE_NAME \
        -n $NAMESPACE

    echo "Deployment completed"
}

# 健康检查
health_check() {
    echo "Performing health check..."

    # 获取Pod状态
    kubectl get pods -n $NAMESPACE -l app.kubernetes.io/name=my-app

    # 检查服务状态
    kubectl get services -n $NAMESPACE

    # 检查Ingress状态
    kubectl get ingress -n $NAMESPACE

    echo "Health check completed"
}

# 回滚部署
rollback_deployment() {
    echo "Rolling back deployment..."

    helm rollback $RELEASE_NAME -n $NAMESPACE

    echo "Rollback completed"
}

# 主函数
main() {
    create_namespace
    deploy_secrets
    deploy_configmap
    deploy_with_helm
    wait_for_deployment
    health_check

    echo "Kubernetes deployment completed successfully!"
}

# 处理命令行参数
case "${1:-deploy}" in
    "deploy")
        main
        ;;
    "rollback")
        rollback_deployment
        ;;
    *)
        echo "Usage: $0 {deploy|rollback} [image-tag]"
        exit 1
        ;;
esac
```

---

## 🌐 云平台部署

### AWS ECS部署脚本

```bash
#!/bin/bash
# scripts/aws-deploy.sh

set -e

echo "Starting AWS ECS deployment..."

# 配置变量
CLUSTER_NAME="my-cluster"
SERVICE_NAME="my-service"
TASK_FAMILY="my-app"
REGION="us-west-2"

# 构建并推送镜像
build_and_push() {
    echo "Building and pushing Docker image..."

    # 获取AWS账户ID
    AWS_ACCOUNT_ID=$(aws sts get-caller-identity --query Account --output text)
    ECR_REGISTRY="$AWS_ACCOUNT_ID.dkr.ecr.$REGION.amazonaws.com"

    # 登录ECR
    aws ecr get-login-password --region $REGION | docker login --username AWS --password-stdin $ECR_REGISTRY

    # 构建镜像
    docker build -t $TASK_FAMILY .

    # 标记镜像
    docker tag $TASK_FAMILY:latest $ECR_REGISTRY/$TASK_FAMILY:latest

    # 推送镜像
    docker push $ECR_REGISTRY/$TASK_FAMILY:latest

    echo "Image built and pushed"
}

# 更新任务定义
update_task_definition() {
    echo "Updating task definition..."

    # 获取最新的任务定义
    TASK_DEFINITION=$(aws ecs describe-task-definition --task-definition $TASK_FAMILY --region $REGION)

    # 更新镜像URI
    NEW_TASK_DEFINITION=$(echo $TASK_DEFINITION | jq --arg IMAGE "$ECR_REGISTRY/$TASK_FAMILY:latest" '.taskDefinition.containerDefinitions[0].image = $IMAGE | del(.taskDefinition.taskDefinitionArn) | del(.taskDefinition.revision) | del(.taskDefinition.status) | del(.taskDefinition.requiresAttributes) | del(.taskDefinition.placementConstraints) | del(.taskDefinition.compatibilities) | del(.taskDefinition.registeredAt) | del(.taskDefinition.registeredBy)')

    # 注册新的任务定义
    aws ecs register-task-definition --cli-input-json "$NEW_TASK_DEFINITION" --region $REGION

    echo "Task definition updated"
}

# 更新服务
update_service() {
    echo "Updating ECS service..."

    # 强制新部署
    aws ecs update-service \
        --cluster $CLUSTER_NAME \
        --service $SERVICE_NAME \
        --force-new-deployment \
        --region $REGION

    echo "Service update initiated"
}

# 等待部署完成
wait_for_deployment() {
    echo "Waiting for deployment to complete..."

    aws ecs wait services-stable \
        --cluster $CLUSTER_NAME \
        --services $SERVICE_NAME \
        --region $REGION

    echo "Deployment completed"
}

# 健康检查
health_check() {
    echo "Performing health check..."

    # 获取服务状态
    aws ecs describe-services \
        --cluster $CLUSTER_NAME \
        --services $SERVICE_NAME \
        --region $REGION

    echo "Health check completed"
}

# 主函数
main() {
    build_and_push
    update_task_definition
    update_service
    wait_for_deployment
    health_check

    echo "AWS ECS deployment completed successfully!"
}

main "$@"
```

### Google Cloud Run部署脚本

```bash
#!/bin/bash
# scripts/gcp-deploy.sh

set -e

echo "Starting Google Cloud Run deployment..."

# 配置变量
PROJECT_ID="my-project"
SERVICE_NAME="my-app"
REGION="us-central1"
IMAGE_NAME="gcr.io/$PROJECT_ID/$SERVICE_NAME"

# 构建并推送镜像
build_and_push() {
    echo "Building and pushing Docker image..."

    # 构建镜像
    docker build -t $IMAGE_NAME .

    # 推送镜像
    docker push $IMAGE_NAME

    echo "Image built and pushed"
}

# 部署到Cloud Run
deploy_to_cloud_run() {
    echo "Deploying to Cloud Run..."

    gcloud run deploy $SERVICE_NAME \
        --image $IMAGE_NAME \
        --platform managed \
        --region $REGION \
        --allow-unauthenticated \
        --memory 512Mi \
        --cpu 1 \
        --concurrency 100 \
        --max-instances 10 \
        --set-env-vars RUST_LOG=info \
        --set-env-vars DATABASE_URL="$DATABASE_URL"

    echo "Deployment completed"
}

# 获取服务URL
get_service_url() {
    echo "Getting service URL..."

    SERVICE_URL=$(gcloud run services describe $SERVICE_NAME --platform managed --region $REGION --format 'value(status.url)')

    echo "Service URL: $SERVICE_URL"
}

# 健康检查
health_check() {
    echo "Performing health check..."

    # 等待服务启动
    sleep 30

    # 检查服务状态
    curl -f $SERVICE_URL/health || exit 1

    echo "Health check passed"
}

# 主函数
main() {
    build_and_push
    deploy_to_cloud_run
    get_service_url
    health_check

    echo "Google Cloud Run deployment completed successfully!"
}

main "$@"
```

---

## 📊 部署监控

### 部署状态监控

```yaml
# monitoring/deployment-monitor.yml
apiVersion: v1
kind: ConfigMap
metadata:
  name: deployment-monitor
  namespace: monitoring
data:
  monitor.sh: |
    #!/bin/bash
    set -e

    NAMESPACE="my-app"
    SERVICE_NAME="my-app"

    # 检查部署状态
    check_deployment_status() {
        echo "Checking deployment status..."

        kubectl get deployments -n $NAMESPACE
        kubectl get pods -n $NAMESPACE -l app=$SERVICE_NAME
        kubectl get services -n $NAMESPACE
    }

    # 检查Pod健康状态
    check_pod_health() {
        echo "Checking pod health..."

        PODS=$(kubectl get pods -n $NAMESPACE -l app=$SERVICE_NAME -o jsonpath='{.items[*].metadata.name}')

        for pod in $PODS; do
            echo "Checking pod: $pod"
            kubectl describe pod $pod -n $NAMESPACE
        done
    }

    # 检查服务端点
    check_service_endpoints() {
        echo "Checking service endpoints..."

        kubectl get endpoints -n $NAMESPACE
        kubectl get ingress -n $NAMESPACE
    }

    # 主函数
    main() {
        check_deployment_status
        check_pod_health
        check_service_endpoints
    }

    main "$@"
```

### 部署告警配置

```yaml
# monitoring/deployment-alerts.yml
groups:
  - name: deployment_alerts
    rules:
      - alert: DeploymentFailed
        expr: kube_deployment_status_replicas_unavailable > 0
        for: 5m
        labels:
          severity: critical
        annotations:
          summary: "Deployment has failed replicas"
          description: "Deployment {{ $labels.deployment }} has {{ $value }} unavailable replicas"

      - alert: PodCrashLooping
        expr: rate(kube_pod_container_status_restarts_total[15m]) > 0
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "Pod is crash looping"
          description: "Pod {{ $labels.pod }} is restarting frequently"

      - alert: HighMemoryUsage
        expr: (container_memory_usage_bytes / container_spec_memory_limit_bytes) > 0.8
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "High memory usage"
          description: "Container {{ $labels.container }} memory usage is {{ $value }}%"

      - alert: HighCPUUsage
        expr: (rate(container_cpu_usage_seconds_total[5m]) / container_spec_cpu_quota * container_spec_cpu_period) > 0.8
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "High CPU usage"
          description: "Container {{ $labels.container }} CPU usage is {{ $value }}%"
```

---

## 📝 最佳实践

### 部署自动化原则

1. **自动化优先**: 优先使用自动化部署
2. **版本控制**: 所有配置版本控制
3. **环境一致性**: 确保环境一致性
4. **监控完整**: 提供完整监控
5. **快速回滚**: 支持快速回滚

### 部署检查清单

- [ ] CI/CD流程配置
- [ ] 容器化配置
- [ ] Kubernetes配置
- [ ] 云平台配置
- [ ] 监控配置
- [ ] 告警配置
- [ ] 健康检查配置
- [ ] 回滚机制配置

### 维护建议

1. **定期更新**: 定期更新部署配置
2. **监控部署**: 监控部署状态
3. **优化流程**: 优化部署流程
4. **备份策略**: 建立备份策略
5. **团队培训**: 定期进行部署培训

---

-**遵循这些部署自动化配置，您将能够建立高效、可靠的自动化部署体系！🦀**-
