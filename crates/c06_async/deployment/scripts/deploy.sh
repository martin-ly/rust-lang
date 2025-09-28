#!/bin/bash
# Rust 1.90 异步特性部署脚本
# 支持多种部署环境和自动化流程

set -euo pipefail

# 颜色定义
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# 日志函数
log_info() {
    echo -e "${BLUE}[INFO]${NC} $1"
}

log_success() {
    echo -e "${GREEN}[SUCCESS]${NC} $1"
}

log_warning() {
    echo -e "${YELLOW}[WARNING]${NC} $1"
}

log_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

# 配置变量
PROJECT_NAME="rust-async-190"
VERSION="${VERSION:-latest}"
ENVIRONMENT="${ENVIRONMENT:-development}"
NAMESPACE="${NAMESPACE:-rust-async-190}"
REGISTRY="${REGISTRY:-ghcr.io}"
IMAGE_NAME="${REGISTRY}/${PROJECT_NAME}:${VERSION}"

# 部署类型
DEPLOYMENT_TYPE="${DEPLOYMENT_TYPE:-docker}"

# 显示帮助信息
show_help() {
    cat << EOF
Rust 1.90 异步特性部署脚本

用法: $0 [选项]

选项:
    -h, --help              显示此帮助信息
    -v, --version VERSION   指定版本号 (默认: latest)
    -e, --env ENVIRONMENT   指定环境 (development|staging|production)
    -t, --type TYPE         指定部署类型 (docker|kubernetes|helm)
    -n, --namespace NAMESPACE 指定 Kubernetes 命名空间
    -r, --registry REGISTRY 指定镜像仓库
    --skip-tests           跳过测试
    --skip-build           跳过构建
    --skip-deploy          跳过部署
    --force                强制部署

示例:
    $0 --env production --version 1.90.0
    $0 --type kubernetes --namespace production
    $0 --skip-tests --force
EOF
}

# 解析命令行参数
parse_args() {
    while [[ $# -gt 0 ]]; do
        case $1 in
            -h|--help)
                show_help
                exit 0
                ;;
            -v|--version)
                VERSION="$2"
                shift 2
                ;;
            -e|--env)
                ENVIRONMENT="$2"
                shift 2
                ;;
            -t|--type)
                DEPLOYMENT_TYPE="$2"
                shift 2
                ;;
            -n|--namespace)
                NAMESPACE="$2"
                shift 2
                ;;
            -r|--registry)
                REGISTRY="$2"
                shift 2
                ;;
            --skip-tests)
                SKIP_TESTS=true
                shift
                ;;
            --skip-build)
                SKIP_BUILD=true
                shift
                ;;
            --skip-deploy)
                SKIP_DEPLOY=true
                shift
                ;;
            --force)
                FORCE_DEPLOY=true
                shift
                ;;
            *)
                log_error "未知选项: $1"
                show_help
                exit 1
                ;;
        esac
    done
}

# 检查依赖
check_dependencies() {
    log_info "检查部署依赖..."
    
    case $DEPLOYMENT_TYPE in
        docker)
            if ! command -v docker &> /dev/null; then
                log_error "Docker 未安装"
                exit 1
            fi
            ;;
        kubernetes)
            if ! command -v kubectl &> /dev/null; then
                log_error "kubectl 未安装"
                exit 1
            fi
            if ! command -v docker &> /dev/null; then
                log_error "Docker 未安装"
                exit 1
            fi
            ;;
        helm)
            if ! command -v helm &> /dev/null; then
                log_error "Helm 未安装"
                exit 1
            fi
            if ! command -v kubectl &> /dev/null; then
                log_error "kubectl 未安装"
                exit 1
            fi
            if ! command -v docker &> /dev/null; then
                log_error "Docker 未安装"
                exit 1
            fi
            ;;
        *)
            log_error "不支持的部署类型: $DEPLOYMENT_TYPE"
            exit 1
            ;;
    esac
    
    log_success "依赖检查完成"
}

# 运行测试
run_tests() {
    if [[ "${SKIP_TESTS:-false}" == "true" ]]; then
        log_warning "跳过测试"
        return 0
    fi
    
    log_info "运行测试..."
    
    cd "$(dirname "$0")/../.."
    
    # 单元测试
    log_info "运行单元测试..."
    cargo test --verbose
    
    # 集成测试
    log_info "运行集成测试..."
    cargo test --test integration_test_suite --verbose
    
    # 文档测试
    log_info "运行文档测试..."
    cargo test --doc
    
    # 安全检查
    if command -v cargo-audit &> /dev/null; then
        log_info "运行安全检查..."
        cargo audit
    fi
    
    log_success "所有测试通过"
}

# 构建应用
build_application() {
    if [[ "${SKIP_BUILD:-false}" == "true" ]]; then
        log_warning "跳过构建"
        return 0
    fi
    
    log_info "构建应用..."
    
    cd "$(dirname "$0")/../.."
    
    # 构建 Docker 镜像
    log_info "构建 Docker 镜像: $IMAGE_NAME"
    
    case $ENVIRONMENT in
        development)
            docker build --target development -t "$IMAGE_NAME" -f deployment/docker/Dockerfile .
            ;;
        production)
            docker build --target runtime -t "$IMAGE_NAME" -f deployment/docker/Dockerfile .
            ;;
        *)
            docker build -t "$IMAGE_NAME" -f deployment/docker/Dockerfile .
            ;;
    esac
    
    log_success "Docker 镜像构建完成"
    
    # 推送镜像（如果指定了仓库）
    if [[ "$REGISTRY" != "local" ]]; then
        log_info "推送镜像到仓库..."
        docker push "$IMAGE_NAME"
        log_success "镜像推送完成"
    fi
}

# Docker 部署
deploy_docker() {
    log_info "Docker 部署到 $ENVIRONMENT 环境..."
    
    # 停止现有容器
    if docker ps -q --filter "name=$PROJECT_NAME" | grep -q .; then
        log_info "停止现有容器..."
        docker stop "$PROJECT_NAME" || true
        docker rm "$PROJECT_NAME" || true
    fi
    
    # 启动新容器
    log_info "启动新容器..."
    docker run -d \
        --name "$PROJECT_NAME" \
        --restart unless-stopped \
        -p 8080:8080 \
        -p 9090:9090 \
        -e RUST_LOG=info \
        -e ENVIRONMENT="$ENVIRONMENT" \
        "$IMAGE_NAME"
    
    # 等待服务启动
    log_info "等待服务启动..."
    sleep 10
    
    # 健康检查
    if curl -f http://localhost:8080/health > /dev/null 2>&1; then
        log_success "服务启动成功"
    else
        log_error "服务启动失败"
        docker logs "$PROJECT_NAME"
        exit 1
    fi
}

# Kubernetes 部署
deploy_kubernetes() {
    log_info "Kubernetes 部署到 $ENVIRONMENT 环境..."
    
    # 创建命名空间
    kubectl create namespace "$NAMESPACE" --dry-run=client -o yaml | kubectl apply -f -
    
    # 更新镜像标签
    sed -i "s|image: rust-async-190:latest|image: $IMAGE_NAME|g" deployment/kubernetes/deployment.yaml
    
    # 应用 Kubernetes 配置
    kubectl apply -f deployment/kubernetes/deployment.yaml -n "$NAMESPACE"
    
    # 等待部署完成
    log_info "等待部署完成..."
    kubectl rollout status deployment/rust-async-190 -n "$NAMESPACE" --timeout=300s
    
    # 检查服务状态
    if kubectl get pods -n "$NAMESPACE" -l app.kubernetes.io/name=rust-async-190 --field-selector=status.phase=Running | grep -q "rust-async-190"; then
        log_success "Kubernetes 部署成功"
    else
        log_error "Kubernetes 部署失败"
        kubectl describe pods -n "$NAMESPACE" -l app.kubernetes.io/name=rust-async-190
        exit 1
    fi
}

# Helm 部署
deploy_helm() {
    log_info "Helm 部署到 $ENVIRONMENT 环境..."
    
    # 检查 Helm Chart 是否存在
    if [[ ! -d "deployment/helm" ]]; then
        log_error "Helm Chart 不存在"
        exit 1
    fi
    
    # 添加 Helm 仓库（如果需要）
    # helm repo add stable https://charts.helm.sh/stable
    
    # 部署 Helm Chart
    helm upgrade --install "$PROJECT_NAME" deployment/helm \
        --namespace "$NAMESPACE" \
        --create-namespace \
        --set image.repository="$REGISTRY/$PROJECT_NAME" \
        --set image.tag="$VERSION" \
        --set environment="$ENVIRONMENT" \
        --wait \
        --timeout=300s
    
    log_success "Helm 部署成功"
}

# 执行部署
deploy_application() {
    if [[ "${SKIP_DEPLOY:-false}" == "true" ]]; then
        log_warning "跳过部署"
        return 0
    fi
    
    log_info "开始部署到 $ENVIRONMENT 环境..."
    
    case $DEPLOYMENT_TYPE in
        docker)
            deploy_docker
            ;;
        kubernetes)
            deploy_kubernetes
            ;;
        helm)
            deploy_helm
            ;;
        *)
            log_error "不支持的部署类型: $DEPLOYMENT_TYPE"
            exit 1
            ;;
    esac
}

# 健康检查
health_check() {
    log_info "执行健康检查..."
    
    local max_attempts=30
    local attempt=1
    
    while [[ $attempt -le $max_attempts ]]; do
        case $DEPLOYMENT_TYPE in
            docker)
                if curl -f http://localhost:8080/health > /dev/null 2>&1; then
                    log_success "健康检查通过"
                    return 0
                fi
                ;;
            kubernetes|helm)
                if kubectl get pods -n "$NAMESPACE" -l app.kubernetes.io/name=rust-async-190 --field-selector=status.phase=Running | grep -q "rust-async-190"; then
                    log_success "健康检查通过"
                    return 0
                fi
                ;;
        esac
        
        log_info "健康检查尝试 $attempt/$max_attempts..."
        sleep 10
        ((attempt++))
    done
    
    log_error "健康检查失败"
    return 1
}

# 清理函数
cleanup() {
    log_info "执行清理..."
    
    case $DEPLOYMENT_TYPE in
        docker)
            # 清理旧镜像
            docker image prune -f
            ;;
        kubernetes|helm)
            # 清理失败的 Pod
            kubectl delete pods -n "$NAMESPACE" --field-selector=status.phase=Failed
            ;;
    esac
}

# 发送通知
send_notification() {
    local status="$1"
    local message="$2"
    
    # 这里可以添加通知逻辑，比如发送到 Slack、邮件等
    log_info "部署状态: $status - $message"
}

# 主函数
main() {
    log_info "开始 Rust 1.90 异步特性部署流程..."
    log_info "项目: $PROJECT_NAME"
    log_info "版本: $VERSION"
    log_info "环境: $ENVIRONMENT"
    log_info "部署类型: $DEPLOYMENT_TYPE"
    
    # 解析参数
    parse_args "$@"
    
    # 检查依赖
    check_dependencies
    
    # 设置清理陷阱
    trap cleanup EXIT
    
    # 运行测试
    if ! run_tests; then
        log_error "测试失败，终止部署"
        send_notification "FAILED" "测试失败"
        exit 1
    fi
    
    # 构建应用
    if ! build_application; then
        log_error "构建失败，终止部署"
        send_notification "FAILED" "构建失败"
        exit 1
    fi
    
    # 部署应用
    if ! deploy_application; then
        log_error "部署失败"
        send_notification "FAILED" "部署失败"
        exit 1
    fi
    
    # 健康检查
    if ! health_check; then
        log_error "健康检查失败"
        send_notification "FAILED" "健康检查失败"
        exit 1
    fi
    
    # 发送成功通知
    send_notification "SUCCESS" "部署成功完成"
    
    log_success "部署流程完成！"
    log_info "访问地址:"
    
    case $DEPLOYMENT_TYPE in
        docker)
            log_info "  HTTP: http://localhost:8080"
            log_info "  健康检查: http://localhost:8080/health"
            log_info "  指标: http://localhost:9090/metrics"
            ;;
        kubernetes|helm)
            log_info "  服务端点: kubectl get svc -n $NAMESPACE"
            ;;
    esac
}

# 执行主函数
main "$@"
