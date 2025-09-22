#!/bin/bash

# c19_ai 启动脚本

set -e

echo "🚀 启动 c19_ai 服务..."

# 检查Docker是否安装
if ! command -v docker &> /dev/null; then
    echo "❌ Docker 未安装，请先安装 Docker"
    exit 1
fi

# 检查docker-compose是否安装
if ! command -v docker-compose &> /dev/null; then
    echo "❌ docker-compose 未安装，请先安装 docker-compose"
    exit 1
fi

# 创建必要的目录
echo "📁 创建必要的目录..."
mkdir -p data logs config

# 设置权限
chmod 755 data logs config

# 构建并启动服务
echo "🔨 构建并启动服务..."
docker-compose up --build -d

# 等待服务启动
echo "⏳ 等待服务启动..."
sleep 30

# 检查服务状态
echo "🔍 检查服务状态..."
docker-compose ps

# 显示服务信息
echo ""
echo "✅ c19_ai 服务已启动！"
echo ""
echo "📊 服务访问地址："
echo "  - API服务: http://localhost:8080"
echo "  - 健康检查: http://localhost:8080/health"
echo "  - 指标监控: http://localhost:8080/metrics"
echo "  - Nginx代理: http://localhost"
echo "  - Grafana仪表板: http://localhost:3000 (admin/c19_ai_grafana_password)"
echo "  - Prometheus: http://localhost:9090"
echo "  - MinIO控制台: http://localhost:9001 (c19_ai_minio/c19_ai_minio_password)"
echo ""
echo "📝 查看日志: docker-compose logs -f"
echo "🛑 停止服务: docker-compose down"
echo "🔄 重启服务: docker-compose restart"
echo ""
