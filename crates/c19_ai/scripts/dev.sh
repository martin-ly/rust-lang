#!/bin/bash

# c19_ai 开发环境脚本

set -e

echo "🔧 启动 c19_ai 开发环境..."

# 检查Rust是否安装
if ! command -v cargo &> /dev/null; then
    echo "❌ Rust 未安装，请先安装 Rust"
    exit 1
fi

# 设置环境变量
export RUST_LOG=debug
export RUST_BACKTRACE=1
export DATABASE_URL="postgresql://c19_ai:c19_ai_password@localhost:5432/c19_ai"
export REDIS_URL="redis://localhost:6379"

# 启动依赖服务
echo "🚀 启动依赖服务..."
docker-compose up -d postgres redis minio

# 等待数据库启动
echo "⏳ 等待数据库启动..."
sleep 10

# 运行数据库迁移
echo "🗄️  运行数据库迁移..."
# 这里可以添加数据库迁移命令

# 构建并运行应用
echo "🔨 构建并运行应用..."
cargo run --features "api-server"

echo "✅ 开发环境已启动"
