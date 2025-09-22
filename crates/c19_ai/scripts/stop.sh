#!/bin/bash

# c19_ai 停止脚本

set -e

echo "🛑 停止 c19_ai 服务..."

# 停止所有服务
docker-compose down

# 可选：清理数据卷（谨慎使用）
if [ "$1" = "--clean" ]; then
    echo "🧹 清理数据卷..."
    docker-compose down -v
    echo "⚠️  所有数据已被删除！"
fi

echo "✅ c19_ai 服务已停止"
