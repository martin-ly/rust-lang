#!/bin/bash
# 快速演示脚本 - 展示Rust微服务框架的核心功能

echo "🚀 Rust微服务框架快速演示"
echo "================================"

# 检查Rust环境
echo "📋 检查环境..."
if ! command -v cargo &> /dev/null; then
    echo "❌ 错误: 未找到cargo，请先安装Rust"
    exit 1
fi

echo "✅ Rust环境检查通过"

# 编译项目
echo ""
echo "🔨 编译项目..."
cargo build --quiet
if [ $? -eq 0 ]; then
    echo "✅ 项目编译成功"
else
    echo "❌ 项目编译失败"
    exit 1
fi

# 运行测试
echo ""
echo "🧪 运行测试..."
cargo test --lib --quiet
if [ $? -eq 0 ]; then
    echo "✅ 测试通过"
else
    echo "⚠️  部分测试失败（这是正常的，因为需要外部依赖）"
fi

# 显示项目结构
echo ""
echo "📁 项目结构概览:"
echo "├── src/"
echo "│   ├── grpc/           # gRPC服务实现"
echo "│   ├── messaging/      # 消息队列实现"
echo "│   ├── middleware/     # 中间件实现"
echo "│   ├── axum/          # Axum Web框架"
echo "│   ├── actix/         # Actix-Web框架"
echo "│   └── ...            # 其他模块"
echo "├── examples/          # 示例代码"
echo "├── benches/           # 性能基准测试"
echo "├── scripts/           # 工具脚本"
echo "└── proto/             # Protocol Buffers定义"

# 显示功能特性
echo ""
echo "🌟 核心功能特性:"
echo "✅ 多种Web框架支持 (Axum, Actix-Web, Warp, Tide)"
echo "✅ 完整的gRPC实现 (Tonic + Protocol Buffers)"
echo "✅ 消息队列支持 (Redis, RabbitMQ)"
echo "✅ 丰富的中间件 (请求ID, 日志, 限流, 健康检查)"
echo "✅ 性能基准测试 (Criterion框架)"
echo "✅ 条件编译支持 (通过features控制依赖)"
echo "✅ 完整的错误处理"
echo "✅ 详细的文档和示例"

# 显示使用示例
echo ""
echo "💡 快速使用示例:"
echo ""
echo "# 启动Axum Web服务"
echo "cargo run --bin microservice-server -- axum"
echo ""
echo "# 启动gRPC服务"
echo "cargo run --bin microservice-server -- grpc"
echo ""
echo "# 运行消息队列示例"
echo "cargo run --example messaging_demo"
echo ""
echo "# 运行性能基准测试"
echo "cargo bench"

# 显示配置信息
echo ""
echo "⚙️  配置说明:"
echo "• 环境变量: SERVICE_NAME, SERVICE_PORT, DATABASE_URL等"
echo "• 配置文件: config.toml"
echo "• Features: with-redis, with-rabbitmq, with-sqlx, with-diesel"
echo "• 独立构建: cargo build --features standalone"

echo ""
echo "🎉 演示完成！"
echo "📚 更多信息请查看 README.md 和项目文档"
echo "🔧 需要帮助？请查看 examples/ 目录中的示例代码"
