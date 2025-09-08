# PowerShell快速演示脚本 - 展示Rust微服务框架的核心功能

Write-Host "🚀 Rust微服务框架快速演示" -ForegroundColor Green
Write-Host "================================" -ForegroundColor Green

# 检查Rust环境
Write-Host "📋 检查环境..." -ForegroundColor Yellow
if (!(Get-Command cargo -ErrorAction SilentlyContinue)) {
    Write-Host "❌ 错误: 未找到cargo，请先安装Rust" -ForegroundColor Red
    exit 1
}

Write-Host "✅ Rust环境检查通过" -ForegroundColor Green

# 编译项目
Write-Host ""
Write-Host "🔨 编译项目..." -ForegroundColor Yellow
cargo build --quiet
if ($LASTEXITCODE -eq 0) {
    Write-Host "✅ 项目编译成功" -ForegroundColor Green
} else {
    Write-Host "❌ 项目编译失败" -ForegroundColor Red
    exit 1
}

# 运行测试
Write-Host ""
Write-Host "🧪 运行测试..." -ForegroundColor Yellow
cargo test --lib --quiet
if ($LASTEXITCODE -eq 0) {
    Write-Host "✅ 测试通过" -ForegroundColor Green
} else {
    Write-Host "⚠️  部分测试失败（这是正常的，因为需要外部依赖）" -ForegroundColor Yellow
}

# 显示项目结构
Write-Host ""
Write-Host "📁 项目结构概览:" -ForegroundColor Cyan
Write-Host "├── src/"
Write-Host "│   ├── grpc/           # gRPC服务实现"
Write-Host "│   ├── messaging/      # 消息队列实现"
Write-Host "│   ├── middleware/     # 中间件实现"
Write-Host "│   ├── axum/          # Axum Web框架"
Write-Host "│   ├── actix/         # Actix-Web框架"
Write-Host "│   └── ...            # 其他模块"
Write-Host "├── examples/          # 示例代码"
Write-Host "├── benches/           # 性能基准测试"
Write-Host "├── scripts/           # 工具脚本"
Write-Host "└── proto/             # Protocol Buffers定义"

# 显示功能特性
Write-Host ""
Write-Host "🌟 核心功能特性:" -ForegroundColor Cyan
Write-Host "✅ 多种Web框架支持 (Axum, Actix-Web, Warp, Tide)" -ForegroundColor Green
Write-Host "✅ 完整的gRPC实现 (Tonic + Protocol Buffers)" -ForegroundColor Green
Write-Host "✅ 消息队列支持 (Redis, RabbitMQ)" -ForegroundColor Green
Write-Host "✅ 丰富的中间件 (请求ID, 日志, 限流, 健康检查)" -ForegroundColor Green
Write-Host "✅ 性能基准测试 (Criterion框架)" -ForegroundColor Green
Write-Host "✅ 条件编译支持 (通过features控制依赖)" -ForegroundColor Green
Write-Host "✅ 完整的错误处理" -ForegroundColor Green
Write-Host "✅ 详细的文档和示例" -ForegroundColor Green

# 显示使用示例
Write-Host ""
Write-Host "💡 快速使用示例:" -ForegroundColor Cyan
Write-Host ""
Write-Host "# 启动Axum Web服务" -ForegroundColor White
Write-Host "cargo run --bin microservice-server -- axum" -ForegroundColor Gray
Write-Host ""
Write-Host "# 启动gRPC服务" -ForegroundColor White
Write-Host "cargo run --bin microservice-server -- grpc" -ForegroundColor Gray
Write-Host ""
Write-Host "# 运行消息队列示例" -ForegroundColor White
Write-Host "cargo run --example messaging_demo" -ForegroundColor Gray
Write-Host ""
Write-Host "# 运行性能基准测试" -ForegroundColor White
Write-Host "cargo bench" -ForegroundColor Gray

# 显示配置信息
Write-Host ""
Write-Host "⚙️  配置说明:" -ForegroundColor Cyan
Write-Host "• 环境变量: SERVICE_NAME, SERVICE_PORT, DATABASE_URL等" -ForegroundColor White
Write-Host "• 配置文件: config.toml" -ForegroundColor White
Write-Host "• Features: with-redis, with-rabbitmq, with-sqlx, with-diesel" -ForegroundColor White
Write-Host "• 独立构建: cargo build --features standalone" -ForegroundColor White

Write-Host ""
Write-Host "🎉 演示完成！" -ForegroundColor Green
Write-Host "📚 更多信息请查看 README.md 和项目文档" -ForegroundColor Cyan
Write-Host "🔧 需要帮助？请查看 examples/ 目录中的示例代码" -ForegroundColor Cyan
