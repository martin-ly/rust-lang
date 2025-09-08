#!/bin/bash
# 运行性能基准测试脚本

echo "🚀 开始运行Rust微服务框架性能基准测试..."

# 检查是否安装了criterion
if ! cargo install --list | grep -q "criterion"; then
    echo "📦 安装criterion基准测试工具..."
    cargo install criterion
fi

# 创建基准测试结果目录
mkdir -p benchmark_results

echo "📊 运行Axum性能基准测试..."
cargo bench --bench axum_benchmark -- --output-format html --output benchmark_results/axum_benchmark.html

echo "📊 运行gRPC性能基准测试..."
cargo bench --bench grpc_benchmark -- --output-format html --output benchmark_results/grpc_benchmark.html

echo "📊 运行消息队列性能基准测试..."
cargo bench --bench messaging_benchmark -- --output-format html --output benchmark_results/messaging_benchmark.html

echo "📈 生成性能报告..."
cat > benchmark_results/performance_report.md << EOF
# Rust微服务框架性能基准测试报告

## 测试环境
- 操作系统: $(uname -s)
- 架构: $(uname -m)
- Rust版本: $(rustc --version)
- 测试时间: $(date)

## 测试结果

### Axum Web框架性能
- 基本路由性能: 查看 axum_benchmark.html
- 健康检查性能: 查看 axum_benchmark.html
- 并发请求性能: 查看 axum_benchmark.html
- 中间件性能影响: 查看 axum_benchmark.html
- 负载测试结果: 查看 axum_benchmark.html

### gRPC服务性能
- 服务创建性能: 查看 grpc_benchmark.html
- 用户操作性能: 查看 grpc_benchmark.html
- 并发操作性能: 查看 grpc_benchmark.html
- 批量操作性能: 查看 grpc_benchmark.html

### 消息队列性能
- Redis操作性能: 查看 messaging_benchmark.html
- RabbitMQ操作性能: 查看 messaging_benchmark.html
- 并发消息处理性能: 查看 messaging_benchmark.html
- 批量消息处理性能: 查看 messaging_benchmark.html

## 性能优化建议

1. **Web框架优化**
   - 使用连接池减少连接开销
   - 启用压缩减少网络传输
   - 合理配置中间件顺序

2. **gRPC优化**
   - 使用连接复用
   - 启用流式处理
   - 合理设置超时时间

3. **消息队列优化**
   - 使用批量操作
   - 合理设置预取数量
   - 启用消息持久化

## 测试文件说明

- \`axum_benchmark.html\`: Axum框架性能测试结果
- \`grpc_benchmark.html\`: gRPC服务性能测试结果
- \`messaging_benchmark.html\`: 消息队列性能测试结果

EOF

echo "✅ 性能基准测试完成！"
echo "📁 测试结果保存在 benchmark_results/ 目录中"
echo "🌐 打开 benchmark_results/performance_report.md 查看详细报告"
echo "📊 使用浏览器打开 HTML 文件查看交互式图表"
