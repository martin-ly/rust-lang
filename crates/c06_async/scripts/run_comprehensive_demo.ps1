# Rust 异步生态系统综合演示运行脚本
# 本脚本演示了 std、tokio、smol 等异步库的全面特性

Write-Host "🚀 Rust 异步生态系统综合演示" -ForegroundColor Green
Write-Host "================================================" -ForegroundColor Yellow

# 检查 Rust 环境
Write-Host "🔍 检查 Rust 环境..." -ForegroundColor Cyan
rustc --version
cargo --version

# 构建项目
Write-Host "`n🔨 构建项目..." -ForegroundColor Cyan
cargo build --release

if ($LASTEXITCODE -ne 0) {
    Write-Host "❌ 构建失败" -ForegroundColor Red
    exit 1
}

Write-Host "✅ 构建成功" -ForegroundColor Green

# 运行综合演示
Write-Host "`n🎯 运行异步生态系统综合演示..." -ForegroundColor Cyan
cargo run --example async_ecosystem_comprehensive_demo --release

if ($LASTEXITCODE -ne 0) {
    Write-Host "❌ 演示运行失败" -ForegroundColor Red
    exit 1
}

# 运行测试
Write-Host "`n🧪 运行测试..." -ForegroundColor Cyan
cargo test --release

if ($LASTEXITCODE -ne 0) {
    Write-Host "❌ 测试失败" -ForegroundColor Red
    exit 1
}

Write-Host "✅ 所有测试通过" -ForegroundColor Green

# 运行基准测试
Write-Host "`n⚡ 运行基准测试..." -ForegroundColor Cyan
cargo bench --no-run

if ($LASTEXITCODE -ne 0) {
    Write-Host "❌ 基准测试编译失败" -ForegroundColor Red
    exit 1
}

Write-Host "✅ 基准测试编译成功" -ForegroundColor Green

# 生成文档
Write-Host "`n📚 生成文档..." -ForegroundColor Cyan
cargo doc --no-deps --open

Write-Host "`n✅ Rust 异步生态系统综合演示完成!" -ForegroundColor Green
Write-Host "================================================" -ForegroundColor Yellow
Write-Host "演示内容包括:" -ForegroundColor White
Write-Host "- 异步运行时特性对比分析" -ForegroundColor White
Write-Host "- 集成框架层面的共性分析" -ForegroundColor White
Write-Host "- 异步同步转换机制演示" -ForegroundColor White
Write-Host "- 聚合组合设计模式实现" -ForegroundColor White
Write-Host "- 异步日志调试和跟踪系统" -ForegroundColor White
Write-Host "- 性能基准测试和监控" -ForegroundColor White
Write-Host "- 2025年最新特性和最佳实践" -ForegroundColor White
