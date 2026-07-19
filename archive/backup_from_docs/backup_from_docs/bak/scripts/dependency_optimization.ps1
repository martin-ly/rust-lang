# 依赖优化脚本 - 2025年1月
# 用于检查和优化项目依赖

param(
    [switch]$Audit,
    [switch]$Outdated,
    [switch]$Tree,
    [switch]$Timing,
    [switch]$All
)

Write-Host "🔍 Rust项目依赖优化工具" -ForegroundColor Green
Write-Host "================================" -ForegroundColor Green

if ($All -or $Audit) {
    Write-Host "`n🔒 执行安全审计..." -ForegroundColor Yellow
    cargo audit
    if ($LASTEXITCODE -ne 0) {
        Write-Host "❌ 发现安全漏洞，请查看上述报告" -ForegroundColor Red
    } else {
        Write-Host "✅ 安全审计通过" -ForegroundColor Green
    }
}

if ($All -or $Outdated) {
    Write-Host "`n📅 检查过时依赖..." -ForegroundColor Yellow
    cargo outdated
    if ($LASTEXITCODE -ne 0) {
        Write-Host "⚠️ 有过时依赖，建议更新" -ForegroundColor Yellow
    } else {
        Write-Host "✅ 所有依赖都是最新版本" -ForegroundColor Green
    }
}

if ($All -or $Tree) {
    Write-Host "`n🌳 分析依赖树..." -ForegroundColor Yellow
    Write-Host "检查重复依赖..." -ForegroundColor Cyan
    cargo tree --duplicates
    Write-Host "`n依赖树统计..." -ForegroundColor Cyan
    cargo tree --format "{p}" | Measure-Object | Select-Object Count
}

if ($All -or $Timing) {
    Write-Host "`n⏱️ 编译时间分析..." -ForegroundColor Yellow
    Write-Host "开始编译并记录时间..." -ForegroundColor Cyan
    $startTime = Get-Date
    cargo build --timings
    $endTime = Get-Date
    $duration = $endTime - $startTime
    Write-Host "`n编译完成，耗时: $($duration.TotalSeconds.ToString('F2')) 秒" -ForegroundColor Green
    Write-Host "详细时间报告已保存到 target/cargo-timings/" -ForegroundColor Cyan
}

if (-not ($Audit -or $Outdated -or $Tree -or $Timing -or $All)) {
    Write-Host "`n📋 可用选项:" -ForegroundColor Cyan
    Write-Host "  -Audit     : 执行安全审计" -ForegroundColor White
    Write-Host "  -Outdated  : 检查过时依赖" -ForegroundColor White
    Write-Host "  -Tree      : 分析依赖树" -ForegroundColor White
    Write-Host "  -Timing    : 编译时间分析" -ForegroundColor White
    Write-Host "  -All       : 执行所有检查" -ForegroundColor White
    Write-Host "`n示例: .\dependency_optimization.ps1 -All" -ForegroundColor Yellow
}

Write-Host "`n🎯 优化建议:" -ForegroundColor Green
Write-Host "1. 使用特性标志减少编译时间: cargo build --no-default-features" -ForegroundColor White
Write-Host "2. 仅编译特定crate: cargo build -p <crate-name>" -ForegroundColor White
Write-Host "3. 使用并行编译: cargo build -j <num-jobs>" -ForegroundColor White
Write-Host "4. 定期运行安全审计: cargo audit" -ForegroundColor White
