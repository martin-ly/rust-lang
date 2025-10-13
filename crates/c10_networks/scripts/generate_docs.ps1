# scripts/generate_docs.ps1 - 生成 C10 Networks API 文档

param(
    [switch]$Open,
    [switch]$AllFeatures,
    [switch]$Examples,
    [switch]$Benches,
    [switch]$Tests
)

Write-Host "🚀 生成 C10 Networks API 文档..." -ForegroundColor Green

# 检查 Rust 工具链
if (-not (Get-Command cargo -ErrorAction SilentlyContinue)) {
    Write-Host "❌ 错误: 未找到 cargo 命令" -ForegroundColor Red
    Write-Host "请安装 Rust 工具链: https://rustup.rs/" -ForegroundColor Yellow
    exit 1
}

# 检查 Rust 版本
$rustVersion = (cargo --version).Split(' ')[1]
Write-Host "📦 Rust 版本: $rustVersion" -ForegroundColor Cyan

# 清理之前的文档
Write-Host "🧹 清理之前的文档..." -ForegroundColor Yellow
if (Test-Path "target/doc") {
    Remove-Item -Recurse -Force "target/doc"
}

# 构建文档生成命令
$docArgs = @("doc", "--no-deps", "--document-private-items")

if ($AllFeatures) {
    $docArgs += "--all-features"
    Write-Host "🔧 生成包含所有特性的文档..." -ForegroundColor Cyan
} else {
    Write-Host "📚 生成基础文档..." -ForegroundColor Cyan
}

if ($Examples) {
    $docArgs += "--examples"
    Write-Host "📖 生成示例文档..." -ForegroundColor Cyan
}

if ($Benches) {
    $docArgs += "--benches"
    Write-Host "📊 生成基准测试文档..." -ForegroundColor Cyan
}

if ($Tests) {
    $docArgs += "--tests"
    Write-Host "🧪 生成测试文档..." -ForegroundColor Cyan
}

if ($Open) {
    $docArgs += "--open"
    Write-Host "🌐 生成并打开文档..." -ForegroundColor Cyan
}

# 生成文档
try {
    & cargo @docArgs
    if ($LASTEXITCODE -ne 0) {
        throw "文档生成失败"
    }
} catch {
    Write-Host "❌ 文档生成失败: $_" -ForegroundColor Red
    exit 1
}

# 检查文档生成结果
if (Test-Path "target/doc/c10_networks") {
    Write-Host "✅ 文档生成成功！" -ForegroundColor Green
    
    $docPath = Join-Path (Get-Location) "target/doc/c10_networks/index.html"
    Write-Host "📖 查看文档: file:///$docPath" -ForegroundColor Cyan
    
    # 统计文档信息
    $docSize = (Get-ChildItem "target/doc/c10_networks" -Recurse | Measure-Object -Property Length -Sum).Sum
    $docSizeMB = [math]::Round($docSize / 1MB, 2)
    Write-Host "📊 文档大小: $docSizeMB MB" -ForegroundColor Cyan
    
    # 检查文档覆盖率
    Write-Host "🔍 检查文档覆盖率..." -ForegroundColor Yellow
    $missingDocs = (cargo doc --document-private-items --no-deps 2>&1 | Select-String "warning.*missing.*docs").Count
    if ($missingDocs -gt 0) {
        Write-Host "⚠️  发现 $missingDocs 个缺失的文档注释" -ForegroundColor Yellow
    } else {
        Write-Host "✅ 文档覆盖率良好" -ForegroundColor Green
    }
    
    # 检查链接有效性
    Write-Host "🔗 检查文档链接..." -ForegroundColor Yellow
    $unresolvedLinks = (cargo doc --document-private-items --no-deps 2>&1 | Select-String "warning.*unresolved.*link").Count
    if ($unresolvedLinks -gt 0) {
        Write-Host "⚠️  发现 $unresolvedLinks 个未解析的链接" -ForegroundColor Yellow
    } else {
        Write-Host "✅ 文档链接有效" -ForegroundColor Green
    }
    
} else {
    Write-Host "❌ 文档生成失败" -ForegroundColor Red
    exit 1
}

Write-Host "🎉 文档生成完成！" -ForegroundColor Green
Write-Host ""
Write-Host "📋 可用命令:" -ForegroundColor Cyan
Write-Host "  .\scripts\generate_docs.ps1 -Open          # 生成并打开文档" -ForegroundColor White
Write-Host "  .\scripts\generate_docs.ps1 -AllFeatures  # 生成包含所有特性的文档" -ForegroundColor White
Write-Host "  .\scripts\generate_docs.ps1 -Examples     # 生成示例文档" -ForegroundColor White
Write-Host "  .\scripts\generate_docs.ps1 -Benches      # 生成基准测试文档" -ForegroundColor White
Write-Host "  .\scripts\generate_docs.ps1 -Tests        # 生成测试文档" -ForegroundColor White
