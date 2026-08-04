# 简化的依赖版本检查脚本
# 快速检查项目依赖状态

Write-Host "🔍 检查 Rust 项目依赖状态..." -ForegroundColor Cyan

# 检查版本冲突
Write-Host "`n检查版本冲突..." -ForegroundColor Yellow
$conflicts = cargo tree --duplicates 2>$null
if ($conflicts) {
    Write-Host "发现版本冲突:" -ForegroundColor Red
    Write-Host $conflicts
} else {
    Write-Host "✅ 无版本冲突" -ForegroundColor Green
}

# 检查编译状态
Write-Host "`n检查编译状态..." -ForegroundColor Yellow
cargo check --quiet
if ($LASTEXITCODE -eq 0) {
    Write-Host "✅ 编译通过" -ForegroundColor Green
} else {
    Write-Host "❌ 编译失败" -ForegroundColor Red
}

# 显示关键依赖版本
Write-Host "`n关键依赖版本:" -ForegroundColor Yellow
$keyDeps = @("serde", "tokio", "tracing", "anyhow", "thiserror", "reqwest", "axum", "criterion")
foreach ($dep in $keyDeps) {
    $version = cargo search $dep --limit 1 2>$null | Select-String $dep
    if ($version) {
        Write-Host "  $version" -ForegroundColor White
    }
}

Write-Host "`n✅ 依赖检查完成" -ForegroundColor Green
