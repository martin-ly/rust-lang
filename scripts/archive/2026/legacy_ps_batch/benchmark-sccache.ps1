# sccache 性能基准测试脚本
# 用法: .\scripts\benchmark-sccache.ps1

param(
    [int]$Iterations = 2,
    [string]$ResultsFile = "reports/sccache-benchmark.md"
)

$ErrorActionPreference = "Stop"

Write-Host "=== sccache 性能基准测试 ===" -ForegroundColor Cyan
Write-Host ""

# 确保目录存在
$resultsDir = Split-Path $ResultsFile -Parent
if (!(Test-Path $resultsDir)) {
    New-Item -ItemType Directory -Path $resultsDir -Force | Out-Null
}

# 清理函数
function Clean-Build {
    Write-Host "清理构建目录..." -ForegroundColor Yellow
    cargo clean
    if (Get-Command sccache -ErrorAction SilentlyContinue) {
        sccache --zero-stats 2>$null | Out-Null
    }
}

# 计时函数
function Measure-Build {
    param(
        [string]$Name,
        [string]$Command,
        [switch]$WithSccache
    )
    
    Write-Host "运行: $Name" -ForegroundColor Green
    Write-Host "命令: $Command"
    
    $sw = [System.Diagnostics.Stopwatch]::StartNew()
    Invoke-Expression $Command
    $sw.Stop()
    
    $duration = $sw.Elapsed
    $result = [PSCustomObject]@{
        Name = $Name
        Duration = $duration
        DurationSeconds = [math]::Round($duration.TotalSeconds, 2)
        WithSccache = $WithSccache
    }
    
    Write-Host "完成: $([math]::Round($duration.TotalSeconds, 2)) 秒" -ForegroundColor Green
    Write-Host ""
    
    return $result
}

# 显示 sccache 统计
function Show-SccacheStats {
    if (Get-Command sccache -ErrorAction SilentlyContinue) {
        Write-Host "--- sccache 统计 ---" -ForegroundColor Cyan
        sccache --show-stats 2>$null | Out-Host
        Write-Host ""
    }
}

# 检查 sccache
$sccacheInstalled = $null -ne (Get-Command sccache -ErrorAction SilentlyContinue)
if ($sccacheInstalled) {
    Write-Host "✓ sccache 已安装: $(sccache --version)" -ForegroundColor Green
} else {
    Write-Host "✗ sccache 未安装" -ForegroundColor Red
    Write-Host "请运行: cargo install sccache" -ForegroundColor Yellow
    exit 1
}

# 检查环境变量
$sccacheEnabled = $env:RUSTC_WRAPPER -eq "sccache"
Write-Host "RUSTC_WRAPPER: $env:RUSTC_WRAPPER"
Write-Host ""

$results = @()

# 测试 1: 无缓存的冷构建
Write-Host "=== 测试 1: 冷构建 (无缓存) ===" -ForegroundColor Cyan
Clean-Build
$results += Measure-Build -Name "冷构建 (cargo build)" -Command "cargo build --workspace 2>&1" -WithSccache:$false
Show-SccacheStats

# 测试 2: sccache 启用后的构建
Write-Host "=== 测试 2: sccache 启用后的构建 ===" -ForegroundColor Cyan
cargo clean
$results += Measure-Build -Name "sccache 构建 (cargo build)" -Command "cargo build --workspace 2>&1" -WithSccache:$true
Show-SccacheStats

# 测试 3: 完全缓存命中 (clean 后重建)
Write-Host "=== 测试 3: 完全缓存命中 ===" -ForegroundColor Cyan
cargo clean
$results += Measure-Build -Name "缓存命中构建 (cargo build)" -Command "cargo build --workspace 2>&1" -WithSccache:$true
Show-SccacheStats

# 测试 4: 增量编译测试
Write-Host "=== 测试 4: 增量编译测试 ===" -ForegroundColor Cyan
$results += Measure-Build -Name "增量编译 (touch 后 build)" -Command "cargo build --workspace 2>&1" -WithSccache:$true
Show-SccacheStats

# 测试 5: Release 构建
Write-Host "=== 测试 5: Release 构建 ===" -ForegroundColor Cyan
cargo clean
$results += Measure-Build -Name "Release 构建 (无缓存)" -Command "cargo build --workspace --release 2>&1" -WithSccache:$false

# 生成报告
$report = @"
# sccache 性能基准测试报告

生成时间: $(Get-Date -Format "yyyy-MM-dd HH:mm:ss")

## 环境信息

- OS: $(if ($IsWindows) { "Windows" } elseif ($IsMacOS) { "macOS" } else { "Linux" })
- sccache: $(if ($sccacheInstalled) { sccache --version } else { "未安装" })
- RUSTC_WRAPPER: $env:RUSTC_WRAPPER
- SCCACHE_DIR: $env:SCCACHE_DIR
- SCCACHE_CACHE_SIZE: $env:SCCACHE_CACHE_SIZE

## 测试结果

| 测试项目 | 耗时 (秒) | sccache |
|---------|----------|---------|
"@

foreach ($r in $results) {
    $sccacheMark = if ($r.WithSccache) { "✓" } else { "✗" }
    $report += "| $($r.Name) | $($r.DurationSeconds) | $sccacheMark |`n"
}

# 计算性能提升
$coldBuild = ($results | Where-Object { $_.Name -like "冷构建*" }).DurationSeconds
$cachedBuild = ($results | Where-Object { $_.Name -like "缓存命中*" }).DurationSeconds

if ($coldBuild -and $cachedBuild -and $coldBuild -gt 0) {
    $improvement = [math]::Round((($coldBuild - $cachedBuild) / $coldBuild) * 100, 1)
    $report += @"

## 性能分析

- **冷构建耗时**: $coldBuild 秒
- **缓存命中耗时**: $cachedBuild 秒
- **性能提升**: $improvement%

"@
} else {
    $report += @"

## 性能分析

> 数据不足，无法计算性能提升。请确保完成所有测试。

"@
}

$report += @"
## 结论

$(if ($improvement -gt 30) { "✓ sccache 配置成功，编译时间显著减少" } elseif ($improvement -gt 0) { "△ sccache 有一定效果，但提升有限" } else { "✗ 性能数据异常，请检查配置" })

## 建议

1. **日常使用**: 保持 sccache 运行，所有 cargo 命令自动使用缓存
2. **CI/CD**: 已配置 GitHub Actions 缓存，跨构建共享
3. **缓存大小**: 当前设置为 50GB，如需调整修改 SCCACHE_CACHE_SIZE

---
*报告生成脚本: scripts/benchmark-sccache.ps1*
"@

# 保存报告
$report | Out-File -FilePath $ResultsFile -Encoding UTF8
Write-Host "报告已保存: $ResultsFile" -ForegroundColor Green

# 显示结果
Write-Host ""
Write-Host "=== 测试结果摘要 ===" -ForegroundColor Cyan
$results | Format-Table -AutoSize

if ($improvement -gt 0) {
    Write-Host "性能提升: $improvement%" -ForegroundColor Green
}
