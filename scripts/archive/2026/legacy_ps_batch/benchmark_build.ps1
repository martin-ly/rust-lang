#!/usr/bin/env pwsh
# 编译时间基准测试脚本

param(
    [string]$Crate = "",
    [string]$Profile = "release",
    [switch]$Clean = $false
)

$ErrorActionPreference = "Stop"

function Measure-BuildTime {
    param(
        [string]$Command,
        [string]$Description
    )
    
    Write-Host "`n=== $Description ===" -ForegroundColor Cyan
    Write-Host "Command: $Command" -ForegroundColor Gray
    
    $start = Get-Date
    try {
        Invoke-Expression $Command 2>&1 | Tee-Object -Variable output | Out-Null
        $end = Get-Date
        $duration = ($end - $start).TotalSeconds
        
        Write-Host "✓ Completed in $([math]::Round($duration, 2)) seconds" -ForegroundColor Green
        return $duration
    }
    catch {
        Write-Host "✗ Build failed" -ForegroundColor Red
        Write-Host $output -ForegroundColor Red
        return $null
    }
}

function Get-BinarySize {
    param([string]$Profile)
    
    $binaries = Get-ChildItem -Path "target/$Profile" -File -ErrorAction SilentlyContinue | 
                Where-Object { $_.Extension -eq '.exe' -or $_.Name -notlike '*.*' }
    
    $totalSize = 0
    foreach ($binary in $binaries) {
        $totalSize += $binary.Length
        Write-Host "  $($binary.Name): $([math]::Round($binary.Length / 1MB, 2)) MB" -ForegroundColor Gray
    }
    
    return $totalSize
}

# 主程序
Write-Host "`n========================================"
Write-Host "  Rust 编译时间基准测试"
Write-Host "========================================" -ForegroundColor Cyan

# 可选: 清理缓存
if ($Clean) {
    Write-Host "`nCleaning target directory..." -ForegroundColor Yellow
    cargo clean
}

# 确定 crate 参数
$crateArg = if ($Crate) { "-p $Crate" } else { "" }

# 测试1: 全量编译
$fullBuildTime = Measure-BuildTime "cargo build --profile $Profile $crateArg" "全量编译 (cargo build --profile $Profile)"

# 获取二进制大小
Write-Host "`n=== 二进制大小 ===" -ForegroundColor Cyan
$binarySize = Get-BinarySize $Profile
Write-Host "Total: $([math]::Round($binarySize / 1MB, 2)) MB" -ForegroundColor Green

# 测试2: 增量编译 (touch 一个文件)
if ($Crate) {
    $cratePath = "crates/$Crate"
    $srcFile = Get-ChildItem -Path "$cratePath/src" -Filter "*.rs" | Select-Object -First 1
    if ($srcFile) {
        $touchTime = Measure-BuildTime "`$null > $($srcFile.FullName); cargo build --profile $Profile $crateArg" "增量编译 (touch 后重新编译)"
    }
}
else {
    # touch 主 crate 的文件
    $srcFile = Get-ChildItem -Path "crates/c01_ownership_borrow_scope/src" -Filter "*.rs" | Select-Object -First 1
    if ($srcFile) {
        $touchTime = Measure-BuildTime "`$null > $($srcFile.FullName); cargo build --profile $Profile $crateArg" "增量编译 (touch 后重新编译)"
    }
}

# 测试3: Check 时间
$checkTime = Measure-BuildTime "cargo check $crateArg" "快速检查 (cargo check)"

# 汇总
Write-Host "`n========================================"
Write-Host "  测试结果汇总"
Write-Host "========================================" -ForegroundColor Cyan
Write-Host "Profile: $Profile" -ForegroundColor Yellow
if ($Crate) {
    Write-Host "Crate: $Crate" -ForegroundColor Yellow
}
Write-Host "`n编译时间:" -ForegroundColor White
if ($fullBuildTime) {
    Write-Host "  全量编译: $([math]::Round($fullBuildTime, 2))s" -ForegroundColor Green
}
if ($touchTime) {
    Write-Host "  增量编译: $([math]::Round($touchTime, 2))s" -ForegroundColor Green
}
if ($checkTime) {
    Write-Host "  快速检查: $([math]::Round($checkTime, 2))s" -ForegroundColor Green
}
Write-Host "`n二进制大小: $([math]::Round($binarySize / 1MB, 2)) MB" -ForegroundColor Green

# 保存结果到文件
$results = @{
    timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    profile = $Profile
    crate = $Crate
    full_build_seconds = $fullBuildTime
    incremental_build_seconds = $touchTime
    check_seconds = $checkTime
    binary_size_mb = [math]::Round($binarySize / 1MB, 2)
} | ConvertTo-Json

$results | Out-File -FilePath "reports/build_benchmark_$Profile.json" -Encoding UTF8
Write-Host "`n结果已保存到: reports/build_benchmark_$Profile.json" -ForegroundColor Gray
