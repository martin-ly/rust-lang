# 性能检查脚本 / Performance Check Script
# 运行性能基准测试和回归检测 / Run performance benchmarks and regression detection

param(
    [string]$Target = "all",
    [switch]$Verbose = $false,
    [switch]$GenerateReport = $false
)

$ErrorActionPreference = "Stop"

Write-Host "开始性能检查 / Starting performance check..." -ForegroundColor Green

# 检查必要工具 / Check required tools
function Test-RequiredTools {
    Write-Host "检查必要工具 / Checking required tools..." -ForegroundColor Yellow
    
    $tools = @("cargo", "rustc")
    foreach ($tool in $tools) {
        if (-not (Get-Command $tool -ErrorAction SilentlyContinue)) {
            Write-Error "工具 $tool 未找到 / Tool $tool not found"
        }
    }
    
    # 检查 Criterion
    if (-not (cargo bench --help 2>$null)) {
        Write-Warning "Criterion 未安装，将跳过基准测试 / Criterion not installed, skipping benchmarks"
    }
    
    Write-Host "工具检查完成 / Tool check completed" -ForegroundColor Green
}

# 运行基准测试 / Run benchmarks
function Invoke-Benchmarks {
    Write-Host "运行基准测试 / Running benchmarks..." -ForegroundColor Yellow
    
    try {
        # 运行所有基准测试
        cargo bench --all-targets --workspace
        
        if ($LASTEXITCODE -ne 0) {
            Write-Warning "基准测试失败 / Benchmarks failed"
            return $false
        }
        
        Write-Host "基准测试完成 / Benchmarks completed" -ForegroundColor Green
        return $true
    }
    catch {
        Write-Error "基准测试执行失败 / Benchmark execution failed: $_"
        return $false
    }
}

# 运行 Miri 测试 / Run Miri tests
function Invoke-MiriTests {
    Write-Host "运行 Miri 测试 / Running Miri tests..." -ForegroundColor Yellow
    
    try {
        # 检查 Miri 是否可用
        if (-not (Get-Command "cargo" -ErrorAction SilentlyContinue | ForEach-Object { cargo miri --version 2>$null })) {
            Write-Warning "Miri 未安装，跳过内存安全测试 / Miri not installed, skipping memory safety tests"
            return $true
        }
        
        # 运行 Miri 测试
        cargo miri test --all-targets --workspace
        
        if ($LASTEXITCODE -ne 0) {
            Write-Warning "Miri 测试失败 / Miri tests failed"
            return $false
        }
        
        Write-Host "Miri 测试完成 / Miri tests completed" -ForegroundColor Green
        return $true
    }
    catch {
        Write-Error "Miri 测试执行失败 / Miri test execution failed: $_"
        return $false
    }
}

# 运行 Loom 测试 / Run Loom tests
function Invoke-LoomTests {
    Write-Host "运行 Loom 并发测试 / Running Loom concurrency tests..." -ForegroundColor Yellow
    
    try {
        # 检查是否有 Loom 测试
        $loomTests = Get-ChildItem -Path "crates" -Recurse -Filter "*.rs" | 
            Select-String -Pattern "loom::" | 
            Select-Object -First 1
        
        if (-not $loomTests) {
            Write-Host "未找到 Loom 测试，跳过 / No Loom tests found, skipping" -ForegroundColor Yellow
            return $true
        }
        
        # 运行 Loom 测试
        cargo test --all-targets --workspace --features loom
        
        if ($LASTEXITCODE -ne 0) {
            Write-Warning "Loom 测试失败 / Loom tests failed"
            return $false
        }
        
        Write-Host "Loom 测试完成 / Loom tests completed" -ForegroundColor Green
        return $true
    }
    catch {
        Write-Error "Loom 测试执行失败 / Loom test execution failed: $_"
        return $false
    }
}

# 生成性能报告 / Generate performance report
function New-PerformanceReport {
    param([bool]$BenchmarkSuccess, [bool]$MiriSuccess, [bool]$LoomSuccess)
    
    if (-not $GenerateReport) {
        return
    }
    
    Write-Host "生成性能报告 / Generating performance report..." -ForegroundColor Yellow
    
    $reportPath = "reports/performance-report-$(Get-Date -Format 'yyyy-MM-dd-HH-mm-ss').md"
    $reportDir = Split-Path $reportPath -Parent
    
    if (-not (Test-Path $reportDir)) {
        New-Item -ItemType Directory -Path $reportDir -Force | Out-Null
    }
    
    $report = @"
# 性能检查报告 / Performance Check Report

**生成时间 / Generated**: $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')
**目标 / Target**: $Target

## 测试结果 / Test Results

| 测试类型 / Test Type | 状态 / Status | 备注 / Notes |
|---------------------|---------------|--------------|
| 基准测试 / Benchmarks | $(if ($BenchmarkSuccess) { "✅ 通过 / Passed" } else { "❌ 失败 / Failed" }) | 性能基准测试 |
| Miri 测试 / Miri Tests | $(if ($MiriSuccess) { "✅ 通过 / Passed" } else { "❌ 失败 / Failed" }) | 内存安全测试 |
| Loom 测试 / Loom Tests | $(if ($LoomSuccess) { "✅ 通过 / Passed" } else { "❌ 失败 / Failed" }) | 并发安全测试 |

## 系统信息 / System Information

- **操作系统 / OS**: $($env:OS)
- **Rust 版本 / Rust Version**: $(rustc --version)
- **Cargo 版本 / Cargo Version**: $(cargo --version)

## 建议 / Recommendations

$(if (-not $BenchmarkSuccess) { "- 检查基准测试失败原因 / Check benchmark failure reasons" })
$(if (-not $MiriSuccess) { "- 修复内存安全问题 / Fix memory safety issues" })
$(if (-not $LoomSuccess) { "- 修复并发安全问题 / Fix concurrency safety issues" })

$(if ($BenchmarkSuccess -and $MiriSuccess -and $LoomSuccess) { "- 所有性能检查通过 / All performance checks passed" })
"@

    $report | Out-File -FilePath $reportPath -Encoding UTF8
    Write-Host "性能报告已生成: $reportPath / Performance report generated: $reportPath" -ForegroundColor Green
}

# 主执行逻辑 / Main execution logic
function Main {
    Test-RequiredTools
    
    $benchmarkSuccess = $true
    $miriSuccess = $true
    $loomSuccess = $true
    
    switch ($Target.ToLower()) {
        "benchmarks" {
            $benchmarkSuccess = Invoke-Benchmarks
        }
        "miri" {
            $miriSuccess = Invoke-MiriTests
        }
        "loom" {
            $loomSuccess = Invoke-LoomTests
        }
        "all" {
            $benchmarkSuccess = Invoke-Benchmarks
            $miriSuccess = Invoke-MiriTests
            $loomSuccess = Invoke-LoomTests
        }
        default {
            Write-Error "未知目标: $Target / Unknown target: $Target"
        }
    }
    
    New-PerformanceReport -BenchmarkSuccess $benchmarkSuccess -MiriSuccess $miriSuccess -LoomSuccess $loomSuccess
    
    # 总结 / Summary
    Write-Host "`n性能检查总结 / Performance check summary:" -ForegroundColor Cyan
    Write-Host "基准测试 / Benchmarks: $(if ($benchmarkSuccess) { '✅' } else { '❌' })" -ForegroundColor $(if ($benchmarkSuccess) { 'Green' } else { 'Red' })
    Write-Host "Miri 测试 / Miri Tests: $(if ($miriSuccess) { '✅' } else { '❌' })" -ForegroundColor $(if ($miriSuccess) { 'Green' } else { 'Red' })
    Write-Host "Loom 测试 / Loom Tests: $(if ($loomSuccess) { '✅' } else { '❌' })" -ForegroundColor $(if ($loomSuccess) { 'Green' } else { 'Red' })
    
    if ($benchmarkSuccess -and $miriSuccess -and $loomSuccess) {
        Write-Host "`n🎉 所有性能检查通过 / All performance checks passed!" -ForegroundColor Green
        exit 0
    } else {
        Write-Host "`n⚠️ 部分性能检查失败 / Some performance checks failed" -ForegroundColor Yellow
        exit 1
    }
}

# 执行主函数 / Execute main function
Main
