# 控制流和函数作业评估脚本 / Control Flow and Functions Assignment Assessment Script

param(
    [switch]$Verbose = $false,
    [switch]$GenerateReport = $false
)

$ErrorActionPreference = "Stop"

Write-Host "开始 c03_control_fn 作业评估 / Starting c03_control_fn assignment assessment..." -ForegroundColor Green

# 检查必要文件 / Check required files
function Test-RequiredFiles {
    Write-Host "检查必要文件 / Checking required files..." -ForegroundColor Yellow
    
    $requiredFiles = @(
        "crates/c03_control_fn/src/lib.rs",
        "crates/c03_control_fn/src/control_flow.rs",
        "crates/c03_control_fn/src/functions.rs",
        "crates/c03_control_fn/tests/integration_tests.rs"
    )
    
    $missingFiles = @()
    foreach ($file in $requiredFiles) {
        if (-not (Test-Path $file)) {
            $missingFiles += $file
        }
    }
    
    if ($missingFiles.Count -gt 0) {
        Write-Warning "缺少必要文件 / Missing required files:"
        foreach ($file in $missingFiles) {
            Write-Warning "  - $file"
        }
        return $false
    }
    
    Write-Host "所有必要文件存在 / All required files exist" -ForegroundColor Green
    return $true
}

# 检查控制流实现 / Check control flow implementation
function Test-ControlFlowImplementation {
    Write-Host "检查控制流实现 / Checking control flow implementation..." -ForegroundColor Yellow
    
    $score = 0
    $maxScore = 100
    
    # 检查 if-else 语句 / Check if-else statements
    $ifElseContent = Get-Content "crates/c03_control_fn/src/control_flow.rs" -Raw
    if ($ifElseContent -match "if\s+.*\s*\{") {
        $score += 20
        Write-Host "✅ if-else 语句实现 / if-else statements implemented" -ForegroundColor Green
    } else {
        Write-Warning "❌ if-else 语句缺失 / if-else statements missing"
    }
    
    # 检查 match 语句 / Check match statements
    if ($ifElseContent -match "match\s+.*\s*\{") {
        $score += 20
        Write-Host "✅ match 语句实现 / match statements implemented" -ForegroundColor Green
    } else {
        Write-Warning "❌ match 语句缺失 / match statements missing"
    }
    
    # 检查循环语句 / Check loop statements
    if ($ifElseContent -match "(for|while|loop)\s+.*\s*\{") {
        $score += 20
        Write-Host "✅ 循环语句实现 / loop statements implemented" -ForegroundColor Green
    } else {
        Write-Warning "❌ 循环语句缺失 / loop statements missing"
    }
    
    # 检查模式匹配 / Check pattern matching
    if ($ifElseContent -match "if\s+let\s+.*\s*=") {
        $score += 20
        Write-Host "✅ 模式匹配实现 / pattern matching implemented" -ForegroundColor Green
    } else {
        Write-Warning "❌ 模式匹配缺失 / pattern matching missing"
    }
    
    # 检查错误处理 / Check error handling
    if ($ifElseContent -match "(Result|Option)") {
        $score += 20
        Write-Host "✅ 错误处理实现 / error handling implemented" -ForegroundColor Green
    } else {
        Write-Warning "❌ 错误处理缺失 / error handling missing"
    }
    
    Write-Host "控制流实现得分: $score/$maxScore / Control flow implementation score: $score/$maxScore" -ForegroundColor Cyan
    return $score
}

# 检查函数实现 / Check function implementation
function Test-FunctionImplementation {
    Write-Host "检查函数实现 / Checking function implementation..." -ForegroundColor Yellow
    
    $score = 0
    $maxScore = 100
    
    $functionContent = Get-Content "crates/c03_control_fn/src/functions.rs" -Raw
    
    # 检查函数定义 / Check function definitions
    if ($functionContent -match "fn\s+\w+\s*\(") {
        $score += 20
        Write-Host "✅ 函数定义实现 / function definitions implemented" -ForegroundColor Green
    } else {
        Write-Warning "❌ 函数定义缺失 / function definitions missing"
    }
    
    # 检查参数和返回值 / Check parameters and return values
    if ($functionContent -match "->\s+\w+") {
        $score += 20
        Write-Host "✅ 参数和返回值实现 / parameters and return values implemented" -ForegroundColor Green
    } else {
        Write-Warning "❌ 参数和返回值缺失 / parameters and return values missing"
    }
    
    # 检查闭包 / Check closures
    if ($functionContent -match "\|\s*\w*\s*\|") {
        $score += 20
        Write-Host "✅ 闭包实现 / closures implemented" -ForegroundColor Green
    } else {
        Write-Warning "❌ 闭包缺失 / closures missing"
    }
    
    # 检查高阶函数 / Check higher-order functions
    if ($functionContent -match "(map|filter|fold|reduce)") {
        $score += 20
        Write-Host "✅ 高阶函数实现 / higher-order functions implemented" -ForegroundColor Green
    } else {
        Write-Warning "❌ 高阶函数缺失 / higher-order functions missing"
    }
    
    # 检查递归函数 / Check recursive functions
    if ($functionContent -match "fn\s+\w+.*\w+\s*\(") {
        $score += 20
        Write-Host "✅ 递归函数实现 / recursive functions implemented" -ForegroundColor Green
    } else {
        Write-Warning "❌ 递归函数缺失 / recursive functions missing"
    }
    
    Write-Host "函数实现得分: $score/$maxScore / Function implementation score: $score/$maxScore" -ForegroundColor Cyan
    return $score
}

# 检查测试覆盖 / Check test coverage
function Test-TestCoverage {
    Write-Host "检查测试覆盖 / Checking test coverage..." -ForegroundColor Yellow
    
    $score = 0
    $maxScore = 100
    
    # 运行测试 / Run tests
    try {
        if ($Verbose) {
            $testOutput = cargo test --package c03_control_fn 2>&1
            if ($LASTEXITCODE -eq 0) {
                $score += 50
                Write-Host "✅ 测试通过 / tests passed" -ForegroundColor Green
                if ($Verbose) {
                    Write-Host "测试输出 / Test output: $testOutput" -ForegroundColor Gray
                }
            } else {
                Write-Warning "❌ 测试失败 / tests failed"
                if ($Verbose) {
                    Write-Warning "测试错误 / Test error: $testOutput"
                }
            }
        } else {
            $null = cargo test --package c03_control_fn 2>&1
            if ($LASTEXITCODE -eq 0) {
                $score += 50
                Write-Host "✅ 测试通过 / tests passed" -ForegroundColor Green
            } else {
                Write-Warning "❌ 测试失败 / tests failed"
            }
        }
    } catch {
        Write-Warning "❌ 测试执行失败 / test execution failed: $_"
    }
    
    # 检查测试文件 / Check test files
    $testFiles = @(
        "crates/c03_control_fn/tests/integration_tests.rs",
        "crates/c03_control_fn/src/control_flow.rs",
        "crates/c03_control_fn/src/functions.rs"
    )
    
    $testCount = 0
    foreach ($file in $testFiles) {
        if (Test-Path $file) {
            $content = Get-Content $file -Raw
            if ($content -match "#\[test\]") {
                $testCount++
            }
        }
    }
    
    if ($testCount -ge 3) {
        $score += 50
        Write-Host "✅ 测试文件完整 / test files complete" -ForegroundColor Green
    } else {
        Write-Warning "❌ 测试文件不完整 / test files incomplete"
    }
    
    Write-Host "测试覆盖得分: $score/$maxScore / Test coverage score: $score/$maxScore" -ForegroundColor Cyan
    return $score
}

# 检查代码质量 / Check code quality
function Test-CodeQuality {
    Write-Host "检查代码质量 / Checking code quality..." -ForegroundColor Yellow
    
    $score = 0
    $maxScore = 100
    
    # 运行 clippy / Run clippy
    try {
        if ($Verbose) {
            $clippyOutput = cargo clippy --package c03_control_fn -- -D warnings 2>&1
            if ($LASTEXITCODE -eq 0) {
                $score += 50
                Write-Host "✅ Clippy 检查通过 / Clippy check passed" -ForegroundColor Green
                if ($Verbose) {
                    Write-Host "Clippy 输出 / Clippy output: $clippyOutput" -ForegroundColor Gray
                }
            } else {
                Write-Warning "❌ Clippy 检查失败 / Clippy check failed"
                if ($Verbose) {
                    Write-Warning "Clippy 错误 / Clippy error: $clippyOutput"
                }
            }
        } else {
            $null = cargo clippy --package c03_control_fn -- -D warnings 2>&1
            if ($LASTEXITCODE -eq 0) {
                $score += 50
                Write-Host "✅ Clippy 检查通过 / Clippy check passed" -ForegroundColor Green
            } else {
                Write-Warning "❌ Clippy 检查失败 / Clippy check failed"
            }
        }
    } catch {
        Write-Warning "❌ Clippy 执行失败 / Clippy execution failed: $_"
    }
    
    # 运行格式化检查 / Run format check
    try {
        if ($Verbose) {
            $fmtOutput = cargo fmt --package c03_control_fn -- --check 2>&1
            if ($LASTEXITCODE -eq 0) {
                $score += 50
                Write-Host "✅ 格式化检查通过 / format check passed" -ForegroundColor Green
                if ($Verbose) {
                    Write-Host "格式化检查输出 / Format check output: $fmtOutput" -ForegroundColor Gray
                }
            } else {
                Write-Warning "❌ 格式化检查失败 / format check failed"
                if ($Verbose) {
                    Write-Warning "格式化检查错误 / Format check error: $fmtOutput"
                }
            }
        } else {
            $null = cargo fmt --package c03_control_fn -- --check 2>&1
            if ($LASTEXITCODE -eq 0) {
                $score += 50
                Write-Host "✅ 格式化检查通过 / format check passed" -ForegroundColor Green
            } else {
                Write-Warning "❌ 格式化检查失败 / format check failed"
            }
        }
    } catch {
        Write-Warning "❌ 格式化检查执行失败 / format check execution failed: $_"
    }
    
    Write-Host "代码质量得分: $score/$maxScore / Code quality score: $score/$maxScore" -ForegroundColor Cyan
    return $score
}

# 生成评估报告 / Generate assessment report
function New-AssessmentReport {
    param(
        [int]$ControlFlowScore,
        [int]$FunctionScore,
        [int]$TestScore,
        [int]$QualityScore
    )
    
    if (-not $GenerateReport) {
        return
    }
    
    Write-Host "生成评估报告 / Generating assessment report..." -ForegroundColor Yellow
    
    $reportPath = "reports/c03_control_fn-assessment-$(Get-Date -Format 'yyyy-MM-dd-HH-mm-ss').md"
    $reportDir = Split-Path $reportPath -Parent
    
    if (-not (Test-Path $reportDir)) {
        New-Item -ItemType Directory -Path $reportDir -Force | Out-Null
    }
    
    $totalScore = $ControlFlowScore + $FunctionScore + $TestScore + $QualityScore
    $maxTotalScore = 400
    $percentage = [math]::Round(($totalScore / $maxTotalScore) * 100, 2)
    
    $grade = switch ($percentage) {
        { $_ -ge 95 } { "A+" }
        { $_ -ge 90 } { "A" }
        { $_ -ge 85 } { "B+" }
        { $_ -ge 80 } { "B" }
        { $_ -ge 75 } { "C+" }
        { $_ -ge 70 } { "C" }
        { $_ -ge 60 } { "D" }
        default { "F" }
    }
    
    $report = @"
# c03_control_fn 作业评估报告 / Assignment Assessment Report

**生成时间 / Generated**: $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')
**作业名称 / Assignment**: 控制流和函数 / Control Flow and Functions

## 评估结果 / Assessment Results

| 评估维度 / Assessment Dimension | 得分 / Score | 满分 / Max Score | 百分比 / Percentage |
|--------------------------------|-------------|------------------|-------------------|
| 控制流实现 / Control Flow Implementation | $ControlFlowScore | 100 | $([math]::Round(($ControlFlowScore / 100) * 100, 2))% |
| 函数实现 / Function Implementation | $FunctionScore | 100 | $([math]::Round(($FunctionScore / 100) * 100, 2))% |
| 测试覆盖 / Test Coverage | $TestScore | 100 | $([math]::Round(($TestScore / 100) * 100, 2))% |
| 代码质量 / Code Quality | $QualityScore | 100 | $([math]::Round(($QualityScore / 100) * 100, 2))% |

## 总分 / Total Score

**总分 / Total Score**: $totalScore / $maxTotalScore
**百分比 / Percentage**: $percentage%
**等级 / Grade**: $grade

## 详细评估 / Detailed Assessment

### 控制流实现 / Control Flow Implementation

- **if-else 语句**: $(if ($ControlFlowScore -ge 20) { "✅ 实现" } else { "❌ 缺失" })
- **match 语句**: $(if ($ControlFlowScore -ge 40) { "✅ 实现" } else { "❌ 缺失" })
- **循环语句**: $(if ($ControlFlowScore -ge 60) { "✅ 实现" } else { "❌ 缺失" })
- **模式匹配**: $(if ($ControlFlowScore -ge 80) { "✅ 实现" } else { "❌ 缺失" })
- **错误处理**: $(if ($ControlFlowScore -ge 100) { "✅ 实现" } else { "❌ 缺失" })

### 函数实现 / Function Implementation

- **函数定义**: $(if ($FunctionScore -ge 20) { "✅ 实现" } else { "❌ 缺失" })
- **参数和返回值**: $(if ($FunctionScore -ge 40) { "✅ 实现" } else { "❌ 缺失" })
- **闭包**: $(if ($FunctionScore -ge 60) { "✅ 实现" } else { "❌ 缺失" })
- **高阶函数**: $(if ($FunctionScore -ge 80) { "✅ 实现" } else { "❌ 缺失" })
- **递归函数**: $(if ($FunctionScore -ge 100) { "✅ 实现" } else { "❌ 缺失" })

### 测试覆盖 / Test Coverage

- **测试通过**: $(if ($TestScore -ge 50) { "✅ 通过" } else { "❌ 失败" })
- **测试文件完整**: $(if ($TestScore -ge 100) { "✅ 完整" } else { "❌ 不完整" })

### 代码质量 / Code Quality

- **Clippy 检查**: $(if ($QualityScore -ge 50) { "✅ 通过" } else { "❌ 失败" })
- **格式化检查**: $(if ($QualityScore -ge 100) { "✅ 通过" } else { "❌ 失败" })

## 改进建议 / Improvement Suggestions

$(if ($ControlFlowScore -lt 100) { "- 完善控制流实现，确保包含所有必要的控制结构 / Improve control flow implementation to include all necessary control structures" })
$(if ($FunctionScore -lt 100) { "- 完善函数实现，确保包含所有必要的函数特性 / Improve function implementation to include all necessary function features" })
$(if ($TestScore -lt 100) { "- 增加测试覆盖，确保所有功能都有测试 / Increase test coverage to ensure all features are tested" })
$(if ($QualityScore -lt 100) { "- 改进代码质量，遵循 Rust 最佳实践 / Improve code quality by following Rust best practices" })

$(if ($totalScore -eq $maxTotalScore) { "- 恭喜！所有评估项目都达到了优秀标准 / Congratulations! All assessment items meet excellent standards" })

## 学习资源 / Learning Resources

- [Rust 控制流文档](https://doc.rust-lang.org/book/ch03-05-control-flow.html)
- [Rust 函数文档](https://doc.rust-lang.org/book/ch03-03-how-functions-work.html)
- [Rust 测试文档](https://doc.rust-lang.org/book/ch11-00-testing.html)
- [Rust 最佳实践](https://doc.rust-lang.org/book/ch01-02-hello-world.html)
"@

    $report | Out-File -FilePath $reportPath -Encoding UTF8
    Write-Host "评估报告已生成: $reportPath / Assessment report generated: $reportPath" -ForegroundColor Green
}

# 主执行逻辑 / Main execution logic
function Main {
    if (-not (Test-RequiredFiles)) {
        Write-Error "必要文件检查失败 / Required files check failed"
        exit 1
    }
    
    $controlFlowScore = Test-ControlFlowImplementation
    $functionScore = Test-FunctionImplementation
    $testScore = Test-TestCoverage
    $qualityScore = Test-CodeQuality
    
    New-AssessmentReport -ControlFlowScore $controlFlowScore -FunctionScore $functionScore -TestScore $testScore -QualityScore $qualityScore
    
    # 总结 / Summary
    $totalScore = $controlFlowScore + $functionScore + $testScore + $qualityScore
    $maxTotalScore = 400
    $percentage = [math]::Round(($totalScore / $maxTotalScore) * 100, 2)
    
    $grade = switch ($percentage) {
        { $_ -ge 95 } { "A+" }
        { $_ -ge 90 } { "A" }
        { $_ -ge 85 } { "B+" }
        { $_ -ge 80 } { "B" }
        { $_ -ge 75 } { "C+" }
        { $_ -ge 70 } { "C" }
        { $_ -ge 60 } { "D" }
        default { "F" }
    }
    
    Write-Host "`nc03_control_fn 作业评估总结 / Assignment assessment summary:" -ForegroundColor Cyan
    Write-Host "控制流实现 / Control Flow: $controlFlowScore/100" -ForegroundColor $(if ($controlFlowScore -ge 80) { 'Green' } else { 'Red' })
    Write-Host "函数实现 / Functions: $functionScore/100" -ForegroundColor $(if ($functionScore -ge 80) { 'Green' } else { 'Red' })
    Write-Host "测试覆盖 / Tests: $testScore/100" -ForegroundColor $(if ($testScore -ge 80) { 'Green' } else { 'Red' })
    Write-Host "代码质量 / Quality: $qualityScore/100" -ForegroundColor $(if ($qualityScore -ge 80) { 'Green' } else { 'Red' })
    Write-Host "总分 / Total: $totalScore/$maxTotalScore ($percentage%)" -ForegroundColor Cyan
    Write-Host "等级 / Grade: $grade" -ForegroundColor $(if ($percentage -ge 80) { 'Green' } else { 'Red' })
    
    if ($percentage -ge 80) {
        Write-Host "`n🎉 作业评估通过 / Assignment assessment passed!" -ForegroundColor Green
        exit 0
    } else {
        Write-Host "`n⚠️ 作业需要改进 / Assignment needs improvement" -ForegroundColor Yellow
        exit 1
    }
}

# 执行主函数 / Execute main function
Main
