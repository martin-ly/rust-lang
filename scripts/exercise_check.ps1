#!/usr/bin/env pwsh
<#
.SYNOPSIS
    Rust 练习题自动化评测脚本 (PowerShell)
.DESCRIPTION
    遍历 exercises/ 目录，运行每个练习的测试，生成评分报告。
    支持按主题筛选。
.PARAMETER Topic
    要筛选的主题，可选值：
    ownership_borrowing, type_system, generics_traits,
    concurrency, async_programming, error_handling,
    macros, unsafe_rust, rustlings, all
.PARAMETER Json
    以 JSON 格式输出报告
.EXAMPLE
    .\scripts\exercise-check.ps1
    .\scripts\exercise-check.ps1 -Topic concurrency
    .\scripts\exercise-check.ps1 -Topic all -Json
#>

param(
    [string]$Topic = "all",
    [switch]$Json
)

$ErrorActionPreference = "Stop"

# 颜色代码
$Green = "`e[32m"
$Red = "`e[31m"
$Yellow = "`e[33m"
$Cyan = "`e[36m"
$Reset = "`e[0m"

# 主题配置
$topicConfig = @{
    "ownership_borrowing" = @{ filter = "ownership_borrowing::"; label = "所有权与借用" }
    "type_system"         = @{ filter = "type_system::"; label = "类型系统" }
    "generics_traits"     = @{ filter = "generics_traits::"; label = "泛型与特质" }
    "concurrency"         = @{ filter = "concurrency::"; label = "并发编程" }
    "async_programming"   = @{ filter = "async_programming::"; label = "异步编程" }
    "error_handling"      = @{ filter = "error_handling::"; label = "错误处理" }
    "macros"              = @{ filter = "macros::"; label = "宏系统" }
    "unsafe_rust"         = @{ filter = "unsafe_rust::"; label = "Unsafe Rust" }
    "rustlings"           = @{ filter = $null; label = "Rustlings 风格" }
}

function Write-ColorLine($text, $color) {
    Write-Host "$color$text$Reset"
}

function Test-ExercisesCrate($filter) {
    $result = @{
        topic = $filter
        tests_run = 0
        tests_passed = 0
        tests_failed = 0
        status = "unknown"
        output = ""
    }

    try {
        $cmd = "cargo test -p exercises --lib $filter"
        $proc = Start-Process -FilePath "cmd" -ArgumentList "/c", $cmd -WorkingDirectory (Get-Location) -PassThru -RedirectStandardOutput "__ex_stdout.txt" -RedirectStandardError "__ex_stderr.txt" -WindowStyle Hidden -Wait
        $stdout = Get-Content "__ex_stdout.txt" -Raw -ErrorAction SilentlyContinue
        $stderr = Get-Content "__ex_stderr.txt" -Raw -ErrorAction SilentlyContinue
        Remove-Item "__ex_stdout.txt", "__ex_stderr.txt" -ErrorAction SilentlyContinue
        $text = ($stdout + "`n" + $stderr)
        $result.output = $text

        # 解析测试结果
        if ($text -match "test result: ok\. (\d+) passed; (\d+) failed;") {
            $result.tests_passed = [int]$Matches[1]
            $result.tests_failed = [int]$Matches[2]
            $result.tests_run = $result.tests_passed + $result.tests_failed
            $result.status = if ($result.tests_failed -eq 0) { "passed" } else { "partial" }
        }
        elseif ($text -match "test result: FAILED\. (\d+) passed; (\d+) failed;") {
            $result.tests_passed = [int]$Matches[1]
            $result.tests_failed = [int]$Matches[2]
            $result.tests_run = $result.tests_passed + $result.tests_failed
            $result.status = if ($result.tests_passed -gt 0) { "partial" } else { "failed" }
        }
        elseif ($text -match "running 0 tests") {
            $result.status = "no_tests"
            $result.tests_run = 0
        }
        else {
            $result.status = "failed"
            $result.tests_run = 0
        }
    }
    catch {
        $result.status = "failed"
        $result.output = $_.Exception.Message
    }

    return $result
}

function Test-RustlingsStyle {
    $results = @()
    $rustlingsDir = Join-Path (Join-Path (Join-Path $PSScriptRoot "..") "exercises") "rustlings_style"

    if (-not (Test-Path $rustlingsDir)) {
        return $results
    }

    $dirs = Get-ChildItem -Path $rustlingsDir -Directory | Sort-Object Name
    foreach ($dir in $dirs) {
        $cargoToml = Join-Path $dir.FullName "Cargo.toml"
        if (-not (Test-Path $cargoToml)) { continue }

        $item = @{
            name = $dir.Name
            path = $dir.FullName
            status = "unknown"
            tests_run = 0
            tests_passed = 0
            tests_failed = 0
            output = ""
        }

        try {
            $cmd = "cargo test --manifest-path `"$cargoToml`""
            $proc = Start-Process -FilePath "cmd" -ArgumentList "/c", $cmd -WorkingDirectory (Get-Location) -PassThru -RedirectStandardOutput "__rl_stdout.txt" -RedirectStandardError "__rl_stderr.txt" -WindowStyle Hidden -Wait
            $stdout = Get-Content "__rl_stdout.txt" -Raw -ErrorAction SilentlyContinue
            $stderr = Get-Content "__rl_stderr.txt" -Raw -ErrorAction SilentlyContinue
            Remove-Item "__rl_stdout.txt", "__rl_stderr.txt" -ErrorAction SilentlyContinue
            $text = ($stdout + "`n" + $stderr)
            $item.output = $text

            if ($text -match "test result: ok\. (\d+) passed; (\d+) failed;") {
                $item.tests_passed = [int]$Matches[1]
                $item.tests_failed = [int]$Matches[2]
                $item.tests_run = $item.tests_passed + $item.tests_failed
                $item.status = if ($item.tests_failed -eq 0) { "passed" } else { "partial" }
            }
            elseif ($text -match "test result: FAILED\. (\d+) passed; (\d+) failed;") {
                $item.tests_passed = [int]$Matches[1]
                $item.tests_failed = [int]$Matches[2]
                $item.tests_run = $item.tests_passed + $item.tests_failed
                $item.status = if ($item.tests_passed -gt 0) { "partial" } else { "failed" }
            }
            elseif ($text -match "test result: ok\. 0 passed; 0 failed;") {
                $item.status = "no_tests"
                $item.tests_run = 0
            }
            elseif ($text -match "error\[E") {
                # Rustlings 风格练习预期编译失败
                $item.status = "broken"
                $item.tests_run = 0
            }
            elseif ($text -match "error") {
                $item.status = "failed"
                $item.tests_run = 0
            }
            else {
                $item.status = "no_tests"
                $item.tests_run = 0
            }
        }
        catch {
            $item.status = "failed"
            $item.output = $_.Exception.Message
        }

        $results += $item
    }

    return $results
}

# ====== 主程序 ======

Push-Location (Join-Path $PSScriptRoot "..")

try {
    $allResults = @()

    if ($Topic -eq "all") {
        $topicsToRun = $topicConfig.Keys | Sort-Object
    }
    else {
        if (-not $topicConfig.ContainsKey($Topic)) {
            Write-ColorLine "错误: 未知主题 '$Topic'" $Red
            Write-Host "可用主题: $($topicConfig.Keys -join ', ')"
            exit 1
        }
        $topicsToRun = @($Topic)
    }

    foreach ($t in $topicsToRun) {
        $cfg = $topicConfig[$t]
        if ($t -eq "rustlings") {
            $rustlingResults = Test-RustlingsStyle
            foreach ($r in $rustlingResults) {
                $allResults += @{
                    topic = "rustlings"
                    label = "Rustlings: $($r.name)"
                    filter = $r.name
                    status = $r.status
                    tests_run = $r.tests_run
                    tests_passed = $r.tests_passed
                    tests_failed = $r.tests_failed
                }
            }
        }
        else {
            $result = Test-ExercisesCrate $cfg.filter
            $result.topic = $t
            $result.label = $cfg.label
            $allResults += $result
        }
    }

    # 统计
    $totalPassed = 0
    $totalFailed = 0
    $totalPartial = 0
    $totalTestsRun = 0
    $totalTestsPassed = 0
    foreach ($r in $allResults) {
        switch ($r.status) {
            "passed"  { $totalPassed++ }
            "failed"  { $totalFailed++ }
            "partial" { $totalPartial++ }
            "broken"  { $totalPartial++ }
        }
        $totalTestsRun += $r.tests_run
        $totalTestsPassed += $r.tests_passed
    }

    if ($Json) {
        $jsonObj = @{
            summary = @{
                topics_checked = $allResults.Count
                passed = $totalPassed
                failed = $totalFailed
                partial = $totalPartial
                total_tests_run = $totalTestsRun
                total_tests_passed = $totalTestsPassed
            }
            details = $allResults
        }
        $jsonObj | ConvertTo-Json -Depth 3
    }
    else {
        Write-Host ""
        Write-ColorLine "═══════════════════════════════════════════" $Cyan
        Write-ColorLine "      Rust 练习题自动化评测报告" $Cyan
        Write-ColorLine "═══════════════════════════════════════════" $Cyan
        Write-Host ""

        foreach ($r in $allResults) {
            $color = switch ($r.status) {
                "passed"  { $Green }
                "failed"  { $Red }
                "partial" { $Yellow }
                "broken"  { $Cyan }
                default   { $Yellow }
            }
            $icon = switch ($r.status) {
                "passed"  { "✓" }
                "failed"  { "✗" }
                "partial" { "◐" }
                "broken"  { "⚒" }
                default   { "?" }
            }
            $label = if ($r.label) { $r.label } else { $r.topic }
            Write-Host "$icon [$($r.status.ToUpper().PadRight(7))] " -NoNewline
            Write-ColorLine "$label ($($r.tests_passed)/$($r.tests_run) 测试通过)" $color
        }

        Write-Host ""
        Write-ColorLine "───────────────────────────────────────────" $Cyan
        Write-Host "  主题数: $($allResults.Count)"
        Write-ColorLine "  通过  : $totalPassed" $Green
        Write-ColorLine "  失败  : $totalFailed" $Red
        Write-ColorLine "  部分  : $totalPartial" $Yellow
        Write-Host "  测试数: $totalTestsPassed / $totalTestsRun 通过"
        Write-ColorLine "───────────────────────────────────────────" $Cyan

        if ($totalFailed -eq 0 -and $totalPartial -eq 0) {
            Write-Host ""
            Write-ColorLine "🎉 所有测试全部通过！" $Green
        }
        elseif ($totalFailed -eq 0) {
            Write-Host ""
            Write-ColorLine "⚠️  所有主题都有测试通过，但部分未完全通过。" $Yellow
        }
        else {
            Write-Host ""
            Write-ColorLine "❌ 存在完全失败的主题，请检查输出。" $Red
        }
        Write-Host ""
    }
}
finally {
    Pop-Location
}
