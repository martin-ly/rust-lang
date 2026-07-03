<#
.SYNOPSIS
    Cargo update automation check script
.DESCRIPTION
    Runs cargo update, generates report, and optionally runs cargo audit.
    Supports --dry-run, --weekly, and --format modes.
.PARAMETER DryRun
    Show packages that would be updated without applying changes
.PARAMETER Weekly
    Weekly check mode: only check without applying updates, generate Markdown report
.PARAMETER Format
    Output format: text (default), markdown, email
#>
[CmdletBinding()]
param(
    [switch]$DryRun,
    [switch]$Weekly,
    [string]$Format = "text"
)

$ErrorActionPreference = "Stop"
$scriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$projectRoot = Resolve-Path (Join-Path $scriptDir "..")
Set-Location $projectRoot

# 确定运行模式
$isWeekly = $Weekly -or ($Format -eq "markdown") -or ($Format -eq "email")
$isDryRun = $DryRun -or $isWeekly

$report = [System.Collections.Generic.List[string]]::new()
$markdownReport = [System.Collections.Generic.List[string]]::new()
$emailReport = [System.Collections.Generic.List[string]]::new()

function Add-ReportLine($Line) {
    $report.Add($Line)
    Write-Host $Line
}

function Add-MarkdownLine($Line) {
    $markdownReport.Add($Line)
}

function Add-EmailLine($Line) {
    $emailReport.Add($Line)
}

# ===== 文本报告 =====
Add-ReportLine "========================================"
Add-ReportLine "Cargo Update Check Report"
Add-ReportLine "Date: $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')"
Add-ReportLine "Project: $projectRoot"
Add-ReportLine "Mode: $(if ($isDryRun) { 'DRY-RUN' } else { 'LIVE' })$(if ($isWeekly) { ' (WEEKLY)' })"
Add-ReportLine "========================================"

# ===== Markdown 报告头 =====
Add-MarkdownLine "# 📦 依赖更新周报"
Add-MarkdownLine ""
Add-MarkdownLine "> **生成时间:** $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')  
"
Add-MarkdownLine "> **项目:** rust-lang  
"
Add-MarkdownLine "> **模式:** $(if ($isDryRun) { '只读检查' } else { '实际更新' })"
Add-MarkdownLine ""

# ===== Email 报告头 =====
Add-EmailLine "Subject: [rust-lang] 每周依赖更新检查 - $(Get-Date -Format 'yyyy-MM-dd')"
Add-EmailLine "From: automation@rust-lang.local"
Add-EmailLine "To: maintainers@rust-lang.local"
Add-EmailLine ""
Add-EmailLine "========================================"
Add-EmailLine "📦 rust-lang 每周依赖更新检查"
Add-EmailLine "========================================"
Add-EmailLine "生成时间: $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')"
Add-EmailLine ""

# Verify cargo
try {
    $cv = cargo --version 2>$null
    Add-ReportLine "Cargo: $cv"
    Add-MarkdownLine "- **Cargo:** $cv"
    Add-EmailLine "Cargo: $cv"
} catch {
    Write-Error "cargo not found"
    exit 1
}

Add-MarkdownLine ""

# Outdated check
$hasOutdated = [bool](Get-Command cargo-outdated -ErrorAction SilentlyContinue)
$outdatedPackages = @()
if ($hasOutdated) {
    Add-ReportLine ""
    Add-ReportLine "--- Outdated Packages ---"
    Add-MarkdownLine "## 📊 过期依赖概览"
    Add-MarkdownLine ""
    Add-EmailLine "--- 过期依赖概览 ---"
    Add-EmailLine ""
    try {
        $out = cargo outdated -R 2>&1
        $out | ForEach-Object {
            $s = "$_"
            Add-ReportLine "$s"
            if ($s -match '^([^\s]+)\s+v?([\d\.\-+a-zA-Z]+)\s+->\s+v?([\d\.\-+a-zA-Z]+)') {
                $outdatedPackages += [PSCustomObject]@{ Package=$matches[1]; Old=$matches[2]; New=$matches[3] }
            }
        }
    } catch { Add-ReportLine "cargo outdated failed: $_" }
    
    if ($outdatedPackages.Count -gt 0) {
        Add-MarkdownLine "| 包名 | 当前版本 | 最新版本 | 优先级 |"
        Add-MarkdownLine "|------|----------|----------|--------|"
        foreach ($pkg in $outdatedPackages) {
            $priority = "普通"
            if ($pkg.New -match "^(0\.\d+|[1-9]\d*)\.(0\d*|[1-9]\d*)\.(0\d*|[1-9]\d*)") {
                $majorDiff = [int]$matches[2] - [int]($pkg.Old -replace "^.*\.(\d+)\..*$","`$1")
                if ($majorDiff -gt 0) { $priority = "🔴 高（主版本更新）" }
                elseif ($majorDiff -lt 0) { $priority = "普通" }
                else { $priority = "🟡 中（次版本更新）" }
            }
            Add-MarkdownLine "| $($pkg.Package) | $($pkg.Old) | $($pkg.New) | $priority |"
            Add-EmailLine "  $($pkg.Package) $($pkg.Old) -> $($pkg.New) [$priority]"
        }
    } else {
        Add-MarkdownLine "✅ 所有根依赖均为最新版本。"
        Add-EmailLine "✅ 所有根依赖均为最新版本。"
    }
} else {
    Add-ReportLine "Note: cargo-outdated not installed"
    Add-MarkdownLine "⚠️ 未安装 cargo-outdated，无法获取过期依赖信息。"
    Add-EmailLine "⚠️ 未安装 cargo-outdated，无法获取过期依赖信息。"
}

Add-MarkdownLine ""

# Cargo update
Add-ReportLine ""
Add-ReportLine "--- cargo update $(if ($isDryRun) { '--dry-run' }) ---"
Add-MarkdownLine "## 🔄 可更新依赖详情"
Add-MarkdownLine ""
Add-EmailLine "--- 可更新依赖详情 ---"
Add-EmailLine ""

$updateArgs = @("update"); if ($isDryRun) { $updateArgs += "--dry-run" }
$updateOutput = & cargo @updateArgs 2>&1
$updated = @()
$locked = @()
foreach ($line in $updateOutput) {
    $s = "$line"
    if ($s -match '^\s+Updating\s+(\S+)\s+v?([\d\.\-+a-zA-Z]+)\s+->\s+v?([\d\.\-+a-zA-Z]+)') {
        $updated += [PSCustomObject]@{ Package=$matches[1]; Old=$matches[2]; New=$matches[3] }
    } elseif ($s -match '^\s+Locking\s') { $locked += $s.Trim() }
}

if ($updated.Count -gt 0) {
    Add-ReportLine "Packages Updated:"
    Add-MarkdownLine "| 包名 | 旧版本 | 新版本 |"
    Add-MarkdownLine "|------|--------|--------|"
    $updated | ForEach-Object {
        Add-ReportLine ("  {0,-40} {1,-20} -> {2}" -f $_.Package, $_.Old, $_.New)
        Add-MarkdownLine "| $($_.Package) | $($_.Old) | $($_.New) |"
        Add-EmailLine "  $($_.Package) $($_.Old) -> $($_.New)"
    }
} else {
    Add-ReportLine "No packages were updated."
    Add-MarkdownLine "✅ 无可更新依赖（所有依赖均已锁定到最新兼容版本）。"
    Add-EmailLine "✅ 无可更新依赖。"
}
if ($locked.Count -gt 0) {
    Add-ReportLine "Locked/Unchanged count: $($locked.Count)"
    Add-MarkdownLine ""
    Add-MarkdownLine "- 锁定/未变更依赖数: **$($locked.Count)**"
}

Add-MarkdownLine ""

# Audit
Add-ReportLine ""
Add-ReportLine "--- Security Audit ---"
Add-MarkdownLine "## 🔒 安全审计"
Add-MarkdownLine ""
Add-EmailLine "--- 安全审计 ---"
Add-EmailLine ""

$hasAudit = [bool](Get-Command cargo-audit -ErrorAction SilentlyContinue)
$auditWarnings = $false
if ($hasAudit) {
    try {
        $aout = cargo audit --json 2>$null | ConvertFrom-Json -ErrorAction SilentlyContinue
        if ($aout.vulnerabilities.list.Count -gt 0) {
            $auditWarnings = $true
            Add-ReportLine "⚠️ Found $($aout.vulnerabilities.list.Count) vulnerabilities"
            Add-MarkdownLine "🔴 发现 **$($aout.vulnerabilities.list.Count)** 个安全漏洞："
            Add-EmailLine "🔴 发现 $($aout.vulnerabilities.list.Count) 个安全漏洞："
            foreach ($v in $aout.vulnerabilities.list) {
                Add-MarkdownLine "- **$($v.advisory.package)** ($($v.advisory.id)): $($v.advisory.title)"
                Add-EmailLine "  - $($v.advisory.package) ($($v.advisory.id)): $($v.advisory.title)"
            }
        } else {
            Add-ReportLine "No security advisories found."
            Add-MarkdownLine "✅ 未发现安全漏洞。"
            Add-EmailLine "✅ 未发现安全漏洞。"
        }
    } catch {
        Add-ReportLine "cargo audit failed: $_"
        Add-MarkdownLine "⚠️ cargo audit 执行失败，请手动检查。"
        Add-EmailLine "⚠️ cargo audit 执行失败，请手动检查。"
    }
} else {
    Add-ReportLine "Note: cargo-audit not installed"
    Add-MarkdownLine "⚠️ 未安装 cargo-audit，无法执行安全审计。"
    Add-EmailLine "⚠️ 未安装 cargo-audit，无法执行安全审计。"
}

Add-MarkdownLine ""

# Recommendations
Add-ReportLine ""
Add-ReportLine "--- Recommendations ---"
Add-ReportLine "  libp2p  - verify hickory-resolver compatibility before upgrading to 0.56+"
Add-ReportLine "  dioxus  - check for stable releases when upgrading from RC"
Add-ReportLine "  sea-orm - 2.0.0 is still in RC; verify API stability before upgrading"
Add-ReportLine "  bincode - keep pinned at 2.0.1 until 3.0 stable is released"

Add-MarkdownLine "## 💡 更新建议"
Add-MarkdownLine ""
Add-MarkdownLine "| 包名 | 建议 |"
Add-MarkdownLine "|------|------|"
Add-MarkdownLine "| libp2p | 升级到 0.56+ 前验证 hickory-resolver 兼容性 |"
Add-MarkdownLine "| dioxus | 从 RC 升级时检查是否有稳定版发布 |"
Add-MarkdownLine "| sea-orm | 2.0.0 仍为 RC；升级前验证 API 稳定性 |"
Add-MarkdownLine "| bincode | 3.0 稳定版发布前保持锁定在 2.0.1 |"
Add-MarkdownLine ""

Add-EmailLine "--- 更新建议 ---"
Add-EmailLine "  libp2p  - 升级到 0.56+ 前验证 hickory-resolver 兼容性"
Add-EmailLine "  dioxus  - 从 RC 升级时检查是否有稳定版发布"
Add-EmailLine "  sea-orm - 2.0.0 仍为 RC；升级前验证 API 稳定性"
Add-EmailLine "  bincode - 3.0 稳定版发布前保持锁定在 2.0.1"
Add-EmailLine ""

# 周报模板专用区域
if ($isWeekly) {
    Add-MarkdownLine "## 📋 本周行动项"
    Add-MarkdownLine ""
    Add-MarkdownLine "- [ ] 审核上述过期依赖，确认是否安全升级"
    Add-MarkdownLine "- [ ] 处理安全审计中发现的问题（如有）"
    Add-MarkdownLine "- [ ] 运行 `cargo test --workspace` 验证兼容性"
    Add-MarkdownLine "- [ ] 运行 `cargo clippy --workspace` 检查警告"
    Add-MarkdownLine "- [ ] 更新 CHANGELOG.md（如应用了更新）"
    Add-MarkdownLine ""
    Add-MarkdownLine "## 📝 备注"
    Add-MarkdownLine ""
    Add-MarkdownLine "<!-- 在此填写本周特殊情况说明 -->"
    Add-MarkdownLine ""
    Add-MarkdownLine "---"
    Add-MarkdownLine ""
    Add-MarkdownLine "*此报告由自动化脚本生成。*"
}

Add-ReportLine ""
Add-ReportLine "========================================"
Add-ReportLine "Report Complete"
Add-ReportLine "========================================"

# 保存报告
$timestamp = Get-Date -Format 'yyyyMMdd-HHmmss'
$outDir = Join-Path $projectRoot "target"
New-Item -ItemType Directory -Force -Path $outDir | Out-Null

# 保存文本报告
$outFile = Join-Path $outDir "cargo-update-report-$timestamp.txt"
$report | Out-File -FilePath $outFile -Encoding UTF8
Add-ReportLine ""
Add-ReportLine "Text report saved to: $outFile"

# 保存 Markdown 报告（weekly 模式或 format=markdown）
if ($isWeekly -or $Format -eq "markdown") {
    $mdFile = Join-Path $outDir "cargo-update-weekly-$timestamp.md"
    $markdownReport | Out-File -FilePath $mdFile -Encoding UTF8
    Add-ReportLine "Markdown report saved to: $mdFile"
}

# 保存 Email 报告
if ($Format -eq "email") {
    $emailFile = Join-Path $outDir "cargo-update-email-$timestamp.txt"
    $emailReport | Out-File -FilePath $emailFile -Encoding UTF8
    Add-ReportLine "Email report saved to: $emailFile"
}
