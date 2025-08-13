Param(
    [Parameter(Mandatory=$true, Position=0)]
    [string]$TargetDir,

    [switch]$DryRun,
    [switch]$NoBackup
)

$ErrorActionPreference = "Stop"

function Write-Info($msg) { Write-Host "[INFO] $msg" -ForegroundColor Cyan }
function Write-Success($msg) { Write-Host "[SUCCESS] $msg" -ForegroundColor Green }
function Write-WarningMsg($msg) { Write-Host "[WARNING] $msg" -ForegroundColor Yellow }
function Write-ErrorMsg($msg) { Write-Host "[ERROR] $msg" -ForegroundColor Red }

if (-not (Test-Path $TargetDir)) {
    Write-ErrorMsg "目标目录不存在: $TargetDir"
    exit 1
}

# 标准必需章节
$RequiredSections = @(
    "概述","技术背景","核心概念","技术实现","形式化分析",
    "应用案例","性能分析","最佳实践","常见问题","未来展望"
)

# 统计
$Results = @()
$files = Get-ChildItem -Path $TargetDir -Include *.md -Recurse -File

Write-Info "开始结构自动补全(模板) ..."
Write-Info "目标目录: $TargetDir"
Write-Info "试运行: $($DryRun.IsPresent)"
Write-Info "备份: $(-not $NoBackup.IsPresent)"

foreach ($file in $files) {
    try { $content = Get-Content -LiteralPath $file.FullName -Raw -Encoding UTF8 } catch { try { $content = Get-Content -LiteralPath $file.FullName -Raw } catch { $content = '' } }
    if ($null -eq $content) { $content = '' }

    # 提取现有章节标题
    $existingSections = @()
    foreach ($sec in $RequiredSections) {
        if ($content -match "(?m)^(?:#){1,6}\s*.*$sec.*$") { $existingSections += $sec }
    }

    $missing = @()
    foreach ($sec in $RequiredSections) { if (-not ($existingSections -contains $sec)) { $missing += $sec } }

    $added = 0
    $newContent = $content

    if ($missing.Count -gt 0 -and -not $DryRun) {
        if (-not $NoBackup) { Set-Content -LiteralPath ("$($file.FullName).backup.struct") -Value $content -Encoding UTF8 }
        # 在文末追加缺失章节的占位段落
        $append = """`n`n---`n`n<!-- 以下为按标准模板自动补全的占位章节，待后续填充 -->`n"""
        foreach ($m in $missing) {
            $append += "`n## $m`n(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n"
            $added++
        }
        $newContent = $content + $append
        Set-Content -LiteralPath $file.FullName -Value $newContent -Encoding UTF8
    }

    $Results += [pscustomobject]@{
        FilePath = $file.FullName
        MissingCount = $missing.Count
        MissingList = ($missing -join ', ')
        AddedCount = if ($DryRun) { 0 } else { $added }
        Success = $true
    }
}

# 生成报告
$reportPath = Join-Path $TargetDir "structure_autofix_template_report.md"
$fixedFiles = ($Results | Where-Object { $_.AddedCount -gt 0 })
$sumAdded = ($fixedFiles | Measure-Object -Property AddedCount -Sum).Sum
$sumMissing = ($Results | Measure-Object -Property MissingCount -Sum).Sum

$lines = @()
$lines += "# 结构自动补全(模板) 报告`n"
$lines += "## 总体统计"
$lines += "- 处理文件数: $($Results.Count)"
$lines += "- 总缺失章节数: $sumMissing"
$lines += "- 实际补全章节数: $sumAdded"
$lines += "- 试运行: $($DryRun.IsPresent)" + "`n"
$lines += "## 文件详情"
foreach ($r in $Results) {
    if ($r.MissingCount -gt 0) {
        $lines += "### $($r.FilePath)"
        $lines += "- 缺失章节数: $($r.MissingCount)"
        $lines += "- 缺失列表: $($r.MissingList)"
        $lines += "- 本次补全: $($r.AddedCount)" + "`n"
    }
}
$lines -join "`n" | Set-Content -LiteralPath $reportPath -Encoding UTF8

Write-Success "补全报告已生成: $reportPath"
if (-not $DryRun) { Write-Success "已补全部分缺失章节占位标题，共计: $sumAdded" } else { Write-Info "试运行完成(未修改文件)" } 