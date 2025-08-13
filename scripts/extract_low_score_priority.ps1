Param(
    [string]$ReportPath = "formal_rust/structure_check_report.md",
    [string]$OutputPath = "formal_rust/STRUCTURE_LOW_SCORE_PRIORITY.md",
    [int]$ComplianceThreshold = 95,
    [int]$Top = 200
)

$ErrorActionPreference = "Stop"

function Write-Info($msg) { Write-Host "[INFO] $msg" -ForegroundColor Cyan }
function Write-Success($msg) { Write-Host "[SUCCESS] $msg" -ForegroundColor Green }
function Write-ErrorMsg($msg) { Write-Host "[ERROR] $msg" -ForegroundColor Red }

if (-not (Test-Path $ReportPath)) {
    Write-ErrorMsg "未找到结构检查报告: $ReportPath"
    exit 1
}

Write-Info "读取结构检查报告: $ReportPath"
$lines = Get-Content -LiteralPath $ReportPath -Encoding UTF8

$results = @()
$current = $null

foreach ($line in $lines) {
    if ($line -match '^###\s+(.+)$') {
        if ($null -ne $current) { $results += $current }
        $current = [pscustomobject]@{
            Path = $matches[1].Trim()
            StructureScore = $null
            Compliance = $null
            Missing = @()
        }
        continue
    }
    if ($null -eq $current) { continue }

    if ($line -match '-\s*结构分数:\s*([0-9]+)\/100') {
        $current.StructureScore = [int]$matches[1]
        continue
    }
    if ($line -match '-\s*合规率:\s*([0-9]+(?:\.[0-9]+)?)%') {
        $current.Compliance = [double]$matches[1]
        continue
    }
    if ($line -match '^-\s*缺失章节:\s*(.+)$') {
        $missing = $matches[1].Trim()
        if ($missing.Length -gt 0) {
            $current.Missing = $missing -split '\s*,\s*'
        }
        continue
    }
}
if ($null -ne $current) { $results += $current }

# 过滤：合规率低于阈值或存在缺失章节
$filtered = $results | Where-Object { ($_ -ne $null) -and (($_.Compliance -lt $ComplianceThreshold) -or ($_.Missing.Count -gt 0)) }

# 计算优先级分数：缺失章节权重5分，合规率差距权重1分
$ranked = $filtered | ForEach-Object {
    $missingCount = if ($_.Missing) { $_.Missing.Count } else { 0 }
    $gap = if ($_.Compliance -ne $null) { [math]::Max(0, $ComplianceThreshold - $_.Compliance) } else { $ComplianceThreshold }
    $priority = $gap + ($missingCount * 5)
    [pscustomobject]@{
        Path = $_.Path
        StructureScore = $_.StructureScore
        Compliance = if ($_.Compliance -ne $null) { [math]::Round($_.Compliance,2) } else { 0 }
        MissingCount = $missingCount
        MissingList = if ($missingCount -gt 0) { ($_.Missing -join ', ') } else { '' }
        Priority = [math]::Round($priority,2)
    }
}

$sorted = $ranked | Sort-Object -Property @{Expression='Priority';Descending=$true}, @{Expression='StructureScore';Ascending=$true}
$topN = $sorted | Select-Object -First $Top

# 输出Markdown
$lines = @()
$lines += "# 结构低分/缺失章节 优先级清单"
$lines += ""
$lines += "- 生成时间: $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')"
$lines += "- 报告来源: $ReportPath"
$lines += "- 合规率阈值: $ComplianceThreshold%"
$lines += "- TOP条目数: $Top"
$lines += ""
$lines += "## 概览"
$lines += "- 总条目: $($sorted.Count)"
$lines += "- 缺失章节条目: $((($sorted | Where-Object { $_.MissingCount -gt 0 }).Count))"
$lines += "- 低于阈值条目: $((($sorted | Where-Object { $_.Compliance -lt $ComplianceThreshold }).Count))"
$lines += ""
$lines += "## 优先级列表 (TOP $Top)"
$idx = 1
foreach ($item in $topN) {
    $lines += "### $idx. $($item.Path)"
    $lines += "- 合规率: $($item.Compliance)%"
    $lines += "- 结构分数: $($item.StructureScore)/100"
    $lines += "- 缺失章节数: $($item.MissingCount)"
    if ($item.MissingCount -gt 0) { $lines += "- 缺失列表: $($item.MissingList)" }
    $lines += "- 优先级分: $($item.Priority)"
    $lines += ""
    $idx++
}

$lines -join "`n" | Set-Content -LiteralPath $OutputPath -Encoding UTF8
Write-Success "优先级清单已生成: $OutputPath" 