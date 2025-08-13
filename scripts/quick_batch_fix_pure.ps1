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

Write-Info "开始(纯脚本)快速批量修复..."
Write-Info "目标目录: $TargetDir"
Write-Info "试运行: $($DryRun.IsPresent)"
Write-Info "备份: $(-not $NoBackup.IsPresent)"

# -------------------------------
# 术语修正映射
# -------------------------------
$TermMap = @{
    "特性" = "特征"
    "拥有权" = "所有权"
    "生存期" = "生命周期"
    "转移" = "移动"
    "拷贝" = "复制"
    "结构" = "结构体"
    "联合" = "联合体"
    "内存安全性" = "内存安全"
    "并发性" = "并发"
    "并行性" = "并行"
    "互斥量" = "互斥锁"
    "未来" = "未来值"
    "堆栈" = "栈"
    "堆内存" = "堆"
    "范围" = "作用域"
    "安全性" = "安全"
}

# -------------------------------
# 结构检查标准
# -------------------------------
$RequiredSections = @(
    "概述","技术背景","核心概念","技术实现","形式化分析",
    "应用案例","性能分析","最佳实践","常见问题","未来展望"
)
$SectionWeights = @{
    "概述"=0.10; "技术背景"=0.12; "核心概念"=0.15; "技术实现"=0.18;
    "形式化分析"=0.15; "应用案例"=0.12; "性能分析"=0.08; "最佳实践"=0.05;
    "常见问题"=0.03; "未来展望"=0.02
}

# -------------------------------
# 遍历Markdown文件
# -------------------------------
$mdFiles = Get-ChildItem -Path $TargetDir -Include *.md -Recurse -File
if ($mdFiles.Count -eq 0) {
    Write-WarningMsg "未找到Markdown文件 (*.md)"
}

# 报告数据结构
$TermResults = @()
$StructResults = @()
$totalReplacements = 0
$totalTerms = 0

# -------------------------------
# 术语批量修正
# -------------------------------
Write-Info "步骤1: 执行术语标准化(纯脚本)..."
foreach ($file in $mdFiles) {
    try {
        $content = Get-Content -LiteralPath $file.FullName -Raw -Encoding UTF8
    } catch {
        # 读取失败时尝试无编码回退
        try { $content = Get-Content -LiteralPath $file.FullName -Raw } catch { $content = '' }
    }
    if ($null -eq $content) { $content = '' }

    $original = $content
    $fileTotalTerms = 0
    $fileReplacements = 0

    foreach ($incorrect in $TermMap.Keys) {
        $correct = $TermMap[$incorrect]
        $escapedIncorrect = [regex]::Escape($incorrect)
        $count = ([regex]::Matches($content, $escapedIncorrect)).Count
        if ($count -gt 0) {
            $fileTotalTerms += $count
            if (-not $DryRun) {
                # 纯文本替换（无反向引用）
                $content = [regex]::Replace($content, $escapedIncorrect, [System.Text.RegularExpressions.MatchEvaluator]{ param($m) $correct })
            }
            $fileReplacements += $count
        }
    }

    if (-not $DryRun -and $fileReplacements -gt 0) {
        if (-not $NoBackup) {
            $backupPath = "$($file.FullName).backup"
            Set-Content -LiteralPath $backupPath -Value $original -Encoding UTF8
        }
        Set-Content -LiteralPath $file.FullName -Value $content -Encoding UTF8
    }

    $totalReplacements += $fileReplacements
    $totalTerms += $fileTotalTerms

    $TermResults += [pscustomobject]@{
        FilePath = $file.FullName
        ReplacementsMade = $fileReplacements
        TotalTerms = $fileTotalTerms
        Success = $true
        ErrorMessage = ''
    }
}
Write-Success "术语标准化完成: 文件=$($mdFiles.Count) 修正数=$totalReplacements 术语总数=$totalTerms 修正率=$([math]::Round((if($totalTerms -gt 0){$totalReplacements/$totalTerms}else{0})*100,2))%"

# 生成术语修正报告
$termReportPath = Join-Path $TargetDir "terminology_fix_report.md"
$termReport = @()
$termReport += "# 术语批量修正报告`n"
$termReport += "## 总体统计"
$termReport += "- 处理文件数: $($mdFiles.Count)"
$termReport += "- 总修正数: $totalReplacements"
$termReport += "- 总术语数: $totalTerms"
$termReport += ("- 修正率: {0}%`n" -f ([math]::Round((if($totalTerms -gt 0){$totalReplacements/$totalTerms}else{0})*100,2)))
$termReport += "## 成功修正文件"
foreach ($r in $TermResults | Where-Object { $_.ReplacementsMade -gt 0 }) {
    $termReport += "### $($r.FilePath)"
    $termReport += "- 修正数: $($r.ReplacementsMade)"
    $termReport += "- 总术语数: $($r.TotalTerms)"
    $termReport += ("- 修正率: {0}%`n" -f ([math]::Round((if($r.TotalTerms -gt 0){$r.ReplacementsMade/$r.TotalTerms}else{0})*100,2)))
}
$termReport += "## 修正映射详情"
foreach ($k in $TermMap.Keys) { $termReport += "- **$k** → **$($TermMap[$k])**" }
$termReport -join "`n" | Set-Content -LiteralPath $termReportPath -Encoding UTF8
Write-Info "术语修正报告已生成: $termReportPath"

# -------------------------------
# 文档结构检查
# -------------------------------
Write-Info "步骤2: 执行结构检查(纯脚本)..."
foreach ($file in $mdFiles) {
    try { $content = Get-Content -LiteralPath $file.FullName -Raw -Encoding UTF8 } catch { try { $content = Get-Content -LiteralPath $file.FullName -Raw } catch { $content = '' } }
    if ($null -eq $content) { $content = '' }

    $lines = $content -split "`n"
    $sections = @()
    for ($i=0; $i -lt $lines.Length; $i++) {
        $line = $lines[$i]
        if ($line -match '^(#+)\s*(.+)$') {
            $level = $matches[1].Length
            $name = $matches[2].Trim()
            if ($name.Length -gt 0) {
                # 计算内容长度（直到下一个同级或更高级标题）
                $contentLen = 0
                for ($j=$i+1; $j -lt $lines.Length; $j++) {
                    if ($lines[$j] -match '^(#+)\s*') {
                        $nextLevel = $matches[1].Length
                        if ($nextLevel -le $level) { break }
                    }
                    if ($lines[$j].Trim().Length -gt 0) { $contentLen += $lines[$j].Length }
                }
                $sections += [pscustomobject]@{ Name=$name; Level=$level; LineNumber=$i+1; ContentLength=$contentLen }
            }
        }
    }

    # 必需章节命中
    $found = @()
    $missing = @()
    foreach ($req in $RequiredSections) {
        if ($sections | Where-Object { $_.Name -like "*$req*" }) { $found += $req } else { $missing += $req }
    }

    # 结构分数
    $totalWeight = ($SectionWeights.Values | Measure-Object -Sum).Sum
    $achieved = 0.0
    foreach ($sec in $sections) {
        foreach ($kv in $SectionWeights.GetEnumerator()) {
            if ($sec.Name -like "*" + $kv.Key + "*") { $achieved += [double]$kv.Value; break }
        }
    }
    $structureScore = if ($totalWeight -gt 0) { [math]::Round(($achieved/$totalWeight)*100,2) } else { 0 }
    $compliance = if ($RequiredSections.Count -gt 0) { [math]::Round(($found.Count/$RequiredSections.Count)*100,2) } else { 0 }

    $StructResults += [pscustomobject]@{
        FilePath = $file.FullName
        TotalSections = $sections.Count
        StructureScore = $structureScore
        ComplianceRate = $compliance
        MissingSections = ($missing -join ', ')
        Success = $true
        ErrorMessage = ''
    }
}

# 生成结构检查报告
$structReportPath = Join-Path $TargetDir "structure_check_report.md"
$succ = ($StructResults | Where-Object { $_.Success })
$avgScore = if ($succ.Count -gt 0) { [math]::Round((($succ | Measure-Object -Property StructureScore -Average).Average),2) } else { 0 }
$avgComp = if ($succ.Count -gt 0) { [math]::Round((($succ | Measure-Object -Property ComplianceRate -Average).Average),2) } else { 0 }

$structReport = @()
$structReport += "# 文档结构检查报告`n"
$structReport += "## 总体统计"
$structReport += "- 检查文件数: $($StructResults.Count)"
$structReport += "- 成功文件数: $($succ.Count)"
$structReport += "- 平均结构分数: $avgScore/100"
$structReport += "- 平均合规率: $avgComp%`n"
$structReport += "## 详细报告"
foreach ($r in $StructResults) {
    $structReport += "### $($r.FilePath)"
    $structReport += "- 结构分数: $($r.StructureScore)/100"
    $structReport += "- 合规率: $($r.ComplianceRate)%"
    $structReport += "- 章节数: $($r.TotalSections)"
    if ($r.MissingSections) { $structReport += "- 缺失章节: $($r.MissingSections)" }
    $structReport += ""
}
$structReport -join "`n" | Set-Content -LiteralPath $structReportPath -Encoding UTF8
Write-Info "结构检查报告已生成: $structReportPath"

# 综合报告
$comprehensive = Join-Path $TargetDir "quick_batch_fix_report.md"
$summary = @()
$summary += "# 快速批量修复综合报告 (纯脚本)"
$summary += "- 执行时间: $(Get-Date)"
$summary += "- 目标目录: $TargetDir"
$summary += "- 试运行: $($DryRun.IsPresent)"
$summary += "- 备份: $(-not $NoBackup.IsPresent)"
$summary += ""
$summary += "## 术语修正摘要"
$summary += "- 处理文件数: $($mdFiles.Count)"
$summary += "- 总修正数: $totalReplacements"
$summary += "- 总术语数: $totalTerms"
$summary += ("- 修正率: {0}%" -f ([math]::Round((if($totalTerms -gt 0){$totalReplacements/$totalTerms}else{0})*100,2)))
$summary += "- 报告: $termReportPath"
$summary += ""
$summary += "## 结构检查摘要"
$summary += "- 检查文件数: $($StructResults.Count)"
$summary += "- 平均结构分数: $avgScore/100"
$summary += "- 平均合规率: $avgComp%"
$summary += "- 报告: $structReportPath"
$summary -join "`n" | Set-Content -LiteralPath $comprehensive -Encoding UTF8

Write-Success "综合报告已生成: $comprehensive"
Write-Host ""
Write-Success "(纯脚本)快速批量修复执行完成!" 