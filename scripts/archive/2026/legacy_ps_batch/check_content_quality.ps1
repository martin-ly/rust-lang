# 文档内容质量检查脚本
# 检查 docs 目录下 Markdown 文件的实质内容质量

param(
    [string]$DocsPath = "docs",
    [switch]$Verbose
)

$issues = @()
$stats = @{
    TotalFiles = 0
    WeakContentFiles = 0
    MissingFormalization = 0
    MissingCode = 0
    MissingScenario = 0
    MissingCounterexample = 0
    MissingLink = 0
}

function Write-ColorOutput($Text, $Color) {
    Write-Host $Text -ForegroundColor $Color
}

function Test-Formalization($Content) {
    # 检查是否包含 Def/Axiom/定理/证明
    return ($Content -match "Def\s+\w+|Axiom\s+\w+|定理|Theorem|证明|Proof") -or 
           ($Content -match "形式化定义|形式化|formalization")
}

function Test-CodeExample($Content) {
    # 检查是否包含 Rust 代码块
    return $Content -match "```rust[\s\S]*?```"
}

function Test-Scenario($Content) {
    # 检查是否包含具体场景（非泛泛描述）
    # 检查是否有具体场景标记、用例、或详细描述段落
    return ($Content -match "场景|用例|示例|案例|scenario|use case|example" -and 
            $Content -match "具体|典型|实际|实战")
}

function Test-Counterexample($Content) {
    # 检查是否包含反例或边界说明
    return $Content -match "反例|边界|错误|失败|panic|unsafe|避免|注意"
}

function Test-FormalMethodsLink($Content) {
    # 检查是否链接到 formal_methods/type_theory/PROOF_INDEX
    return $Content -match "formal_methods|type_theory|PROOF_INDEX|ownership_model|borrow_checker"
}

# 获取所有 Markdown 文件
$files = Get-ChildItem -Path $DocsPath -Recurse -Filter "*.md" | 
    Where-Object { $_.FullName -notmatch "archive" }  # 排除归档文件

$stats.TotalFiles = $files.Count

Write-ColorOutput "开始检查 $DocsPath 目录下的 $($files.Count) 个 Markdown 文件内容质量..." "Cyan"
Write-Host ""

foreach ($file in $files) {
    $relativePath = $file.FullName.Replace((Get-Location).Path + "\", "")
    $content = Get-Content $file.FullName -Raw -ErrorAction SilentlyContinue
    
    if ($null -eq $content) { continue }
    
    # 跳过索引/概览类文档（放宽要求）
    $isIndex = $file.Name -match "README|INDEX|SUMMARY|OVERVIEW|MASTER|NAVIGATION|CHECKLIST|GUIDE|TEMPLATE"
    
    $fileIssues = @()
    $score = 0
    
    # 检查形式化
    if (-not (Test-Formalization $content)) {
        $fileIssues += "缺少形式化定义 (Def/Axiom/定理)"
        $stats.MissingFormalization++
    } else { $score++ }
    
    # 检查代码示例（索引类放宽）
    if (-not $isIndex -and -not (Test-CodeExample $content)) {
        $fileIssues += "缺少可运行 Rust 代码示例"
        $stats.MissingCode++
    } elseif (Test-CodeExample $content) { $score++ }
    
    # 检查场景
    if (-not (Test-Scenario $content)) {
        $fileIssues += "缺少具体使用场景"
        $stats.MissingScenario++
    } else { $score++ }
    
    # 检查反例
    if (-not (Test-Counterexample $content)) {
        $fileIssues += "缺少反例或边界说明"
        $stats.MissingCounterexample++
    } else { $score++ }
    
    # 检查形式化链接
    if (-not (Test-FormalMethodsLink $content)) {
        $fileIssues += "缺少与 formal_methods/type_theory 的衔接"
        $stats.MissingLink++
    } else { $score++ }
    
    # 计算质量等级
    $maxScore = if ($isIndex) { 4 } else { 5 }
    $quality = if ($score -ge $maxScore) { "优秀" } 
               elseif ($score -ge $maxScore - 1) { "良好" }
               elseif ($score -ge $maxScore - 2) { "一般" }
               else { "薄弱" }
    
    if ($fileIssues.Count -gt 2 -or $quality -eq "薄弱") {
        $stats.WeakContentFiles++
        Write-ColorOutput "⚠️ $relativePath [$quality]" "Yellow"
        foreach ($issue in $fileIssues) {
            Write-Host "   - $issue" -ForegroundColor DarkYellow
        }
        
        $issues += [PSCustomObject]@{
            File = $relativePath
            Quality = $quality
            Score = "$score/$maxScore"
            Issues = $fileIssues -join "; "
        }
    }
    elseif ($Verbose) {
        Write-ColorOutput "✅ $relativePath [$quality]" "Green"
    }
}

Write-Host ""
Write-ColorOutput "========== 内容质量检查完成 ==========" "Cyan"
Write-Host ""
Write-ColorOutput "📊 统计信息:" "White"
Write-Host "   总文件数: $($stats.TotalFiles)"
Write-Host "   薄弱内容文件: $($stats.WeakContentFiles)"
Write-Host ""
Write-ColorOutput "📋 内容缺陷分布:" "White"
Write-Host "   缺少形式化定义: $($stats.MissingFormalization)"
Write-Host "   缺少代码示例: $($stats.MissingCode)"
Write-Host "   缺少具体场景: $($stats.MissingScenario)"
Write-Host "   缺少反例/边界: $($stats.MissingCounterexample)"
Write-Host "   缺少形式化链接: $($stats.MissingLink)"
Write-Host ""

if ($issues.Count -gt 0) {
    Write-ColorOutput "❌ 发现 $($issues.Count) 个文件内容需要加强" "Red"
    
    # 导出问题报告
    $reportPath = "docs_content_issues_$(Get-Date -Format 'yyyyMMdd_HHmmss').csv"
    $issues | Export-Csv -Path $reportPath -NoTypeInformation -Encoding UTF8
    Write-Host "📄 详细报告已导出: $reportPath" -ForegroundColor Cyan
}
else {
    Write-ColorOutput "✅ 所有文件内容质量检查通过！" "Green"
}
