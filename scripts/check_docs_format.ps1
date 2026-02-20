# 文档格式检查脚本
# 检查 docs 目录下所有 Markdown 文件的格式合规性

param(
    [string]$DocsPath = "docs",
    [switch]$Fix,
    [switch]$Verbose
)

$issues = @()
$stats = @{
    TotalFiles = 0
    IssuesFound = 0
    MissingRustVersion = 0
    MissingCreateDate = 0
    MissingUpdateDate = 0
    MissingStatus = 0
    InvalidDateFormat = 0
    InvalidTableFormat = 0
    InvalidHeadingEmoji = 0
}

function Write-ColorOutput($Text, $Color) {
    Write-Host $Text -ForegroundColor $Color
}

function Test-DateFormat($DateString) {
    return $DateString -match "^\d{4}-\d{2}-\d{2}$"
}

function Test-TableFormat($Content) {
    # 检查表格分隔行格式
    $tableSeparators = [regex]::Matches($Content, "\|[-:]+\|")
    foreach ($match in $tableSeparators) {
        $separator = $match.Value
        # 检查是否使用了 :--- 格式
        if ($separator -notmatch "\:\-{3,}" -and $separator -match "\-{3,}") {
            return $false
        }
    }
    return $true
}

function Test-HeadingEmoji($Content) {
    # 检查一级标题是否含 emoji
    $h1Headings = [regex]::Matches($Content, "^# (.+)$", [System.Text.RegularExpressions.RegexOptions]::Multiline)
    foreach ($match in $h1Headings) {
        $heading = $match.Groups[1].Value
        # 简单 emoji 检测
        if ($heading -match "[\x{1F600}-\x{1F64F}]|[\x{1F300}-\x{1F5FF}]|[\x{1F680}-\x{1F6FF}]|[\x{1F1E0}-\x{1F1FF}]|[\x{2600}-\x{26FF}]|[\x{2700}-\x{27BF}]|[📊📚🔬💻🔗📋🔄✅🆕🎯📖🦀📦🧹]" -or $heading -match "^[^a-zA-Z0-9\u4e00-\u9fa5]") {
            return $false
        }
    }
    return $true
}

# 获取所有 Markdown 文件
$files = Get-ChildItem -Path $DocsPath -Recurse -Filter "*.md"
$stats.TotalFiles = $files.Count

Write-ColorOutput "开始检查 $DocsPath 目录下的 $($files.Count) 个 Markdown 文件..." "Cyan"
Write-Host ""

foreach ($file in $files) {
    $relativePath = $file.FullName.Replace((Get-Location).Path + "\", "")
    $content = Get-Content $file.FullName -Raw -ErrorAction SilentlyContinue
    
    if ($null -eq $content) {
        continue
    }
    
    $fileIssues = @()
    
    # 检查元信息
    if ($content -notmatch "\*\*Rust 版本\*\*:") {
        $fileIssues += "缺少 Rust 版本"
        $stats.MissingRustVersion++
    }
    
    if ($content -notmatch "\*\*创建日期\*\*:") {
        $fileIssues += "缺少创建日期"
        $stats.MissingCreateDate++
    }
    else {
        # 检查日期格式
        $dateMatch = [regex]::Match($content, "\*\*创建日期\*\*:\s*(.+?)(?:\r?\n|")
        if ($dateMatch.Success -and -not (Test-DateFormat $dateMatch.Groups[1].Value.Trim())) {
            $fileIssues += "创建日期格式不正确 (应为 YYYY-MM-DD)"
            $stats.InvalidDateFormat++
        }
    }
    
    if ($content -notmatch "\*\*最后更新\*\*:") {
        $fileIssues += "缺少最后更新日期"
        $stats.MissingUpdateDate++
    }
    else {
        # 检查日期格式
        $dateMatch = [regex]::Match($content, "\*\*最后更新\*\*:\s*(.+?)(?:\r?\n|")
        if ($dateMatch.Success -and -not (Test-DateFormat $dateMatch.Groups[1].Value.Trim())) {
            $fileIssues += "最后更新日期格式不正确 (应为 YYYY-MM-DD)"
            $stats.InvalidDateFormat++
        }
    }
    
    if ($content -notmatch "\*\*状态\*\*:") {
        $fileIssues += "缺少状态"
        $stats.MissingStatus++
    }
    
    # 检查表格格式
    if (-not (Test-TableFormat $content)) {
        $fileIssues += "表格分隔行格式不正确 (应使用 :--- 左对齐)"
        $stats.InvalidTableFormat++
    }
    
    # 检查一级标题 emoji
    if (-not (Test-HeadingEmoji $content)) {
        $fileIssues += "一级标题含 emoji 或特殊字符"
        $stats.InvalidHeadingEmoji++
    }
    
    if ($fileIssues.Count -gt 0) {
        $stats.IssuesFound += $fileIssues.Count
        Write-ColorOutput "⚠️ $relativePath" "Yellow"
        foreach ($issue in $fileIssues) {
            Write-Host "   - $issue" -ForegroundColor DarkYellow
        }
        
        $issues += [PSCustomObject]@{
            File = $relativePath
            Issues = $fileIssues -join "; "
        }
    }
    elseif ($Verbose) {
        Write-ColorOutput "✅ $relativePath" "Green"
    }
}

Write-Host ""
Write-ColorOutput "========== 检查完成 ==========" "Cyan"
Write-Host ""
Write-ColorOutput "📊 统计信息:" "White"
Write-Host "   总文件数: $($stats.TotalFiles)"
Write-Host "   问题总数: $($stats.IssuesFound)"
Write-Host ""
Write-ColorOutput "📋 问题分布:" "White"
Write-Host "   缺少 Rust 版本: $($stats.MissingRustVersion)"
Write-Host "   缺少创建日期: $($stats.MissingCreateDate)"
Write-Host "   缺少最后更新: $($stats.MissingUpdateDate)"
Write-Host "   缺少状态: $($stats.MissingStatus)"
Write-Host "   日期格式错误: $($stats.InvalidDateFormat)"
Write-Host "   表格格式错误: $($stats.InvalidTableFormat)"
Write-Host "   一级标题含 emoji: $($stats.InvalidHeadingEmoji)"
Write-Host ""

if ($issues.Count -gt 0) {
    Write-ColorOutput "❌ 发现 $($issues.Count) 个文件存在格式问题" "Red"
    
    # 导出问题报告
    $reportPath = "docs_format_issues_$(Get-Date -Format 'yyyyMMdd_HHmmss').csv"
    $issues | Export-Csv -Path $reportPath -NoTypeInformation -Encoding UTF8
    Write-Host "📄 详细报告已导出: $reportPath" -ForegroundColor Cyan
}
else {
    Write-ColorOutput "✅ 所有文件格式检查通过！" "Green"
}
