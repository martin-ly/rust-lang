# 文档格式检查脚本（简化版）
param(
    [string]$DocsPath = "docs"
)

$issues = @()
$stats = @{
    TotalFiles = 0
    MissingRustVersion = 0
    MissingCreateDate = 0
    MissingUpdateDate = 0
    MissingStatus = 0
}

Write-Host "开始检查 $DocsPath 目录..." -ForegroundColor Cyan

$files = Get-ChildItem -Path $DocsPath -Recurse -Filter "*.md"
$stats.TotalFiles = $files.Count

foreach ($file in $files) {
    $relativePath = $file.FullName.Replace((Get-Location).Path + "\", "")
    $content = Get-Content $file.FullName -Raw -ErrorAction SilentlyContinue
    
    if ($null -eq $content) { continue }
    
    $fileIssues = @()
    
    if ($content -notmatch "\*\*Rust 版本\*\*:") {
        $fileIssues += "缺少 Rust 版本"
        $stats.MissingRustVersion++
    }
    
    if ($content -notmatch "\*\*创建日期\*\*:") {
        $fileIssues += "缺少创建日期"
        $stats.MissingCreateDate++
    }
    
    if ($content -notmatch "\*\*最后更新\*\*:") {
        $fileIssues += "缺少最后更新日期"
        $stats.MissingUpdateDate++
    }
    
    if ($content -notmatch "\*\*状态\*\*:") {
        $fileIssues += "缺少状态"
        $stats.MissingStatus++
    }
    
    if ($fileIssues.Count -gt 0) {
        Write-Host "⚠️ $relativePath" -ForegroundColor Yellow
        foreach ($issue in $fileIssues) {
            Write-Host "   - $issue" -ForegroundColor DarkYellow
        }
        $issues += "$relativePath : $($fileIssues -join ', ')"
    }
}

Write-Host ""
Write-Host "========== 检查完成 ==========" -ForegroundColor Cyan
Write-Host "总文件数: $($stats.TotalFiles)" -ForegroundColor White
Write-Host "缺少 Rust 版本: $($stats.MissingRustVersion)" -ForegroundColor $(if($stats.MissingRustVersion -eq 0){"Green"}else{"Red"})
Write-Host "缺少创建日期: $($stats.MissingCreateDate)" -ForegroundColor $(if($stats.MissingCreateDate -eq 0){"Green"}else{"Red"})
Write-Host "缺少最后更新: $($stats.MissingUpdateDate)" -ForegroundColor $(if($stats.MissingUpdateDate -eq 0){"Green"}else{"Red"})
Write-Host "缺少状态: $($stats.MissingStatus)" -ForegroundColor $(if($stats.MissingStatus -eq 0){"Green"}else{"Red"})

if ($issues.Count -gt 0) {
    Write-Host ""
    Write-Host "发现 $($issues.Count) 个文件存在格式问题" -ForegroundColor Red
}
