# Content quality check script (simplified)
param([string]$DocsPath = "docs")

$issues = @()
$stats = @{ TotalFiles = 0; WeakFiles = 0 }

Write-Host "Checking content quality in $DocsPath..." -ForegroundColor Cyan

$files = Get-ChildItem -Path $DocsPath -Recurse -Filter "*.md" | 
    Where-Object { $_.FullName -notmatch "archive" }

$stats.TotalFiles = $files.Count

foreach ($file in $files) {
    $relativePath = $file.FullName.Replace((Get-Location).Path + "\", "")
    $content = Get-Content $file.FullName -Raw -ErrorAction SilentlyContinue
    if ($null -eq $content) { continue }
    
    $fileIssues = @()
    
    # Check for Rust code
    if ($content -notmatch "```rust") {
        $fileIssues += "No Rust code example"
    }
    
    # Check for formalization
    if ($content -notmatch "Def |Axiom |Theorem|定理|定义") {
        $fileIssues += "No formalization"
    }
    
    # Check for links to formal methods
    if ($content -notmatch "formal_methods|type_theory|ownership_model|borrow_checker") {
        $fileIssues += "No formal methods link"
    }
    
    if ($fileIssues.Count -ge 2) {
        $stats.WeakFiles++
        Write-Host "! $relativePath" -ForegroundColor Yellow
        foreach ($issue in $fileIssues) {
            Write-Host "   - $issue" -ForegroundColor DarkYellow
        }
        $issues += "$relativePath : $($fileIssues -join ', ')"
    }
}

Write-Host ""
Write-Host "========== Content Quality Check Complete ==========" -ForegroundColor Cyan
Write-Host "Total files: $($stats.TotalFiles)" -ForegroundColor White
Write-Host "Weak content files: $($stats.WeakFiles)" -ForegroundColor $(if($stats.WeakFiles -eq 0){"Green"}else{"Red"})

if ($issues.Count -gt 0) {
    $reportPath = "docs_content_issues_$(Get-Date -Format 'yyyyMMdd_HHmmss').txt"
    $issues | Out-File -FilePath $reportPath -Encoding UTF8
    Write-Host "Report exported: $reportPath" -ForegroundColor Cyan
}
