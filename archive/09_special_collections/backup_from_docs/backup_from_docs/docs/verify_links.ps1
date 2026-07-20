# C01 项目链接完整性验证脚本
# 生成日期: 2025-10-22

$ErrorActionPreference = "Continue"
$baseDir = Split-Path -Parent $MyInvocation.MyCommand.Path

# 结果统计
$totalLinks = 0
$validLinks = 0
$invalidLinks = 0
$brokenLinks = @()

# 获取所有 Markdown 文件
$mdFiles = Get-ChildItem -Path $baseDir -Filter "*.md" -Recurse

Write-Host "=== C01 链接完整性验证 ===" -ForegroundColor Cyan
Write-Host "扫描目录: $baseDir" -ForegroundColor Yellow
Write-Host "文件数量: $($mdFiles.Count)" -ForegroundColor Yellow
Write-Host ""

foreach ($file in $mdFiles) {
    $content = Get-Content $file.FullName -Raw -ErrorAction SilentlyContinue
    if (-not $content) { continue }
    
    # 提取所有 Markdown 链接 [text](path)
    $linkPattern = '\[([^\]]+)\]\(([^)]+)\)'
    $matches = [regex]::Matches($content, $linkPattern)
    
    foreach ($match in $matches) {
        $linkText = $match.Groups[1].Value
        $linkPath = $match.Groups[2].Value
        
        # 跳过外部链接和锚点链接
        if ($linkPath -match '^https?://' -or $linkPath -match '^#') {
            continue
        }
        
        # 移除锚点部分
        $linkPathClean = ($linkPath -split '#')[0]
        if ([string]::IsNullOrWhiteSpace($linkPathClean)) {
            continue
        }
        
        $totalLinks++
        
        # 解析相对路径
        $fileDir = $file.DirectoryName
        $targetPath = Join-Path $fileDir $linkPathClean
        $targetPath = [System.IO.Path]::GetFullPath($targetPath)
        
        # 检查文件是否存在
        if (Test-Path $targetPath) {
            $validLinks++
        } else {
            $invalidLinks++
            $brokenLinks += [PSCustomObject]@{
                SourceFile = $file.FullName.Substring($baseDir.Length + 1)
                LinkText = $linkText
                LinkPath = $linkPath
                ResolvedPath = $targetPath.Substring($baseDir.Length + 1)
            }
        }
    }
}

# 输出结果
Write-Host "=== 验证结果 ===" -ForegroundColor Cyan
Write-Host "总链接数: $totalLinks" -ForegroundColor White
Write-Host "有效链接: $validLinks ($([math]::Round($validLinks/$totalLinks*100, 2))%)" -ForegroundColor Green
Write-Host "失效链接: $invalidLinks ($([math]::Round($invalidLinks/$totalLinks*100, 2))%)" -ForegroundColor Red
Write-Host ""

if ($invalidLinks -gt 0) {
    Write-Host "=== 失效链接详情 ===" -ForegroundColor Red
    $brokenLinks | ForEach-Object {
        Write-Host "文件: $($_.SourceFile)" -ForegroundColor Yellow
        Write-Host "  文本: $($_.LinkText)" -ForegroundColor White
        Write-Host "  链接: $($_.LinkPath)" -ForegroundColor White
        Write-Host "  目标: $($_.ResolvedPath)" -ForegroundColor Red
        Write-Host ""
    }
}

# 生成 JSON 报告
$report = @{
    GeneratedAt = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    Statistics = @{
        TotalLinks = $totalLinks
        ValidLinks = $validLinks
        InvalidLinks = $invalidLinks
        ValidityRate = [math]::Round($validLinks/$totalLinks*100, 2)
    }
    BrokenLinks = $brokenLinks
}

$reportPath = Join-Path $baseDir "link_validation_report.json"
$report | ConvertTo-Json -Depth 10 | Out-File $reportPath -Encoding UTF8
Write-Host "JSON 报告已生成: link_validation_report.json" -ForegroundColor Green

