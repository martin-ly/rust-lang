# 文档质量检查工具
# 用于检查Rust形式化理论项目的文档质量

param(
    [string]$RootPath = "formal_rust/refactor",
    [switch]$CheckLinks = $true,
    [switch]$CheckStructure = $true,
    [switch]$GenerateReport = $true
)

Write-Host "开始文档质量检查..." -ForegroundColor Green
Write-Host "根目录: $RootPath" -ForegroundColor Yellow

# 初始化统计
$stats = @{
    TotalFiles = 0
    CompleteDocs = 0
    TransitionDocs = 0
    IndexDocs = 0
    BrokenLinks = 0
    StructureIssues = 0
    QualityIssues = @()
}

# 获取所有Markdown文件
$mdFiles = Get-ChildItem -Path $RootPath -Recurse -Filter "*.md"
$stats.TotalFiles = $mdFiles.Count

Write-Host "扫描到 $($stats.TotalFiles) 个Markdown文件" -ForegroundColor Cyan

# 按大小分类
foreach ($file in $mdFiles) {
    if ($file.Length -gt 10KB) {
        $stats.CompleteDocs++
    } elseif ($file.Length -gt 1KB) {
        $stats.TransitionDocs++
    } else {
        $stats.IndexDocs++
    }
}

# 检查文档结构
if ($CheckStructure) {
    Write-Host "`n检查文档结构..." -ForegroundColor Cyan
    
    foreach ($file in $mdFiles) {
        $content = Get-Content $file.FullName -Raw -ErrorAction SilentlyContinue
        if (-not $content) { continue }
        
        $issues = @()
        
        # 检查文档信息部分
        if (-not ($content -match "## 文档信息")) {
            $issues += "缺少文档信息部分"
        }
        
        # 检查质量等级
        if (-not ($content -match "质量等级.*⭐")) {
            $issues += "缺少质量等级标识"
        }
        
        # 检查模块概述
        if (-not ($content -match "## 模块概述")) {
            $issues += "缺少模块概述"
        }
        
        # 检查代码示例
        if (-not ($content -match "```rust")) {
            $issues += "缺少Rust代码示例"
        }
        
        # 检查应用案例
        if (-not ($content -match "## 应用案例")) {
            $issues += "缺少应用案例"
        }
        
        if ($issues.Count -gt 0) {
            $stats.StructureIssues++
            $stats.QualityIssues += @{
                File = $file.FullName
                Issues = $issues
            }
        }
    }
}

# 检查链接完整性
if ($CheckLinks) {
    Write-Host "`n检查链接完整性..." -ForegroundColor Cyan
    
    foreach ($file in $mdFiles) {
        $content = Get-Content $file.FullName -Raw -ErrorAction SilentlyContinue
        if (-not $content) { continue }
        
        # 提取所有链接
        $links = [regex]::Matches($content, '\[([^\]]+)\]\(([^)]+)\)')
        
        foreach ($link in $links) {
            $linkText = $link.Groups[1].Value
            $linkUrl = $link.Groups[2].Value
            
            # 检查相对路径链接
            if ($linkUrl -match '^[^/]') {
                $targetPath = Join-Path $file.DirectoryName $linkUrl
                if (-not (Test-Path $targetPath)) {
                    $stats.BrokenLinks++
                    Write-Host "  断链: $($file.FullName) -> $linkUrl" -ForegroundColor Red
                }
            }
        }
    }
}

# 生成质量报告
if ($GenerateReport) {
    Write-Host "`n生成质量报告..." -ForegroundColor Cyan
    
    $report = @"
# 文档质量检查报告

## 检查统计
- 检查时间: $(Get-Date)
- 总文件数: $($stats.TotalFiles)
- 完整文档: $($stats.CompleteDocs)
- 过渡文档: $($stats.TransitionDocs)
- 索引文档: $($stats.IndexDocs)

## 质量指标
- 完整文档比例: $([math]::Round($stats.CompleteDocs / $stats.TotalFiles * 100, 1))%
- 结构问题数: $($stats.StructureIssues)
- 断链数量: $($stats.BrokenLinks)

## 文档分布
- 钻石级文档 (>10KB): $($stats.CompleteDocs)
- 黄金级文档 (1-10KB): $($stats.TransitionDocs)
- 白银级文档 (<1KB): $($stats.IndexDocs)

## 结构问题详情
$($stats.QualityIssues | ForEach-Object { 
    "- $($_.File): $($_.Issues -join ', ')" 
} | Out-String)

## 改进建议
1. 结构问题: 需要补充文档信息、质量等级、模块概述等
2. 链接问题: 需要修复断开的链接
3. 内容质量: 建议增加代码示例和应用案例
"@

    $reportPath = "doc_quality_report_$(Get-Date -Format 'yyyyMMdd_HHmmss').md"
    $report | Out-File -FilePath $reportPath -Encoding UTF8
    Write-Host "质量报告已保存到: $reportPath" -ForegroundColor Cyan
}

# 输出检查结果
Write-Host "`n检查完成!" -ForegroundColor Green
Write-Host "总文件数: $($stats.TotalFiles)" -ForegroundColor White
Write-Host "完整文档: $($stats.CompleteDocs)" -ForegroundColor Green
Write-Host "过渡文档: $($stats.TransitionDocs)" -ForegroundColor Yellow
Write-Host "索引文档: $($stats.IndexDocs)" -ForegroundColor Blue
Write-Host "结构问题: $($stats.StructureIssues)" -ForegroundColor Red
Write-Host "断链数量: $($stats.BrokenLinks)" -ForegroundColor Red

# 计算质量分数
$qualityScore = 0
$qualityScore += $stats.CompleteDocs * 5  # 完整文档5分
$qualityScore += $stats.TransitionDocs * 3  # 过渡文档3分
$qualityScore += $stats.IndexDocs * 1  # 索引文档1分
$qualityScore -= $stats.StructureIssues * 2  # 结构问题扣2分
$qualityScore -= $stats.BrokenLinks * 1  # 断链扣1分

$maxScore = $stats.TotalFiles * 5
$qualityPercentage = [math]::Round($qualityScore / $maxScore * 100, 1)

Write-Host "`n质量评分: $qualityScore/$maxScore ($qualityPercentage%)" -ForegroundColor Cyan

if ($qualityPercentage -ge 80) {
    Write-Host "质量等级: 优秀 ⭐⭐⭐⭐⭐" -ForegroundColor Green
} elseif ($qualityPercentage -ge 60) {
    Write-Host "质量等级: 良好 ⭐⭐⭐⭐" -ForegroundColor Yellow
} elseif ($qualityPercentage -ge 40) {
    Write-Host "质量等级: 一般 ⭐⭐⭐" -ForegroundColor Orange
} else {
    Write-Host "质量等级: 需要改进 ⭐⭐" -ForegroundColor Red
} 