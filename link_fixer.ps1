# 链接修复工具 v2.0
# 修复Markdown文件中的断链

param(
    [switch]$DryRun = $true,
    [switch]$FixBrokenLinks = $false,
    [string]$ReportPath = "link_fix_report_$(Get-Date -Format 'yyyyMMdd_HHmmss').md"
)

Write-Host "链接修复工具 v2.0" -ForegroundColor Green
Write-Host "模式: $(if ($DryRun) { '预览模式' } else { '修复模式' })" -ForegroundColor Yellow
Write-Host ""

# 获取所有Markdown文件
$mdFiles = Get-ChildItem -Path "formal_rust/refactor" -Recurse -Filter "*.md" | Where-Object { $_.Name -ne "link_fix_report_*.md" }

$totalFiles = $mdFiles.Count
$totalLinks = 0
$brokenLinks = 0
$fixedLinks = 0
$brokenLinkDetails = @()

Write-Host "开始检查 $totalFiles 个文件..." -ForegroundColor Cyan

# 自定义相对路径计算函数
function Get-RelativePath {
    param(
        [string]$FromPath,
        [string]$ToPath
    )
    
    # 标准化路径
    $fromPath = [System.IO.Path]::GetFullPath($FromPath)
    $toPath = [System.IO.Path]::GetFullPath($ToPath)
    
    # 如果路径相同，返回当前目录
    if ($fromPath -eq $toPath) {
        return "."
    }
    
    # 获取公共前缀
    $fromParts = $fromPath.Split([System.IO.Path]::DirectorySeparatorChar)
    $toParts = $toPath.Split([System.IO.Path]::DirectorySeparatorChar)
    
    $commonPrefix = 0
    for ($i = 0; $i -lt [Math]::Min($fromParts.Length, $toParts.Length); $i++) {
        if ($fromParts[$i] -eq $toParts[$i]) {
            $commonPrefix++
        } else {
            break
        }
    }
    
    # 构建相对路径
    $relativePath = ""
    
    # 向上导航到公共目录
    for ($i = $commonPrefix; $i -lt $fromParts.Length; $i++) {
        if ($relativePath -eq "") {
            $relativePath = ".."
        } else {
            $relativePath = Join-Path $relativePath ".."
        }
    }
    
    # 向下导航到目标
    for ($i = $commonPrefix; $i -lt $toParts.Length; $i++) {
        if ($relativePath -eq "") {
            $relativePath = $toParts[$i]
        } else {
            $relativePath = Join-Path $relativePath $toParts[$i]
        }
    }
    
    return $relativePath
}

# 改进的链接解析函数
function Resolve-LinkPath {
    param(
        [string]$LinkUrl,
        [string]$CurrentFilePath
    )
    
    # 跳过外部链接和锚点
    if ($LinkUrl.StartsWith("http") -or $LinkUrl.StartsWith("mailto:") -or $LinkUrl.StartsWith("#")) {
        return $null
    }
    
    # 跳过包含特殊字符的链接（可能是代码片段或数学公式）
    if ($LinkUrl -match '[<>{}[\]\\|`~!@#$%^&*+=?]') {
        return $null
    }
    
    # 获取当前文件所在目录
    $currentDir = Split-Path $CurrentFilePath -Parent
    
    # 解析相对路径
    $targetPath = if ($LinkUrl.StartsWith("./")) {
        Join-Path $currentDir $LinkUrl.Substring(2)
    } elseif ($LinkUrl.StartsWith("../")) {
        Join-Path $currentDir $LinkUrl
    } elseif ($LinkUrl.StartsWith("/")) {
        Join-Path "formal_rust/refactor" $LinkUrl.Substring(1)
    } else {
        Join-Path $currentDir $LinkUrl
    }
    
    # 标准化路径
    $targetPath = [System.IO.Path]::GetFullPath($targetPath)
    
    # 确保路径在项目范围内
    if (-not $targetPath.StartsWith([System.IO.Path]::GetFullPath("formal_rust/refactor"))) {
        return $null
    }
    
    return $targetPath
}

# 改进的链接修复函数
function Fix-BrokenLink {
    param(
        [string]$LinkUrl,
        [string]$CurrentFilePath,
        [string]$Content
    )
    
    $originalLink = $LinkUrl
    $targetPath = Resolve-LinkPath -LinkUrl $LinkUrl -CurrentFilePath $CurrentFilePath
    
    if (-not $targetPath) {
        return $Content, $false
    }
    
    # 检查目标文件是否存在
    if (Test-Path $targetPath -PathType Leaf) {
        return $Content, $false  # 链接正常
    }
    
    # 尝试修复链接
    $fixed = $false
    $currentDir = Split-Path $CurrentFilePath -Parent
    
    # 策略1: 查找同名文件
    $fileName = Split-Path $LinkUrl -Leaf
    $possibleFiles = Get-ChildItem -Path "formal_rust/refactor" -Recurse -Filter $fileName -ErrorAction SilentlyContinue
    
    if ($possibleFiles.Count -gt 0) {
        $bestMatch = $possibleFiles | Sort-Object { 
            $filePath = $_.FullName
            $currentPath = $CurrentFilePath
            
            # 计算路径相似度
            $currentParts = $currentPath.Split([System.IO.Path]::DirectorySeparatorChar)
            $fileParts = $filePath.Split([System.IO.Path]::DirectorySeparatorChar)
            
            $commonPrefix = 0
            for ($i = 0; $i -lt [Math]::Min($currentParts.Length, $fileParts.Length); $i++) {
                if ($currentParts[$i] -eq $fileParts[$i]) {
                    $commonPrefix++
                } else {
                    break
                }
            }
            
            return -$commonPrefix  # 负值使相似度高的排在前面
        } | Select-Object -First 1
        
        if ($bestMatch) {
            $relativePath = Get-RelativePath -FromPath $currentDir -ToPath $bestMatch.FullName
            $newLink = $relativePath.Replace('\', '/')
            
            if ($newLink -ne $originalLink) {
                $Content = $Content.Replace("]($originalLink)", "]($newLink)")
                $fixed = $true
            }
        }
    }
    
    # 策略2: 查找相似路径
    if (-not $fixed) {
        $linkDir = Split-Path $LinkUrl -Parent
        if ($linkDir -and $linkDir -ne ".") {
            $possibleDirs = Get-ChildItem -Path "formal_rust/refactor" -Recurse -Directory -ErrorAction SilentlyContinue | 
                           Where-Object { $_.Name -like "*$linkDir*" }
            
            foreach ($dir in $possibleDirs) {
                $testPath = Join-Path $dir.FullName $fileName
                if (Test-Path $testPath -PathType Leaf) {
                    $relativePath = Get-RelativePath -FromPath $currentDir -ToPath $testPath
                    $newLink = $relativePath.Replace('\', '/')
                    
                    if ($newLink -ne $originalLink) {
                        $Content = $Content.Replace("]($originalLink)", "]($newLink)")
                        $fixed = $true
                        break
                    }
                }
            }
        }
    }
    
    return $Content, $fixed
}

# 主处理循环
foreach ($file in $mdFiles) {
    try {
        $content = Get-Content $file.FullName -Raw -ErrorAction Stop
        $links = [regex]::Matches($content, '\[([^\]]+)\]\(([^)]+)\)')
        
        foreach ($link in $links) {
            $totalLinks++
            $linkUrl = $link.Groups[2].Value
            
            # 跳过外部链接和锚点
            if ($linkUrl.StartsWith("http") -or $linkUrl.StartsWith("mailto:") -or $linkUrl.StartsWith("#")) {
                continue
            }
            
            # 跳过包含特殊字符的链接
            if ($linkUrl -match '[<>{}[\]\\|`~!@#$%^&*+=?]') {
                continue
            }
            
            $targetPath = Resolve-LinkPath -LinkUrl $linkUrl -CurrentFilePath $file.FullName
            
            if ($targetPath) {
                if (-not (Test-Path $targetPath -PathType Leaf)) {
                    $brokenLinks++
                    $brokenLinkDetails += [PSCustomObject]@{
                        File = $file.FullName
                        Link = $linkUrl
                        Target = $targetPath
                    }
                    
                    if ($FixBrokenLinks -and -not $DryRun) {
                        $content, $fixed = Fix-BrokenLink -LinkUrl $linkUrl -CurrentFilePath $file.FullName -Content $content
                        if ($fixed) {
                            $fixedLinks++
                        }
                    }
                }
            }
        }
        
        # 保存修复后的内容
        if ($FixBrokenLinks -and -not $DryRun -and $fixedLinks -gt 0) {
            Set-Content -Path $file.FullName -Value $content -Encoding UTF8
        }
        
    } catch {
        Write-Host "处理文件 $($file.FullName) 时出错: $($_.Exception.Message)" -ForegroundColor Red
    }
}

# 生成报告
$report = @"
# 链接修复报告

**生成时间**: $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')
**模式**: $(if ($DryRun) { '预览模式' } else { '修复模式' })

## 统计信息

- **总文件数**: $totalFiles
- **总链接数**: $totalLinks
- **断链数量**: $brokenLinks
- **修复数量**: $fixedLinks
- **修复率**: $(if ($totalLinks -gt 0) { [math]::Round(($fixedLinks / $totalLinks) * 100, 2) } else { 0 })%

## 断链详情

"@

if ($brokenLinkDetails.Count -gt 0) {
    $report += "`n### 前20个断链示例`n"
    $brokenLinkDetails | Select-Object -First 20 | ForEach-Object {
        $report += "- **$($_.File)** -> $($_.Link)`n"
    }
}

$report += @"

## 修复建议

1. **创建缺失文件**: 为断链目标创建对应的Markdown文件
2. **修正路径**: 检查并修正相对路径错误
3. **更新链接**: 将过时的链接更新为正确的路径
4. **清理无效链接**: 删除指向不存在文件的链接

---
*报告由链接修复工具自动生成*
"@

# 保存报告
Set-Content -Path $ReportPath -Value $report -Encoding UTF8

Write-Host ""
Write-Host "检查完成!" -ForegroundColor Green
Write-Host "总文件数: $totalFiles" -ForegroundColor Cyan
Write-Host "总链接数: $totalLinks" -ForegroundColor Cyan
Write-Host "断链数量: $brokenLinks" -ForegroundColor Yellow
Write-Host "修复数量: $fixedLinks" -ForegroundColor Green
Write-Host "修复率: $(if ($totalLinks -gt 0) { [math]::Round(($fixedLinks / $totalLinks) * 100, 2) } else { 0 })%" -ForegroundColor Green
Write-Host ""
Write-Host "修复报告已保存到: $ReportPath" -ForegroundColor Magenta 