# PowerShell Script: 为Markdown文件添加目录
# 功能：扫描所有.md文件，检测并添加目录

param(
    [string]$Directory = "crates",
    [switch]$DryRun = $false,
    [switch]$Verbose = $false
)

# 统计信息
$stats = @{
    Total = 0
    WithTOC = 0
    WithoutTOC = 0
    AddedTOC = 0
    Skipped = 0
    Errors = 0
}

# 检测是否已有目录
function Test-HasTOC {
    param([string]$Content)
    
    $tocPatterns = @(
        '##?\s*目录',
        '##?\s*📊\s*目录',
        '##?\s*Table of Contents',
        '##?\s*TOC',
        '<!-- TOC -->',
        '\[TOC\]'
    )
    
    foreach ($pattern in $tocPatterns) {
        if ($Content -match $pattern) {
            return $true
        }
    }
    return $false
}

# 提取标题
function Get-Headers {
    param([string]$Content)
    
    $headers = @()
    $lines = $Content -split "`n"
    
    foreach ($line in $lines) {
        if ($line -match '^(#{2,6})\s+(.+)$') {
            $level = $Matches[1].Length
            $title = $Matches[2].Trim()
            
            # 生成锚点
            $anchor = $title -replace '[^\w\s\u4e00-\u9fff-]', '' `
                            -replace '\s+', '-' `
                            -replace '-+', '-'
            $anchor = $anchor.ToLower().Trim('-')
            
            $headers += @{
                Level = $level
                Title = $title
                Anchor = $anchor
            }
        }
    }
    
    return $headers
}

# 生成目录
function New-TOC {
    param([array]$Headers)
    
    if ($Headers.Count -eq 0) {
        return ""
    }
    
    $toc = "## 📊 目录`n`n"
    
    foreach ($header in $Headers) {
        $indent = "  " * ($header.Level - 2)
        $toc += "$indent- [$($header.Title)](#$($header.Anchor))`n"
    }
    
    $toc += "`n"
    return $toc
}

# 判断是否应该跳过
function Test-ShouldSkip {
    param([string]$Path)
    
    $skipPatterns = @(
        'README.md$',
        'CHANGELOG.md$',
        'LICENSE.md$',
        'CONTRIBUTING.md$',
        '\\target\\',
        '\\node_modules\\',
        '\\.git\\'
    )
    
    foreach ($pattern in $skipPatterns) {
        if ($Path -match $pattern) {
            return $true
        }
    }
    return $false
}

# 处理单个文件
function Add-TOCToFile {
    param(
        [string]$FilePath,
        [bool]$DryRun
    )
    
    try {
        $content = Get-Content -Path $FilePath -Raw -Encoding UTF8
        
        # 检查是否已有目录
        if (Test-HasTOC -Content $content) {
            $script:stats.WithTOC++
            if ($Verbose) {
                Write-Host "⏭️  已有目录: $FilePath" -ForegroundColor Gray
            }
            return $false
        }
        
        $script:stats.WithoutTOC++
        
        # 提取标题
        $headers = Get-Headers -Content $content
        
        # 如果标题太少，跳过
        if ($headers.Count -lt 3) {
            $script:stats.Skipped++
            if ($Verbose) {
                Write-Host "⏭️  标题太少: $FilePath ($($headers.Count) 个)" -ForegroundColor Yellow
            }
            return $false
        }
        
        # 生成目录
        $toc = New-TOC -Headers $headers
        
        if (-not $toc) {
            $script:stats.Skipped++
            return $false
        }
        
        # 找到插入位置
        $lines = $content -split "`n"
        $insertPos = 0
        
        # 跳过标题和元信息
        for ($i = 0; $i -lt $lines.Count; $i++) {
            $line = $lines[$i]
            
            if ($i -eq 0 -and $line -match '^#') {
                $insertPos = $i + 1
                continue
            }
            if ($line -match '^>') {
                $insertPos = $i + 1
                continue
            }
            if ($line.Trim() -eq '---') {
                $insertPos = $i + 1
                continue
            }
            if ($line.Trim() -eq '') {
                continue
            }
            break
        }
        
        # 跳过空行
        while ($insertPos -lt $lines.Count -and $lines[$insertPos].Trim() -eq '') {
            $insertPos++
        }
        
        if (-not $DryRun) {
            # 插入目录
            $before = $lines[0..($insertPos-1)] -join "`n"
            $after = $lines[$insertPos..($lines.Count-1)] -join "`n"
            $newContent = "$before`n`n$toc`n$after"
            
            Set-Content -Path $FilePath -Value $newContent -Encoding UTF8 -NoNewline
            
            $script:stats.AddedTOC++
            Write-Host "✅ 已添加目录: $FilePath" -ForegroundColor Green
        }
        else {
            Write-Host "🔍 将添加目录: $FilePath" -ForegroundColor Cyan
        }
        
        return $true
    }
    catch {
        $script:stats.Errors++
        Write-Host "❌ 处理错误: $FilePath - $_" -ForegroundColor Red
        return $false
    }
}

# 主处理流程
Write-Host "`n============================================================" -ForegroundColor Cyan
Write-Host "Markdown 目录自动添加工具" -ForegroundColor Cyan
Write-Host "============================================================" -ForegroundColor Cyan
Write-Host "扫描目录: $Directory"
Write-Host "模式: $(if ($DryRun) { '检测模式 (不修改)' } else { '修改模式' })"
Write-Host "============================================================`n" -ForegroundColor Cyan

# 获取所有Markdown文件
$mdFiles = Get-ChildItem -Path $Directory -Filter "*.md" -Recurse -File

$stats.Total = $mdFiles.Count

Write-Host "找到 $($mdFiles.Count) 个Markdown文件`n"

# 处理每个文件
foreach ($file in $mdFiles) {
    if (Test-ShouldSkip -Path $file.FullName) {
        if ($Verbose) {
            Write-Host "⏭️  跳过特殊文件: $($file.FullName)" -ForegroundColor Gray
        }
        continue
    }
    
    Add-TOCToFile -FilePath $file.FullName -DryRun $DryRun
}

# 打印统计
Write-Host "`n============================================================" -ForegroundColor Cyan
Write-Host "统计结果" -ForegroundColor Cyan
Write-Host "============================================================" -ForegroundColor Cyan
Write-Host "总文件数:       $($stats.Total)"
Write-Host "已有目录:       $($stats.WithTOC)" -ForegroundColor Green
Write-Host "缺少目录:       $($stats.WithoutTOC)" -ForegroundColor Yellow
if ($DryRun) {
    Write-Host "将添加目录:     $($stats.WithoutTOC - $stats.Skipped)" -ForegroundColor Cyan
} else {
    Write-Host "已添加目录:     $($stats.AddedTOC)" -ForegroundColor Green
}
Write-Host "跳过文件:       $($stats.Skipped) (标题太少或特殊文件)" -ForegroundColor Gray
Write-Host "处理错误:       $($stats.Errors)" -ForegroundColor Red
Write-Host "============================================================`n" -ForegroundColor Cyan

if ($DryRun) {
    Write-Host "💡 这是检测模式，未修改任何文件" -ForegroundColor Yellow
    Write-Host "💡 运行不带 -DryRun 参数来实际添加目录`n" -ForegroundColor Yellow
}

