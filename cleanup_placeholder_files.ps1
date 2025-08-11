# 占位文档清理脚本
# 用于批量处理formal_rust/refactor目录中的占位文档

param(
    [string]$RootPath = "formal_rust/refactor",
    [switch]$DryRun = $false,
    [switch]$Backup = $true
)

Write-Host "开始清理占位文档..." -ForegroundColor Green
Write-Host "根目录: $RootPath" -ForegroundColor Yellow
Write-Host "模拟运行: $DryRun" -ForegroundColor Yellow
Write-Host "创建备份: $Backup" -ForegroundColor Yellow

# 创建备份目录
if ($Backup -and -not $DryRun) {
    $backupDir = "backup_$(Get-Date -Format 'yyyyMMdd_HHmmss')"
    Write-Host "创建备份目录: $backupDir" -ForegroundColor Cyan
    New-Item -ItemType Directory -Path $backupDir -Force | Out-Null
}

# 查找所有占位文档
Write-Host "扫描占位文档..." -ForegroundColor Cyan
$placeholderFiles = Get-ChildItem -Path $RootPath -Recurse -Filter "*.md" | 
    Where-Object { $_.Length -lt 1KB } | 
    Where-Object { 
        $content = Get-Content $_.FullName -Raw -ErrorAction SilentlyContinue
        $content -and ($content -match "占位文档" -or $content -match "待补充")
    }

Write-Host "找到 $($placeholderFiles.Count) 个占位文档" -ForegroundColor Yellow

# 按目录分组
$filesByDirectory = $placeholderFiles | Group-Object { Split-Path $_.DirectoryName -Leaf }

Write-Host "`n按目录分组的占位文档:" -ForegroundColor Cyan
foreach ($group in $filesByDirectory) {
    Write-Host "  $($group.Name): $($group.Count) 个文件" -ForegroundColor White
}

# 处理策略
$deleteCount = 0
$keepCount = 0

foreach ($file in $placeholderFiles) {
    $relativePath = $file.FullName.Replace((Get-Location).Path + "\", "")
    
    # 检查是否有其他非占位文档在同一目录
    $siblingFiles = Get-ChildItem -Path $file.DirectoryName -Filter "*.md" | 
        Where-Object { $_.Name -ne $file.Name -and $_.Length -ge 1KB }
    
    # 检查是否有其他索引文件
    $hasOtherIndex = Get-ChildItem -Path $file.DirectoryName -Filter "*index*.md" | 
        Where-Object { $_.Name -ne $file.Name }
    
    $shouldDelete = $false
    $reason = ""
    
    if ($siblingFiles.Count -gt 0) {
        $shouldDelete = $true
        $reason = "目录中有其他内容文件"
    } elseif ($hasOtherIndex) {
        $shouldDelete = $true
        $reason = "目录中有其他索引文件"
    } elseif ($file.Name -eq "00_index.md" -and (Get-ChildItem -Path $file.DirectoryName -Filter "*.md" | Measure-Object).Count -eq 1) {
        $shouldDelete = $false
        $reason = "这是目录中唯一的索引文件，保留"
    } else {
        $shouldDelete = $true
        $reason = "无其他有用文件"
    }
    
    if ($shouldDelete) {
        Write-Host "删除: $relativePath ($reason)" -ForegroundColor Red
        $deleteCount++
        
        if (-not $DryRun) {
            if ($Backup) {
                $backupPath = Join-Path $backupDir $relativePath
                $backupDirPath = Split-Path $backupPath -Parent
                if (-not (Test-Path $backupDirPath)) {
                    New-Item -ItemType Directory -Path $backupDirPath -Force | Out-Null
                }
                Copy-Item $file.FullName $backupPath
            }
            Remove-Item $file.FullName -Force
        }
    } else {
        Write-Host "保留: $relativePath ($reason)" -ForegroundColor Green
        $keepCount++
    }
}

Write-Host "`n清理完成!" -ForegroundColor Green
Write-Host "删除文件数: $deleteCount" -ForegroundColor Red
Write-Host "保留文件数: $keepCount" -ForegroundColor Green

if ($Backup -and -not $DryRun) {
    Write-Host "备份位置: $backupDir" -ForegroundColor Cyan
}

# 生成清理报告
$report = @"
# 占位文档清理报告

## 清理统计
- 扫描文件总数: $($placeholderFiles.Count)
- 删除文件数: $deleteCount
- 保留文件数: $keepCount
- 清理时间: $(Get-Date)

## 删除的文件
$($placeholderFiles | Where-Object { $shouldDelete } | ForEach-Object { "- $($_.FullName)" } | Out-String)

## 保留的文件
$($placeholderFiles | Where-Object { -not $shouldDelete } | ForEach-Object { "- $($_.FullName)" } | Out-String)
"@

$reportPath = "placeholder_cleanup_report_$(Get-Date -Format 'yyyyMMdd_HHmmss').md"
$report | Out-File -FilePath $reportPath -Encoding UTF8
Write-Host "清理报告已保存到: $reportPath" -ForegroundColor Cyan 