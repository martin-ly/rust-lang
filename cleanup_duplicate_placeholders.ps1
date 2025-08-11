# 重复占位文档清理脚本
# 专门处理内容完全相同的占位文档

param(
    [string]$RootPath = "formal_rust/refactor",
    [switch]$DryRun = $false,
    [switch]$Backup = $true
)

Write-Host "开始清理重复占位文档..." -ForegroundColor Green
Write-Host "根目录: $RootPath" -ForegroundColor Yellow
Write-Host "模拟运行: $DryRun" -ForegroundColor Yellow

# 创建备份目录
if ($Backup -and -not $DryRun) {
    $backupDir = "backup_duplicates_$(Get-Date -Format 'yyyyMMdd_HHmmss')"
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

# 按内容哈希分组
Write-Host "按内容分组..." -ForegroundColor Cyan
$contentGroups = @{}

foreach ($file in $placeholderFiles) {
    $content = Get-Content $file.FullName -Raw -ErrorAction SilentlyContinue
    $hash = [System.Security.Cryptography.MD5]::Create().ComputeHash([System.Text.Encoding]::UTF8.GetBytes($content))
    $hashString = [System.BitConverter]::ToString($hash).Replace("-", "")
    
    if (-not $contentGroups.ContainsKey($hashString)) {
        $contentGroups[$hashString] = @()
    }
    $contentGroups[$hashString] += $file
}

Write-Host "找到 $($contentGroups.Count) 种不同的占位文档内容" -ForegroundColor Yellow

# 处理重复内容
$deleteCount = 0
$keepCount = 0
$deletedFiles = @()
$keptFiles = @()

foreach ($hash in $contentGroups.Keys) {
    $files = $contentGroups[$hash]
    
    if ($files.Count -gt 1) {
        Write-Host "`n发现重复内容组 (共 $($files.Count) 个文件):" -ForegroundColor Cyan
        
        # 选择保留的文件（优先选择更合适的路径）
        $keepFile = $files | Sort-Object { 
            # 优先保留更浅层级的文件
            ($_.FullName.Split('\').Count - 1)
        } | Select-Object -First 1
        
        Write-Host "  保留: $($keepFile.FullName)" -ForegroundColor Green
        $keptFiles += $keepFile
        $keepCount++
        
        # 删除其他重复文件
        $duplicateFiles = $files | Where-Object { $_.FullName -ne $keepFile.FullName }
        foreach ($duplicateFile in $duplicateFiles) {
            Write-Host "  删除: $($duplicateFile.FullName)" -ForegroundColor Red
            $deletedFiles += $duplicateFile
            $deleteCount++
            
            if (-not $DryRun) {
                if ($Backup) {
                    $backupPath = Join-Path $backupDir $duplicateFile.FullName.Replace((Get-Location).Path + "\", "")
                    $backupDirPath = Split-Path $backupPath -Parent
                    if (-not (Test-Path $backupDirPath)) {
                        New-Item -ItemType Directory -Path $backupDirPath -Force | Out-Null
                    }
                    Copy-Item $duplicateFile.FullName $backupPath
                }
                Remove-Item $duplicateFile.FullName -Force
            }
        }
    } else {
        # 单个文件，保留
        Write-Host "保留唯一文件: $($files[0].FullName)" -ForegroundColor Green
        $keptFiles += $files[0]
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
# 重复占位文档清理报告

## 清理统计
- 扫描文件总数: $($placeholderFiles.Count)
- 删除文件数: $deleteCount
- 保留文件数: $keepCount
- 清理时间: $(Get-Date)

## 删除的文件
$($deletedFiles | ForEach-Object { "- $($_.FullName)" } | Out-String)

## 保留的文件
$($keptFiles | ForEach-Object { "- $($_.FullName)" } | Out-String)

## 内容分组统计
$($contentGroups | ForEach-Object { "- 哈希 $($_.Key): $($_.Value.Count) 个文件" } | Out-String)
"@

$reportPath = "duplicate_cleanup_report_$(Get-Date -Format 'yyyyMMdd_HHmmss').md"
$report | Out-File -FilePath $reportPath -Encoding UTF8
Write-Host "清理报告已保存到: $reportPath" -ForegroundColor Cyan 