# 目录结构分析脚本

Write-Output "=== Rust语言形式化理论目录重构分析 ==="
Write-Output ""

# 分析C编号系统目录
Write-Output "=== C编号系统目录 ==="
$cDirs = Get-ChildItem -Path "formal_rust/language" -Directory | Where-Object { $_.Name -match "^c\d+" }
foreach ($dir in $cDirs) {
    $fileCount = (Get-ChildItem -Path $dir.FullName -Recurse -File -Name "*.md" | Measure-Object).Count
    Write-Output "$($dir.Name): $fileCount files"
}

Write-Output ""

# 分析标准编号系统目录
Write-Output "=== 标准编号系统目录 ==="
$standardDirs = Get-ChildItem -Path "formal_rust/language" -Directory | Where-Object { $_.Name -match "^\d{2}_" }
foreach ($dir in $standardDirs) {
    $fileCount = (Get-ChildItem -Path $dir.FullName -Recurse -File -Name "*.md" | Measure-Object).Count
    Write-Output "$($dir.Name): $fileCount files"
}

Write-Output ""

# 分析编号冲突
Write-Output "=== 编号系统冲突分析 ==="

# 检查04编号冲突
$conflict04 = Get-ChildItem -Path "formal_rust/language" -Directory | Where-Object { $_.Name -match "04_" }
Write-Output "04编号冲突:"
foreach ($dir in $conflict04) {
    $fileCount = (Get-ChildItem -Path $dir.FullName -Recurse -File -Name "*.md" | Measure-Object).Count
    Write-Output "  $($dir.Name): $fileCount files"
}

Write-Output ""
Write-Output "=== 分析完成 ==="
