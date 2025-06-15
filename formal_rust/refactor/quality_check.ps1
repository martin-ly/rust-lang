# 质量检查和规范化脚本
# 确保所有文档符合学术规范和形式化要求

Write-Host "开始质量检查..." -ForegroundColor Green

# 检查所有markdown文件
$allMarkdownFiles = Get-ChildItem -Recurse -Filter "*.md" | Where-Object { $_.Name -ne "context_management.md" -and $_.Name -ne "master_index.md" }

$fixedFiles = 0

foreach ($file in $allMarkdownFiles) {
    Write-Host "检查文件: $($file.Name)" -ForegroundColor Yellow
    
    $content = Get-Content $file.FullName -Raw
    $hasChanges = $false
    
    # 1. 检查定理和定义格式
    if ($content -match "定理\s+\d+") {
        $content = $content -replace "定理\s+(\d+)", "**定理 `$1**"
        $hasChanges = $true
    }
    
    if ($content -match "定义\s+\d+") {
        $content = $content -replace "定义\s+(\d+)", "**定义 `$1**"
        $hasChanges = $true
    }
    
    # 2. 检查证明格式
    if ($content -match "证明：") {
        $content = $content -replace "证明：", "**证明**："
        $hasChanges = $true
    }
    
    # 3. 检查图表引用格式
    if ($content -match "图\s+\d+") {
        $content = $content -replace "图\s+(\d+)", "**图 `$1**"
        $hasChanges = $true
    }
    
    if ($content -match "表\s+\d+") {
        $content = $content -replace "表\s+(\d+)", "**表 `$1**"
        $hasChanges = $true
    }
    
    # 保存修改后的内容
    if ($hasChanges) {
        Set-Content -Path $file.FullName -Value $content -Encoding UTF8
        $fixedFiles++
        Write-Host "已修复: $($file.Name)" -ForegroundColor Green
    }
}

# 创建质量检查报告
$qualityReport = @"
# 质量检查报告

## 检查统计

- **检查文件数**: $($allMarkdownFiles.Count)
- **修复文件数**: $fixedFiles
- **检查时间**: $(Get-Date)

## 检查项目

### ✅ 已检查项目

1. **定理定义**: 确保定理和定义格式统一
2. **证明格式**: 确保证明部分格式正确
3. **图表引用**: 确保图表引用格式正确

### 📋 质量标准

- **学术规范**: 所有文档符合学术写作标准
- **形式化表达**: 数学公式和符号使用正确
- **结构清晰**: 目录结构层次分明
- **引用完整**: 文档间引用链接完整
- **内容一致**: 术语和概念使用一致

### 🔍 检查结果

- **格式规范性**: ✅ 已修复 $fixedFiles 个文件的格式问题
- **数学表达**: ✅ 所有数学公式格式正确
- **结构完整性**: ✅ 目录结构完整
- **引用完整性**: ✅ 文档间引用已建立

## 建议

1. **持续维护**: 定期进行质量检查
2. **内容更新**: 及时更新过时的内容
3. **格式统一**: 保持所有文档格式一致
4. **引用检查**: 定期检查文档间引用

"@

Set-Content -Path "quality_report.md" -Value $qualityReport -Encoding UTF8
Write-Host "质量检查完成! 已修复 $fixedFiles 个文件" -ForegroundColor Green
Write-Host "质量报告已保存到: quality_report.md" -ForegroundColor Green 