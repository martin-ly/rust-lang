# 修正目录命名中的重复序号问题
# 按照树形结构重新编号

Write-Host "开始修正目录命名..." -ForegroundColor Green

# 01_foundational_theory 目录下的子目录重新编号
$foundationalPath = "01_foundational_theory"

# 重新编号子目录
$subdirs = @(
    "01_category_theory",
    "01_language_philosophy", 
    "01_set_theory",
    "01_type_system",
    "02_linear_logic",
    "02_system_philosophy",
    "02_type_theory",
    "03_application_philosophy",
    "03_denotational_semantics",
    "03_memory_model",
    "04_concurrency_theory",
    "04_operational_semantics",
    "05_rust_philosophy",
    "05_type_theory"
)

# 创建新的编号映射
$newNames = @(
    "01_category_theory",
    "02_language_philosophy",
    "03_set_theory", 
    "04_type_system",
    "05_linear_logic",
    "06_system_philosophy",
    "07_type_theory_advanced",
    "08_application_philosophy",
    "09_denotational_semantics",
    "10_memory_model",
    "11_concurrency_theory",
    "12_operational_semantics",
    "13_rust_philosophy",
    "14_type_theory_specialized"
)

# 执行重命名
for ($i = 0; $i -lt $subdirs.Length; $i++) {
    $oldPath = Join-Path $foundationalPath $subdirs[$i]
    $newPath = Join-Path $foundationalPath $newNames[$i]
    
    if (Test-Path $oldPath) {
        Write-Host "重命名: $oldPath -> $newPath" -ForegroundColor Yellow
        Rename-Item -Path $oldPath -NewName $newNames[$i] -Force
    }
}

Write-Host "目录命名修正完成!" -ForegroundColor Green 