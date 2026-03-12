#!/usr/bin/env pwsh
# 版本化文件迁移脚本
# 将旧版本特性文件迁移到 archive 目录

$ErrorActionPreference = "Stop"

$crates = @(
    "c01_ownership_borrow_scope",
    "c02_type_system", 
    "c03_control_fn",
    "c04_generic",
    "c05_threads",
    "c06_async",
    "c07_process",
    "c08_algorithms",
    "c09_design_pattern",
    "c10_networks",
    "c11_macro_system",
    "c12_wasm"
)

# 当前活跃版本
$activeVersions = @("193", "194")  # 1.93 和 1.94 保持活跃

# 需要归档的版本 (1.89 - 1.92)
$archiveVersions = @("189", "190", "191", "192")

foreach ($crate in $crates) {
    Write-Host "`n处理 crate: $crate" -ForegroundColor Cyan
    
    $srcDir = "crates/$crate/src"
    $archiveDir = "$srcDir/archive"
    
    # 获取所有版本化文件
    $versionFiles = Get-ChildItem "$srcDir" -Filter "rust_1*.rs" -ErrorAction SilentlyContinue
    
    foreach ($file in $versionFiles) {
        $fileName = $file.Name
        
        # 提取版本号 (如 rust_189_basic_syntax.rs -> 189)
        if ($fileName -match "rust_(\d\d\d)") {
            $version = $matches[1]
            
            if ($archiveVersions -contains $version) {
                # 需要归档
                $sourcePath = "$srcDir/$fileName"
                $destPath = "$archiveDir/$fileName"
                
                # 检查是否已在 archive 中
                if (Test-Path $destPath) {
                    Write-Host "  已存在: $fileName" -ForegroundColor Yellow
                } else {
                    # 复制文件到 archive
                    Copy-Item $sourcePath $destPath
                    Write-Host "  已归档: $fileName -> archive/" -ForegroundColor Green
                }
            } else {
                Write-Host "  保持活跃: $fileName" -ForegroundColor Gray
            }
        }
    }
}

Write-Host "`n迁移完成!" -ForegroundColor Green
