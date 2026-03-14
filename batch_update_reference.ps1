# 批量更新 docs/02_reference/

$files = @(
    "ALIGNMENT_GUIDE.md",
    "CROSS_LANGUAGE_COMPARISON.md",
    "EDGE_CASES_AND_SPECIAL_CASES.md",
    "ERROR_CODE_MAPPING.md",
    "STANDARD_LIBRARY_COMPREHENSIVE_ANALYSIS_2025_12_25.md"
)

$section = @"

---

## 🆕 Rust 1.94 更新

> **适用版本**: Rust 1.94.0+

详见 [Rust 1.94 发布说明](../06_toolchain/16_rust_1.94_release_notes.md)

**最后更新**: 2026-03-14
"@

foreach ($file in $files) {
    $path = "docs/02_reference/$file"
    if (Test-Path $path) {
        $content = Get-Content $path -Raw
        
        if (-not ($content -match "Rust 1\.94")) {
            $content = $content + $section
            Set-Content $path $content -NoNewline
            Write-Host "✅ 已更新: $file"
        } else {
            Write-Host "⏭️  跳过: $file"
        }
    }
}

Write-Host "`n参考资料更新完成!"
