# 批量更新 docs/06_toolchain/

$files = @(
    "01_compiler_features.md",
    "02_cargo_workspace_guide.md",
    "03_rustdoc_advanced.md",
    "04_rust_1.91_vs_1.90_comparison.md",
    "08_rust_version_evolution_1.89_to_1.93.md",
    "10_rust_1.89_to_1.93_cumulative_features_overview.md",
    "12_rust_1.93.1_vs_1.93.0_comparison.md",
    "14_rust_1.95_nightly_preview.md"
)

$section = @"

---

## 🆕 Rust 1.94 更新

> **最新版本**: Rust 1.94.0 (2026-03-05)

本文档基于 Rust 1.93/1.92，最新版本请参见：
- [Rust 1.94 完整发布说明](./16_rust_1.94_release_notes.md)
- [Rust 1.94 采用指南](./18_rust_1.94_adoption_guide.md)
- [Rust 1.93 vs 1.94 对比](./17_rust_1.93_vs_1.94_comparison.md)

**最后更新**: 2026-03-14 (添加 1.94 引用)
"@

foreach ($file in $files) {
    $path = "docs/06_toolchain/$file"
    if (Test-Path $path) {
        $content = Get-Content $path -Raw
        
        if (-not ($content -match "Rust 1\.94 更新")) {
            # 在文件末尾添加
            $content = $content + $section
            Set-Content $path $content -NoNewline
            Write-Host "✅ 已更新: $file"
        } else {
            Write-Host "⏭️  跳过: $file"
        }
    }
}

Write-Host "`n工具链文档更新完成!"
