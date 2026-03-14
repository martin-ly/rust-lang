# 批量更新核心研究笔记

$files = @(
    "CARGO_194_FEATURES.md",
    "FORMAL_METHODS_MASTER_INDEX.md",
    "PROOF_INDEX.md",
    "README.md"
)

$section = @"

---

## 🆕 Rust 1.94 更新

> **最新版本**: Rust 1.94.0 (2026-03-05)

- TOML 1.1 支持
- `Cargo.toml` 多行内联表
- 配置文件 `include` 支持

详见 [Rust 1.94 研究更新](./RUST_194_RESEARCH_UPDATE.md)

**最后更新**: 2026-03-14
"@

foreach ($file in $files) {
    $path = "docs/research_notes/$file"
    if (Test-Path $path) {
        $content = Get-Content $path -Raw
        
        if (-not ($content -match "Rust 1\.94 更新")) {
            $content = $content + $section
            Set-Content $path $content -NoNewline
            Write-Host "✅ 已更新: $file"
        } else {
            Write-Host "⏭️  跳过: $file"
        }
    } else {
        Write-Host "❌ 未找到: $file"
    }
}

Write-Host "`n研究笔记更新完成!"
