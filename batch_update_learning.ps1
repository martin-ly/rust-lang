# 批量更新 docs/01_learning/

$files = @(
    "LEARNING_PATH_PLANNING.md",
    "MDBOOK_QUIZ_GUIDE.md",
    "OFFICIAL_RESOURCES_MAPPING.md"
)

$section = @"

---

## 🆕 Rust 1.94 学习路径

> **适用版本**: Rust 1.94.0+

### 1.94 新特性学习要点

| 特性 | 学习难度 | 推荐顺序 |
|------|---------|---------|
| `array_windows` | ⭐ | 第1周 |
| `ControlFlow` | ⭐⭐ | 第2周 |
| `LazyCell/LazyLock` 新方法 | ⭐⭐ | 第3周 |
| `Peekable::next_if_map` | ⭐ | 第4周 |

### 学习资源

- [Rust 1.94 迁移指南](../05_guides/RUST_194_MIGRATION_GUIDE.md)
- [Rust 1.94 发布说明](../06_toolchain/16_rust_1.94_release_notes.md)

**最后更新**: 2026-03-14 (添加 Rust 1.94 学习路径)
"@

foreach ($file in $files) {
    $path = "docs/01_learning/$file"
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

Write-Host "`ndocs/01_learning/ 更新完成!"
