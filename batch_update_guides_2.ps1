# 第二批批量更新

$guides = @(
    "AI_RUST_ECOSYSTEM_GUIDE.md",
    "CLI_APPLICATIONS_GUIDE.md",
    "EMBEDDED_RUST_GUIDE.md",
    "FFI_PRACTICAL_GUIDE.md",
    "INLINE_ASSEMBLY_GUIDE.md",
    "PERFORMANCE_TUNING_GUIDE.md",
    "TESTING_COVERAGE_GUIDE.md",
    "TOKIO_ECOSYSTEM_GUIDE.md"
)

$rust194Section = @"

## 🆕 Rust 1.94 特性

> **适用版本**: Rust 1.94.0+

### 新特性概览

Rust 1.94 带来了以下重要更新：

- **`array_windows`** - 固定大小的数组窗口迭代器
- **`ControlFlow`** - 控制流抽象类型  
- **`LazyCell/LazyLock` 新方法** - `get()`, `get_mut()`, `force_mut()`
- **`Peekable::next_if_map`** - 条件映射迭代
- **`TryFrom<char> for usize`** - Unicode 标量值转换
- **数学常量** - `EULER_GAMMA`, `GOLDEN_RATIO`

**最后更新**: 2026-03-14 (添加 Rust 1.94 特性)

"@

foreach ($guide in $guides) {
    $path = "docs/05_guides/$guide"
    if (Test-Path $path) {
        $content = Get-Content $path -Raw
        
        if (-not ($content -match "Rust 1\.94 特性")) {
            $content = $content -replace "(---\s*\n\*\*维护者.*)", "$rust194Section`n`$1"
            Set-Content $path $content -NoNewline
            Write-Host "✅ 已更新: $guide"
        } else {
            Write-Host "⏭️  跳过: $guide"
        }
    }
}

Write-Host "`n第二批更新完成!"
