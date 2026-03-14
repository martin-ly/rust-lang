# 批量更新 docs/rust-ownership-decidability/ 核心文件

$files = @(
    "README.md",
    "ULTIMATE_COMPREHENSIVE_GUIDE.md",
    "UNIFIED_THEORETICAL_FRAMEWORK.md",
    "INTERACTIVE_LEARNING_GUIDE.md",
    "QUICK_REFERENCE_CARD.md",
    "READING_GUIDE.md",
    "THEOREM_DEPENDENCY_GRAPH.md",
    "THEOREM_INTUITIONS.md",
    "PROOF_STRATEGIES.md",
    "DESIGN_RATIONALE.md"
)

$section = @"

---

## 🆕 Rust 1.94 所有权系统更新

> **适用版本**: Rust 1.94.0+

### 新特性对所有权系统的影响

| 特性 | 所有权影响 | 可判定性 |
|------|-----------|---------|
| `array_windows` | 安全的切片访问 | ✅ 编译期检查 |
| `ControlFlow` | 控制流语义 | ✅ 类型安全 |
| `LazyCell/LazyLock` | 延迟初始化 | ✅ Send/Sync 检查 |

### 形式化更新

- `array_windows` 的边界安全证明
- `ControlFlow` 的代数性质
- 延迟初始化的生命周期分析

**最后更新**: 2026-03-14
"@

$count = 0
foreach ($file in $files) {
    $path = "docs/rust-ownership-decidability/$file"
    if (Test-Path $path) {
        $content = Get-Content $path -Raw
        
        if (-not ($content -match "Rust 1\.94")) {
            $content = $content + $section
            Set-Content $path $content -NoNewline
            Write-Host "✅ 已更新: $file"
            $count++
        } else {
            Write-Host "⏭️  跳过: $file"
        }
    }
}

Write-Host "`n✅ 更新了 $count 个文件"
