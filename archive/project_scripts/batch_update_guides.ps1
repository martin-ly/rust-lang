# 批量更新 docs/05_guides/ 中的指南文档
# 添加 Rust 1.94 特性内容

$guides = @(
    "DESIGN_PATTERNS_USAGE_GUIDE.md",
    "MACRO_SYSTEM_USAGE_GUIDE.md", 
    "WASM_USAGE_GUIDE.md",
    "UNSAFE_RUST_GUIDE.md",
    "TROUBLESHOOTING_GUIDE.md"
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

### 代码示例

```rust
// array_windows 示例
let data = [1, 2, 3, 4, 5];
let sums: Vec<i32> = data.array_windows::<2>()
    .map(|&[a, b]| a + b)
    .collect();

// ControlFlow 示例  
use std::ops::ControlFlow;
let result = items.iter().try_for_each(|&n| {
    if n < 0 { ControlFlow::Break(n) }
    else { ControlFlow::Continue(()) }
});
```

**最后更新**: 2026-03-14 (添加 Rust 1.94 特性)

"@

foreach ($guide in $guides) {
    $path = "docs/05_guides/$guide"
    if (Test-Path $path) {
        $content = Get-Content $path -Raw
        
        # 检查是否已有 Rust 1.94 特性章节
        if (-not ($content -match "Rust 1\.94 特性")) {
            # 在文件末尾添加
            $content = $content -replace "(---\s*\n\*\*维护者.*)", "$rust194Section`n`$1"
            Set-Content $path $content -NoNewline
            Write-Host "✅ 已更新: $guide"
        } else {
            Write-Host "⏭️  跳过: $guide (已包含)"
        }
    } else {
        Write-Host "❌ 未找到: $guide"
    }
}

Write-Host "`n批量更新完成!"
