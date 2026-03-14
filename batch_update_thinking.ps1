# 批量更新 docs/04_thinking/

$files = @(
    "APPLICATIONS_ANALYSIS_VIEW.md",
    "DECISION_GRAPH_NETWORK.md",
    "MIND_MAP_COLLECTION.md",
    "MULTI_DIMENSIONAL_CONCEPT_MATRIX.md",
    "PROOF_GRAPH_NETWORK.md",
    "THINKING_REPRESENTATION_METHODS.md"
)

$section = @"

---

## 🆕 Rust 1.94 思维表征更新

> **适用版本**: Rust 1.94.0+

### 新增思维表征

Rust 1.94 引入了以下新特性，可扩展思维表征：

| 特性 | 思维表征类型 | 说明 |
|------|-------------|------|
| `array_windows` | 模式识别 | 固定大小窗口的模式检测 |
| `ControlFlow` | 决策树 | 控制流的提前终止决策 |
| `LazyCell/LazyLock` | 状态图 | 延迟初始化的状态转换 |

### 示例

```rust
// array_windows 的思维导图节点
// [数据切片] -> [array_windows<N>] -> [模式匹配]

// ControlFlow 的决策树
// [迭代开始] -> [条件检查] -> [Break/Continue]
```

**最后更新**: 2026-03-14 (添加 Rust 1.94 支持)
"@

foreach ($file in $files) {
    $path = "docs/04_thinking/$file"
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

Write-Host "`ndocs/04_thinking/ 更新完成!"
