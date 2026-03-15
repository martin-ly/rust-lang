#!/usr/bin/env pwsh
# 批量更新所有 crates 到 Rust 1.94

$crates = @(
    @{ Name="c04_generic"; Features=@("RPITIT", "use<> 语法", "泛型类型推断增强") },
    @{ Name="c05_threads"; Features=@("Send/Sync 边界", "Mutex 改进", "并发模式") },
    @{ Name="c06_async"; Features=@("gen 关键字", "异步生成器", "ControlFlow") },
    @{ Name="c07_process"; Features=@("标准库 API", "IO 改进", "错误处理") },
    @{ Name="c08_algorithms"; Features=@("迭代器优化", "ControlFlow", "性能") },
    @{ Name="c09_design_pattern"; Features=@("RPITIT 模式", "use<> 模式", "新特性应用") },
    @{ Name="c10_networks"; Features=@("异步网络", "生成器", "性能优化") },
    @{ Name="c11_macro_system"; Features=@("过程宏", "生成器集成", "新语法") },
    @{ Name="c12_wasm"; Features=@("WASM 2024", "性能", "互操作") }
)

foreach ($crate in $crates) {
    $crateName = $crate.Name
    $features = $crate.Features -join ", "
    
    Write-Host "Updating $crateName..." -ForegroundColor Cyan
    Write-Host "  Features: $features" -ForegroundColor Gray
    
    $docsPath = "crates/$crateName/docs"
    $updatePath = "$docsPath/rust_194_updates"
    
    # 创建目录
    if (!(Test-Path $updatePath)) {
        New-Item -ItemType Directory -Path $updatePath -Force | Out-Null
        Write-Host "  Created $updatePath" -ForegroundColor Green
    }
    
    # 创建占位符文件（实际内容需要手动编写或后续填充）
    $placeholderContent = @"
# $crateName - Rust 1.94 更新

> **Rust 版本**: 1.94.0
> **Edition**: 2024
> **最后更新**: 2026-03-10

## 主要特性

- $features

## 详细内容

TODO: 添加详细文档

## 相关文档

- [Rust 1.94 发布说明](../../../docs/06_toolchain/16_rust_1.94_release_notes.md)
- [主索引](../00_MASTER_INDEX.md)
"@
    
    $placeholderPath = "$updatePath/00_rust_194_overview.md"
    if (!(Test-Path $placeholderPath)) {
        $placeholderContent | Out-File -FilePath $placeholderPath -Encoding UTF8
        Write-Host "  Created $placeholderPath" -ForegroundColor Green
    }
}

Write-Host "`nAll crates updated!" -ForegroundColor Green
Write-Host "Next steps:" -ForegroundColor Yellow
Write-Host "  1. Fill in detailed content for each crate"
Write-Host "  2. Update main indices"
Write-Host "  3. Run link checker"
