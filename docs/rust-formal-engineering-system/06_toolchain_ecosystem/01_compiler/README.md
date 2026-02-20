# 编译器理论

> **创建日期**: 2026-02-20
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成

> 内容已整合至： [01_compiler_features.md](../../../06_toolchain/01_compiler_features.md)

[返回主索引](../../00_master_index.md)

---

## Rust 编译器核心概念

### 编译流程

```rust
// 1. 词法分析：源代码 → Token
// 2. 语法分析：Token → AST
// 3. 语义分析：AST → HIR
// 4. 类型检查：HIR → 类型注解 HIR
// 5. 借用检查：HIR → MIR
// 6. MIR 优化
// 7. 代码生成：MIR → LLVM IR
// 8. LLVM 优化和代码生成
```

### 编译器属性

```rust
// 条件编译
#[cfg(target_os = "linux")]
fn linux_only() {}

#[cfg(all(feature = "serde", not(target_arch = "wasm32")))]
fn conditional_feature() {}

// 内联控制
#[inline]           // 建议内联
fn suggested_inline() {}

#[inline(always)]   // 总是内联
fn force_inline() {}

#[inline(never)]    // 从不内联
fn never_inline() {}

// 优化提示
#[cold]             // 冷路径（很少执行）
fn error_handler() {}

#[must_use]         // 返回值必须使用
fn important_result() -> i32 { 42 }

// 链接控制
#[link(name = "mylib")]
extern "C" {
    fn c_function();
}
```

### 编译器标志

```bash
# 优化级别
rustc -C opt-level=0    # 无优化（调试）
rustc -C opt-level=3    # 最大优化
rustc -C opt-level=s    # 优化大小

# 链接时优化
rustc -C lto=fat        # 完整 LTO
rustc -C lto=thin       # 轻量 LTO

# 代码生成单元
rustc -C codegen-units=1  # 单代码生成单元（最大优化）

# 目标 CPU
rustc -C target-cpu=native  # 针对本机 CPU
rustc -C target-cpu=haswell # 针对特定 CPU
```

## 形式化方法

| 文档 | 描述 | 路径 |
| :--- | :--- | :--- |
| 形式化方法概述 | 形式化验证基础理论 | [../../../../research_notes/formal_methods/README.md](../../../../research_notes/formal_methods/README.md) |
| 所有权模型形式化 | 所有权系统数学定义 | [../../../../research_notes/formal_methods/ownership_model.md](../../../../research_notes/formal_methods/ownership_model.md) |
| 生命周期形式化 | 生命周期理论证明 | [../../../../research_notes/formal_methods/lifetime_formalization.md](../../../../research_notes/formal_methods/lifetime_formalization.md) |

## 相关研究笔记

| 文档 | 描述 | 路径 |
| :--- | :--- | :--- |
| 编译器特性 | 完整编译器指南 | [../../../06_toolchain/01_compiler_features.md](../../../06_toolchain/01_compiler_features.md) |
| 编译器优化实验 | 优化分析 | [../../../../research_notes/experiments/compiler_optimizations.md](../../../../research_notes/experiments/compiler_optimizations.md) |
| 研究方法论 | 研究方法指南 | [../../../../research_notes/research_methodology.md](../../../../research_notes/research_methodology.md) |
| 工具指南 | 验证工具使用 | [../../../../research_notes/TOOLS_GUIDE.md](../../../../research_notes/TOOLS_GUIDE.md) |
