# 编译器（Compiler）索引

## 主题

- 编译流程：HIR → MIR → LLVM（或 Cranelift）
- 优化要点：内联、去虚、逃逸分析、跨模块优化（LTO）
- 诊断与建议：lint、polonius（研究）、错误改进

## 工具与实践

- 后端选择：`-Z codegen-backend=cranelift`（Nightly）
- 构建优化：`RUSTFLAGS="-C target-cpu=native"`、`lto=true`、`codegen-units=1`
- MIR 观察：`RUSTC_LOG=rustc_mir=info`（按需）

## 导航

- 返回工具链生态：[`../00_index.md`](../00_index.md)
- 质量保障：[`../../10_quality_assurance/00_index.md`](../../10_quality_assurance/00_index.md)
