# Rust 1.92.0 WASM 性能基准测试

**EN**: Advanced WebAssembly
**Summary**: Stub redirecting to the canonical concept page for `Advanced WebAssembly`. Crate-specific API notes remain here; general explanations live in `concept/`.

> **权威来源**: [06_ecosystem/11_domain_applications/54_webassembly_advanced.md](../../../concept/06_ecosystem/11_domain_applications/54_webassembly_advanced.md)

本文件为 crate 文档占位页。通用 Rust 概念解释已迁移/整合至上方的 `concept/` 权威页；如需深入了解，请访问权威来源。

## 主题速览

- 测试概述
- 测试结果
- 1. 内存管理性能测试
- 测试场景: WasmBuffer vs Vec
- 2. 计算性能测试
- 测试场景: NonZero::div_ceil vs 手动计算
- 3. 迭代器性能测试
- 测试场景: 特化迭代器 vs 通用迭代器
- 4. 数据操作性能测试
- 测试场景: rotate_right vs 手动实现
