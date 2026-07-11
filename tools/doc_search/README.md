# 智能文档搜索工具

> **状态**: ⚠️ 未实现（placeholder）。本目录仅有本 README，无任何代码。
> **最后更新**: 2026-07-12

---

## 说明

本目录曾规划提供独立的全文搜索 CLI（`cargo run -- build-index` / `search`），
但该实现从未落地，目录中不存在任何 Rust 源码或 `Cargo.toml`。

当前项目的搜索能力由以下机制提供：

- **mdbook 内置搜索**：`mdbook build` 自动生成 `book/searchindex.js`，
  在线文档平台与本地 `mdbook serve` 均可直接使用页面右上角搜索框。
- **KG 语义检索原型**：[`tools/kg_rag/`](../kg_rag/) 提供基于
  `concept/00_meta/kg_data_v3.json` 的向量混合检索。

如未来需要独立搜索 CLI，请在本目录新建 Rust crate 并更新本文件。

## 相关文档

- [项目 README](../../README.md)
- [KG-RAG 检索原型](../kg_rag/README.md)

---

**文档版本**: 2.0
**对应 Rust 版本**: 1.97.0+ (Edition 2024)
**最后更新**: 2026-07-12
