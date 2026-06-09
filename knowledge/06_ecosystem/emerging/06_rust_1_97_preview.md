# Rust 1.97 前沿特性预览

> **Bloom 层级**: 理解
> **深度**: [综述级]
>
> 本文档为 `concept/07_future/rust_1_97_preview.md` 的摘要索引。
> 完整内容（含详细语法说明、可编译示例、RFC 引用）请参见概念文档。
>
> **🔗 完整文档**: [Rust 1.97 前沿特性预览](../../../concept/07_future/rust_1_97_preview.md)
>
> **发布日期**: 2026-07-09（预计）
> **跟踪版本**: nightly 1.98.0
> **版本状态**: 🧪 Nightly / 1.97 已进入 Beta 分支
> **权威来源**:
> [Rust Internals](https://internals.rust-lang.org/) ·
> [GitHub rust-lang/rust](https://github.com/rust-lang/rust) ·
> [releases.rs nightly](https://releases.rs/)
>
> **受众**: [进阶] / [专家]
> **内容分级**: [实验级]

---

## 核心看点速览

- **AFIDT（async fn in dyn Trait）**: 原生支持 `dyn Trait` 中的异步方法
- **标准库扩展**: `VecDeque::truncate_front`、`RefCell::try_map`、`int_format_into`
- **Cargo 演进**: `cargo script` 和 frontmatter 格式持续完善
- **编译器**: 新的 Range 类型（RFC 3550）实验性推进

> 如需深入理解每项特性的设计动机、语法细节与工程实践，请阅读 [完整概念文档](../../../concept/07_future/rust_1_97_preview.md)。
