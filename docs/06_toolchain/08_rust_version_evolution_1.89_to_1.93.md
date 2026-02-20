# Rust 版本演进链（1.89–1.93）

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-15
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成

---

## 演进概览

| 版本 | 发布日期 | 主要变更摘要 |
| :--- | :--- | :--- || 1.89 | 2025-08 | 稳定化、性能、错误诊断 |
| 1.90 | 2025-09 | LLD 默认链接器、cargo publish --workspace、平台变更 |
| 1.91 | 2025-10 | aarch64-pc-windows-msvc Tier 1、dangling_pointers_from_locals lint |
| 1.92 | 2025-12 | Never 类型 Lint 严格化、musl 预告、标准库 API |
| 1.93 | 2026-01 | musl 1.2.5、全局分配器 TLS、asm_cfg、大量 API 稳定化、兼容性变更 |

---

## 1.89 → 1.90

**关键变更**:

- **LLD 默认链接器**：`x86_64-unknown-linux-gnu` 默认使用 LLD
- **cargo publish --workspace**：工作区一并发布
- **平台**：`x86_64-apple-darwin` 等平台支持调整

**参考**：[Rust 1.90.0](https://blog.rust-lang.org/2025/09/18/Rust-1.90.0/)

---

## 1.90 → 1.91

**关键变更**:

- **aarch64-pc-windows-msvc** 升级为 Tier 1
- **dangling_pointers_from_locals** lint（warn-by-default）

**参考**：[Rust 1.91.0](https://blog.rust-lang.org/2025/10/30/Rust-1.91.0/)

---

## 1.91 → 1.92

**关键变更**:

- **Never 类型 Lint**：`never_type_fallback_flowing_into_unsafe`、`dependency_on_unit_never_type_fallback` 从 warn 升级为 deny
- **musl 更新预告**：为 1.93 musl 1.2.5 做准备
- **标准库**：Box::new_zeroed、Rc/Arc::new_zeroed、迭代器特化等

**参考**：[Rust 1.92.0](https://blog.rust-lang.org/2025/12/11/Rust-1.92.0/)

---

## 1.92 → 1.93

**关键变更**:

- **musl 1.2.5**：DNS 解析改进
- **全局分配器**：支持 thread_local
- **asm_cfg**：asm! 行上 cfg
- **API 稳定化**：MaybeUninit、String/Vec raw parts、VecDeque、Duration、char、fmt 等
- **兼容性**：deref_nullptr deny、#[test] 无效位置报错、Emscripten ABI、offset_of 等

**参考**：[05_rust_1.93_vs_1.92_comparison.md](./05_rust_1.93_vs_1.92_comparison.md)、[06_rust_1.93_compatibility_notes.md](./06_rust_1.93_compatibility_notes.md)

---

## 迁移路径建议

| 当前版本 | 目标 1.93 | 建议 |
| :--- | :--- | :--- || 1.89 | 1.93 | 检查 Never 类型 Lint、deref_nullptr、#[test] |
| 1.90 | 1.93 | 检查 LLD、cargo 变更 |
| 1.91 | 1.93 | 检查平台、dangling_pointers |
| 1.92 | 1.93 | 少量变更，关注兼容性文档 |

---

## 相关文档

- [Rust 1.93 vs 1.92 对比](./05_rust_1.93_vs_1.92_comparison.md)
- [Rust 1.93 兼容性注意事项](./06_rust_1.93_compatibility_notes.md)
- [Rust 1.93 完整变更清单](./07_rust_1.93_full_changelog.md)

---

**最后对照 releases.rs**: 2026-02-14
