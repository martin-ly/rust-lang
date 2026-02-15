# 嵌入式 Rust 专题指南

> **创建日期**: 2026-02-13
> **权威源**: [The Embedded Rust Book](https://doc.rust-lang.org/embedded-book/)
> **用途**: 对标官方 Embedded Book，提供本项目内导航与补充

---

## 文档定位

本指南为官方 **Embedded Rust Book** 的入口与项目内导航，帮助在开发嵌入式 Rust 应用时快速定位到本项目的相关模块和官方资源。

---

## 官方 Embedded 资源入口

| 资源 | URL | 说明 |
|------|-----|------|
| **Embedded Rust Book** | <https://doc.rust-lang.org/embedded-book/> | 官方嵌入式 Rust 教程 |
| **Discovery Book** | <https://docs.rust-embedded.org/discovery/> | 零基础嵌入式入门 |
| **Embedonomicon** | <https://docs.rust-embedded.org/embedonomicon/> | 嵌入式 Rust 底层细节 |
| **Embedded FAQ** | <https://docs.rust-embedded.org/faq.html> | 常见问题 |
| **Comprehensive Rust: Bare Metal** | <https://google.github.io/comprehensive-rust/bare-metal.html> | Google 裸机开发课程 |

---

## 本项目对应模块

| 嵌入式主题 | 官方 Embedded Book | 本项目对应 |
|------------|-------------------|------------|
| 所有权与内存安全 | 内存管理、无堆 | [C01 所有权](../../crates/c01_ownership_borrow_scope/) |
| 类型系统与 no_std | 最小运行时 | [C02 类型系统](../../crates/c02_type_system/) |
| 并发与中断 | 临界区、原子操作 | [C05 线程与并发](../../crates/c05_threads/) |
| 进程与系统调用 | - | [C07 进程管理](../../crates/c07_process/) |
| WASM 与边缘计算 | - | [C12 WASM](../../crates/c12_wasm/) |

---

## 推荐学习路径

1. **前置**: 熟练掌握 C01 所有权、C02 类型系统（本项目核心模块）
2. **入门**: [Discovery Book](https://docs.rust-embedded.org/discovery/)（零嵌入式经验）
3. **进阶**: [Embedded Rust Book](https://doc.rust-lang.org/embedded-book/)（ARM Cortex-M）
4. **深入**: [Embedonomicon](https://docs.rust-embedded.org/embedonomicon/)

---

## 相关文档

- [C01 所有权](../../crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md)
- [C02 类型系统](../../crates/c02_type_system/docs/)
- [C05 线程与并发](../../crates/c05_threads/docs/)
- [C12 WASM](../../crates/c12_wasm/docs/)
- [官方 Embedded Book](https://doc.rust-lang.org/embedded-book/)
