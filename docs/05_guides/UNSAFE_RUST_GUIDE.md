# Unsafe Rust 专题指南

> **最后更新**: 2026-02-11
> **前置**: 需熟练掌握 C01 所有权、C02 类型系统
> **官方权威**: [The Rustonomicon](https://doc.rust-lang.org/nomicon/)

---

## 文档定位

本指南为 **Rustonomicon** 的补充与项目内导航，帮助在系统学习 unsafe Rust 时快速定位到本项目的相关模块和示例。

---

## 核心内容导航（对标 Rustonomicon）

> **权威源**: [The Rustonomicon](https://doc.rust-lang.org/nomicon/) | 最后对照: 2026-02-14

| 主题 | 对应 Nomicon 章节 | 直接链接 | 本项目对应 |
|------|------------------|----------|------------|
| 安全与 unsafe 分离 | Meet Safe and Unsafe | [nomicon/meet-safe-and-unsafe](https://doc.rust-lang.org/nomicon/meet-safe-and-unsafe.html) | 本文档、C01 |
| Safe/Unsafe 交互 | How Safe and Unsafe Interact | [nomicon/safe-unsafe-meaning](https://doc.rust-lang.org/nomicon/safe-unsafe-meaning.html) | 本文档 |
| Unsafe 可做之事 | What Unsafe Rust Can Do | [nomicon/what-unsafe-does](https://doc.rust-lang.org/nomicon/what-unsafe-does.html) | 本文档 |
| 实践 unsafe | Working with Unsafe | [nomicon/working-with-unsafe](https://doc.rust-lang.org/nomicon/working-with-unsafe.html) | C01 高级所有权 |
| 数据表示与布局 | Data Representation | [nomicon/data.html](https://doc.rust-lang.org/nomicon/data.html) | C02 类型系统 |
| 类型转换 | Type Coercions / Conversions | [nomicon/conversions](https://doc.rust-lang.org/nomicon/conversions.html) | C02 类型转换 |
| 未初始化内存 | Uninitialized Memory | [nomicon/uninitialized](https://doc.rust-lang.org/nomicon/uninitialized.html) | 本文档、EDGE_CASES |
| 所有权与 Vec | Implementing Vec | [nomicon/vec](https://doc.rust-lang.org/nomicon/vec.html) | C01 |
| 析构与异常安全 | Drop / Exception Safety | [nomicon/exception-safety](https://doc.rust-lang.org/nomicon/exception-safety.html) | C01、本文档 |
| 并发与数据竞争 | Concurrency / Races | [nomicon/races](https://doc.rust-lang.org/nomicon/races.html) | C05 线程与并发 |
| FFI | FFI | [nomicon/ffi](https://doc.rust-lang.org/nomicon/ffi.html) | 系统编程、C07 |

---

## 安全抽象原则

> **对应 Nomicon**: [Working with Unsafe](https://doc.rust-lang.org/nomicon/working-with-unsafe.html)（实践 unsafe 的封装与抽象）

1. **封装 unsafe**: 将 `unsafe` 块封装在安全 API 内部
2. **不变式文档化**: 明确写出 `unsafe` 依赖的前提条件
3. **最小化范围**: 仅对必需的操作使用 `unsafe`

---

## 本项目 unsafe 相关资源

> **对应 Nomicon**: [Meet Safe and Unsafe](https://doc.rust-lang.org/nomicon/meet-safe-and-unsafe.html) · [What Unsafe Rust Can Do](https://doc.rust-lang.org/nomicon/what-unsafe-does.html)

- **理论体系与安全论证**（顶层）: [research_notes/THEORETICAL_AND_ARGUMENTATION_SYSTEM_ARCHITECTURE.md](../research_notes/THEORETICAL_AND_ARGUMENTATION_SYSTEM_ARCHITECTURE.md) - 安全与非安全边界、理论四层
- **安全与非安全全面论证**: [research_notes/SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS.md](../research_notes/SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS.md) - 契约、UB、安全抽象
- **C01**: [高级所有权模式](../../crates/c01_ownership_borrow_scope/docs/tier_03_references/06_高级所有权模式参考.md)
- **C05**: 同步原语、原子操作
- **forms**: [research_notes/formal_methods/](../research_notes/formal_methods/) - 借用检查器证明、生命周期形式化

---

## 推荐学习顺序

> **对应 Nomicon 阅读顺序**: [Meet Safe and Unsafe](https://doc.rust-lang.org/nomicon/meet-safe-and-unsafe.html) → [How Safe and Unsafe Interact](https://doc.rust-lang.org/nomicon/safe-unsafe-meaning.html) → [What Unsafe Rust Can Do](https://doc.rust-lang.org/nomicon/what-unsafe-does.html) → [Working with Unsafe](https://doc.rust-lang.org/nomicon/working-with-unsafe.html)

1. **通读 Nomicon 前 4 节**（Meet Safe、Interact、What Unsafe Does、Working with Unsafe）
2. 学习 C01 的零成本抽象与高级所有权
3. 研究本项目 `formal_methods` 中的形式化证明
4. 实践：为现有安全 API 编写 `unsafe` 实现（如自定义集合）
