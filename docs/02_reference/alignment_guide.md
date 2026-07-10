# Rust 对齐知识综合指南 (Alignment Guide) {#rust-对齐知识综合指南}

> **EN**: Alignment Guide
> **Summary**: Rust 对齐知识综合指南 Alignment Guide. (stub/archive redirect)
> **分级**: [A]
> **Bloom 层级**: L2 (理解)
> **创建日期**: 2026-02-13
> > **权威来源**:
>
> [Rust Reference — Type Layout](https://doc.rust-lang.org/reference/type-layout.html),
> [Rustonomicon — Data Layout](https://doc.rust-lang.org/nomicon/data.html),
> [The Rust Programming Language — Ch04](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference 类型布局来源标注、Rustonomicon 数据布局引用 [Authority Source Sprint Batch 8](../../concept/00_meta/02_sources/international_authority_index.md)
>
> **受众**: [初学者] / [进阶]
> **内容分级**: [综述级]

**文档版本**: 1.1
**对应 Rust 版本**: 1.97.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **文档定位**: 全面覆盖 Rust 中「对齐」相关的各类知识
> **关联**:
>
> [02_type_system.md](quick_reference/02_type_system.md) |
> [02_strings_formatting_cheatsheet.md](quick_reference/02_strings_formatting_cheatsheet.md)

---

---

## 二、内存对齐（核心） {#二内存对齐核心}
> **权威来源**: [Rust 类型系统与内存布局](../../concept/01_foundation/02_type_system/04_type_system.md)
> 通用概念解释已在 `concept/` 权威页中覆盖，本节不再重复，请直接参考权威页。
## 三、格式化对齐 {#三格式化对齐}
> **权威来源**: [Rust 格式化与 Display](../../concept/01_foundation/06_strings_and_text/46_formatting_and_display.md)
> 通用概念解释已在 `concept/` 权威页中覆盖，本节不再重复，请直接参考权威页。
## 四、unsafe 与对齐 {#四unsafe-与对齐}
> **权威来源**: [Rust Unsafe 与原始指针](../../concept/03_advanced/02_unsafe/03_unsafe.md)
> 通用概念解释已在 `concept/` 权威页中覆盖，本节不再重复，请直接参考权威页。
## 五、缓存行对齐与并发 {#五缓存行对齐与并发}
> **权威来源**: [Rust 并发与性能](../../concept/03_advanced/00_concurrency/01_concurrency.md)
> 通用概念解释已在 `concept/` 权威页中覆盖，本节不再重复，请直接参考权威页。
## 六、权威来源（非技术对齐） {#六权威来源非技术对齐}
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**
> **说明**：此处「对齐」指项目文档与官方发布的一致性（Coherence），与内存对齐无技术关联。技术读者可跳过。

版本追踪与权威来源： [版本对齐检查清单](../00_meta/00_rust_version_alignment_checklist.md)、[INCREMENTAL_UPDATE_FLOW](../../archive/research_notes_2026_06_25/10_incremental_update_flow.md)。

---

## 七、对齐选型决策树 {#七对齐选型决策树}
>
> **[来源: [crates.io](https://crates.io/)]**

```text
需要控制内存布局？
├─ 否 → 使用默认 #[repr(Rust)]
└─ 是
   ├─ 与 C/FFI 交互？ → #[repr(C)]
   ├─ 需要紧凑无填充（如协议解析）？ → #[repr(packed)] 或 #[repr(packed(N))]
   ├─ 需要 newtype 与内层同布局？ → #[repr(transparent)]
   ├─ 多线程共享、避免伪共享？ → #[repr(align(64))] + 填充
   └─ 组合需求？ → #[repr(C, align(N))]
```

| 场景 | 推荐 |
| :--- | :--- | :--- | :--- | :--- |
| C 互操作、FFI | `#[repr(C)]` |
| 网络/二进制协议 | `#[repr(C)]` 或 `packed`，注意未对齐用 `read_unaligned` |
| 多线程原子计数器 | `#[repr(align(64))]` 每计数器独占缓存行 |
| 零成本 newtype | `#[repr(transparent)]` |

---

## 八、相关文档与示例 {#八相关文档与示例}
>
> **[来源: [docs.rs](https://docs.rs/)]**

### 项目内文档 {#项目内文档}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

| 主题 | 路径 |
| :--- | :--- | :--- | :--- | :--- |
| 性能优化参考 | [c01/tier_03/09_性能优化参考](../../crates/c01_ownership_borrow_scope/docs/tier_03_references/09_performance_optimization_reference.md) |
| 内存安全（Memory Safety）参考 | [c01/tier_03/08_内存安全参考](../../crates/c01_ownership_borrow_scope/docs/tier_03_references/08_memory_safety_reference.md) |
| 缓存行对齐 | [c05/02_系统编程优化](../../crates/c05_threads/docs/tier_04_advanced/02_systems_programming_optimization.md#51-缓存行对齐) |
| 无锁编程 | [c05/04_lock_free_programming](../../crates/c05_threads/docs/04_lock_free_programming.md) |
| 格式化对齐 | [strings_formatting_cheatsheet](quick_reference/02_strings_formatting_cheatsheet.md) |

### 代码示例 {#代码示例}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

| 模块（Module） | 示例 |
| :--- | :--- | :--- | :--- | :--- |
| c02 | `memory_safety_advanced`、`rust_192_features_demo` 对齐计算 |
| c04 | `rust_192_features_demo` 泛型（Generics）对齐大小 |
| c05 | 并行算法中的缓存行对齐；`benches/false_sharing_bench` 伪共享基准 |
| c08 | `rust_192_features` align_size |

### 研究笔记 {#研究笔记}
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

- [ownership_model](../research_notes/formal_methods/10_ownership_model.md) - transmute 形式化约束
- [THEORETICAL_AND_ARGUMENTATION_SYSTEM_ARCHITECTURE](../../archive/research_notes_2026_06_25/10_theoretical_and_argumentation_system_architecture.md) - 指针有效性
- [memory_analysis](../../archive/research_notes_2026_06_25/experiments/10_memory_analysis.md) - align_of 实验

---

**维护**: 对齐知识随 Rust 版本更新。新版本发布时检查 [Rust Reference - Type layout](https://doc.rust-lang.org/reference/type-layout.html)。发现错误或遗漏请提 issue。

**批判性评估与推进计划**: [完成状态报告](../07_project/07_completion_status.md)

---

## Rust 1.95+ 更新 {#rust-195-更新}
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**
> **适用版本**: Rust 1.97.0+

详见 Rust 1.94 发布说明

**最后更新**: 2026-05-08

---

## 相关概念 {#相关概念}
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

- [02_reference 目录](README.md)
- [上级目录](../README.md)

---

## 权威来源索引 {#权威来源索引}

> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**
> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
> **来源: [ACM](https://dl.acm.org/)**
> **来源: [IEEE](https://standards.ieee.org/)**
> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**
> **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)**

---
