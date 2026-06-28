# Safety Tags 预研指南

> **深度**: [专家级]
> **主轨引用**: 概念级深度分析请参阅 [concept/07_future/08_safety_tags_preview.md](../../concept/07_future/08_safety_tags_preview.md)
>
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **分级**: [A]
> **层级**: L7 前沿 / L3 高级 Unsafe
> **前置概念**: [Unsafe Rust](../../concept/03_advanced/03_unsafe.md) · [Safety-Critical](../04_research/04_safety_critical_alignment_2026.md)
> **Bloom 层级**: 评价 → 创造
> **来源: [Rust Project Goals 2026](https://rust-lang.github.io/rust-project-goals/2026/)** · **[来源: Rust-for-Linux Mailing List]** ✅
> **受众**: [专家] / [研究者]
> **内容分级**: [研究者级]

---

## 📑 目录
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [Safety Tags 预研指南](.#safety-tags-预研指南)
  - [📑 目录](.#-目录)
  - [概述](.#概述)
  - [为什么需要 Safety Tags](.#为什么需要-safety-tags)
  - [提议设计（草案阶段）](.#提议设计草案阶段)
    - [Tag 语法设想](.#tag-语法设想)
    - [标准 Tag 库设想](.#标准-tag-库设想)
  - [与现有工具的协同](.#与现有工具的协同)
  - [当前状态](.#当前状态)
  - [行动建议](.#行动建议)
  - [相关概念](.#相关概念)
  - [权威来源索引](.#权威来源索引)

## 概述

> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)** · **来源: [Rust Project Goals 2026](https://rust-lang.github.io/rust-project-goals/2026/)** ✅

**Safety Tags** 是 Rust 社区正在讨论的一套**形式化安全契约标注系统**，目标是为 `unsafe` 代码提供机器可验证的安全前提条件。

```text
当前 unsafe 文档:
  // SAFETY: caller must ensure ptr is valid and aligned
  unsafe fn deref_unchecked<T>(ptr: *const T) -> &T { ... }

Safety Tags 愿景:
  #[safety_tag(valid_ptr, aligned)]
  unsafe fn deref_unchecked<T>(ptr: *const T) -> &T { ... }
  // ↑ 机器可验证的契约，可被 Miri/Clippy/Safety-Critical 工具链检查
```

---

## 为什么需要 Safety Tags

> **[来源: Rust Internals Forum]** · **[来源: Rust-for-Linux Mailing List]** ✅？

| 当前问题 | Safety Tags 解决方案 |
|:---|:---|
| Safety Comment 是自由文本 | 结构化、机器可解析的契约 |
| 无法静态验证 | 与 Miri/Clippy 集成，自动检查 |
| 跨函数边界不传递 | 调用者必须显式满足 tag 条件 |
| 文档与代码不同步 | Tag 即文档，修改即检查 |
| Safety-Critical 审计困难 | 自动生成安全证据报告 |

---

## 提议设计（草案阶段）
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### Tag 语法设想
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```rust,ignore
// 基础 tag：前置条件
#[safety_tag(pre: valid_ptr(self), aligned(self))]
unsafe fn as_ref_unchecked(&self) -> &T { ... }

// 效果 tag：后置条件
#[safety_tag(post: initialized(result))]
unsafe fn read_unaligned<T>(src: *const T) -> T { ... }

// 不变量 tag：结构体级别
#[safety_tag(invariant: self.ptr.is_null() || self.len <= isize::MAX)]
struct RawSlice<T> {
    ptr: *const T,
    len: usize,
}
```

### 标准 Tag 库设想
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

| Tag | 语义 | 适用场景 |
|:---|:---|:---|
| `valid_ptr(p)` | `p` 是非空且已分配的指针 | 所有解引用操作 |
| `aligned(p)` | `p` 满足 `T` 的对齐要求 | 非包装解引用 |
| `non_overlapping(a, b)` | `a` 和 `b` 的内存范围不重叠 | `copy_nonoverlapping` |
| `initialized(p)` | `p` 指向已初始化的内存 | `read` / 转型 |
| `no_alias(p)` | `p` 在生命周期内是唯一的访问路径 | `&mut` 构造 |
| `valid_utf8(s)` | `s` 是合法的 UTF-8 字节序列 | `str::from_utf8_unchecked` |

---

## 与现有工具的协同
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

```text
Safety Tags 生态:
┌─────────────────────────────────────────┐
│  开发者: 编写带 #[safety_tag] 的代码      │
└─────────────────────────────────────────┘
           │
    ┌──────┴──────┬──────────────┐
    ▼             ▼              ▼
┌─────────┐  ┌─────────┐   ┌───────────┐
│ Miri    │  │ Clippy  │   │ Safety    │
│ 运行时  │  │ 静态检查 │   │ Auditor   │
│ 验证    │  │ lint    │   │ (报告生成) │
└─────────┘  └─────────┘   └───────────┘
```

---

## 当前状态

> **[来源: 各工具官方文档 2026-05]** ✅（2026-05）

| 方面 | 状态 |
|:---|:---:|
| RFC 草案 | 🔴 尚未提交 |
| 社区讨论 | 🟡 Rust Internals / Zulip 活跃讨论 |
| 原型实现 | 🔴 无 |
| Rust-for-Linux 兴趣 | 🟢 已表达强烈兴趣 |
| 预计 RFC 时间 | 2026 H2 |

---

## 行动建议
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

1. **跟踪** [Rust Internals 论坛](https://internals.rust-lang.org/) 的 Safety Tags 讨论
2. **准备** 在项目中统一 Safety Comment 格式，为迁移做准备
3. **实验** 使用现有 `#[doc = "SAFETY: ..."]` 规范化为结构化注释

---

> **权威来源**: [Rust Project Goals 2026](https://rust-lang.github.io/rust-project-goals/2026/flagships.html), [Rust-for-Linux Mailing List](https://lore.kernel.org/rust-for-linux/)
>
> **文档版本**: 1.0
> **对应 Rust 版本**: 1.96.0+ (Edition 2024)
> **最后更新**: 2026-05-21
> **状态**: 🟡 预研跟踪

---

## 相关概念
>
> **[来源: [crates.io](https://crates.io/)]**

- [05_guides 目录](README.md)
- [docs 索引](../README.md)

---

## 权威来源索引

> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**
> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
> **来源: [ACM](https://dl.acm.org/)**
> **来源: [IEEE](https://standards.ieee.org/)**
> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**
> **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)**

---
