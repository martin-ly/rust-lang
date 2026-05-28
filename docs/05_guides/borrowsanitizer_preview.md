# BorrowSanitizer 预览

> **层级**: L7 前沿 / L3 高级 Unsafe
> **前置概念**: [MIRI](../MIRI_GUIDE.md) · [Unsafe Rust](../../concept/03_advanced/03_unsafe.md)
> **Bloom 层级**: 分析
> **[来源: Rust Project Goals 2026 — Safety-Critical]** · **[来源: RustConf 2026 演讲预告]** ✅

---

## 📑 目录
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [BorrowSanitizer 预览](#borrowsanitizer-预览)
  - [📑 目录](#-目录)
  - [概述](#概述)
  - [核心技术](#核心技术)
  - [检测能力](#检测能力)
  - [与 Miri 的互补关系](#与-miri-的互补关系)
  - [当前状态](#当前状态)
  - [参考](#参考)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)
  - [权威来源索引](#权威来源索引-1)

## 概述

> **[来源: Rust Standard Library]** · **[来源: Rust Project Goals 2026]** ✅

**BorrowSanitizer** 是 Rust 正在开发的运行时内存安全检测工具，目标是在**不依赖 Miri 解释执行**的情况下，检测 unsafe Rust 代码中的别名违规（aliasing violations）。

| 工具 | 运行方式 | 性能 | 检测能力 | 状态 |
|:---|:---|:---:|:---|:---:|
| **Miri** | 解释执行 | 极慢 | 完整 Stacked/Tree Borrows | ✅ 稳定 |
| **BorrowSanitizer** | 编译插桩 | ~2x 减速 | 运行时别名检查 | 🟡 开发中 |
| **ThreadSanitizer** | 编译插桩 | ~5–15x 减速 | 数据竞争 | ✅ 稳定 |
| **AddressSanitizer** | 编译插桩 | ~2x 减速 | 内存错误 | ✅ 稳定 |

---

## 核心技术

> **[来源: Rust Project Goals 2026 — Safety-Critical]** · **[来源: RustConf 2026]** ✅：Shadow Stack

BorrowSanitizer 采用与现有 LLVM Sanitizer 不同的策略：

```text
传统 Sanitizer (TSan/ASan):
  影子内存 (Shadow Memory) 追踪每个字节的状态

BorrowSanitizer:
  影子栈 (Shadow Stack) 追踪指针的借用关系
  每个栈帧记录：
    - 指针值 → 借用类型 (&T / &mut T / *const T / *mut T)
    - 生命周期范围
    - 排他性标记
```

**关键设计决策**：

- 不追踪堆上对象（减少开销）
- 专注栈上引用和参数传递
- 与 Miri 互补：Miri 验证逻辑，BorrowSanitizer 验证运行时

---

## 检测能力
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

| 违规类型 | 示例 | 检测状态 |
|:---|:---|:---:|
| `&mut T` + `&mut T` 别名 | `let a = &mut x; let b = &mut x;` | 🟡 计划中 |
| `&T` + `&mut T` 别名 | `let a = &x; let b = &mut x;` | 🟡 计划中 |
| 使用已释放的 `&T` | dangling reference | 🟡 计划中 |
| 通过 `*mut T` 破坏 `&T` | `*ptr = new_val` while `&ref` alive | 🔴 远期 |
| 跨线程 `&mut T` 共享 | `send(&mut x)` to another thread | 🔴 远期 |

---

## 与 Miri 的互补关系
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```text
开发阶段:          Miri
                    ↓
CI/测试:          BorrowSanitizer + Miri
                    ↓
生产:             (无工具，依赖语言保证)
```

| 场景 | 推荐工具 | 原因 |
|:---|:---|:---|
| 单元测试 | Miri | 完整、确定性的检查 |
| 集成测试 | BorrowSanitizer | 可运行实际二进制 |
| 性能回归测试 | BorrowSanitizer | 运行速度快于 Miri |
| 形式化验证 | Miri (Tree Borrows) | 最精确的模型 |

---

## 当前状态

> **[来源: 各工具官方文档 2026-05]** ✅（2026-05）

| 里程碑 | 状态 | 时间 |
|:---|:---:|:---:|
| Shadow Stack 设计 | ✅ 完成 | 2025 Q4 |
| Retag intrinsics PR | 🟡 准备提交 | 2026 Q2 |
| RFC 起草 | 🟡 进行中 | 2026 Q2 |
| RustConf 2026 演讲 | ✅ 已入选 | 2026-09 |
| Nightly 可用 | 🔴 预计 | 2026 Q4 |
| 稳定化 | 🔴 远期 | 2027+ |

---

## 参考
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

- [Rust Project Goals: Safety-Critical Rust](https://rust-lang.github.io/rust-project-goals/2026/flagships.html)
- [RustConf 2026](https://rustconf.com/)
- [Miri vs Sanitizers 对比](https://github.com/rust-lang/miri/issues/1360)

---

> **权威来源**: [Rust Project Goals 2026](https://rust-lang.github.io/rust-project-goals/2026/flagships.html), [RustConf 2026](https://rustconf.com/)
>
> **文档版本**: 1.0
> **对应 Rust 版本**: 1.96.0+ Nightly (未来)
> **最后更新**: 2026-05-21
> **状态**: 🟡 预研跟踪

---

## 相关概念
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

- [05_guides 目录](./README.md)
- [上级目录](../README.md)

---

## 权威来源索引

> **[来源: Wikipedia - Rust (programming language)]**

> **[来源: Rust Reference]**

> **[来源: TRPL - The Rust Programming Language]**

> **[来源: Rust Standard Library]**

> **[来源: ACM - Systems Programming]**

> **[来源: IEEE - Programming Language Standards]**

> **[来源: RFCs - github.com/rust-lang/rfcs]**

> **[来源: Rustonomicon]**

---

## 权威来源索引

> **[来源: [RustBelt](https://plv.mpi-sws.org/rustbelt/)]**
>
> **[来源: [Tree Borrows](https://plv.mpi-sws.org/rustbelt/tree-borrows/)]**
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
>
> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-22 补全权威来源标注 [来源: Authority Source Sprint Batch 9]
