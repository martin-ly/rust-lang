# Rust 特性跟踪看板模板 {#rust-特性跟踪看板模板}

> **分级**: [B]
> **Bloom 层级**: L2 (理解)
> **用途**: 每月更新 Rust 稳定版/Nightly 特性矩阵
> **更新频率**: 每月一次（跟随 Rust 稳定版发布节奏）
> **最后更新**: 2026-05-08

---

## 📑 目录 {#目录}

- [Rust 特性跟踪看板模板](#rust-特性跟踪看板模板)
  - [📑 目录](#目录)
  - [当前版本状态](#当前版本状态)
  - [特性跟踪矩阵](#特性跟踪矩阵)
    - [语言特性](#语言特性)
    - [标准库 API](#标准库-api)
    - [工具链与生态](#工具链与生态)
    - [平台与系统编程](#平台与系统编程)
  - [更新检查清单](#更新检查清单)
  - [趋势跟踪](#趋势跟踪)
    - [2026 Q2 关键里程碑](#2026-q2-关键里程碑)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)

## 当前版本状态 {#当前版本状态}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 通道 | 版本 | 发布日期 | 状态 |
|------|------|---------|------|
| Stable | 1.96.0 | 2026-05-28 | ✅ 当前项目 MSRV |
| Beta | 1.97.0 | 2026-07-09 (预计) | 🔄 跟踪中 |
| Nightly | 1.98.0 | 2026-08 (预计) | 🧪 实验跟踪 |

---

## 特性跟踪矩阵 {#特性跟踪矩阵}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### 语言特性 {#语言特性}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 特性 | 版本 | 状态 | 项目覆盖 | 优先级 | 负责人 | 备注 |
|------|------|------|---------|--------|--------|------|
| `if let` guards | 1.95.0 | ✅ 稳定 | ✅ 已覆盖 | - | - | c03_control_fn |
| `cfg_select!` | 1.95.0 | ✅ 稳定 | ✅ 已覆盖 | - | - | 多 crate |
| `core::range` | 1.95.0 | ✅ 稳定 | ✅ 已覆盖 | - | - | c02_type_system |
| Async Closures | 1.85.0 | ✅ 稳定 | ⚠️ 代码有，指南缺 | P1 | - | 需完善指南 |
| `use<..>` precise capturing | 2024 Ed | ✅ 部分稳定 | 🔴 未覆盖 | P1 | - | 需创建指南 |
| AFIDT (dyn async trait) | 1.97+ | 🧪 Nightly 实验中（暂无稳定时间表） | ⚠️ 跟踪中 | P2 | - | c06_async；`dyn Trait` 场景继续用 `async_trait` |
| Gen blocks | 1.98+ | 📋 RFC | 🔴 未覆盖 | P2 | - | 预留关键词 |
| Never type `!` | 1.97+ | 🔄 PFCP | 🔴 未覆盖 | P2 | - | - |
| Pattern types | 1.98+ | 📋 RFC | 🔴 未覆盖 | P3 | - | - |

### 标准库 API {#标准库-api}

| API | 版本 | 状态 | 项目覆盖 | 优先级 | 备注 |
|-----|------|------|---------|--------|------|
| `Atomic*::update` | 1.95.0 | ✅ 稳定 | ✅ 已覆盖 | - | c05_threads |
| `cold_path` | 1.95.0 | ✅ 稳定 | ✅ 已覆盖 | - | c05_threads |
| 裸指针 `as_ref_unchecked` | 1.95.0 | ✅ 稳定 | ✅ 已覆盖 | - | c13_embedded |
| `MaybeUninit` 数组互转 | 1.95.0 | ✅ 稳定 | ✅ 已覆盖 | - | c01_ownership |
| `Vec::push_mut` | 1.95.0 | ✅ 稳定 | ✅ 已覆盖 | - | c08_algorithms |
| `VecDeque::push_*_mut` | 1.95.0 | ✅ 稳定 | ✅ 已覆盖 | - | c08_algorithms |
| `LinkedList::push_*_mut` | 1.95.0 | ✅ 稳定 | ✅ 已覆盖 | - | c08_algorithms |
| `Layout::dangling_ptr` 等 | 1.95.0 | ✅ 稳定 | ✅ 已覆盖 | - | c01_ownership |
| `VecDeque::truncate_front` | 1.97+ | ❌ 未进入 1.96 | 🔴 未覆盖 | P2 | 1.96 未稳定，继续跟踪 |
| `refcell_try_map` | 1.97+ | 🧪 等待作者 | 🔴 未覆盖 | P3 | - |

### 工具链与生态 {#工具链与生态}

| 特性 | 版本 | 状态 | 项目覆盖 | 优先级 | 备注 |
|------|------|------|---------|--------|------|
| Cargo Script / Frontmatter | 1.97+ | ❌ 未进入 1.96 | 🔴 未覆盖 | P1 | 指南已创建，继续跟踪 |
| 并行前端编译 | 1.97+ | 🧪 Nightly | 🔴 未覆盖 | P2 | 指南已创建 |
| `derive(CoercePointee)` | 1.97+ | ❌ 未进入 1.96 | 🔴 未覆盖 | P2 | 继续跟踪 |
| Safety Tags | - | 📋 RFC 讨论 | 🔴 未覆盖 | P2 | 指南已创建 |
| Stack protector | 1.97+ | 🔄 PFCP | 🔴 未覆盖 | P3 | - |
| Miri 改进 | 持续 | ✅ 可用 | ⚠️ 基础覆盖 | P3 | - |

### 平台与系统编程 {#平台与系统编程}

| 特性 | 版本 | 状态 | 项目覆盖 | 优先级 | 备注 |
|------|------|------|---------|--------|------|
| io_uring | Linux 5.1+ | ✅ 成熟 | ⚠️ 占位 | P1 | 已深化 |
| QUIC/HTTP3 | 生态成熟 | ✅ 可用 | ⚠️ 占位 | P1 | 需深化 |
| libp2p | 0.54+ | ✅ 可用 | ⚠️ 占位 | P1 | 需深化 |
| Embassy | MSRV 1.75 | ✅ 稳定 | ⚠️ 占位 | P1 | 已深化 |
| RTIC | 1.0 | ✅ 稳定 | ⚠️ 占位 | P2 | 需深化 |
| Rust for Linux | 内核 6.1+ | 🧪 实验 | 🔴 占位 | P1 | 需深化 |
| eBPF + Rust (Aya) | 生态成熟 | ✅ 可用 | 🔴 占位 | P2 | 需深化 |

---

## 更新检查清单 {#更新检查清单}

每月更新时执行：

- [ ] 检查 [releases.rs](https://releases.rs/) 获取最新版本信息
- [ ] 检查 [Rust Forge](https://forge.rust-lang.org/) 获取发布时间表
- [ ] 检查 [rust-lang/rust](https://github.com/rust-lang/rust) 的 stabilization PRs
- [ ] 运行 `scripts/audit_stable_apis.py` 扫描缺失 API
- [ ] 更新本看板的版本状态和特性矩阵
- [ ] 评估新稳定特性是否需要纳入项目
- [ ] 调整任务优先级和负责人

---

## 趋势跟踪 {#趋势跟踪}

### 2026 Q2 关键里程碑 {#2026-q2-关键里程碑}

| 日期 | 事件 | 影响 |
|------|------|------|
| 2026-05-28 | Rust 1.96.0 已发布 | Cargo Script 未进入 stable |
| 2026-06-xx | Rust Project Goals 2026H1 中期评审 | 可能影响趋势优先级 |
| 2026-07-09 | Rust 1.97.0 预计发布 | Never type 可能进展；AFIDT 仍为实验性，暂无稳定时间表 |

---

*本模板基于 2026-05-08 的对称差分析报告创建。*

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 相关概念 {#相关概念}

- [概念文档模板](00_template_concept_doc.md)
- [决策树模板](00_template_decision_tree.md)
- [docs 总览](../README.md)

---

## 权威来源索引 {#权威来源索引}

> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**
> **来源: [Rust Reference - doc.rust-lang.org/reference](https://doc.rust-lang.org/reference/)**
> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
> **来源: [ACM](https://dl.acm.org/)**
> **来源: [IEEE](https://standards.ieee.org/)**
> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**
> **来源: [Rustonomicon - doc.rust-lang.org/nomicon](https://doc.rust-lang.org/nomicon/)**