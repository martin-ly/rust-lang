# 概念一致性审计报告 (Concept Consistency Audit)

> 生成时间: 2026-07-14T15:56:19.851087
> 生成脚本: `scripts/concept_consistency_auditor.py`(质量门 17,语义观察门)
> 扫描文件数: 497
> 提取概念定义数: 1979
> 跨文件引用数: 290

## 目录

- [概念一致性审计报告 (Concept Consistency Audit)](#概念一致性审计报告-concept-consistency-audit)
  - [目录](#目录)
  - [一、执行摘要](#一执行摘要)
  - [二、权威页基线](#二权威页基线)
  - [三、概念一致性检查](#三概念一致性检查)
  - [四、跨文件段落引用有效性检查](#四跨文件段落引用有效性检查)
  - [五、附录:概念定义统计](#五附录概念定义统计)
    - [5.1 按概念分类统计](#51-按概念分类统计)

---

## 一、执行摘要

| 检查项 | 状态 | 详情 |
|:---|:---|:---|
| 权威页存在性 | ✅ 通过 | 检测到 0 项 |
| Send/Sync 属性矛盾 | ✅ 通过 | 检测到 0 项 |
| 变型矛盾 | ✅ 通过 | 检测到 0 项 |
| 极性矛盾 | ✅ 通过 | 检测到 0 项 |
| 术语覆盖 | ✅ 通过 | 检测到 0 项 |
| 跨文件段落引用有效性 | ✅ 全部有效 | 共 290 个引用 |
| **总计** | **0 错误 / 0 警告 / 0 提示** | — |

## 二、权威页基线

| 概念 | 权威页 | 状态 |
|:---|:---|:---|
| Send/Sync | `03_advanced/00_concurrency/02_send_sync_auto_traits.md` | ✅ `concept/03_advanced/00_concurrency/02_send_sync_auto_traits.md` |
| 所有权 | `01_foundation/01_ownership_borrow_lifetime/01_ownership.md` | ✅ `concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md` |
| 借用 | `01_foundation/01_ownership_borrow_lifetime/02_borrowing.md` | ✅ `concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md` |
| 生命周期 | `01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md` | ✅ `concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md` |
| 内部可变性 | `02_intermediate/02_memory_management/02_interior_mutability.md` | ✅ `concept/02_intermediate/02_memory_management/02_interior_mutability.md` |
| Pin/Unpin | `03_advanced/01_async/08_pin_unpin.md` | ✅ `concept/03_advanced/01_async/08_pin_unpin.md` |
| 变型 | `04_formal/00_type_theory/02_subtype_variance.md` | ✅ `concept/04_formal/00_type_theory/02_subtype_variance.md` |
| unsafe | `03_advanced/02_unsafe/01_unsafe.md` | ✅ `concept/03_advanced/02_unsafe/01_unsafe.md` |

## 三、概念一致性检查

> ✅ 未检测到一致性问题。

## 四、跨文件段落引用有效性检查

> ✅ 所有跨文件段落引用均有效。

## 五、附录:概念定义统计

### 5.1 按概念分类统计

| 概念 | 提取次数 | 涉及文件数 |
|:---|:---|:---|
| unsafe-UB | 441 | 119 |
| 所有权-Move语义 | 259 | 94 |
| Pin-自引用 | 218 | 62 |
| Send+Sync | 121 | 61 |
| 变型-定义 | 102 | 22 |
| 内部可变性-运行时检查 | 101 | 32 |
| 借用-可变独占 | 101 | 38 |
| 所有权-作用域绑定 | 95 | 53 |
| 变型-规则 | 71 | 14 |
| 所有权-唯一所有权 | 65 | 32 |
| unsafe-契约 | 59 | 31 |
| 内部可变性-定义 | 51 | 25 |
| Sync | 42 | 20 |
| unsafe-不变式 | 37 | 6 |
| Unpin-定义 | 35 | 12 |
| 借用-引用有效 | 32 | 18 |
| unsafe-语义 | 23 | 15 |
| Pin-定义 | 21 | 15 |
| 生命周期-定义 | 20 | 10 |
| Send | 19 | 9 |
| 借用-读写互斥 | 16 | 7 |
| 所有权-Copy例外 | 11 | 7 |
| 生命周期-Rule2 | 11 | 4 |
| 借用-共享引用 | 9 | 7 |
| 生命周期-Rule3 | 9 | 3 |
| 生命周期-Rule1 | 7 | 2 |
| 内部可变性-UnsafeCell | 3 | 3 |

---

> 本报告由 `scripts/concept_consistency_auditor.py` 自动生成。
