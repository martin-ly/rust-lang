# 概念一致性审计报告 (Concept Consistency Audit)

> 生成时间: 2026-07-12T04:55:11.208905
> 生成脚本: `scripts/concept_consistency_auditor.py`(质量门 17,语义观察门)
> 扫描文件数: 467
> 提取概念定义数: 1623
> 跨文件引用数: 219

## 目录

1. [执行摘要](#一执行摘要)
2. [权威页基线](#二权威页基线)
3. [概念一致性检查](#三概念一致性检查)
4. [跨文件段落引用有效性检查](#四跨文件段落引用有效性检查)
5. [附录:概念定义统计](#五附录概念定义统计)

---

## 一、执行摘要

| 检查项 | 状态 | 详情 |
|:---|:---|:---|
| 权威页存在性 | ✅ 通过 | 检测到 0 项 |
| Send/Sync 属性矛盾 | ✅ 通过 | 检测到 0 项 |
| 变型矛盾 | ✅ 通过 | 检测到 0 项 |
| 极性矛盾 | ✅ 通过 | 检测到 0 项 |
| 术语覆盖 | ✅ 通过 | 检测到 0 项 |
| 跨文件段落引用有效性 | ✅ 全部有效 | 共 219 个引用 |
| **总计** | **0 错误 / 0 警告 / 0 提示** | — |

## 二、权威页基线

| 概念 | 权威页 | 状态 |
|:---|:---|:---|
| Send/Sync | `03_advanced/00_concurrency/17_send_sync_auto_traits.md` | ✅ `concept/03_advanced/00_concurrency/17_send_sync_auto_traits.md` |
| 所有权 | `01_foundation/01_ownership_borrow_lifetime/01_ownership.md` | ✅ `concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md` |
| 借用 | `01_foundation/01_ownership_borrow_lifetime/02_borrowing.md` | ✅ `concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md` |
| 生命周期 | `01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md` | ✅ `concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md` |
| 内部可变性 | `02_intermediate/02_memory_management/08_interior_mutability.md` | ✅ `concept/02_intermediate/02_memory_management/08_interior_mutability.md` |
| Pin/Unpin | `03_advanced/01_async/06_pin_unpin.md` | ✅ `concept/03_advanced/01_async/06_pin_unpin.md` |
| 变型 | `04_formal/00_type_theory/06_subtype_variance.md` | ✅ `concept/04_formal/00_type_theory/06_subtype_variance.md` |
| unsafe | `03_advanced/02_unsafe/03_unsafe.md` | ✅ `concept/03_advanced/02_unsafe/03_unsafe.md` |

## 三、概念一致性检查

> ✅ 未检测到一致性问题。

## 四、跨文件段落引用有效性检查

> ✅ 所有跨文件段落引用均有效。

## 五、附录:概念定义统计

### 5.1 按概念分类统计

| 概念 | 提取次数 | 涉及文件数 |
|:---|:---|:---|
| unsafe-UB | 366 | 104 |
| 所有权-Move语义 | 188 | 82 |
| Pin-自引用 | 175 | 52 |
| Send+Sync | 99 | 53 |
| 内部可变性-运行时检查 | 88 | 26 |
| 变型-定义 | 84 | 18 |
| 借用-可变独占 | 81 | 28 |
| 所有权-作用域绑定 | 70 | 41 |
| 变型-规则 | 59 | 13 |
| 所有权-唯一所有权 | 57 | 30 |
| unsafe-契约 | 56 | 30 |
| 内部可变性-定义 | 47 | 25 |
| unsafe-不变式 | 31 | 4 |
| Sync | 28 | 13 |
| 借用-引用有效 | 28 | 18 |
| unsafe-语义 | 23 | 15 |
| Unpin-定义 | 23 | 8 |
| 生命周期-定义 | 20 | 10 |
| Pin-定义 | 18 | 13 |
| Send | 18 | 9 |
| 借用-读写互斥 | 15 | 7 |
| 所有权-Copy例外 | 11 | 7 |
| 生命周期-Rule2 | 11 | 4 |
| 借用-共享引用 | 9 | 7 |
| 生命周期-Rule3 | 9 | 3 |
| 生命周期-Rule1 | 7 | 2 |
| 内部可变性-UnsafeCell | 2 | 2 |

---

> 本报告由 `scripts/concept_consistency_auditor.py` 自动生成。
