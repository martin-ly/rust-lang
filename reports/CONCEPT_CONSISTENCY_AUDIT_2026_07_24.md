# 概念一致性审计报告 (Concept Consistency Audit)

> 生成时间: 2026-07-24T04:35:44.552368
> 生成脚本: `scripts/concept_consistency_auditor.py`(扩展后监控 22 个核心概念)
> 扫描文件数: 529
> 提取概念定义数: 4678
> 跨文件引用数: 297

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
| 跨文件段落引用有效性 | ✅ 全部有效 | 共 297 个引用 |
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
| async fn/Future | `03_advanced/01_async/01_async.md` | ✅ `concept/03_advanced/01_async/01_async.md` |
| unsafe superpowers | `03_advanced/02_unsafe/01_unsafe.md` | ✅ `concept/03_advanced/02_unsafe/01_unsafe.md` |
| Pin 投影 | `03_advanced/01_async/08_pin_unpin.md` | ✅ `concept/03_advanced/01_async/08_pin_unpin.md` |
| 生命周期子类型 | `01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md` | ✅ `concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md` |
| Send/Sync 边界 | `03_advanced/00_concurrency/04_send_sync_boundaries.md` | ✅ `concept/03_advanced/00_concurrency/04_send_sync_boundaries.md` |
| let chains | `01_foundation/04_control_flow/03_let_chains.md` | ✅ `concept/01_foundation/04_control_flow/03_let_chains.md` |
| unsafe extern blocks | `03_advanced/04_ffi/05_unsafe_extern_blocks.md` | ✅ `concept/03_advanced/04_ffi/05_unsafe_extern_blocks.md` |
| const trait impl | `07_future/02_preview_features/06_const_trait_impl_preview.md` | ✅ `concept/07_future/02_preview_features/06_const_trait_impl_preview.md` |
| effects system | `07_future/02_preview_features/01_effects_system.md` | ✅ `concept/07_future/02_preview_features/01_effects_system.md` |
| RPITIT/RTN/TAIT | `07_future/02_preview_features/15_rpitit_preview.md` | ✅ `concept/07_future/02_preview_features/15_rpitit_preview.md` |
| GAT + async | `03_advanced/01_async/14_gat_async_boundary.md` | ✅ `concept/03_advanced/01_async/14_gat_async_boundary.md` |
| allocator_api | `03_advanced/06_low_level_patterns/01_custom_allocators.md` | ✅ `concept/03_advanced/06_low_level_patterns/01_custom_allocators.md` |
| match ergonomics | `01_foundation/04_control_flow/02_patterns.md` | ✅ `concept/01_foundation/04_control_flow/02_patterns.md` |
| 临时作用域/tail drop | `04_formal/05_rustc_internals/09_destructors.md` | ✅ `concept/04_formal/05_rustc_internals/09_destructors.md` |

## 三、概念一致性检查

> ✅ 未检测到一致性问题。

## 四、跨文件段落引用有效性检查

> ✅ 所有跨文件段落引用均有效。

## 五、附录:概念定义统计

### 5.1 按概念分类统计

| 概念 | 提取次数 | 涉及文件数 |
|:---|:---|:---|
| RPITIT-RTN-TAIT-定义 | 470 | 47 |
| unsafe-UB | 455 | 126 |
| effects-system-定义 | 359 | 39 |
| 所有权-Move语义 | 258 | 94 |
| Pin-自引用 | 239 | 69 |
| const-trait-impl-定义 | 179 | 34 |
| effects-system-现有 | 167 | 22 |
| allocator-api-GlobalAlloc | 166 | 38 |
| Pin-投影-结构 | 165 | 33 |
| Send+Sync | 132 | 66 |
| 所有权-作用域绑定 | 105 | 61 |
| 借用-可变独占 | 103 | 40 |
| 变型-定义 | 102 | 22 |
| 内部可变性-运行时检查 | 101 | 32 |
| async-Future-状态机 | 97 | 39 |
| let-chains-守卫 | 93 | 35 |
| 生命周期-子类型-outlives | 92 | 27 |
| const-trait-impl-效果 | 86 | 19 |
| RPITIT-RTN-TAIT-捕获 | 80 | 24 |
| GAT-async-生命周期 | 79 | 17 |
| unsafe-extern-块 | 79 | 14 |
| unsafe-extern-safe | 78 | 16 |
| GAT-async-边界 | 73 | 19 |
| 变型-规则 | 71 | 14 |
| 所有权-唯一所有权 | 70 | 36 |
| let-chains-链式 | 69 | 8 |
| unsafe-契约 | 61 | 32 |
| unsafe-superpowers-unsafe_op | 52 | 12 |
| 内部可变性-定义 | 50 | 24 |
| match-ergonomics-默认绑定 | 50 | 30 |
| Sync | 49 | 24 |
| async-Future-等价 | 38 | 22 |
| unsafe-不变式 | 37 | 6 |
| Unpin-定义 | 36 | 12 |
| 生命周期-子类型-static | 35 | 13 |
| 借用-引用有效 | 35 | 21 |
| Send/Sync边界-trait对象 | 35 | 10 |
| temporary-scope-临时作用域 | 31 | 11 |
| unsafe-语义 | 24 | 16 |
| 生命周期-定义 | 22 | 12 |
| Send | 22 | 12 |
| Pin-定义 | 21 | 15 |
| Send/Sync边界-充分必要 | 19 | 5 |
| 借用-读写互斥 | 16 | 7 |
| 借用-共享引用 | 11 | 9 |
| 所有权-Copy例外 | 11 | 7 |
| 生命周期-Rule2 | 11 | 4 |
| allocator-api-Allocator | 10 | 4 |
| 生命周期-Rule3 | 9 | 3 |
| Pin-投影-安全 | 9 | 6 |
| 生命周期-Rule1 | 7 | 2 |
| unsafe-superpowers-五种能力 | 4 | 3 |
| 内部可变性-UnsafeCell | 2 | 2 |
| match-ergonomics-引用 | 2 | 2 |
| temporary-scope-tail | 1 | 1 |

---

> 本报告由 `scripts/concept_consistency_auditor.py` 自动生成。
