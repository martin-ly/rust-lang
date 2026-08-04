# 概念一致性审计报告 (Concept Consistency Audit)

> 生成时间: 2026-08-04T23:04:02.385570
> 生成脚本: `scripts/concept_consistency_auditor.py`(扩展后监控 22 个核心概念)
> 扫描文件数: 791
> 提取概念定义数: 5331
> 跨文件引用数: 340

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
| 跨文件段落引用有效性 | ✅ 全部有效 | 共 340 个引用 |
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
| unsafe-UB | 561 | 161 |
| RPITIT-RTN-TAIT-定义 | 491 | 55 |
| effects-system-定义 | 382 | 45 |
| Pin-自引用 | 286 | 79 |
| 所有权-Move语义 | 277 | 98 |
| allocator-api-GlobalAlloc | 243 | 53 |
| Pin-投影-结构 | 188 | 41 |
| const-trait-impl-定义 | 180 | 35 |
| effects-system-现有 | 173 | 23 |
| Send+Sync | 147 | 73 |
| 所有权-作用域绑定 | 137 | 69 |
| 借用-可变独占 | 120 | 49 |
| async-Future-状态机 | 117 | 53 |
| 生命周期-子类型-outlives | 113 | 32 |
| unsafe-extern-块 | 110 | 20 |
| 内部可变性-运行时检查 | 109 | 36 |
| 变型-定义 | 108 | 24 |
| let-chains-守卫 | 108 | 38 |
| unsafe-extern-safe | 103 | 22 |
| let-chains-链式 | 93 | 11 |
| const-trait-impl-效果 | 90 | 21 |
| RPITIT-RTN-TAIT-捕获 | 86 | 28 |
| GAT-async-生命周期 | 83 | 20 |
| 变型-规则 | 80 | 21 |
| 所有权-唯一所有权 | 74 | 39 |
| GAT-async-边界 | 74 | 20 |
| unsafe-契约 | 66 | 37 |
| match-ergonomics-默认绑定 | 60 | 34 |
| 内部可变性-定义 | 54 | 28 |
| unsafe-superpowers-unsafe_op | 54 | 14 |
| Sync | 52 | 26 |
| unsafe-不变式 | 45 | 10 |
| Send/Sync边界-trait对象 | 44 | 14 |
| async-Future-等价 | 41 | 25 |
| Unpin-定义 | 41 | 12 |
| 生命周期-子类型-static | 40 | 15 |
| 借用-引用有效 | 40 | 25 |
| temporary-scope-临时作用域 | 38 | 14 |
| unsafe-语义 | 27 | 19 |
| 生命周期-定义 | 26 | 15 |
| Send | 24 | 13 |
| Pin-定义 | 23 | 17 |
| Send/Sync边界-充分必要 | 23 | 7 |
| 借用-读写互斥 | 17 | 8 |
| allocator-api-Allocator | 14 | 7 |
| Pin-投影-安全 | 12 | 9 |
| 所有权-Copy例外 | 11 | 7 |
| 生命周期-Rule2 | 11 | 4 |
| 借用-共享引用 | 10 | 8 |
| 生命周期-Rule3 | 9 | 3 |
| 生命周期-Rule1 | 7 | 2 |
| unsafe-superpowers-五种能力 | 4 | 3 |
| 内部可变性-UnsafeCell | 2 | 2 |
| match-ergonomics-引用 | 2 | 2 |
| temporary-scope-tail | 1 | 1 |

---

> 本报告由 `scripts/concept_consistency_auditor.py` 自动生成。
