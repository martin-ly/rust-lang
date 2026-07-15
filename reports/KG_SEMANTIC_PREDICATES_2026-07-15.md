# KG 核心 50 实体语义谓词实例化报告

**日期**: 2026-07-15
**模式**: 已写回 kg_data_v3.json
**核心实体数**: 50  **核心关系数**: 2389

## 1. 核心 50 实体周边通用谓词残留

- `ex:RelationAnnotation` 残留: 0
- 核心周边通用谓词占比: **0.00%**

## 2. 改动统计

- 修改的关系数: 0

## 3. 核心周边语义谓词分布

| 谓词 | 计数 |
|:---|---:|
| `ex:entails` | 1261 |
| `ex:dependsOn` | 1051 |
| `ex:refines` | 67 |
| `ex:equivalentTo` | 7 |
| `ex:enables` | 2 |
| `ex:mutexWith` | 1 |

## 4. 全局 @type 分布前后对比

| 谓词 | 修改前 | 修改后 | Δ |
|:---|---:|---:|---:|
| `ex:RelationAnnotation` | 5600 | 5600 | +0 |
| `ex:entails` | 1261 | 1261 | +0 |
| `ex:dependsOn` | 1051 | 1051 | +0 |
| `ex:refines` | 67 | 67 | +0 |
| `ex:equivalentTo` | 7 | 7 | +0 |
| `ex:enables` | 2 | 2 | +0 |
| `ex:mutexWith` | 1 | 1 | +0 |

## 5. 核心 50 实体路径列表

| 序号 | 路径 |
|---:|:---|
| 1 | `01_foundation/01_ownership_borrow_lifetime/01_ownership.md` |
| 2 | `01_foundation/01_ownership_borrow_lifetime/02_borrowing.md` |
| 3 | `01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md` |
| 4 | `01_foundation/01_ownership_borrow_lifetime/04_lifetimes_advanced.md` |
| 5 | `01_foundation/01_ownership_borrow_lifetime/05_move_semantics.md` |
| 6 | `01_foundation/02_type_system/01_type_system.md` |
| 7 | `01_foundation/03_values_and_references/01_reference_semantics.md` |
| 8 | `01_foundation/03_values_and_references/03_variable_model.md` |
| 9 | `02_intermediate/00_traits/01_traits.md` |
| 10 | `02_intermediate/00_traits/02_dispatch_mechanisms.md` |
| 11 | `02_intermediate/00_traits/04_advanced_traits.md` |
| 12 | `02_intermediate/00_traits/06_derive_traits.md` |
| 13 | `02_intermediate/00_traits/07_generic_associated_types.md` |
| 14 | `02_intermediate/01_generics/01_generics.md` |
| 15 | `02_intermediate/01_generics/02_const_generics.md` |
| 16 | `02_intermediate/01_generics/03_type_level_programming.md` |
| 17 | `02_intermediate/02_memory_management/01_memory_management.md` |
| 18 | `02_intermediate/02_memory_management/02_interior_mutability.md` |
| 19 | `02_intermediate/02_memory_management/04_smart_pointers.md` |
| 20 | `02_intermediate/04_types_and_conversions/04_type_system_advanced.md` |
| 21 | `03_advanced/00_concurrency/01_concurrency.md` |
| 22 | `03_advanced/00_concurrency/02_send_sync_auto_traits.md` |
| 23 | `03_advanced/00_concurrency/03_concurrency_patterns.md` |
| 24 | `03_advanced/00_concurrency/06_atomics_and_memory_ordering.md` |
| 25 | `03_advanced/00_concurrency/07_lock_free.md` |
| 26 | `03_advanced/00_concurrency/08_parallel_distributed_pattern_spectrum.md` |
| 27 | `03_advanced/01_async/01_async.md` |
| 28 | `03_advanced/01_async/02_async_advanced.md` |
| 29 | `03_advanced/01_async/03_async_patterns.md` |
| 30 | `03_advanced/01_async/04_future_and_executor_mechanisms.md` |
| 31 | `03_advanced/01_async/05_async_cancellation_safety.md` |
| 32 | `03_advanced/01_async/06_async_boundary_panorama.md` |
| 33 | `03_advanced/01_async/07_async_closures.md` |
| 34 | `03_advanced/01_async/08_pin_unpin.md` |
| 35 | `03_advanced/01_async/09_stream_algebra_and_backpressure.md` |
| 36 | `03_advanced/01_async/10_executor_fairness_and_scheduling.md` |
| 37 | `03_advanced/01_async/11_pin_projection_counterexamples.md` |
| 38 | `03_advanced/02_unsafe/01_unsafe.md` |
| 39 | `03_advanced/02_unsafe/02_unsafe_boundary_panorama.md` |
| 40 | `03_advanced/02_unsafe/03_nll_and_polonius.md` |
| 41 | `03_advanced/02_unsafe/04_unsafe_rust_patterns.md` |
| 42 | `03_advanced/02_unsafe/06_memory_model.md` |
| 43 | `03_advanced/04_ffi/01_rust_ffi.md` |
| 44 | `03_advanced/04_ffi/02_ffi_advanced.md` |
| 45 | `03_advanced/04_ffi/03_linkage.md` |
| 46 | `03_advanced/04_ffi/04_async_ffi_boundary.md` |
| 47 | `04_formal/01_ownership_logic/01_linear_logic.md` |
| 48 | `04_formal/01_ownership_logic/02_ownership_formal.md` |
| 49 | `04_formal/07_concurrency_semantics/01_process_calculi_for_rust.md` |
| 50 | `04_formal/00_type_theory/01_type_theory.md` |

## 6. 改动样例（前 50 条）

| @id | 主语路径 | 宾语路径 | 旧谓词 | 新谓词 | 规则 |
|:---|:---|:---|:---|:---|:---|

## 7. 结论

✅ 核心 50 实体周边语义谓词实例化完成。

## 8. 机器可读

- JSON: `reports/KG_SEMANTIC_PREDICATES_2026-07-15.json`
