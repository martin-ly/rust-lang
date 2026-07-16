# KG 语义谓词实例化报告（l1, l2, async, unsafe, formal, l5, l6_concept, l7, l3_rem, meta_navigation, ecosystem, future, rustc_internals, framework）

**日期**: 2026-07-16  
**模式**: 已写回 kg_data_v3.json  
**置信度阈值**: 0.75  
**处理实体数**: 487  **处理关系数**: 17216

## 1. 各批次通用谓词残留

| 批次 | 实体数 | 关系数 | 通用谓词残留 | 占比 |
|:---|---:|---:|---:|---:|
| `l1` | 51 | 1459 | 67 | 4.59% |
| `l2` | 40 | 1153 | 44 | 3.82% |
| `async` | 14 | 497 | 17 | 3.42% |
| `unsafe` | 9 | 360 | 11 | 3.06% |
| `formal` | 61 | 1276 | 44 | 3.45% |
| `l5` | 27 | 668 | 21 | 3.14% |
| `l6_concept` | 103 | 1952 | 124 | 6.35% |
| `l7` | 66 | 1273 | 57 | 4.48% |
| `l3_rem` | 43 | 902 | 47 | 5.21% |
| `meta_navigation` | 29 | 3372 | 55 | 1.63% |
| `ecosystem` | 126 | 2265 | 126 | 5.56% |
| `future` | 66 | 1273 | 57 | 4.48% |
| `rustc_internals` | 17 | 291 | 5 | 1.72% |
| `framework` | 21 | 475 | 11 | 2.32% |

- 处理批次内通用谓词总计残留: **686**
- 因低于置信度阈值跳过: **0**

## 2. 改动统计

- 修改的关系数: 89

## 3. 全局 @type 分布前后对比

| 谓词 | 修改前 | 修改后 | Δ |
|:---|---:|---:|---:|
| `ex:relatedTo` | 6263 | 6203 | -60 |
| `ex:dependsOn` | 818 | 838 | +20 |
| `ex:entails` | 752 | 764 | +12 |
| `ex:RelationAnnotation` | 592 | 563 | -29 |
| `ex:instanceOf` | 0 | 18 | +18 |
| `ex:appliesTo` | 0 | 14 | +14 |
| `ex:refines` | 0 | 12 | +12 |
| `ex:counterExample` | 0 | 5 | +5 |
| `ex:mutexWith` | 0 | 5 | +5 |
| `ex:equivalentTo` | 0 | 3 | +3 |

## 4. 改动样例（前 50 条）

| @id | 主语路径 | 宾语路径 | 旧谓词 | 新谓词 | 规则 | 置信度 |
|:---|:---|:---|:---|:---|:---|---:|
| `_:rel1781` | `00_meta/02_sources/02_rustbelt_predicate_map.md` | `04_formal/02_separation_logic/01_rustbelt.md` | `ex:equivalentTo` | `ex:equivalentTo` | existing-semantic | 1.00 |
| `_:rel4624` | `01_foundation/01_ownership_borrow_lifetime/01_ownership.md` | `02_intermediate/01_generics/01_generics.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel4640` | `01_foundation/01_ownership_borrow_lifetime/02_borrowing.md` | `01_foundation/01_ownership_borrow_lifetime/01_ownership.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel4641` | `01_foundation/01_ownership_borrow_lifetime/02_borrowing.md` | `02_intermediate/00_traits/01_traits.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel4643` | `01_foundation/01_ownership_borrow_lifetime/02_borrowing.md` | `03_advanced/00_concurrency/01_concurrency.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel4662` | `01_foundation/01_ownership_borrow_lifetime/04_lifetimes_advanced.md` | `01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md` | `ex:refines` | `ex:refines` | existing-semantic | 1.00 |
| `_:rel4679` | `01_foundation/01_ownership_borrow_lifetime/05_move_semantics.md` | `01_foundation/01_ownership_borrow_lifetime/02_borrowing.md` | `ex:mutexWith` | `ex:mutexWith` | existing-semantic | 1.00 |
| `_:rel4941` | `01_foundation/08_error_handling/03_panic_and_abort.md` | `01_foundation/08_error_handling/01_error_handling_basics.md` | `ex:mutexWith` | `ex:mutexWith` | existing-semantic | 1.00 |
| `_:rel5035` | `02_intermediate/00_traits/01_traits.md` | `03_advanced/00_concurrency/01_concurrency.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel5036` | `02_intermediate/00_traits/01_traits.md` | `01_foundation/01_ownership_borrow_lifetime/01_ownership.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel5040` | `02_intermediate/00_traits/02_dispatch_mechanisms.md` | `02_intermediate/00_traits/01_traits.md` | `ex:appliesTo` | `ex:appliesTo` | existing-semantic | 1.00 |
| `_:rel5042` | `02_intermediate/00_traits/03_serde_patterns.md` | `02_intermediate/00_traits/01_traits.md` | `ex:refines` | `ex:refines` | existing-semantic | 1.00 |
| `_:rel5052` | `02_intermediate/00_traits/04_advanced_traits.md` | `02_intermediate/00_traits/01_traits.md` | `ex:refines` | `ex:refines` | existing-semantic | 1.00 |
| `_:rel5066` | `02_intermediate/00_traits/05_construction_and_initialization.md` | `01_foundation/01_ownership_borrow_lifetime/01_ownership.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel5070` | `02_intermediate/00_traits/06_derive_traits.md` | `02_intermediate/00_traits/01_traits.md` | `ex:instanceOf` | `ex:instanceOf` | existing-semantic | 1.00 |
| `_:rel5113` | `02_intermediate/01_generics/03_type_level_programming.md` | `02_intermediate/04_types_and_conversions/05_rtti_and_dynamic_typing.md` | `ex:mutexWith` | `ex:mutexWith` | existing-semantic | 1.00 |
| `_:rel5133` | `02_intermediate/02_memory_management/01_memory_management.md` | `01_foundation/01_ownership_borrow_lifetime/02_borrowing.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel5136` | `02_intermediate/02_memory_management/01_memory_management.md` | `03_advanced/00_concurrency/01_concurrency.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel5137` | `02_intermediate/02_memory_management/01_memory_management.md` | `03_advanced/01_async/01_async.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel5146` | `02_intermediate/02_memory_management/02_interior_mutability.md` | `01_foundation/01_ownership_borrow_lifetime/02_borrowing.md` | `ex:counterExample` | `ex:counterExample` | existing-semantic | 1.00 |
| `_:rel5148` | `02_intermediate/02_memory_management/02_interior_mutability.md` | `03_advanced/01_async/01_async.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel5154` | `02_intermediate/02_memory_management/03_cow_and_borrowed.md` | `01_foundation/01_ownership_borrow_lifetime/02_borrowing.md` | `ex:refines` | `ex:refines` | existing-semantic | 1.00 |
| `_:rel5162` | `02_intermediate/02_memory_management/04_smart_pointers.md` | `01_foundation/01_ownership_borrow_lifetime/02_borrowing.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel5163` | `02_intermediate/02_memory_management/04_smart_pointers.md` | `02_intermediate/02_memory_management/01_memory_management.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel5179` | `02_intermediate/03_error_handling/01_error_handling.md` | `02_intermediate/00_traits/01_traits.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel5181` | `02_intermediate/03_error_handling/01_error_handling.md` | `03_advanced/01_async/01_async.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel5193` | `02_intermediate/03_error_handling/02_error_handling_deep_dive.md` | `02_intermediate/03_error_handling/01_error_handling.md` | `ex:refines` | `ex:refines` | existing-semantic | 1.00 |
| `_:rel5196` | `02_intermediate/03_error_handling/03_panic.md` | `01_foundation/08_error_handling/03_panic_and_abort.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel5218` | `02_intermediate/04_types_and_conversions/02_closure_types.md` | `01_foundation/01_ownership_borrow_lifetime/01_ownership.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel5219` | `02_intermediate/04_types_and_conversions/02_closure_types.md` | `01_foundation/01_ownership_borrow_lifetime/02_borrowing.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel5221` | `02_intermediate/04_types_and_conversions/02_closure_types.md` | `02_intermediate/01_generics/01_generics.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel5229` | `02_intermediate/04_types_and_conversions/03_newtype_and_wrapper.md` | `06_ecosystem/03_design_patterns/01_patterns.md` | `ex:instanceOf` | `ex:instanceOf` | existing-semantic | 1.00 |
| `_:rel5365` | `03_advanced/00_concurrency/01_concurrency.md` | `01_foundation/01_ownership_borrow_lifetime/02_borrowing.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel5366` | `03_advanced/00_concurrency/01_concurrency.md` | `02_intermediate/00_traits/01_traits.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel5376` | `03_advanced/00_concurrency/02_send_sync_auto_traits.md` | `03_advanced/00_concurrency/06_atomics_and_memory_ordering.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel5377` | `03_advanced/00_concurrency/02_send_sync_auto_traits.md` | `03_advanced/00_concurrency/07_lock_free.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel5380` | `03_advanced/00_concurrency/02_send_sync_auto_traits.md` | `02_intermediate/02_memory_management/02_interior_mutability.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel5381` | `03_advanced/00_concurrency/02_send_sync_auto_traits.md` | `03_advanced/02_unsafe/01_unsafe.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel5382` | `03_advanced/00_concurrency/02_send_sync_auto_traits.md` | `01_foundation/01_ownership_borrow_lifetime/01_ownership.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel5384` | `03_advanced/00_concurrency/03_concurrency_patterns.md` | `03_advanced/00_concurrency/01_concurrency.md` | `ex:refines` | `ex:refines` | existing-semantic | 1.00 |
| `_:rel5395` | `03_advanced/00_concurrency/04_send_sync_boundaries.md` | `03_advanced/01_async/01_async.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel5397` | `03_advanced/00_concurrency/04_send_sync_boundaries.md` | `02_intermediate/00_traits/02_dispatch_mechanisms.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel5400` | `03_advanced/00_concurrency/05_cross_platform_concurrency.md` | `03_advanced/00_concurrency/01_concurrency.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel5425` | `03_advanced/00_concurrency/07_lock_free.md` | `03_advanced/00_concurrency/01_concurrency.md` | `ex:counterExample` | `ex:counterExample` | existing-semantic | 1.00 |
| `_:rel5426` | `03_advanced/00_concurrency/07_lock_free.md` | `03_advanced/00_concurrency/06_atomics_and_memory_ordering.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel5427` | `03_advanced/00_concurrency/07_lock_free.md` | `03_advanced/02_unsafe/01_unsafe.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel5492` | `03_advanced/01_async/02_async_advanced.md` | `03_advanced/01_async/01_async.md` | `ex:refines` | `ex:refines` | existing-semantic | 1.00 |
| `_:rel5549` | `03_advanced/01_async/07_async_closures.md` | `03_advanced/01_async/01_async.md` | `ex:refines` | `ex:refines` | existing-semantic | 1.00 |
| `_:rel5557` | `03_advanced/01_async/08_pin_unpin.md` | `03_advanced/01_async/01_async.md` | `ex:appliesTo` | `ex:appliesTo` | existing-semantic | 1.00 |
| `_:rel5634` | `03_advanced/02_unsafe/01_unsafe.md` | `02_intermediate/02_memory_management/01_memory_management.md` | `ex:counterExample` | `ex:counterExample` | existing-semantic | 1.00 |

## 5. 结论

⚠️ 处理批次内仍有 686 条通用谓词（低于阈值 0 条），需进一步处理。

## 6. 机器可读

- JSON: `reports/KG_SEMANTIC_PREDICATES_2026-07-16.json`