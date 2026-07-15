# KG 关系谓词精度基线报告

**日期**: 2026-07-15  **总关系数**: 7989  **核心 50 实体关系数**: 2389  **核心实体数**: 50

## 1. 全局 ex:RelationAnnotation 占比

- `ex:RelationAnnotation` 数量: 0
- 全局通用谓词占比: **0.00%**
- 核心 50 周边通用谓词占比: **0.00%**

## 2. 核心 50 实体语义谓词覆盖

- 至少有一条语义谓词的核心实体: 50 / 50
- ✅ 全部核心实体周边至少存在一条语义谓词

## 3. 核心 50 实体语义谓词分布

| 谓词 | 计数 | 占比（核心） |
|:---|---:|---:|
| `ex:entails` | 1261 | 52.78% |
| `ex:dependsOn` | 1051 | 43.99% |
| `ex:refines` | 67 | 2.80% |
| `ex:equivalentTo` | 7 | 0.29% |
| `ex:enables` | 2 | 0.08% |
| `ex:mutexWith` | 1 | 0.04% |

## 4. 核心 50 实体列表

| @id | ex:path |
|:---|:---|
| `ex:AsyncAdvanced` | 03_advanced/01_async/02_async_advanced.md |
| `ex:AsyncBoundaryPanorama` | 03_advanced/01_async/06_async_boundary_panorama.md |
| `ex:AsyncCancellationSafety` | 03_advanced/01_async/05_async_cancellation_safety.md |
| `ex:AsyncClosures` | 03_advanced/01_async/07_async_closures.md |
| `ex:AsyncFFIBoundary` | 03_advanced/04_ffi/04_async_ffi_boundary.md |
| `ex:AsyncProgramming` | 03_advanced/01_async/01_async.md |
| `ex:Borrowing` | 01_foundation/01_ownership_borrow_lifetime/02_borrowing.md |
| `ex:Borrowing_02unsafe` | 03_advanced/02_unsafe/03_nll_and_polonius.md |
| `ex:Concurrency` | 03_advanced/00_concurrency/01_concurrency.md |
| `ex:Concurrency_00concurrenc` | 03_advanced/00_concurrency/03_concurrency_patterns.md |
| `ex:Concurrency_00concurrenc_1` | 03_advanced/00_concurrency/06_atomics_and_memory_ordering.md |
| `ex:Concurrency_01async` | 03_advanced/01_async/03_async_patterns.md |
| `ex:ConstGenericsValuesAsTypeParameters` | 02_intermediate/01_generics/02_const_generics.md |
| `ex:DerivableTraits` | 02_intermediate/00_traits/06_derive_traits.md |
| `ex:DispatchMechanisms` | 02_intermediate/00_traits/02_dispatch_mechanisms.md |
| `ex:ExecutorFairnessAndScheduling` | 03_advanced/01_async/10_executor_fairness_and_scheduling.md |
| `ex:ForeignFunctionInterfaceFFI` | 03_advanced/04_ffi/01_rust_ffi.md |
| `ex:ForeignFunctionInterfaceFFI_04ffi` | 03_advanced/04_ffi/02_ffi_advanced.md |
| `ex:FutureAndExecutorMechanisms` | 03_advanced/01_async/04_future_and_executor_mechanisms.md |
| `ex:GenericAssociatedTypesGATs` | 02_intermediate/00_traits/07_generic_associated_types.md |
| `ex:Generics` | 02_intermediate/01_generics/01_generics.md |
| `ex:InteriorMutability` | 02_intermediate/02_memory_management/02_interior_mutability.md |
| `ex:Lifetimes` | 01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md |
| `ex:LifetimesAdvanced` | 01_foundation/01_ownership_borrow_lifetime/04_lifetimes_advanced.md |
| `ex:LinearLogic` | 04_formal/01_ownership_logic/01_linear_logic.md |
| `ex:Linkage` | 03_advanced/04_ffi/03_linkage.md |
| `ex:LockingPrimitives` | 03_advanced/00_concurrency/07_lock_free.md |
| `ex:MemoryManagement` | 02_intermediate/02_memory_management/01_memory_management.md |
| `ex:MemoryModel` | 03_advanced/02_unsafe/06_memory_model.md |
| `ex:MoveSemantics` | 01_foundation/01_ownership_borrow_lifetime/05_move_semantics.md |
| `ex:Ownership` | 01_foundation/01_ownership_borrow_lifetime/01_ownership.md |
| `ex:Ownership_01ownershipl` | 04_formal/01_ownership_logic/02_ownership_formal.md |
| `ex:ParallelDistributedPatternSpectrum` | 03_advanced/00_concurrency/08_parallel_distributed_pattern_spectrum.md |
| `ex:PinAndUnpin` | 03_advanced/01_async/08_pin_unpin.md |
| `ex:PinProjectionCounterexamples` | 03_advanced/01_async/11_pin_projection_counterexamples.md |
| `ex:ProcessCalculiForRustCSPCCSAndThePiCalculus` | 04_formal/07_concurrency_semantics/01_process_calculi_for_rust.md |
| `ex:ReferenceSemantics` | 01_foundation/03_values_and_references/01_reference_semantics.md |
| `ex:SafeAndEffectiveUnsafeRust` | 03_advanced/02_unsafe/01_unsafe.md |
| `ex:SendAndSyncAutoTraitsAsCompileTimeConcurrencyContracts` | 03_advanced/00_concurrency/02_send_sync_auto_traits.md |
| `ex:SmartPointers` | 02_intermediate/02_memory_management/04_smart_pointers.md |
| `ex:StreamAlgebraAndBackpressure` | 03_advanced/01_async/09_stream_algebra_and_backpressure.md |
| `ex:Traits` | 02_intermediate/00_traits/01_traits.md |
| `ex:Traits_00traits` | 02_intermediate/00_traits/04_advanced_traits.md |
| `ex:TypeLevelProgramming` | 02_intermediate/01_generics/03_type_level_programming.md |
| `ex:TypeSystem` | 01_foundation/02_type_system/01_type_system.md |
| `ex:TypeSystem_04typesandco` | 02_intermediate/04_types_and_conversions/04_type_system_advanced.md |
| `ex:TypeTheory` | 04_formal/00_type_theory/01_type_theory.md |
| `ex:UnsafeBoundaryPanorama` | 03_advanced/02_unsafe/02_unsafe_boundary_panorama.md |
| `ex:UnsafeRust` | 03_advanced/02_unsafe/04_unsafe_rust_patterns.md |
| `ex:VariableModel` | 01_foundation/03_values_and_references/03_variable_model.md |

## 5. 检查结论

**结论**: 核心 50 实体均已实例化至少一条语义谓词。

## 6. 机器可读

- JSON: `reports/KG_RELATION_PRECISION_2026-07-15.json`
