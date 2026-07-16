# KG 核心边语义类型化（relatedTo 反塌缩）

**日期**: 2026-07-16  **核心实体**: 68  **核心子集边**: 523 → 529  **改动**: 54  
**模式**: 已写回 kg_data_v3.json

## 规则

- R1 策展互斥 → `ex:mutexWith`（依据为权威页原句，见下文各行）
- R2 策展反例 → `ex:counterExample`（A 页反例章节反驳 B 的朴素假设）
- R3 策展精化 → `ex:refines`（A 为 B 的进阶/模式/机制展开）
- R4 前置元数据 → `ex:dependsOn`（目标在源页 前置概念/前置依赖 元数据中）
- R5 后置元数据 → `ex:entails`（目标在源页 后置概念/后置延伸 元数据中）

## 分布前后对比

### 核心子集（L1–L3 九大主题）

| 谓词 | 前 | 后 | Δ |
|:---|---:|---:|---:|
| ex:relatedTo | 346 | 298 | -48 |
| ex:dependsOn | 114 | 134 | +20 |
| ex:entails | 63 | 75 | +12 |
| ex:refines | 0 | 12 | +12 |
| ex:mutexWith | 0 | 5 | +5 |
| ex:counterExample | 0 | 5 | +5 |

### 全局 KG

| 谓词 | 前 | 后 | Δ |
|:---|---:|---:|---:|
| ex:relatedTo | 6806 | 6758 | -48 |
| ex:dependsOn | 834 | 854 | +20 |
| ex:entails | 756 | 768 | +12 |
| ex:refines | 0 | 12 | +12 |
| ex:mutexWith | 0 | 5 | +5 |
| ex:counterExample | 0 | 5 | +5 |

## 逐边改动与依据

| 规则 | 动作 | 主语 | 谓词 | 宾语 | 依据 |
|:---|:---|:---|:---|:---|:---|
| R1-curated-mutex | retyped relatedTo | ex:MoveSemantics | ex:mutexWith | ex:Borrowing | 01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md:942 “Rust 的所有权（Ownership）转移（move）与借用是互斥的。若变量已被借用…在借用释放前不能转移其所有权。” |
| R1-curated-mutex | added new edge | ex:PinAndUnpin | ex:mutexWith | ex:MoveSemantics | 03_advanced/01_async/08_pin_unpin.md:735 “Pin 通过禁止移动（对 !Unpin 类型）来解决这个问题”；:648 “T: !Unpin — Pin 禁止 get_mut()（数据不可移动）” |
| R1-curated-mutex | added new edge | ex:Unions | ex:mutexWith | ex:MemoryManagement | 02_intermediate/04_types_and_conversions/06_unions.md:105 “Drop: 默认不 drop 字段”；:250 “联合体默认不会自动 drop 字段”——与 RAII 自动析构纪律互斥 |
| R1-curated-mutex | retyped relatedTo | ex:PanicAndAbort | ex:mutexWith | ex:ErrorHandling | 01_foundation/08_error_handling/03_panic_and_abort.md:5 “不可恢复错误的处理机制”；:91 “异常: 可恢复的错误条件”——同一错误现场不可恢复(panic/abort)与可恢复(Result 传播)策略二选一 |
| R1-curated-mutex | retyped relatedTo | ex:TypeLevelProgramming | ex:mutexWith | ex:RTTIAndDynamicTypeIdentification | 02_intermediate/04_types_and_conversions/05_rtti_and_dynamic_typing.md:203 “RTTI 是静态类型系统（Type System）向运行时的有限‘泄漏’”——编译期类型计算与运行期类型识别在同一类型问题上互斥 |
| R2-curated-counterexample | retyped relatedTo | ex:InteriorMutability | ex:counterExample | ex:Borrowing | 01_foundation/01_ownership_borrow_lifetime/02_borrowing.md:781 “&mut vs &: 为什么不能同时有？… AXM: 读写互斥 … UnsafeCell 突破”；:461 “别名与可变互斥公理”——内部可变性（Cell/RefCell/UnsafeCell）是借用规则的受控反例 |
| R2-curated-counterexample | added new edge | ex:SafeAndEffectiveUnsafeRust | ex:counterExample | ex:Lifetimes | 03_advanced/02_unsafe/01_unsafe.md:1125 “8.3 反例：悬垂裸指针（UB）”——裸指针悬垂是对“引用有效性总由生命周期保证”的反例 |
| R2-curated-counterexample | added new edge | ex:SafeAndEffectiveUnsafeRust | ex:counterExample | ex:TypeConversions | 03_advanced/02_unsafe/01_unsafe.md:1140 “8.4 反例：transmute 滥用（UB）”——transmute 滥用是对安全类型转换纪律的反例 |
| R2-curated-counterexample | retyped relatedTo | ex:SafeAndEffectiveUnsafeRust | ex:counterExample | ex:MemoryManagement | 03_advanced/02_unsafe/01_unsafe.md:1422 “❌ 反例: Use-after-free（Miri 会报错）”——UAF 是对自动内存管理保证的反例 |
| R2-curated-counterexample | retyped relatedTo | ex:LockingPrimitives | ex:counterExample | ex:Concurrency | 03_advanced/00_concurrency/07_lock_free.md:409 “命题: 无锁总是优于锁” → :422 “无锁只在高竞争场景显著优于锁”——对朴素并发性能信念的反例 |
| R3-curated-refines | retyped relatedTo | ex:LifetimesAdvanced | ex:refines | ex:Lifetimes | 01_foundation/01_ownership_borrow_lifetime/04_lifetimes_advanced.md 为 03_lifetimes.md 的进阶展开（标题“生命周期进阶”） |
| R3-curated-refines | retyped relatedTo | ex:Traits_00traits | ex:refines | ex:Traits | 02_intermediate/00_traits/04_advanced_traits.md 为 01_traits.md 的高级主题精化（标题“高级 Trait 主题”） |
| R3-curated-refines | retyped relatedTo | ex:AsyncAdvanced | ex:refines | ex:AsyncProgramming | 03_advanced/01_async/02_async_advanced.md 为 02_async.md 的进阶展开（标题“Async 进阶”） |
| R3-curated-refines | retyped relatedTo | ex:ErrorHandling_03errorhandl_1 | ex:refines | ex:ErrorHandling_03errorhandl | 02_intermediate/03_error_handling/02_error_handling_deep_dive.md 为 04_error_handling.md 的深入精化（标题“错误处理深入”） |
| R3-curated-refines | added parallel edge | ex:UnsafeRust | ex:refines | ex:SafeAndEffectiveUnsafeRust | 03_advanced/02_unsafe/04_unsafe_rust_patterns.md 将 03_unsafe.md 精化为可复用 unsafe 模式 |
| R3-curated-refines | retyped relatedTo | ex:Concurrency_00concurrenc | ex:refines | ex:Concurrency | 03_advanced/00_concurrency/03_concurrency_patterns.md 将 01_concurrency.md 精化为并发模式谱系 |
| R3-curated-refines | retyped relatedTo | ex:CowAndBorrowed | ex:refines | ex:Borrowing | 02_intermediate/02_memory_management/03_cow_and_borrowed.md: Cow 将借用语义精化为写时克隆（Clone-on-Write） |
| R3-curated-refines | retyped relatedTo | ex:Borrowing_02unsafe | ex:refines | ex:Borrowing | 03_advanced/02_unsafe/03_nll_and_polonius.md: NLL/Polonius 将借用检查从词法作用域精化到使用点/流敏感 |
| R3-curated-refines | added new edge | ex:FutureAndExecutorMechanisms | ex:refines | ex:AsyncProgramming | 03_advanced/01_async/04_future_and_executor_mechanisms.md 精化 async 的 Future/执行器机制 |
| R3-curated-refines | retyped relatedTo | ex:SerdePatterns | ex:refines | ex:Traits | 02_intermediate/00_traits/03_serde_patterns.md 将 trait 精化为 serde 序列化模式应用 |
| R3-curated-refines | retyped relatedTo | ex:MemoryModel | ex:refines | ex:SafeAndEffectiveUnsafeRust | 03_advanced/02_unsafe/06_memory_model.md 精化 unsafe 语义的内存模型基础 |
| R3-curated-refines | retyped relatedTo | ex:AsyncClosures | ex:refines | ex:AsyncProgramming | 03_advanced/01_async/07_async_closures.md 将 async 精化到闭包捕获场景 |
| R5-postreq-metadata | retyped relatedTo | ex:Ownership | ex:entails | ex:Generics | 权威页后置元数据：01_foundation/01_ownership_borrow_lifetime/01_ownership.md 的 后置概念/后置延伸 含 [01_generics] |
| R4-prereq-metadata | retyped relatedTo | ex:Borrowing | ex:dependsOn | ex:Ownership | 权威页前置元数据：01_foundation/01_ownership_borrow_lifetime/02_borrowing.md 的 前置概念/前置依赖 含 [01_ownership] |
| R5-postreq-metadata | retyped relatedTo | ex:Borrowing | ex:entails | ex:Traits | 权威页后置元数据：01_foundation/01_ownership_borrow_lifetime/02_borrowing.md 的 后置概念/后置延伸 含 [01_traits] |
| R5-postreq-metadata | retyped relatedTo | ex:Borrowing | ex:entails | ex:Concurrency | 权威页后置元数据：01_foundation/01_ownership_borrow_lifetime/02_borrowing.md 的 后置概念/后置延伸 含 [01_concurrency] |
| R5-postreq-metadata | retyped relatedTo | ex:Traits | ex:entails | ex:Concurrency | 权威页后置元数据：02_intermediate/00_traits/01_traits.md 的 后置概念/后置延伸 含 [01_concurrency] |
| R4-prereq-metadata | retyped relatedTo | ex:Traits | ex:dependsOn | ex:Ownership | 权威页前置元数据：02_intermediate/00_traits/01_traits.md 的 前置概念/前置依赖 含 [01_ownership] |
| R4-prereq-metadata | retyped relatedTo | ex:ConstructionAndInitialization | ex:dependsOn | ex:Ownership | 权威页前置元数据：02_intermediate/00_traits/05_construction_and_initialization.md 的 前置概念/前置依赖 含 [01_ownership] |
| R4-prereq-metadata | retyped relatedTo | ex:MemoryManagement | ex:dependsOn | ex:Borrowing | 权威页前置元数据：02_intermediate/02_memory_management/01_memory_management.md 的 前置概念/前置依赖 含 [02_borrowing] |
| R5-postreq-metadata | retyped relatedTo | ex:MemoryManagement | ex:entails | ex:Concurrency | 权威页后置元数据：02_intermediate/02_memory_management/01_memory_management.md 的 后置概念/后置延伸 含 [01_concurrency] |
| R5-postreq-metadata | retyped relatedTo | ex:MemoryManagement | ex:entails | ex:AsyncProgramming | 权威页后置元数据：02_intermediate/02_memory_management/01_memory_management.md 的 后置概念/后置延伸 含 [01_async] |
| R5-postreq-metadata | retyped relatedTo | ex:InteriorMutability | ex:entails | ex:AsyncProgramming | 权威页后置元数据：02_intermediate/02_memory_management/02_interior_mutability.md 的 后置概念/后置延伸 含 [01_async] |
| R4-prereq-metadata | retyped relatedTo | ex:SmartPointers | ex:dependsOn | ex:Borrowing | 权威页前置元数据：02_intermediate/02_memory_management/04_smart_pointers.md 的 前置概念/前置依赖 含 [02_borrowing] |
| R4-prereq-metadata | retyped relatedTo | ex:SmartPointers | ex:dependsOn | ex:MemoryManagement | 权威页前置元数据：02_intermediate/02_memory_management/04_smart_pointers.md 的 前置概念/前置依赖 含 [01_memory_management] |
| R4-prereq-metadata | retyped relatedTo | ex:ErrorHandling_03errorhandl | ex:dependsOn | ex:Traits | 权威页前置元数据：02_intermediate/03_error_handling/01_error_handling.md 的 前置概念/前置依赖 含 [01_traits] |
| R5-postreq-metadata | retyped relatedTo | ex:ErrorHandling_03errorhandl | ex:entails | ex:AsyncProgramming | 权威页后置元数据：02_intermediate/03_error_handling/01_error_handling.md 的 后置概念/后置延伸 含 [01_async] |
| R4-prereq-metadata | retyped relatedTo | ex:Panic | ex:dependsOn | ex:PanicAndAbort | 权威页前置元数据：02_intermediate/03_error_handling/03_panic.md 的 前置概念/前置依赖 含 [03_panic_and_abort] |
| R4-prereq-metadata | retyped relatedTo | ex:ClosureTypes | ex:dependsOn | ex:Ownership | 权威页前置元数据：02_intermediate/04_types_and_conversions/02_closure_types.md 的 前置概念/前置依赖 含 [01_ownership] |
| R4-prereq-metadata | retyped relatedTo | ex:ClosureTypes | ex:dependsOn | ex:Borrowing | 权威页前置元数据：02_intermediate/04_types_and_conversions/02_closure_types.md 的 前置概念/前置依赖 含 [02_borrowing] |
| R5-postreq-metadata | retyped relatedTo | ex:ClosureTypes | ex:entails | ex:Generics | 权威页后置元数据：02_intermediate/04_types_and_conversions/02_closure_types.md 的 后置概念/后置延伸 含 [01_generics] |
| R4-prereq-metadata | retyped relatedTo | ex:Concurrency | ex:dependsOn | ex:Borrowing | 权威页前置元数据：03_advanced/00_concurrency/01_concurrency.md 的 前置概念/前置依赖 含 [02_borrowing] |
| R4-prereq-metadata | retyped relatedTo | ex:Concurrency | ex:dependsOn | ex:Traits | 权威页前置元数据：03_advanced/00_concurrency/01_concurrency.md 的 前置概念/前置依赖 含 [01_traits] |
| R5-postreq-metadata | retyped relatedTo | ex:SendAndSyncAutoTraitsAsCompileTimeConcurrencyContracts | ex:entails | ex:Concurrency_00concurrenc_1 | 权威页后置元数据：03_advanced/00_concurrency/02_send_sync_auto_traits.md 的 后置概念/后置延伸 含 [06_atomics_and_memory_ordering] |
| R5-postreq-metadata | retyped relatedTo | ex:SendAndSyncAutoTraitsAsCompileTimeConcurrencyContracts | ex:entails | ex:LockingPrimitives | 权威页后置元数据：03_advanced/00_concurrency/02_send_sync_auto_traits.md 的 后置概念/后置延伸 含 [07_lock_free] |
| R4-prereq-metadata | retyped relatedTo | ex:SendAndSyncAutoTraitsAsCompileTimeConcurrencyContracts | ex:dependsOn | ex:InteriorMutability | 权威页前置元数据：03_advanced/00_concurrency/02_send_sync_auto_traits.md 的 前置概念/前置依赖 含 [02_interior_mutability] |
| R5-postreq-metadata | retyped relatedTo | ex:SendAndSyncAutoTraitsAsCompileTimeConcurrencyContracts | ex:entails | ex:SafeAndEffectiveUnsafeRust | 权威页后置元数据：03_advanced/00_concurrency/02_send_sync_auto_traits.md 的 后置概念/后置延伸 含 [01_unsafe] |
| R4-prereq-metadata | retyped relatedTo | ex:SendAndSyncAutoTraitsAsCompileTimeConcurrencyContracts | ex:dependsOn | ex:Ownership | 权威页前置元数据：03_advanced/00_concurrency/02_send_sync_auto_traits.md 的 前置概念/前置依赖 含 [01_ownership] |
| R4-prereq-metadata | retyped relatedTo | ex:SendSyncBoundaryJudgmentTraitObjectsClosuresAndAsyncStateMachines | ex:dependsOn | ex:AsyncProgramming | 权威页前置元数据：03_advanced/00_concurrency/04_send_sync_boundaries.md 的 前置概念/前置依赖 含 [01_async] |
| R4-prereq-metadata | retyped relatedTo | ex:SendSyncBoundaryJudgmentTraitObjectsClosuresAndAsyncStateMachines | ex:dependsOn | ex:DispatchMechanisms | 权威页前置元数据：03_advanced/00_concurrency/04_send_sync_boundaries.md 的 前置概念/前置依赖 含 [02_dispatch_mechanisms] |
| R4-prereq-metadata | retyped relatedTo | ex:CrossPlatformConcurrency | ex:dependsOn | ex:Concurrency | 权威页前置元数据：03_advanced/00_concurrency/05_cross_platform_concurrency.md 的 前置概念/前置依赖 含 [01_concurrency] |
| R4-prereq-metadata | retyped relatedTo | ex:LockingPrimitives | ex:dependsOn | ex:Concurrency_00concurrenc_1 | 权威页前置元数据：03_advanced/00_concurrency/07_lock_free.md 的 前置概念/前置依赖 含 [06_atomics_and_memory_ordering] |
| R4-prereq-metadata | retyped relatedTo | ex:LockingPrimitives | ex:dependsOn | ex:SafeAndEffectiveUnsafeRust | 权威页前置元数据：03_advanced/00_concurrency/07_lock_free.md 的 前置概念/前置依赖 含 [01_unsafe] |
| R4-prereq-metadata | retyped relatedTo | ex:UnsafeReference | ex:dependsOn | ex:SafeAndEffectiveUnsafeRust | 权威页前置元数据：03_advanced/02_unsafe/07_unsafe_reference.md 的 前置概念/前置依赖 含 [01_unsafe] |

## 机器可读

- JSON: `reports/KG_CORE_EDGE_TYPING_2026-07-16.json`