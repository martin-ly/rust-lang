# Linux Foundation Certified Rust Programmer (LFRS) 认证映射

> **创建日期**: 2026-04-24
> **用途**: 将 LFRS 认证的 10 大考点映射到本项目内容，建立可量化的学习验证体系
> **认证官网**: <https://www.linuxfoundation.org/certification/linux-foundation-certified-rust-programmer>

---

## 考点总览

| 编号 | 考点 | 掌握程度 | 项目覆盖度 |
| :--- | :--- | :--- | :--- |
| 1 | 语法 / 类型 / 控制流 | ✅ 完整 | 100% |
| 2 | Ownership / Borrowing / Lifetimes | ✅ 完整 | 100% |
| 3 | Structs / Enums / 模式匹配 | ✅ 完整 | 100% |
| 4 | 模块 / Crates | ✅ 完整 | 100% |
| 5 | 集合 / 字符串 | ✅ 完整 | 100% |
| 6 | 错误处理 | ✅ 完整 | 100% |
| 7 | Traits / 泛型 | ✅ 完整 | 100% |
| 8 | 测试 | ✅ 完整 | 100% |
| 9 | 闭包 / 迭代器 / Smart Pointers | ⚠️ 部分 | 85% |
| 10 | 并发（线程 / 通道 / async） | ⚠️ 部分 | 90% |

---

## 考点 1: 语法、类型与控制流

**掌握程度**: ✅ 完整

### 映射文件

| 子主题 | 项目文件路径 | 说明 |
| :--- | :--- | :--- |
| 变量与可变性 | `crates/c03_control_fn/src/basic_syntax.rs` | 变量绑定、mut、shadowing |
| 基本类型 | `crates/c02_type_system/src/primitive_types/` | 标量类型、复合类型完整覆盖 |
| 控制流 | `crates/c03_control_fn/src/control_struct/` | if/let、loop、while、for、match |
| 函数 | `crates/c03_control_fn/src/function/` | 参数、返回值、语句 vs 表达式 |
| 注释与文档 | `docs/02_reference/quick_reference/control_flow_functions_cheatsheet.md` | 速查卡 |

### 练习验证

- `exercises/src/ownership_borrowing/ex01_borrow_checker_fix.rs` (Easy)
- `exercises/src/type_system/ex01_enum_pattern_match.rs` (Easy)
- `exercises/rustlings_style/ex10_match_exhaustive/` (编译修复)

---

## 考点 2: Ownership、Borrowing 与 Lifetimes

**掌握程度**: ✅ 完整

### 映射文件

| 子主题 | 项目文件路径 | 说明 |
| :--- | :--- | :--- |
| 所有权规则 | `crates/c01_ownership_borrow_scope/src/ownership/` | 三大所有权规则详解 |
| 借用检查器 | `crates/c01_ownership_borrow_scope/src/borrow_checker/` | 编译时内存安全验证 |
| 引用与借用 | `crates/c01_ownership_borrow_scope/src/scope/` | &T、&mut T 规则 |
| 生命周期 | `crates/c01_ownership_borrow_scope/src/lifetime/` | 显式标注、省略规则 |
| Copy vs Move | `crates/c01_ownership_borrow_scope/src/copy_move/` | 语义差异与实现 |
| 内部可变性 | `crates/c01_ownership_borrow_scope/src/internal_mut/` | Cell、RefCell、UnsafeCell |

### 练习验证

- `exercises/src/ownership_borrowing/ex01_borrow_checker_fix.rs` (Easy)
- `exercises/src/ownership_borrowing/ex02_string_slice.rs` (Easy)
- `exercises/src/ownership_borrowing/ex03_mutable_borrow.rs` (Easy)
- `exercises/src/ownership_borrowing/ex04_lifetime_basic.rs` (Medium)
- `exercises/src/ownership_borrowing/ex05_smart_pointer_rc.rs` (Medium)
- `exercises/rustlings_style/ex01_borrow_fix/` (编译修复)
- `exercises/rustlings_style/ex02_mutable_borrow/` (编译修复)
- `exercises/rustlings_style/ex03_lifetime_elision/` (编译修复)

---

## 考点 3: Structs、Enums 与模式匹配

**掌握程度**: ✅ 完整

### 映射文件

| 子主题 | 项目文件路径 | 说明 |
| :--- | :--- | :--- |
| 结构体定义 | `crates/c02_type_system/src/type_composition/composite/struct/` | 命名字段、元组结构体、单元结构体 |
| 枚举定义 | `crates/c02_type_system/src/type_composition/composite/enum/` | 变体、带数据变体 |
| 模式匹配 | `crates/c02_type_system/src/type_decomposition/match/` | match、if let、while let |
| Option<T> | `crates/c03_control_fn/src/error_handling/` | 空值安全替代 |
| 方法语法 | `crates/c02_type_system/src/type_class/` | impl 块、关联函数 |

### 练习验证

- `exercises/src/type_system/ex01_enum_pattern_match.rs` (Easy)
- `exercises/src/type_system/ex02_struct_methods.rs` (Easy)
- `exercises/rustlings_style/ex05_struct_lifetime/` (编译修复)

---

## 考点 4: 模块与 Crates

**掌握程度**: ✅ 完整

### 映射文件

| 子主题 | 项目文件路径 | 说明 |
| :--- | :--- | :--- |
| 模块系统 | `crates/c02_type_system/src/type_composition/composite/mod.rs` | mod、pub、use |
| Crate 结构 | `Cargo.toml` (workspace) | 多 crate workspace 实践 |
| 路径系统 | `docs/02_reference/quick_reference/modules_cheatsheet.md` | 绝对路径、相对路径、super |
| 可见性 | 所有 crate 的 `src/lib.rs` | pub、pub(crate)、pub(super) 实例 |

### 练习验证

- 本项目本身就是一个 13+ crate 的 workspace，是最佳实践范例
- `exercises/src/lib.rs` 展示了模块组织方式

---

## 考点 5: 集合与字符串

**掌握程度**: ✅ 完整

### 映射文件

| 子主题 | 项目文件路径 | 说明 |
| :--- | :--- | :--- |
| Vec<T> | `crates/c02_type_system/src/type_composition/collection/vec.rs` | 动态数组操作 |
| String / &str | `crates/c02_type_system/src/primitive_types/scalar_types/string/` | UTF-8、所有权差异 |
| HashMap | `crates/c02_type_system/src/type_composition/collection/hash_map.rs` | 键值对存储 |
| HashSet | `crates/c02_type_system/src/type_composition/collection/hash_set.rs` | 集合操作 |
| BTreeMap / BTreeSet | `crates/c02_type_system/src/type_composition/collection/` | 有序集合 |
| 迭代器 | `docs/02_reference/quick_reference/collections_iterators_cheatsheet.md` | 迭代器适配器 |

### 练习验证

- `exercises/src/type_system/ex02_struct_methods.rs` (Easy, String 使用)
- `exercises/src/type_system/ex04_generics_intro.rs` (Medium, Vec 与泛型)
- `exercises/rustlings_style/ex04_string_ownership/` (编译修复)

---

## 考点 6: 错误处理

**掌握程度**: ✅ 完整

### 映射文件

| 子主题 | 项目文件路径 | 说明 |
| :--- | :--- | :--- |
| Result<T, E> | `crates/c03_control_fn/src/error_handling/result01.rs` | 错误传播与处理 |
| panic! | `crates/c03_control_fn/src/error_handling/define.rs` | 不可恢复错误 |
| ? 运算符 | `crates/c03_control_fn/src/error_handling/` | 错误传播语法糖 |
| 自定义错误 | `crates/c02_type_system/src/advanced_error_handling.rs` | Error trait 实现 |
| anyhow / thiserror | `docs/05_guides/BEST_PRACTICES.md` | 生态库推荐 |

### 练习验证

- `exercises/src/error_handling/ex01_result_option.rs` (Easy)
- `exercises/src/error_handling/ex02_custom_error.rs` (Medium)
- `exercises/src/error_handling/ex03_error_propagation.rs` (Medium)

---

## 考点 7: Traits 与泛型

**掌握程度**: ✅ 完整

### 映射文件

| 子主题 | 项目文件路径 | 说明 |
| :--- | :--- | :--- |
| Trait 定义与实现 | `crates/c04_generic/src/trait_bound/` | 标准库 trait 全覆盖 |
| 泛型函数 | `crates/c04_generic/src/basic_syntax.rs` | 类型参数、约束 |
| Trait Bounds | `crates/c04_generic/src/trait_bound/mod.rs` | 多约束、where 子句 |
| 关联类型 | `crates/c04_generic/src/associated_type/` | associated type 模式 |
| 特质对象 | `crates/c04_generic/src/polymorphism/trait_object.rs` | dyn Trait 动态分发 |
| 运算符重载 | `crates/c04_generic/src/trait_bound/operations.rs` | std::ops 特质 |

### 练习验证

- `exercises/src/generics_traits/ex01_trait_bounds.rs` (Easy)
- `exercises/src/generics_traits/ex02_associated_types.rs` (Medium)
- `exercises/src/generics_traits/ex03_operator_overload.rs` (Medium)
- `exercises/src/generics_traits/ex04_default_trait.rs` (Easy)
- `exercises/src/generics_traits/ex05_trait_composition.rs` (Hard)
- `exercises/src/type_system/ex04_generics_intro.rs` (Medium)
- `exercises/src/type_system/ex05_trait_object.rs` (Medium)
- `exercises/rustlings_style/ex06_trait_bound_fix/` (编译修复)
- `exercises/rustlings_style/ex07_generic_type_fix/` (编译修复)

---

## 考点 8: 测试

**掌握程度**: ✅ 完整

### 映射文件

| 子主题 | 项目文件路径 | 说明 |
| :--- | :--- | :--- |
| 单元测试 | `crates/*/src/lib.rs` 中的 `#[cfg(test)]` | 模块内测试 |
| 集成测试 | `tests/cross_module_integration_tests.rs` | 跨模块测试 |
| 文档测试 | 所有 crate 的文档注释中的 ``` 代码块 | 文档内嵌测试 |
| 属性测试 | `docs/03_guides/FUZZING_GUIDE.md` | proptest 使用指南 |
| 基准测试 | `crates/c08_algorithms/src/performance_benchmarks.rs` | Criterion 实例 |
| Miri | `docs/03_guides/MIRI_GUIDE.md` | 未定义行为检测 |
| 覆盖率 | `docs/03_guides/TEST_COVERAGE.md` | tarpaulin 使用 |

### 练习验证

- 每道练习题都包含完整测试用例
- `scripts/exercise-check.ps1` / `.sh` 提供自动化测试运行

---

## 考点 9: 闭包、迭代器与 Smart Pointers

**掌握程度**: ⚠️ 部分 (85%)

### 映射文件

| 子主题 | 项目文件路径 | 说明 | 状态 |
| :--- | :--- | :--- | :--- |
| 闭包 | `crates/c03_control_fn/src/closure/` | 捕获方式、Fn/FnMut/FnOnce | ✅ |
| 迭代器 | `docs/02_reference/quick_reference/collections_iterators_cheatsheet.md` | 适配器、消费者 | ✅ |
| Box<T> | `crates/c01_ownership_borrow_scope/src/ownership/` | 堆分配 | ✅ |
| Rc<T> | `crates/c01_ownership_borrow_scope/src/internal_mut/refcell/` | 引用计数 | ✅ |
| RefCell<T> | `crates/c01_ownership_borrow_scope/src/internal_mut/refcell/` | 运行时借用检查 | ✅ |
| Arc<T> | `crates/c05_threads/src/synchronization/arc/` | 线程安全 Rc | ✅ |
| Cow<T> | — | 写时克隆 | ❌ 缺失 |
| 自定义智能指针 | — | Deref/Drop 实现 | ❌ 缺失 |

### 补充计划

- 增加 `exercises/src/ownership_borrowing/ex06_cow.rs` (Cow 练习)
- 增加 `exercises/src/ownership_borrowing/ex07_custom_smart_pointer.rs` (Deref/Drop)

### 练习验证

- `exercises/src/ownership_borrowing/ex05_smart_pointer_rc.rs` (Medium)
- `exercises/rustlings_style/ex08_closure_capture/` (编译修复)
- `exercises/rustlings_style/ex09_iterator_consumer/` (编译修复)

---

## 考点 10: 并发（线程 / 通道 / async）

**掌握程度**: ⚠️ 部分 (90%)

### 映射文件

| 子主题 | 项目文件路径 | 说明 | 状态 |
| :--- | :--- | :--- | :--- |
| 线程创建 | `crates/c05_threads/src/threads/creation/` | spawn、JoinHandle | ✅ |
| 消息传递 | `crates/c05_threads/src/message_passing/` | mpsc、crossbeam-channel | ✅ |
| 共享状态 | `crates/c05_threads/src/synchronization/` | Mutex、RwLock、Atomic | ✅ |
| Send / Sync | `crates/c04_generic/src/trait_bound/send.rs` | 线程安全标记 trait | ✅ |
| async/await | `crates/c06_async/src/await/` | 基础语法 | ✅ |
| Future | `crates/c06_async/src/futures/` | Future trait 与执行器 | ✅ |
| Tokio | `crates/c06_async/src/tokio/` | 运行时、任务、通道 | ✅ |
| Stream | `crates/c06_async/src/streams/` | 异步流处理 | ✅ |
| 并行算法 | `crates/c05_threads/src/paralelism/` | Rayon、SIMD | ✅ |
| 无锁数据结构 | `crates/c05_threads/src/lockfree/` | 高级并发 | ✅ |
| async trait | — | async-trait crate | ⚠️ 部分 |

### 缺失内容

- `async fn` in trait（Rust 1.75+ 原生支持，项目已有但分散）
- 更系统的 async 错误处理模式专题

### 练习验证

- `exercises/src/concurrency/ex01_thread_spawn.rs` (Easy)
- `exercises/src/concurrency/ex02_mutex_counter.rs` (Medium)
- `exercises/src/concurrency/ex03_channel_mpsc.rs` (Easy)
- `exercises/src/concurrency/ex04_rwlock_shared.rs` (Medium)
- `exercises/src/concurrency/ex05_arc_atomic.rs` (Medium)
- `exercises/src/async_programming/ex01_basic_async.rs` (Easy)
- `exercises/src/async_programming/ex02_future_combinator.rs` (Medium)
- `exercises/src/async_programming/ex03_tokio_task.rs` (Medium)
- `exercises/src/async_programming/ex04_async_channel.rs` (Medium)
- `exercises/src/async_programming/ex05_timeout_retry.rs` (Hard)

---

## 学习路径建议

### 路径 A：按 LFRS 考点顺序学习

1. 考点 1 → `crates/c03_control_fn/` + `crates/c02_type_system/`
2. 考点 2 → `crates/c01_ownership_borrow_scope/`
3. 考点 3 → `crates/c02_type_system/src/type_composition/`
4. 考点 4 → 阅读本项目 workspace 结构 + `docs/02_reference/quick_reference/modules_cheatsheet.md`
5. 考点 5 → `crates/c02_type_system/src/type_composition/collection/`
6. 考点 6 → `crates/c03_control_fn/src/error_handling/`
7. 考点 7 → `crates/c04_generic/`
8. 考点 8 → 完成所有 `exercises/` 测试 + `cargo test --workspace`
9. 考点 9 → `crates/c03_control_fn/src/closure/` + 补充 Cow/自定义智能指针
10. 考点 10 → `crates/c05_threads/` + `crates/c06_async/`

### 路径 B：以练习驱动

1. 完成 `exercises/rustlings_style/` 中的 10 道编译修复题
2. 按考点顺序完成 `exercises/src/` 下的 30 道练习题
3. 对照本映射文档查漏补缺
4. 运行 `scripts/exercise-check.ps1` 验证掌握度

---

## 量化评估标准

| 掌握度 | 定义 | 行动建议 |
| :--- | :--- | :--- |
| ✅ 完整 | 项目内有专门模块 + 练习 + 文档 | 可直接参加考试 |
| ⚠️ 部分 | 有主要内容，但缺少某些子主题 | 需补充缺失部分后考试 |
| ❌ 缺失 | 尚未建立对应内容 | 需先学习外部资源 |

---

## 相关文档

- [GOOGLE_RUST_MAPPING.md](./GOOGLE_RUST_MAPPING.md) - Google Comprehensive Rust 映射
- [PRAGMATIC_GUIDELINES_CHECKLIST.md](../05_guides/PRAGMATIC_GUIDELINES_CHECKLIST.md) - 代码审查清单
- [exercises/README.md](../../exercises/README.md) - 练习题总入口
- [RUSTLINGS_MAPPING.md](../../exercises/RUSTLINGS_MAPPING.md) - Rustlings 习题映射
