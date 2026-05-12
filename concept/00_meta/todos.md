# 全局待办清单（Global TODO Tracker）

> **定位**：汇总 `concept/` 下所有文件的待补充项，按优先级和层级组织，支持持续审计与迭代。
> **最后更新**：2026-05-12

---

## 一、高优先级 TODO（建议优先处理）

### L1 基础概念层

| 文件 | TODO 内容 | 预计阶段 | 状态 |
|:---|:---|:---|:---|
| `01_ownership.md` | 补充 `Pin<T>` 与所有权的交互 | Phase 2 | 📋 待补充 |
| `01_ownership.md` | 补充跨线程所有权转移（`Send` trait）的形式化视角 | Phase 3 | 📋 待补充 |
| `01_ownership.md` | 补充所有权与 FFI / unsafe 边界的交互 | Phase 3 | 📋 待补充 |
| `02_borrowing.md` | 补充 `Pin<&mut T>` 的自引用结构借用 | Phase 3 | 📋 待补充 |
| `02_borrowing.md` | 补充 `Cell<T>` / `RefCell<T>` 的内部可变性与借用规则的"绕过" | Phase 2 | 📋 待补充 |
| `03_lifetimes.md` | 补充 Higher-Ranked Trait Bounds (HRTB) `for<'a>` 的深度分析 | Phase 2 | 📋 待补充 |
| `03_lifetimes.md` | 补充 Lifetime subtyping 与 Variance（协变/逆变/不变） | Phase 2 | 📋 待补充 |
| `03_lifetimes.md` | 补充 `Generic Associated Types (GATs)` 中的生命周期使用 | Phase 3 | 📋 待补充 |
| `03_lifetimes.md` | 补充 `Pin<&'a mut T>` 的生命周期与自引用结构 | Phase 3 | 📋 待补充 |
| `03_lifetimes.md` | 补充 async/await 中的生命周期: `impl Future` + `Pin` | Phase 3 | 📋 待补充 |
| `04_type_system.md` | 补充 `impl Trait` 与 `dyn Trait` 的类型论差异 | Phase 2 | 📋 待补充 |

### L2 进阶概念层

| 文件 | TODO 内容 | 预计阶段 | 状态 |
|:---|:---|:---|:---|
| `01_traits.md` | 补充 `Specialization`（特化）的完整分析 | Phase 3 | 📋 待补充 |
| `01_traits.md` | 补充 `Generic Associated Types (GATs)` | Phase 3 | 📋 待补充 |
| `01_traits.md` | 补充 Auto trait 的自动推导机制（Send/Sync 判定规则） | Phase 2 | 📋 待补充 |
| `03_memory_management.md` | 补充 `MaybeUninit<T>` 的内存安全边界 | Phase 3 | 📋 待补充 |
| `03_memory_management.md` | 补充 `Pin<&mut T>` 的堆内存语义 | Phase 3 | 📋 待补充 |
| `04_error_handling.md` | 补充 `poll_fn` / `TryFuture` 等异步错误处理 | Phase 3 | 📋 待补充 |

### L3 高级概念层

| 文件 | TODO 内容 | 预计阶段 | 状态 |
|:---|:---|:---|:---|
| `01_concurrency.md` | 补充 `tokio::sync`（RwLock、Semaphore、Barrier） | Phase 3 | 📋 待补充 |
| `01_concurrency.md` | 补充 `std::sync::atomic` 内存序（Relaxed/Acquire/Release/SeqCst） | Phase 3 | 📋 待补充 |
| `01_concurrency.md` | 补充 Send/Sync 的 unsafe impl 规范与责任 | Phase 3 | 📋 待补充 |
| `02_async.md` | 补充 `async trait`（AFIT / RPITIT）的当前方案 | Phase 3 | 📋 待补充 |
| `02_async.md` | 补充 `async fn` 在 trait 中的生命周期问题 | Phase 3 | 📋 待补充 |
| `03_unsafe.md` | 补充 FFI 完整规范（ABI、layout、calling convention） | Phase 3 | 📋 待补充 |
| `03_unsafe.md` | 补充 `#[repr(C)]` / `#[repr(transparent)]` / `#[repr(packed)]` | Phase 3 | 📋 待补充 |

### L4-L7 其他

| 文件 | TODO 内容 | 预计阶段 | 状态 |
|:---|:---|:---|:---|
| `01_linear_logic.md` | 补充线性逻辑的 sequent calculus 完整规则集 | Phase 3 | 📋 待补充 |
| `01_linear_logic.md` | 补充 Phase semantics 与 Rust 的直观联系 | Phase 3 | 📋 待补充 |
| `02_type_theory.md` | 补充 Dependent type 与 Const Generics 的关系 | Phase 3 | 📋 待补充 |
| `02_type_theory.md` | 补充 Higher-Kinded Types 的缺失与 workaround | Phase 3 | 📋 待补充 |
| `03_ownership_formal.md` | 补充 Tree Borrows / Stacked Borrows 内存模型 | Phase 3 | 📋 待补充 |
| `03_ownership_formal.md` | 补充 Creusot/Verus 的功能正确性验证示例 | Phase 3 | 📋 待补充 |
| `04_rustbelt.md` | 补充各工具的具体代码示例 | Phase 3 | 📋 待补充 |
| `04_rustbelt.md` | 补充验证工具与 CI/CD 的集成 | Phase 4 | 📋 待补充 |

---

## 二、中优先级 TODO

| 文件 | TODO 内容 | 预计阶段 |
|:---|:---|:---|
| `01_ownership.md` | 补充 `Drop` 的 `std::mem::forget` 边界分析 | Phase 2 |
| `01_ownership.md` | 补充 `ManuallyDrop` 和 `MaybeUninit` 的所有权例外 | Phase 2 |
| `02_borrowing.md` | 补充 `Deref` / `DerefMut` 与自动借用的交互 | Phase 2 |
| `02_borrowing.md` | 补充 `AsRef` / `AsMut` 的借用语义差异 | Phase 2 |
| `03_lifetimes.md` | 补充 Lifetime Elision 的三条规则的完整形式化描述 | Phase 1 |
| `03_lifetimes.md` | 补充 `impl Trait` 与生命周期推断的交互 | Phase 2 |
| `04_type_system.md` | 补充 `!` (Never type) 的形式化分析 | Phase 1 |
| `04_type_system.md` | 补充 Const Generics（常量泛型）的类型系统扩展 | Phase 2 |
| `04_type_system.md` | 补充 Zero-sized types (ZST) 和 PhantomData | Phase 2 |
| `04_type_system.md` | 补充 Discriminant 和内存布局的底层分析 | Phase 3 |
| `02_generics.md` | 补充 Const Generics 的进阶用法（表达式、where 约束） | Phase 2 |
| `02_generics.md` | 补充 `impl Trait` 在返回位置 vs 参数位置的区别 | Phase 2 |
| `03_memory_management.md` | 补充自定义 Allocator（`#[global_allocator]`） | Phase 3 |
| `03_memory_management.md` | 补充 `ManuallyDrop<T>` 与 `mem::forget` 的形式化分析 | Phase 3 |
| `03_memory_management.md` | 补充 `Vec<T>` / `String` / `HashMap` 的内存布局与扩容策略 | Phase 2 |
| `04_error_handling.md` | 补充 `std::backtrace::Backtrace` 与错误追踪 | Phase 3 |
| `04_error_handling.md` | 补充 `Termination` trait 与 main 返回 Result | Phase 2 |
| `04_error_handling.md` | 补充 `Result<T, !>` 与 `!` (never type) 在错误处理中的使用 | Phase 3 |

---

## 三、低优先级 TODO

| 文件 | TODO 内容 | 预计阶段 |
|:---|:---|:---|
| `01_ownership.md` | 补充与 C++ `unique_ptr` 的深度对比示例 | Phase 3 |
| `02_borrowing.md` | 补充 `Cow<T>`（Clone on Write）的借用-所有权混合模式 | Phase 2 |
| `03_lifetimes.md` | 补充 `union` 的类型安全边界 | Phase 3 |
| `04_type_system.md` | 补充 Type Inference 的 HM 算法完整规则 | Phase 3 |
| `02_generics.md` | 补充 `min_specialization` 的当前状态与使用 | Phase 3 |
| `02_generics.md` | 补充泛型代码的编译时间优化策略 | Phase 4 |
| `02_generics.md` | 补充 Type-level programming（Peano arithmetic、typenum） | Phase 4 |
| `01_traits.md` | 补充 `const_trait` / `~const` 实验特性 | Phase 4 |
| `01_traits.md` | 补充 `#[fundamental]` attribute 与 Orphan Rule 例外 | Phase 4 |
| `03_memory_management.md` | 补充 `std::alloc::System` vs `jemalloc` vs `mimalloc` 对比 | Phase 4 |
| `04_error_handling.md` | 补充 `eyre` / `color-eyre` 等生态库的对比 | Phase 4 |
| `04_error_handling.md` | 补充 `#[track_caller]` 与错误定位优化 | Phase 4 |
| `04_macros.md` | 补充 `proc_macro2` 与 `syn` / `quote` crate 的最佳实践 | Phase 3 |
| `04_macros.md` | 补充编译期计算（`const fn` + `const generics`）替代宏的趋势 | Phase 3 |
| `04_macros.md` | 补充 `const_macro` / `concat!` / `stringify!` 等内置宏 | Phase 4 |
| `04_macros.md` | 补充属性宏修改函数体的完整示例 | Phase 3 |
| `01_concurrency.md` | 补充 `crossbeam` 生态 | Phase 3 |
| `01_concurrency.md` | 补充 `rayon` 数据并行 | Phase 3 |
| `01_concurrency.md` | 补充 `parking_lot` 与标准库锁的对比 | Phase 4 |
| `02_async.md` | 补充 Waker/Context 的底层机制 | Phase 3 |
| `02_async.md` | 补充 `Stream` / `Sink` trait 完整分析 | Phase 3 |
| `02_async.md` | 补充 `Pin<Box<dyn Future>>` vs `impl Future` 的性能差异 | Phase 4 |
| `02_async.md` | 补充 `loom` 并发模型检测工具 | Phase 4 |
| `03_unsafe.md` | 补充 Miri 的使用方法与限制 | Phase 3 |
| `03_unsafe.md` | 补充 `std::ptr::read/write` vs `*ptr` 解引用的区别 | Phase 2 |
| `03_unsafe.md` | 补充 `NonNull<T>` / `Unique<T>` / `Shared<T>` 的演进 | Phase 4 |
| `03_unsafe.md` | 补充 `MaybeUninit` 数组初始化模式 | Phase 3 |
| `01_toolchain.md` | 补充 Workspace 高级用法 | Phase 3 |
| `01_toolchain.md` | 补充 Features 与条件编译 | Phase 3 |
| `01_toolchain.md` | 补充 Cross-compilation 配置 | Phase 3 |
| `02_patterns.md` | 补充更多模式（Command、Observer、State Machine） | Phase 3 |
| `02_patterns.md` | 补充反模式（Over-engineering、Premature abstraction） | Phase 3 |
| `01_ai_integration.md` | 补充具体 AI+Rust 工具（Kiro, Copilot, Codeium） | Phase 3 |
| `01_ai_integration.md` | 补充 "RL on compiler errors" 研究 | Phase 3 |
| `02_formal_methods.md` | 补充具体 TLA+ 规约示例 | Phase 3 |
| `02_formal_methods.md` | 补充 CI/CD 集成方案 | Phase 3 |
| `03_evolution.md` | 补充每个 edition 的完整变更清单 | Phase 3 |
| `03_evolution.md` | 补充不稳定特性的 nightly 使用指南 | Phase 3 |

---

## 四、质量审计检查清单

### 4.1 已完成的门禁检查

- [x] 所有核心概念文件（L1-L3）包含 ≥2 种思维表征方式
- [x] 所有核心概念文件包含 ≥1 正确示例 + ≥1 反例
- [x] 所有文件包含来源标注
- [x] 所有文件包含 TODO 和演进方向
- [x] 文件夹结构完整（L0-L7）
- [x] 各层级 README 索引完整

### 4.2 已完成的门禁检查（v1.1 关系审计）

- [x] 跨层关系图谱构建 (`inter_layer_map.md`)
- [x] 全局概念索引构建 (`concept_index.md`)
- [x] 各层 README 关系图更新
- [x] L1-L4 定理一致性矩阵补充
- [x] L1-L4 反命题树补充
- [x] L1-L4 认知路径补充
- [x] L5-L7 关系映射补充
- [x] 跨文件链接密度 ≥3 个外链/文件

### 4.3 待完成的门禁检查

- [ ] 来源标注率 ≥85% 的论断（需抽样审计）
- [ ] Wikipedia 引用覆盖率 100%（核心概念）
- [ ] 国际课程引用覆盖率 100%（核心概念）
- [ ] 学术论文引用覆盖率 100%（L1-L4）
- [ ] 高优先级 TODO 完成率 ≥50%
- [ ] L4-L7 文件内容深度达到 L1-L3 的 60%

---

## 五、v1.1 权威来源对齐任务清单

### Wave 1: 元信息层（已完成）

- [x] 扩展 `sources.md` —— 新增 Wikipedia 词条、国际课程、学术论文

### Wave 2: L3 权威来源补充（进行中）

- [ ] `03_advanced/02_async.md` —— 补充 Wikipedia、CMU 17-350、PLDI 论文
- [ ] `03_advanced/03_unsafe.md` —— 补充 Wikipedia、Rustonomicon、Miri 论文
- [ ] `03_advanced/04_macros.md` —— 补充 Wikipedia、CMU 17-363、Hygienic Macros
- [ ] `03_advanced/01_concurrency.md` —— 补充 Stanford CS340R、RustBelt CSL

### Wave 3: L5-L7 深度扩展（待开始）

- [ ] `05_comparative/02_rust_vs_go.md` —— 扩展至 400+ 行
- [ ] `05_comparative/03_paradigm_matrix.md` —— 扩展至 350+ 行
- [ ] `06_ecosystem/01_toolchain.md` —— 扩展至 300+ 行
- [ ] `06_ecosystem/02_patterns.md` —— 扩展至 300+ 行
- [ ] `07_future/01_ai_integration.md` —— 扩展至 250+ 行
- [ ] `07_future/02_formal_methods.md` —— 扩展至 250+ 行
- [ ] `07_future/03_evolution.md` —— 扩展至 250+ 行

### Wave 4: L2-L4 精细化增强（待开始）

- [ ] `02_intermediate/01_traits.md` —— CMU 17-363 traits、Type Class 论文
- [ ] `02_intermediate/02_generics.md` —— System F 论文、Const Generics RFC
- [ ] `04_formal/01_linear_logic.md` —— 扩展至 450+ 行
- [ ] `04_formal/02_type_theory.md` —— 扩展至 400+ 行
- [ ] `04_formal/03_ownership_formal.md` —— 扩展至 350+ 行
- [ ] `04_formal/04_rustbelt.md` —— 扩展至 350+ 行

## 六、下一步推进建议

1. **当前（进行中）**: Wave 2 —— L3 权威来源对齐
2. **短期（1-2 周）**: Wave 3 —— L5-L7 深度扩展
3. **中期（2-3 周）**: Wave 4 —— L2-L4 精细化 + 高优先级 TODO
4. **长期（季度）**: 完成中优先级 TODO，来源标注审计
