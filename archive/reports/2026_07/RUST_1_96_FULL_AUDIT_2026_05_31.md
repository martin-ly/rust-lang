# Rust 1.96.0 全量特性梳理与项目覆盖审计报告

> **审计日期**: 2026-05-31
> **审计基准**: Rust 1.96.0 stable (2026-05-28) / Edition 2024
> **官方来源**: [releases.rs/docs/1.96.0](https://releases.rs/docs/1.96.0/) · [GitHub rust-lang/rust #156512](https://github.com/rust-lang/rust/issues/156512)
> **审计方法**: 官方 Release Notes 逐条 ↔ 项目全量文件扫描对比

---

## 一、官方 1.96.0 特性全量清单

### 1.1 语言特性 (Language)

| # | 特性 | 说明 | 重要性 |
|:---:|:---|:---|:---:|
| L1 | `expr` metavariable → `cfg` | 宏中 `expr` 类型参数可传递给 `#[cfg(...)]` | 🟡 中 |
| L2 | Never type tuple coercion | `!` 在 tuple 表达式中始终自动 coercion | 🟡 中 |
| L3 | `ManuallyDrop` 常量模式 | 修复 1.94 回归，允许 `ManuallyDrop` 常量作为 match 模式 | 🟢 低 |
| L4 | s390x vector registers inline asm | s390x 架构向量寄存器内联汇编支持 | 🔴 高* |
| L5 | 函数参数推断修复 | 避免罕见场景下的错误推断引导 | 🟢 低 |

> *L4 重要性高是因为这是特定平台（IBM Z/s390x）的关键基础设施升级，影响企业级部署。

### 1.2 标准库 API (Libraries)

| # | API | 模块 | 重要性 |
|:---:|:---|:---|:---:|
| S1 | `assert_matches!` / `debug_assert_matches!` | `std::assert_matches` | 🔴 高 |
| S2 | `core::range::Range` | `core::range` | 🔴 高 |
| S3 | `core::range::RangeFrom` | `core::range` | 🔴 高 |
| S4 | `core::range::RangeToInclusive` | `core::range` | 🔴 高 |
| S5 | `core::range::RangeIter` / `RangeFromIter` / `RangeToInclusiveIter` | `core::range` | 🔴 高 |
| S6 | `From<T>` for `LazyCell<T, F>` | `std::cell` | 🟡 中 |
| S7 | `From<T>` for `LazyLock<T, F>` | `std::sync` | 🟡 中 |
| S8 | `From<T>` for `AssertUnwindSafe<T>` | `std::panic` | 🟡 中 |
| S9 | `NonZero` 范围迭代 (`Step`) | `core::num` | 🟡 中 |
| S10 | "valid for read/write" 定义重构 | `ptr` 方法文档 | 🟢 低 |
| S11 | SGX `ToSocketAddr` 修复 | `std::net` | 🟢 低 |

### 1.3 编译器改进 (Compiler)

| # | 改进 | 说明 | 重要性 |
|:---:|:---|:---|:---:|
| C1 | LoongArch Linux link relaxation | 龙芯架构链接松弛优化 | 🟡 中 |
| C2 | `riscv64gc-unknown-fuchsia` RVA22 + vector | RISC-V Fuchsia 目标基线提升 | 🟡 中 |

### 1.4 Cargo 变更

| # | 特性 | 说明 | 重要性 |
|:---:|:---|:---|:---:|
| CA1 | Git + alternate registry 共存 | 依赖可同时指定 git 和 registry | 🟡 中 |
| CA2 | `target.'cfg(..)'.rustdocflags` | 按目标条件配置 rustdoc 标志 | 🟡 中 |
| CA3 | CVE-2026-5222 修复 | sparse registry URL 规范化错误 | 🔴 高 |
| CA4 | CVE-2026-5223 修复 | tarball symlink 缓存覆盖 | 🔴 高 |

### 1.5 Rustdoc 改进

| # | 改进 | 说明 | 重要性 |
|:---:|:---|:---|:---:|
| R1 | Deprecation notes rendering | 弃用说明渲染方式变更（更 predictable） | 🟢 低 |
| R2 | `missing_doc_code_examples` lint | 不在 impl items 上触发 | 🟢 低 |
| R3 | Sidebar 分离 | 方法和关联函数在侧边栏分开显示 | 🟢 低 |

### 1.6 兼容性注意 (Compatibility Notes)

| # | 变更 | 影响 |
|:---:|:---|:---|
| CP1 | `#[repr(Int)]` enum layout 修复 | uninhabited ZST 字段边缘情况 |
| CP2 | 禁止 `Pin<Foo>` unsize-coerce | Foo 不实现 `Deref` 时 |
| CP3 | `#![reexport_test_harness_main]` gate | 意外稳定属性的限制 |
| CP4 | RPITIT 类型过严报错 | 过于私有的返回类型 |
| CP5 | `uninhabited_static` deny-by-default | 依赖项中 static uninhabited 类型 |
| CP6 | windows-gnu 非分割 debuginfo | 改善 backtrace 质量 |
| CP7 | 移除 `-Csoft-float` | 改用 `target-feature` |
| CP8 | `use S::{self as Other}` 禁止 | `{self}` 要求模块父级 |
| CP9 | 重复属性首项优先 | `export_name`/`link_name`/`link_section` |
| CP10 | 最低外部 LLVM 升至 21 | 构建 rustc 的 LLVM 要求 |
| CP11 | `avr` 目标 `c_double` 为 `f32` | 匹配 AVR 上 C 的 double 宽度 |
| CP12 | WASM `--allow-undefined` 移除 | wasm-ld 链接器行为变更 |

### 1.7 内部变更 (Internal)

| # | 变更 | 说明 |
|:---:|:---|:---|
| I1 | JSON targets aarch64 softfloat | 需要 `rustc_abi` 设置为 `"softfloat"` |
| I2 | target specs stricter checks | LLVM ABI 值更严格检查 |

---

## 二、项目覆盖矩阵（逐项对比）

### 2.1 语言特性覆盖

| 特性 | 概念文档 | Crate 代码 | 练习 | 测试 | 状态 |
|:---|:---|:---:|:---:|:---:|:---:|
| L1 `expr` → `cfg` | `concept/03_advanced/04_macros.md` | `c11_macro_system_proc` | ❌ | ✅ | 🟢 完成 |
| L2 Never type coercion | `concept/01_foundation/05_never_type.md` | `c02_type_system` | ❌ | ✅ | 🟢 完成 |
| L3 `ManuallyDrop` 模式 | `concept/02_intermediate/03_memory_management.md` | `c02_type_system` | ✅ | ✅ | 🟢 完成 |
| L4 s390x inline asm | `docs/06_toolchain/06_19_rust_1_96_features.md` (提及) | ❌ | ❌ | — | 🟡 概念文档 |
| L5 函数参数推断修复 | ❌ | ❌ | ❌ | — | 🔴 **缺失** |

### 2.2 标准库 API 覆盖

| 特性 | 概念文档 | Crate 代码 | 练习 | 测试 | 状态 |
|:---|:---|:---:|:---:|:---:|:---:|
| S1 `assert_matches!` | `concept/02_intermediate/05_assert_matches.md` | `c02_type_system` + 13 crates | ✅ | ✅ | 🟢 完成 |
| S2-5 `core::range::*` | `concept/02_intermediate/06_range_types.md` | `c02_type_system` + 多 crates | ✅ | ✅ | 🟢 完成 |
| S6-8 `From<T>` for cell types | `concept/02_intermediate/08_interior_mutability.md` | `c02_type_system` + 多 crates | ✅ | ✅ | 🟢 完成 |
| S9 `NonZero` 迭代 | `concept/02_intermediate/06_range_types.md` | `c02_type_system` | ❌ | ✅ | 🟡 缺练习 |
| S10 "valid for read/write" | ❌ | ❌ | ❌ | — | 🔴 **缺失** |
| S11 SGX `ToSocketAddr` | ❌ | ❌ | ❌ | — | 🔴 **缺失** |

### 2.3 编译器改进覆盖

| 特性 | 概念文档 | 状态 |
|:---|:---|:---:|
| C1 LoongArch link relaxation | `docs/06_toolchain/06_19_rust_1_96_features.md` 列表 | 🟡 仅列表 |
| C2 RISC-V Fuchsia RVA22 | `docs/06_toolchain/06_19_rust_1_96_features.md` 列表 | 🟡 仅列表 |

### 2.4 Cargo 变更覆盖

| 特性 | 概念文档 | 配置示例 | 状态 |
|:---|:---|:---:|:---:|
| CA1 Git + registry 共存 | `docs/06_toolchain/06_19_rust_1_96_features.md` | ✅ TOML 示例 | 🟢 完成 |
| CA2 `target.cfg.rustdocflags` | `docs/06_toolchain/06_19_rust_1_96_features.md` | ✅ TOML 示例 | 🟢 完成 |
| CA3-4 CVE-2026-5222/5223 | `concept/07_future/05_rust_version_tracking.md` | — | 🟢 完成 |

### 2.5 Rustdoc 改进覆盖

| 特性 | 概念文档 | 状态 |
|:---|:---|:---:|
| R1 Deprecation notes rendering | ❌ | 🔴 **缺失** |
| R2 `missing_doc_code_examples` lint | ❌ | 🔴 **缺失** |
| R3 Sidebar 分离 | ❌ | 🔴 **缺失** |

### 2.6 兼容性注意覆盖

| 特性 | 概念文档 | 状态 |
|:---|:---|:---:|
| CP1 `#[repr(Int)]` enum layout | `docs/06_toolchain/06_19_rust_1_96_features.md` 列表 | 🟡 列表 |
| CP2 `Pin<Foo>` unsize-coerce | `docs/06_toolchain/06_19_rust_1_96_features.md` 列表 | 🟡 列表 |
| CP3 `reexport_test_harness_main` | `docs/06_toolchain/06_19_rust_1_96_features.md` 列表 | 🟡 列表 |
| CP4 RPITIT 隐私报错 | `docs/06_toolchain/06_19_rust_1_96_features.md` 列表 | 🟡 列表 |
| CP5 `uninhabited_static` lint | `docs/06_toolchain/06_19_rust_1_96_features.md` 列表 | 🟡 列表 |
| CP6 windows-gnu debuginfo | `docs/06_toolchain/06_19_rust_1_96_features.md` 列表 | 🟡 列表 |
| CP7 移除 `-Csoft-float` | `docs/06_toolchain/06_19_rust_1_96_features.md` 列表 | 🟡 列表 |
| CP8 `use S::{self as Other}` | `docs/06_toolchain/06_19_rust_1_96_features.md` 列表 | 🟡 列表 |
| CP9 重复属性首项优先 | `docs/06_toolchain/06_19_rust_1_96_features.md` 列表 | 🟡 列表 |
| CP10 最低 LLVM 21 | `docs/06_toolchain/06_19_rust_1_96_features.md` 列表 | 🟡 列表 |
| CP11 `avr` `c_double` | `docs/06_toolchain/06_19_rust_1_96_features.md` 列表 | 🟡 列表 |
| CP12 WASM `--allow-undefined` | `c12_wasm/src/rust_196_features.rs` + 文档 | 🟢 完成 |

### 2.7 内部变更覆盖

| 特性 | 概念文档 | 状态 |
|:---|:---|:---:|
| I1 JSON targets aarch64 softfloat | ❌ | 🔴 **缺失** |
| I2 target specs stricter checks | ❌ | 🔴 **缺失** |

---

## 三、缺失项汇总与优先级评估

### 🔴 高优先级缺失（建议补充）

| # | 缺失项 | 缺失位置 | 建议补充方式 | 工时 |
|:---:|:---|:---|:---|:---:|
| 1 | rustdoc 改进（R1-R3） | docs/ 或 concept/06_ecosystem/14_documentation.md | 在文档工具链文档中新增 "Rustdoc 1.96 改进" 小节 | 2h |
| 2 | `NonZero` 范围迭代练习 | `exercises/src/rust_196_feature_exercises.rs` | 添加 `NonZeroRangeExercises` 结构体和 2-3 道练习 | 2h |
| 3 | `From<T>` for `AssertUnwindSafe` 练习 | `exercises/src/rust_196_feature_exercises.rs` | 添加 `AssertUnwindSafeExercises` 结构体 | 1h |

### 🟡 中优先级缺失（可选补充）

| # | 缺失项 | 建议补充方式 | 工时 |
|:---:|:---|:---|:---:|
| 4 | s390x inline asm 深度文档 | 在 `concept/06_ecosystem/17_cross_compilation.md` 中补充 IBM Z 架构说明 | 2h |
| 5 | "valid for read/write" 定义重构 | 在 `concept/03_advanced/03_unsafe.md` 中补充 ptr 方法安全契约说明 | 1h |
| 6 | 内部变更（I1-I2） | 在 `concept/06_ecosystem/45_compiler_internals.md` 中补充目标规格说明 | 1h |

### 🟢 低优先级缺失（可暂不处理）

| # | 缺失项 | 理由 |
|:---:|:---|:---|
| 7 | 函数参数推断修复（L5） | 内部编译器修复，无用户可见 API 变更 |
| 8 | SGX `ToSocketAddr` 修复（S11） | SGX 平台特定，受众极窄 |
| 9 | 编译器改进 C1-C2 的深度文档 | 平台特定基础设施，列表形式已足够 |

---

## 四、项目现有 1.96 文档/代码/练习资产清单

### 文档资产

| 文件 | 类型 | 行数 | 内容 |
|:---|:---|:---:|:---|
| `docs/06_toolchain/06_19_rust_1_96_features.md` | 工具链全景 | 296 | 语言特性 + 标准库 API + Cargo + 编译器 + 兼容性注意 |
| `knowledge/06_ecosystem/emerging/05_rust_1_96.md` | 知识层文档 | 249 | 语言特性 + 标准库 + Cargo + 兼容性注意 |
| `docs/02_reference/quick_reference/02_rust_196_features_cheatsheet.md` | 速查表 | 394 | if let guards + Range + Lints + 模板（含 1.95 回顾） |
| `concept/02_intermediate/05_assert_matches.md` | 概念文档 | ~200 | `assert_matches!` 深度解释 |
| `concept/02_intermediate/06_range_types.md` | 概念文档 | ~300 | `core::range` 类型族深度解释 |
| `reports/RUST_1_96_COMPREHENSIVE_REPORT.md` | 审计报告 | 254 | 升级报告 + 覆盖矩阵 |
| `docs/00_meta/00_rust_196_upgrade_plan.md` | 升级计划 | 112 | Cargo.toml/CI 升级检查表 |
| `docs/06_toolchain/06_toml_v11_cargo_guide.md` | 指南 | 260+ | TOML v1.1 in Cargo |

### Crate 代码资产

| Crate | 文件 | 1.96 特性覆盖 |
|:---|:---|:---|
| `c01_ownership_borrow_scope` | `rust_196_features.rs` | ManuallyDrop 模式、AssertUnwindSafe From、core::range Copy |
| `c02_type_system` | `rust_196_features.rs` | assert_matches!、core::range 完整类型族、NonZero 迭代、From for cell types、Never type coercion |
| `c03_control_fn` | `rust_196_features.rs` | assert_matches!、core::range |
| `c04_generic` | `rust_196_features.rs` | LazyLock/LazyCell From、core::range、assert_matches! |
| `c05_threads` | `rust_196_features.rs` | core::range、assert_matches!、LazyLock From、AssertUnwindSafe From |
| `c06_async` | `rust_196_features.rs` | core::range、assert_matches!、LazyLock From |
| `c07_process` | `rust_196_features.rs` | LazyLock/LazyCell From、assert_matches!、core::range |
| `c08_algorithms` | `rust_196_features.rs` | RangeInclusive、RangeToInclusive |
| `c09_design_pattern` | `rust_196_features.rs` | LazyLock From、assert_matches!、ManuallyDrop 模式 |
| `c10_networks` | `rust_196_features.rs` | core::range、assert_matches!、LazyLock From |
| `c11_macro_system_proc` | `rust_196_features.rs` | expr → cfg、assert_matches!、core::range、ManuallyDrop |
| `c11_macro_system_proc` | `rust_196_features.rs` | assert_matches!、LazyLock From、Never type coercion |
| `c12_wasm` | `rust_196_features.rs` | WASM --allow-undefined 移除、core::range、assert_matches!、LazyLock From |
| `c13_embedded` | `rust_196_features.rs` | core::range (no_std)、ManuallyDrop (no_std)、assert_matches! (no_std) |
| `common` | `rust_196_features.rs` | 全特性参考实现 |

### 练习资产

| 练习模块 | 文件 | 1.96 特性 |
|:---|:---|:---|
| `AssertMatchesExercises` | `exercises/src/rust_196_feature_exercises.rs` | assert_matches! 3 题 |
| `CoreRangeExercises` | `exercises/src/rust_196_feature_exercises.rs` | core::range 3 题 |
| `LazyCellLazyLockExercises` | `exercises/src/rust_196_feature_exercises.rs` | LazyCell/LazyLock From 1 题 |
| `ManuallyDropPatternExercises` | `exercises/src/rust_196_feature_exercises.rs` | ManuallyDrop 模式 1 题 |

**注意**: `exercises/src/rust_196_feature_exercises.rs` 中还包含 `GenBlockExercises`（nightly-only）、`ConstVecDequeExercises`（1.68）、`BoolToFloatExercises`（1.68）、`ConstNonNullExercises`（历史特性），这些是历史复习内容，**不属于 1.96 stable 新特性**。

---

## 五、总结与建议

### 覆盖度统计

| 维度 | 官方特性数 | 已覆盖 | 缺失 | 覆盖率 |
|:---|:---:|:---:|:---:|:---:|
| 语言特性 | 5 | 4 | 1 | 80% |
| 标准库 API | 11 | 9 | 2 | 82% |
| 编译器改进 | 2 | 2 (列表) | 0 | 100% |
| Cargo 变更 | 4 | 4 | 0 | 100% |
| Rustdoc 改进 | 3 | 0 | 3 | 0% |
| 兼容性注意 | 12 | 12 (列表) | 0 | 100% |
| 内部变更 | 2 | 0 | 2 | 0% |
| **总计** | **39** | **31** | **8** | **79%** |

### 核心结论

1. **高价值特性已全部覆盖**：`assert_matches!`、`core::range`、LazyLock/LazyCell From、`ManuallyDrop` 模式、Never type coercion、expr → cfg 等核心语言和标准库特性，在概念文档、crate 代码和测试中均有完整覆盖。
2. **文档基础设施完善**：`docs/06_toolchain/06_19_rust_1_96_features.md`（296 行）和 `knowledge/06_ecosystem/emerging/05_rust_1_96.md`（249 行）已与官方 Release Notes 逐条核对，覆盖全面。
3. **练习覆盖有缺口**：`NonZero` 范围迭代和 `AssertUnwindSafe From` 缺少专门练习，但 crate 代码中包含示例。
4. **rustdoc 改进完全缺失**：3 项 rustdoc 改进在项目中无任何覆盖。建议补充。
5. **内部变更和平台特定修复缺失**：函数参数推断修复、SGX ToSocketAddr、JSON targets aarch64 softfloat、target specs stricter checks 等缺失。这些影响面窄，可暂不处理。

### 建议行动

若需进一步补全，建议按以下优先级执行（总计 ~8h）：

| 优先级 | 任务 | 工时 |
|:---:|:---|:---:|
| P1 | 补充 rustdoc 1.96 改进文档 | 2h |
| P2 | 补充 `NonZero` 范围迭代练习 | 2h |
| P3 | 补充 `AssertUnwindSafe From` 练习 | 1h |
| P4 | 补充 s390x inline asm 说明 | 2h |
| P5 | 补充 "valid for read/write" 说明 | 1h |

---

> **审计者**: 自动化扫描 + 人工核对
> **审计日期**: 2026-05-31
> **对应 Rust 版本**: 1.96.0 stable (Edition 2024)
> **状态**: ✅ 全量梳理完成
