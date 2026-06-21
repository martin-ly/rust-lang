# 编译器 & Cargo 分层知识补齐路线图

> **日期**: 2026-06-21  
> **对齐权威来源**: [Rustc Dev Guide](https://rustc-dev-guide.rust-lang.org/)、[Cargo Book](https://doc.rust-lang.org/cargo/)  
> **目标**: 将 `rustc` 与 Cargo 的知识从“综述级”下沉到“分层可教学”，覆盖从使用到原理的完整路径。

---

## 一、现状诊断

### 1.1 已有优势
- `concept/06_ecosystem/45_compiler_internals.md` 提供了全流水线鸟瞰图。
- `concept/06_ecosystem/01_toolchain.md` 覆盖了 Cargo 工作区、features、resolver、profiles 等实用主题。
- `concept/04_formal/08_type_inference.md` 与 `concept/03_advanced/08_nll_and_polonius.md` 在形式化层面较强。

### 1.2 关键缺口
| 维度 | 缺口 |
|:---|:---|
| 编译器 | Query System、增量编译、Name Resolution、Trait Solver、rustc driver、诊断基础设施、编译器测试/UI tests、Bootstrap 等缺少独立概念文件。 |
| Cargo | Build Scripts、Dependency Resolution、Registries/Publishing、Source Replacement、Cargo Lints、Authentication/Cache 等缺少独立概念文件。 |
| 版本 | 部分文件仍引用 Rust 1.90/LLVM 18，需更新到 1.96/LLVM 21。 |

---

## 二、编译器分层知识计划

### L1：流水线与 IR（已较好覆盖，待细化）
- `45_compiler_internals.md` 增强：补充 AST→HIR→THIR→MIR→LLVM 每层的输入输出示例。
- 新增 `concept/04_formal/19_rustc_query_system.md` ✅ **已完成**（Query System + 增量编译）。

### L2：关键分析阶段
| 优先级 | 文件 | 主题 | 权威来源 |
|:---:|:---|:---|:---|
| P0 | `concept/04_formal/25_name_resolution_and_hir.md` | Name resolution、macro hygiene、AST→HIR lowering | Rustc Dev Guide HIR / Name Resolution |
| P0 | `concept/04_formal/26_trait_solver_in_rustc.md` | Fulfillment/select、new solver、coinduction | Rustc Dev Guide Trait Resolution |
| P1 | `concept/04_formal/27_type_checking_and_inference.md` | `typeck` query、`Ty<'tcx>`、约束生成 | Rustc Dev Guide Type Inference |

### L3：代码生成与后端
| 优先级 | 文件 | 主题 | 权威来源 |
|:---:|:---|:---|:---|
| P1 | `concept/06_ecosystem/46_llvm_backend_and_codegen.md` | MIR→LLVM IR、codegen units、target specs | Rustc Dev Guide Codegen |
| P1 | `concept/06_ecosystem/48_rustc_driver_and_stable_mir.md` | rustc driver API、Stable MIR、自定义工具 | Rustc Dev Guide rustc_driver / Stable MIR |
| P2 | `concept/06_ecosystem/49_compiler_diagnostics_and_ui_tests.md` | Diagnostic structs、error codes、UI tests/bless | Rustc Dev Guide Errors and Lints |

### L4：基础设施
| 优先级 | 文件 | 主题 | 权威来源 |
|:---:|:---|:---|:---|
| P2 | `concept/06_ecosystem/50_rustc_bootstrap.md` | 编译器自举、`x.py`、stage0/stage1/stage2 | Rustc Dev Guide Bootstrap |
| P2 | `concept/06_ecosystem/51_compiler_testing.md` | UI tests、compile-fail tests、Miri tests | Rustc Dev Guide Tests |

---

## 三、Cargo 分层知识计划

### L1：Cargo 基础（已覆盖）
- `01_toolchain.md` 继续作为入口；将过长章节拆出。

### L2：依赖与解析
| 优先级 | 文件 | 主题 | 权威来源 |
|:---:|:---|:---|:---|
| P0 | `concept/06_ecosystem/59_cargo_build_scripts.md` ✅ **已完成** | `build.rs`、OUT_DIR、rerun-if-changed、链接原生库 | Cargo Book Build Scripts |
| P0 | `concept/06_ecosystem/60_cargo_dependency_resolution.md` | Resolver v2/v3、SAT/version selection、feature unification、`cargo tree` | Cargo Book Dependency Resolution |
| P1 | `concept/06_ecosystem/61_cargo_source_replacement.md` | `[source]`、vendoring、mirrors、`cargo vendor`、offline mode | Cargo Book Source Replacement |

### L3：Registry 与发布
| 优先级 | 文件 | 主题 | 权威来源 |
|:---:|:---|:---|:---|
| P0 | `concept/06_ecosystem/62_cargo_registries_and_publishing.md` | sparse/git index、`cargo publish`/`yank`、auth、private registries | Cargo Book Registries |
| P1 | `concept/06_ecosystem/63_cargo_authentication_and_cache.md` | credentials、tokens、`CARGO_HOME`、cache layout | Cargo Book Registry Authentication |
| P1 | `concept/06_ecosystem/64_cargo_manifest_reference.md` | 完整 `Cargo.toml` 字段速查 | Cargo Book Manifest Format |

### L4：高级工具
| 优先级 | 文件 | 主题 | 权威来源 |
|:---:|:---|:---|:---|
| P1 | `concept/06_ecosystem/65_cargo_profiles_and_lints.md` | custom profiles、profile overrides、`cargo lints`、lints table | Cargo Book Profiles / Lints |
| P2 | `concept/06_ecosystem/66_cargo_subcommands_and_plugins.md` | 自定义 subcommand、`cargo-xxx` 生态 | Cargo Book External Tools |

---

## 四、即时修复项

1. **更新过时版本示例**
   - `docs/06_toolchain/01_compiler_features.md` 中的 `rustc 1.90.0 / LLVM 18.1.0` 示例需更新为 `rustc 1.96.0 / LLVM 21`。
2. **修正并行前端状态声明**
   - `concept/06_ecosystem/47_compiler_infrastructure.md` 中“1.96 默认启用”的表述需改为“nightly 实验性”。
3. **交叉引用旧 Cargo 研究笔记**
   - `docs/research_notes/10_cargo_194_features.md` 顶部增加指向新 Cargo 文档的提示，避免读者误当作当前指南。

---

## 五、建议执行顺序

1. **本周**：完成 P0 文件（Build Scripts ✅、Dependency Resolution、Name Resolution/HIR、Trait Solver、Registries/Publishing）。
2. **下周**：完成 P1 文件（Source Replacement、LLVM Backend、rustc Driver/Stable MIR、Authentication/Cache、Manifest Reference）。
3. **第三周**：完成 P2 文件（Diagnostics/UI Tests、Bootstrap、Compiler Testing、Cargo Subcommands/Plugins）。
4. **持续**：每次新增概念文件后，更新 `concept/SUMMARY.md` 与 `concept/00_meta/concept_index.md`。

---

## 六、质量检查清单

每个新文件必须包含：
- [ ] 中文标题 + EN title/summary
- [ ] Bloom 层级与受众标注
- [ ] 权威来源链接（Rustc Dev Guide / Cargo Book 官方页面）
- [ ] 至少一个可运行/可验证的代码或配置示例
- [ ] 至少一个 `compile_fail` 或错误边界示例
- [ ] 嵌入式测验 ≥ 3 题
- [ ] 与相邻概念文件的前置/后置链接
