# 权威覆盖扩展报告：content/ 与 crates/docs（2026-07-12）

> **EN**: Authority Coverage Extension — content/ & crates/docs
> **Summary**: Extends the international-authority alignment gate beyond concept/ to content/ (61 files, 100% coverage) and crates/*/docs/ (576 files, per-crate sampling baseline), plus clears two historical debts: `todo!()` placeholders and 「综述级」code-status badges.
>
> 触发：AGENTS.md §5.2 权威覆盖门（18）此前仅审计 `concept/`（any=100%）；本轮按任务书把国际权威对齐扩展到 `content/` 与 `crates/*/docs/`，并清理两处历史遗留（`todo!()` 占位符、「代码状态：综述级」徽标）。

---

## 一、任务 1：content/ 权威覆盖核查

### 1.1 覆盖率

- 扫描范围：`content/` 全部 **61 个** Markdown 文件（safety_critical 58 + ecosystem 3）。
- 口径：文件内含至少 1 个国际权威域外链（ISO/MISRA/ANSSI/Rust Foundation/Ferrocene/rust-lang 官方/docs.rs/学术论文/官方标准组织等，完整域清单见脚本复用 `scripts/maintenance/authority_coverage_dashboard.py` 分级）。
- **结果：61/61 = 100%**（修复前 57/61 = 93.4%）。

### 1.2 补齐动作（4 文件）

| 文件 | 动作 |
|---|---|
| `content/README.md` | 新增「国际权威来源参考」节：doc.rust-lang.org、spec.ferrocene.dev、Safety-Critical Rust Consortium |
| `content/ecosystem/README.md` | 新增「国际权威来源参考」节：tokio.rs、docs.rs/axum、async-book |
| `content/ecosystem/deep_dives/02_tokio_deep_dive.md` | 原有 tokio.rs ×2 + async-book 权威链接，无需补齐 |
| `content/ecosystem/deep_dives/01_axum_deep_dive.md` | 原有 tokio.rs、docs.rs/axum-test 权威链接，无需补齐 |

### 1.3 失效链接修复（92 条去重外链全部 curl 实测，7 处修复）

| 原链接 | 状态 | 修复为（实测 200） | 位置 |
|---|---|---|---|
| `https://ferrous-systems.com`（及 `/ferrocene`、`/training/` 路径） | 000 ERR | `https://www.ferrous-systems.com`（同路径） | 5 文件 10 处 |
| `https://github.com/rust-safety-critical/wg`（及 `/wiki`） | 404 | `https://github.com/rustfoundation/safety-critical-rust-consortium` | 2 文件 2 处 |
| `https://github.com/rust-spac` | 404 | `https://github.com/nasa/cFS`（NASA cFS 开源仓库） | 07_case_studies/02 |
| `https://github.com/autosar-rs` | 404 | `https://www.autosar.org/`（AUTOSAR 官方） | 07_case_studies/03 |
| `https://users.rust-embedded.org/` | 000 ERR（域名失效） | `https://github.com/rust-embedded` | 09_reference/03 |

**保留并记录为 known-broken（非权威来源性质）**：模板占位 URL（`yourorg/*`、`YOUR_USERNAME/*`、`git.company.com`、`internal.company.com`，均为示例代码块内的虚构地址）；bot 拦截类（`crates.io/`、`foundation.rust-lang.org` 403、`intel.com` 403、`reddit.com/r/rust` 超时）——浏览器可达，curl 被反爬拦截，不计为失效。

## 二、任务 2：crates/*/docs 权威覆盖抽样基线

### 2.1 方法

- 全量：19 个 crate、`crates/*/docs/` 共 **576 个** Markdown 文件。
- 抽样（脚本 `tmp/sample_crates_docs.py`，口径已固化）：每 crate 抽 `docs/README.md` + `00_master_index.md` + `tier_01_foundations/` 全部 + `tier_03_references/01_*` 首篇，共抽样 105 文件（其中 stub 占位页 54 个，按 AGENTS §2 归 stub 类，不要求国际权威外链）。
- 对抽样中**完全无权威来源**的非 stub 核心文档追加「国际权威来源」节（每文件 2 个链接，全部 curl 实测 200）。

### 2.2 每 crate 基线（抽样非 stub 覆盖率）

| crate | docs 总数 | 抽样（非 stub） | 修复前 | 修复后 |
|---|---:|---:|---:|---:|
| c01_ownership_borrow_scope | 57 | 2 | 0/2 | **2/2** |
| c02_type_system | 39 | 3 | 0/3 | **3/3** |
| c03_control_fn | 44 | 1 | 0/1 | **1/1** |
| c04_generic | 36 | 6 | 0/6 | **6/6** |
| c05_threads | 41 | 5 | 0/5 | **5/5** |
| c06_async | 44 | 9 | 0/9 | **9/9** |
| c07_process | 63 | 8 | 0/8 | **8/8** |
| c08_algorithms | 42 | 8 | 0/8 | **8/8** |
| c09_design_pattern | 47 | 3 | 0/3 | **3/3** |
| c10_networks | 46 | 2 | 1/2 | **2/2** |
| c11_macro_system_proc | 31 | 0（全 stub） | — | — |
| c12_wasm | 59 | 0（全 stub） | — | — |
| c13_embedded | 6 | 1 | 0/1 | **1/1** |
| c14_semantic_web | 1 | 0（stub） | — | — |
| c15_verification_tools | 1 | 1 | 0/1 | **1/1** |
| c16_gui | 1 | 1 | 0/1 | **1/1** |
| c17_resolver_v3_public_demo | 1 | 1 | 0/1 | **1/1** |
| common / integration_tests | 14 | 0（全 stub） | — | — |
| **合计** | **576** | **51** | **1/51 (2.0%)** | **51/51 (100%)** |

- 本轮共追加权威来源节 **50 个文件**（c10 有 1 个抽样文件原本已达标）。
- 全量覆盖率（含未抽样文件）：修复前 70/576 ≈ 12.2% → 修复后 120/576 ≈ **20.8%**。

### 2.3 后续轮次缺口清单（供基线追踪）

1. **tier_02_guides / tier_03_references / tier_04_advanced / tier_05_exercises 未抽样文件**（约 470 个）：多为 stub 或内容页混杂，下一轮应先按 stub/内容二分，再对内容页补齐。
2. **c11 / c12 抽样全为 stub**：两 crate 的 docs 内容主体在 `src/` 示例与 tier_02+ 深层目录，下一轮需单独评估其非 stub 内容页。
3. 抽样脚本与缺口 JSON 固化在 `tmp/crates_docs_authority_sample.json`（临时）——若转长期门禁，建议并入 `scripts/check_concept_authority_coverage.py` 的扫描域扩展。

## 三、任务 3：`todo!()` 占位符清理

定位：`grep -rn "todo!()" concept/`，正文代码块涉及 3 文件 8 处（另 `rust_1_98_preview.md` 表格、`00_meta/00_framework/todos.md` tracker、`06_ecosystem/03_design_patterns/02_idioms_spectrum.md` 测验题为文本提及，不计）。

| 文件 | 处数 | 裁定 | 处置 |
|---|---:|---|---|
| `02_intermediate/01_generics/02_const_generics.md:59` | 1 | **遗留占位** | 补全为可编译实现（`swap` 手写反转），`rustc --edition 2024` 实测通过（含 assert 运行验证） |
| `02_intermediate/01_generics/02_const_generics.md:155,157` | 2 | 正当用法 | 整体注释掉的 stable 编译错误演示，函数体无从实现；加豁免注释说明 |
| `04_formal/00_type_theory/07_type_checking_and_inference.md:363-368` | 3 | 正当用法 | never type fallback 讲解正例（`todo!()` 类型为 `!` 正是教学对象）；加豁免注释 |
| `01_foundation/08_error_handling/03_panic_and_abort.md:88,350` | 2 | 正当用法 | 决策树/触发方式清单中讲解 `todo!()` 宏本身，保持原样 |

tracker（`concept/00_meta/00_framework/todos.md`）已同步更新两条状态。

## 四、任务 4：「代码状态：综述级」徽标处置

处置前 concept/ 现存 10 页「代码状态：综述级」类徽标（07-09 审计报告的 16 页中，6 页已于前轮改为「示例级 — 已补充代码」）。逐页抽取 ```rust 代码块以 `rustc 1.97.0 --edition 2024` 单文件实测（脚本 `tmp/compile_md_blocks.py`）：

| 文件 | 实测结果 | 裁定与徽标 |
|---|---|---|
| `07_future/03_preview_features/08_inline_const_pattern_preview.md` | 3/3 通过 | **已验证（rustc 1.97）** |
| `07_future/03_preview_features/13_lifetime_capture_preview.md` | 2/2 通过 | **已验证（rustc 1.97）** |
| `07_future/03_preview_features/07_stable_abi_preview.md` | 修复后 2/2 通过（`#[no_mangle]` → `#[unsafe(no_mangle)]`，Edition 2024 要求） | **已验证（rustc 1.97）** |
| `07_future/03_preview_features/15_rpitit_preview.md` | 修复后 4/4 通过（补显式生命周期 `'a`，原例在 2021/2024 edition 均编译失败） | **已验证（rustc 1.97）** |
| `07_future/03_preview_features/10_must_not_suspend_preview.md` | std 示例通过；tokio 示例为设计意图的 `compile_fail` 反例 | **已验证（rustc 1.97）**（注明反例块） |
| `07_future/03_preview_features/17_type_alias_impl_trait_preview.md` | TAIT 在 1.97 stable 未稳定（E0658） | **伪代码（示意）**（注明需 nightly） |
| `07_future/03_preview_features/19_const_trait_preview.md` | const trait 全部 rust,ignore（nightly 特性） | **伪代码（示意）**（注明需 nightly） |
| `07_future/03_preview_features/28_wasm_target_evolution.md` | 示例面向 wasm target/组件模型工具链 | **伪代码（示意）** |
| `07_future/03_preview_features/30_rust_in_space.md` | no_std 嵌入式示例（含 panic handler，host target 不可独立编译） | **伪代码（示意）** |
| `06_ecosystem/00_toolchain/08_platform_rust_integration.md` | 唯一可测块依赖 cxx proc-macro crate，已改标 `rust,ignore` | **伪代码（示意）** |

处置后 `grep "代码状态.*综述级" concept/` 命中 0。

## 五、质量门验证（2026-07-12 实跑）

| 检查 | 结果 |
|---|---|
| `python scripts/kb_auditor.py` | 死链 **0** ✅（跨层问题 1 个 warning，位于未触碰的 `03_advanced/01_async/02_async_advanced.md`，本轮前已存在） |
| `python scripts/check_canonical_uniqueness.py --strict` | exit **0**，无 ERROR（仅既有 W212 词干相似 warning） ✅ |
| `mdbook build` | 通过 ✅ |
| `python scripts/detect_content_overlap.py` | 仍仅既有 1 对（migration_197_decision_tree vs 21_rust_197_features_cheatsheet），未因本轮新增权威节恶化 ✅ |
| 新增外链 curl 实测 | content/ 修复 5 条 + crates docs 追加 24 个域全部 HTTP 200 ✅ |

## 六、变更文件清单

- `content/`：README.md、ecosystem/README.md + 7 个链接修复文件（共 9 文件）
- `crates/*/docs/`：50 个文件追加「国际权威来源」节（清单见 §2 与 `tmp/crates_docs_authority_sample.json`）
- `concept/`：10 个徽标处置文件 + 2 个 todo!() 处置文件 + `00_meta/00_framework/todos.md`（tracker 同步）

---

*本轮产出：reports/AUTHORITY_COVERAGE_EXTENSION_2026_07_12.md（本文件）*
