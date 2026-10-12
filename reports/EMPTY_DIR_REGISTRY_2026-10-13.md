# 非构建空目录登记（F 轨道）— 2026-10-13

> **纪律**: 全部『保留 + 登记』，零删除（AGENTS.md 红线：只移动不删除）。本文件为登记产物，未移动/删除任何目录。
> **口径**: os.walk 全仓枚举，排除 `.git/` 与含 `target` 段的构建产物目录；『空目录』= 目录本身 0 文件 0 子目录（纯叶子）。git 不存储空目录，`git ls-files` 对全部登记目录返回 0 文件。

## 0. 数量核对（实测 vs 计划草案）

| 组 | F_TRACK_PLAN 草案 | 实测（本报告） | 说明 |
|---|---:|---:|---|
| formal_rust 全树 | 27 | **25 个纯叶子空目录**（全树含中间层共 40 个目录，全部 0 文件） | 草案 27 无法复现：叶子口径 25、全树口径 40，均不等于 27；如实登记 |
| crates/c11_frameworks | 6 | 6 | 吻合（含拼写错误目录 api/sercurity） |
| crates/c14_workflow | 5 | 5 | 吻合 |
| book/ | 2 | 2 | 吻合（mdbook 构建骨架） |
| **合计** | 38 | **38** | 总数吻合；组内 formal_rust 口径差异如实登记 |

另有构建产物空目录 560 个（target/debug/.fingerprint、target/debug/build/*/out、examples/*/target 等），不属治理对象。


## 1. formal_rust/ 全树（vestigial 骨架）

全树 0 文件；不在 Cargo.toml workspace members、不在 .gitignore、无脚本引用；全仓唯一提及是检查点文件。若主代理决定清理，按『只移动』原则整体 `Move-Item formal_rust → archive/formal_rust_skeleton_2026-10/` 并逐条记台账，禁止删除。

| # | 目录 | git 跟踪文件 | 处置 |
|---:|---|---:|---|
| 1 | `formal_rust/engineering-practices/design-patterns/classic-patterns/creational-patterns` | 0 | 保留 + 登记 |
| 2 | `formal_rust/language/17_iot/application_practices` | 0 | 保留 + 登记 |
| 3 | `formal_rust/language/17_iot/implementation_mechanisms` | 0 | 保留 + 登记 |
| 4 | `formal_rust/language/17_iot/theory_foundations` | 0 | 保留 + 登记 |
| 5 | `formal_rust/language/18_model/application_practices` | 0 | 保留 + 登记 |
| 6 | `formal_rust/language/18_model/implementation_mechanisms` | 0 | 保留 + 登记 |
| 7 | `formal_rust/language/18_model/theory_foundations` | 0 | 保留 + 登记 |
| 8 | `formal_rust/language/20_theoretical_perspectives/application_practices` | 0 | 保留 + 登记 |
| 9 | `formal_rust/language/20_theoretical_perspectives/implementation_mechanisms` | 0 | 保留 + 登记 |
| 10 | `formal_rust/language/20_theoretical_perspectives/theory_foundations` | 0 | 保留 + 登记 |
| 11 | `formal_rust/language/21_application_domains/application_practices` | 0 | 保留 + 登记 |
| 12 | `formal_rust/language/21_application_domains/implementation_mechanisms` | 0 | 保留 + 登记 |
| 13 | `formal_rust/language/21_application_domains/theory_foundations` | 0 | 保留 + 登记 |
| 14 | `formal_rust/language/22_performance_optimization/application_practices` | 0 | 保留 + 登记 |
| 15 | `formal_rust/language/22_performance_optimization/implementation_mechanisms` | 0 | 保留 + 登记 |
| 16 | `formal_rust/language/22_performance_optimization/theory_foundations` | 0 | 保留 + 登记 |
| 17 | `formal_rust/language/23_security_verification/future_directions` | 0 | 保留 + 登记 |
| 18 | `formal_rust/refactor/01_core_theory/06_algorithms` | 0 | 保留 + 登记 |
| 19 | `formal_rust/refactor/02_design_patterns/01_patterns` | 0 | 保留 + 登记 |
| 20 | `formal_rust/software/03_toolchain_automation` | 0 | 保留 + 登记 |
| 21 | `formal_rust/software/04_dependency_security` | 0 | 保留 + 登记 |
| 22 | `formal_rust/software/05_testing_quality` | 0 | 保留 + 登记 |
| 23 | `formal_rust/software/06_documentation_spec` | 0 | 保留 + 登记 |
| 24 | `formal_rust/software/07_community_ecosystem` | 0 | 保留 + 登记 |
| 25 | `formal_rust/software/08_engineering_comparison` | 0 | 保留 + 登记 |

## 2. crates/c11_frameworks/src/api/（废弃 crate 骨架）

c11_frameworks 不在 workspace members（members 为 c11_macro_system_proc、c14_semantic_web）；无 Cargo.toml；`api/sercurity` 为拼写错误目录（应为 security），保留原样登记不改名。

| # | 目录 | git 跟踪文件 | 处置 |
|---:|---|---:|---|
| 1 | `crates/c11_frameworks/src/api/auth` | 0 | 保留 + 登记 |
| 2 | `crates/c11_frameworks/src/api/graphql` | 0 | 保留 + 登记 |
| 3 | `crates/c11_frameworks/src/api/grpc` | 0 | 保留 + 登记 |
| 4 | `crates/c11_frameworks/src/api/openapi` | 0 | 保留 + 登记 |
| 5 | `crates/c11_frameworks/src/api/rest` | 0 | 保留 + 登记 |
| 6 | `crates/c11_frameworks/src/api/sercurity` | 0 | 保留 + 登记 |

## 3. crates/c14_workflow/src/（废弃 crate 骨架）

c14_workflow 不在 workspace members；无 Cargo.toml；git 0 文件。

| # | 目录 | git 跟踪文件 | 处置 |
|---:|---|---:|---|
| 1 | `crates/c14_workflow/src/benchmarks` | 0 | 保留 + 登记 |
| 2 | `crates/c14_workflow/src/rust189/async` | 0 | 保留 + 登记 |
| 3 | `crates/c14_workflow/src/rust189/concurrency` | 0 | 保留 + 登记 |
| 4 | `crates/c14_workflow/src/rust189/features` | 0 | 保留 + 登记 |
| 5 | `crates/c14_workflow/src/tests` | 0 | 保留 + 登记 |

## 4. book/（mdbook 构建骨架）

book/ 为 mdbook 构建产物目录（AGENTS.md §2.1：除 README 外不应提交）；空骨架随下次 `mdbook build` 再生成，保留不动。

| # | 目录 | git 跟踪文件 | 处置 |
|---:|---|---:|---|
| 1 | `book/05_comparative/06_quizzes` | 0 | 保留 + 登记 |
| 2 | `book/07_future/archive` | 0 | 保留 + 登记 |

## 5. 处置总则

- 38 个目录全部保留原位，已在 `move_ledger.csv` 以 4 条『保留登记』行入账（台账 L8-L11）。
- 任何后续清理一律走『整体移动到 archive/』路径并逐条记台账；禁止 delete。
- 本报告由 os.walk 实测生成（2026-10-13），核验脚本口径：排除 .git/ 与 target 段后，纯叶子空目录 38 个，与 F_TRACK_PLAN 总数 38 吻合。

---

## 6. 附：悬空 knowledge/ 引用修正记录（同日执行，详见 move_ledger.csv 修链行）

实测口径：concept/ + docs/ 活跃目录中指向已删除 knowledge/ 路径的**真实引用**共 13 处（F 轨道草案称 24 处，含 URL 假阳性与『knowledge/docs』类目录名并提，不可复现；如实登记）。修正 12 处，保留 1 处：

| 文件 | 行 | 原悬空路径 | 处置 |
|---|---:|---|---|
| docs/11_project/04_hierarchy_mapping_master.md | 128 | knowledge/01_fundamentals/ownership.md | 改链 concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md |
| 同上 | 129 | knowledge/01_fundamentals/borrowing.md | 改链 concept/.../02_borrowing.md |
| 同上 | 130 | knowledge/02_intermediate/traits.md | 改链现存 stub knowledge/02_intermediate/06_traits.md（注 canonical concept/02_intermediate/00_traits/01_traits.md） |
| 同上 | 131 | knowledge/02_intermediate/generics.md | 改链 concept/02_intermediate/01_generics/01_generics.md |
| 同上 | 132 | knowledge/03_advanced/concurrency/README.md | 改链 concept/03_advanced/00_concurrency/01_concurrency.md |
| 同上 | 133 | knowledge/03_advanced/async/README.md | 改链 concept/03_advanced/01_async/01_async.md |
| 同上 | 135 | knowledge/03_advanced/macros/README.md（草案未列，实测发现） | 改链 concept/03_advanced/03_proc_macros/01_macros.md |
| docs/00_meta/04_documentation_division_of_labor.md | 154 | knowledge/03_advanced/async/ | 改 concept/03_advanced/01_async/01_async.md |
| 同上 | 155 | knowledge/03_advanced/concurrency/ | 改 concept/03_advanced/00_concurrency/01_concurrency.md |
| 同上 | 157 | knowledge/03_advanced/macros/ | 改 concept/03_advanced/03_proc_macros/01_macros.md |
| 同上 | 158 | knowledge/03_advanced/performance_optimization.md | 改现存 stub knowledge/03_advanced/05_performance_optimization.md |
| 同上 | 188 | knowledge/README.md | 保留文字，标注『已删除（86e06ba37）』 |
| concept/00_meta/02_sources/01_authority_source_map.md | 140 | knowledge/01_fundamentals/ownership.md | 改 concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md + 已删除注记 |
| concept/03_advanced/00_concurrency/01_concurrency.md | 10 | knowledge/03_advanced/concurrency（markdown 链接） | 改链现存 stub knowledge/03_advanced/unsafe/README.md + 已删除注记 |
| concept/03_advanced/01_async/08_pin_unpin.md | 10 | knowledge/03_advanced/async（markdown 链接） | 改链现存 stub knowledge/03_advanced/unsafe/README.md + 已删除注记 |
| docs/03_reference/quick_reference/19_rust_195_features_cheatsheet.md | 89 | knowledge/02_intermediate/control_flow/01_if_let_guards.md（文本+链接 2 处） | 改链 canonical concept/01_foundation/04_control_flow/01_control_flow.md |

未改动（判定为非悬空/历史条目）：
- `knowledge/04_expert/miri/README.md` L11：草案称断链，实测 `../../../concept/04_formal/04_model_checking/08_miri.md` 有效——草案口径滞后，未改。
- CHANGELOG.md 全部历史条目：保留原文（不改写历史）。
- 『knowledge/docs』『concept/knowledge/docs』目录名并提、SWEBOK URL（bodies-of-knowledge/...）：非路径引用，不改。
- archive/ 目录内历史断链：归档件，不在活跃目录治理范围。
