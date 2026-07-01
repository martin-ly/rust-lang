# 项目一致性全面审计报告

> **审计日期**: 2026-06-28
> **审计范围**: `e:/_src/rust-lang` 全仓库
> **审计性质**: 只读内容/结构分析，未运行 cargo 测试或 clippy
> **审计工具**: 文件系统遍历、内容搜索、脚本统计

---

## 执行摘要

本次审计对项目的目录结构、内容主题、版本工具链、国际化、链接引用、代码与文档、脚本工具、元数据状态等 8 个维度进行了全面梳理，发现以下最关键问题：

1. **版本/工具链声明与实际严重不符**：项目对外宣称 MSRV 1.96.0 stable、Edition 2024，但 `rust-toolchain.toml` 锁定 `nightly`，CI 使用 nightly，且全仓库存在大量 `#![feature(...)]` nightly feature gate。稳定版用户无法直接构建，MSRV 形同虚设。
2. **治理文档“多主控”**：`.kimi/` 中存在 30+ 份计划/状态文件，互相声称“唯一主控”或“主控来源”，导致真实优先级与待办来源混乱。
3. **同一主题高度分散且重复**：例如 `ownership` 出现在 26 个文件中、`borrow` 29 个、`async` 26 个、`lifetime` 12 个，分布在 `concept/`、`docs/`、`knowledge/`、`docs/rust-ownership-decidability/` 中；同时存在多个同名/同编号文件。
4. **脚本与文档工具严重失控**：`scripts/README.md` 仅覆盖约 1/3 的活跃脚本；多个 `fix_dead_links.py/v2/v3` 等重复版本并存；`scripts/archive/` 已堆积 72 个历史脚本。
5. **归档边界不清晰**：`docs/archive/` 含 258 个文件，最近 30 天内仍有大量 archive 文件被修改，说明 archive 并非只读历史，而是活跃内容的“临时堆放区”。

---

## 1. 目录结构与命名一致性

| # | 问题描述 | 证据 | 严重度 |
|---|---------|------|--------|
| 1.1 | `docs/` 与 `reports/`、`.kimi/` 命名风格极不统一 | `docs/` 中 kebab-case、number_prefix、snake_case、中文文件名、含空格/混合文件名并存；`reports/`、`.kimi/` 几乎全为 `UPPERCASE_DATE` 混合风格 | P2 |
| 1.2 | `concept/` 内部编号冲突严重 | `concept/01_foundation/`：`00_start.md` 与 `00_pl_prerequisites.md`；`03_lifetimes.md` 与 `03_lifetimes_advanced.md`；`02_intermediate/15_error_handling_deep_dive.md` 与 `15_iterator_patterns.md` 等同数字前缀冲突 | P2 |
| 1.3 | Crate 编号重复/混淆 | `crates/c11_macro_system/` 与 `crates/c11_macro_system_proc/` 已合并为统一的 `crates/c11_macro_system_proc/` | ✅ |
| 1.4 | `archive/` 与活跃内容边界模糊 | 最近 30 天内 archive 仍有大量文件被修改；`docs/archive/2026_03_reorganization/`、`docs/archive/c_class_audit_2026_06_08/` 等为近期目录 | P2 |
| 1.5 | `book/` 与 `concept/` 内容重复 | `book.toml:5`：`src = "concept"`，说明 book 是构建输出，但目录结构与 `concept/` 并列存在 | P2 |

---

## 2. 内容主题与子主题一致性

| # | 问题描述 | 证据 | 严重度 |
|---|---------|------|--------|
| 2.1 | 核心主题在多个目录重复出现，缺乏单一权威入口 | `ownership` 26 文件、`borrow` 29 文件、`async` 26 文件、`lifetime` 12 文件 | P1 |
| 2.2 | 同名/同主题文件跨目录存在 | `concept/01_foundation/03_lifetimes.md` 与 `knowledge/01_fundamentals/03_lifetimes.md`；`concept/03_advanced/02_async_patterns.md` 与 `docs/02_reference/quick_reference/02_async_patterns.md`；多个 `INDEX.md` | P1 |
| 2.3 | `LEARNING_MVP_PATH.md` 与实际文件命名存在偏差 | 链接文本与目标文件名不一致 | P2 |
| 2.4 | `README.md` 中的项目统计与实际文件数量不符 | 称“302 concept 文件”，实际更多；称“17 workspace crates”，实际 18 个 | P2 |
| 2.5 | `content/CONTENT_CRATES_MAPPING.md` 中部分 content 文件不存在或无法直接验证 | 引用 `generic_const_items.md`、`coroutines.md` 等未在 `content/` 根目录直接出现 | P2 |

---

## 3. 版本与工具链一致性

| # | 问题描述 | 证据 | 严重度 |
|---|---------|------|--------|
| 3.1 | **MSRV 声明与实际工具链矛盾** | `Cargo.toml` 声明 `rust-version = "1.96.0"`，但 `rust-toolchain.toml` 锁定 `nightly`，CI 也使用 nightly | P1 |
| 3.2 | `.cargo/config.toml` 显式允许不兼容 MSRV 的依赖版本 | `incompatible-rust-versions = "allow"` | P1 |
| 3.3 | 全仓库存在大量 nightly feature gate | 46 处 `#![feature(...)]` 分布在 20 个文件 | P1 |
| 3.4 | 版本号引用混乱 | `.md`/`.toml` 中 `1.96` 5272 次、`nightly` 1401 次、`1.95` 1491 次、`1.97` 724 次、`1.98` 347 次 | P2 |
| 3.5 | `crates/VERSION_INDEX.md` 数据不准确 | 1.89–1.95 发布日期早于实际历史；“活跃版本”仍为 1.96 | P2 |
| 3.6 | 手动版本探测脚本依赖人工维护 | `scripts/probe_rust_197_apis.rs`、`scripts/probe_rust_198_apis.rs` 与 `crates/` 中预览模块并存 | P2 |

---

## 4. 国际化（i18n）一致性

| # | 问题描述 | 证据 | 严重度 |
|---|---------|------|--------|
| 4.1 | `concept/` 双语标注仍有 39 类术语未覆盖 | `reports/I18N_BILINGUAL_BASELINE_2026_06_28.md`：TOP 未覆盖术语 `crate`（17 文件）、`trait`（13）、`生命周期`（10）等 | P2 |
| 4.2 | `knowledge/`、`docs/`、`book/` 等核心学习路径文件缺少 EN/Summary 元数据 | 抽样 `knowledge/01_fundamentals/03_lifetimes.md`、`docs/01_core/01_ownership_borrowing_lifetimes.md` 无 `**EN**` 头部 | P2 |
| 4.3 | `CONTRIBUTING.md` 提到的自查脚本路径与仓库实际不完全一致 | 引用 `scripts/i18n/check_concept_headers.py` 等，路径需核对 | P3 |

---

## 5. 链接与引用一致性

| # | 问题描述 | 证据 | 严重度 |
|---|---------|------|--------|
| 5.1 | `docs/LINK_CHECK_REPORT.md` 未标注生成时间 | 无生成日期；无法判断报告是否已过期 | P2 |
| 5.2 | 外部链接失效数量与内部链接报告口径不一致 | `.kimi/PROJECT_COMPREHENSIVE_PENDING_PLAN_2026_06_28.md` 指出仍有 **506 条外部链接失效/异常** | P2 |
| 5.3 | 历史归档区存在同名/重复文件，且仍在被引用 | `docs/rust-ownership-decidability/comprehensive-analysis/case-studies/tokio-runtime-analysis.md` 与 `docs/rust-ownership-decidability/case-studies/tokio-runtime-analysis.md` 等重复 | P2 |

---

## 6. 代码与文档一致性

| # | 问题描述 | 证据 | 严重度 |
|---|---------|------|--------|
| 6.1 | `crates/c14_semantic_web/` 缺少顶层 `README.md` | 仅在 `docs/README.md` 有 boilerplate，版本号与 workspace 不一致 | P2 |
| 6.2 | `crates/c11_macro_system_proc/src/lib.rs` 文档注释质量极差 | 中英文混杂、缺空格、机器翻译痕迹明显 | P2 |
| 6.3 | `crates/integration_tests/` 基本为空壳 | 仅有一个非常初级的跨模块测试文件 | P2 |
| 6.4 | 批量生成的 56 个 crate boilerplate 文档中部分仍含占位符 | `{{MVC}}`、`{{KNOWLEDGE_GRAPH}}`、`🚧 文档建设中` 等 | P2 |
| 6.5 | `exercises/` 测试与文档不匹配项目宣传 | README 称 80 题，但 `exercises/tests/` 仅 13 个测试文件；`exercises/src/lib.rs` 启用 nightly feature gate | P2 |
| 6.6 | Crate 描述/版本不统一 | 多数 crate 版本为 0.1.0，与 workspace 3.1.0 不一致 | P3 |

---

## 7. 脚本与工具一致性

| # | 问题描述 | 证据 | 严重度 |
|---|---------|------|--------|
| 7.1 | `scripts/README.md` 严重过时 | 最后更新 2026-06-02，仅覆盖约 1/3 活跃脚本 | P2 |
| 7.2 | 同一类修复脚本存在多个版本 | `scripts/fix_dead_links.py`、`fix_dead_links_v2.py`、`fix_dead_links_v3.py` 等 | P2 |
| 7.3 | `scripts/archive/` 已堆积 72 个历史脚本 | 部分可能与根目录脚本同名/同功能 | P3 |
| 7.4 | 工作流文件存在功能重叠/命名相近 | `rust-version-tracker.yml` 与 `rust-version-tracking.yml`；`weekly-deps.yml` 与 `weekly-dependency-check.yml` | P3 |

---

## 8. 元数据与状态标记一致性

| # | 问题描述 | 证据 | 严重度 |
|---|---------|------|--------|
| 8.1 | `concept/` 文件头部元数据不统一 | 354 个含 `受众`、336 个含 `内容分级`、334 个含 `Bloom`，仍有部分文件缺失；`> **分级**` 几乎未出现 | P2 |
| 8.2 | 质量仪表盘与 README 统计不同步 | `reports/kb_quality_dashboard.md` 生成于 2026-06-09；README 称代码块编译通过率 100%，仪表盘显示 90.7% | P2 |
| 8.3 | `.kimi/` 中存在多份互相覆盖的执行清单 | `EXECUTION_CHECKLIST_2026_06_22.md`、`EXECUTION_CHECKLIST_2026_06_26_CONFIRMED.md`、`PROJECT_COMPREHENSIVE_PENDING_PLAN_2026_06_28.md` 等 | P1 |
| 8.4 | `CHANGELOG.md [3.1.0]` 中部分 1.97 API 状态依赖发布日确认 | 已提前生成大量 1.97/1.98 预览文档和探测脚本，若官方 Release Notes 与预期不符将产生批量回滚工作 | P2 |
| 8.5 | 供应链审计文件为空 | `supply-chain/audits.toml` 仅 11 行注释；`.cargo/audit.toml` 忽略 6 条 RUSTSEC | P2 |

---

## 9. 批判性评价

| 维度 | 得分 | 理由 |
|------|------|------|
| **可维护性** | 2/5 | 脚本数量失控、README 与脚本不同步、多份主控计划并存、boilerplate 文档含占位符、质量仪表盘过期。 |
| **可发现性** | 2/5 | 同一主题分散在 4–5 个目录，同名文件多，编号冲突严重，archive 与活跃内容混放。 |
| **可持续性** | 2/5 | 依赖 nightly 工具链 + 大量 feature gate + 1010 个 Cargo.lock 依赖 + 6 条被忽略的 RUSTSEC + 手动版本探测脚本。 |
| **国际化** | 3/5 | `concept/` EN/Summary 元数据已 100% 覆盖，术语表较完整；但基础术语覆盖率仍有缺口，`knowledge/`/`docs/` 缺少完整英文骨架。 |
| **版本管理** | 2/5 | MSRV 与实际 nightly 工具链矛盾是根本问题；版本号引用杂乱、CI/配置/文档口径不一、手动探测脚本脆弱。 |

---

*本报告为批判性审计，后续可持续改进计划见 `.kimi/SUSTAINABLE_IMPROVEMENT_PLAN_2026_06_28.md`。*
