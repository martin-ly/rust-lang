# 术语表与 MSRV 对齐报告（Glossary & MSRV Alignment）

> **日期**: 2026-07-12
> **范围**: 任务 A（glossary 对齐）+ 任务 B（MSRV 单一事实源）
> **结果**: 两项新增检查脚本 `--strict` 均 exit 0；首批真差异已全部修正

---

## 任务 A — Glossary 对齐

### A.1 术语表盘点（全仓 19 个，排除 archive/book/tmp/target/vendor）

| 文件 | 类型 | 处置 |
|---|---|---|
| `concept/00_meta/01_terminology/terminology_glossary.md` | **权威术语表**（184 条，L1–L5+） | 定为唯一权威表（本已声明“权威来源: 本文件为 concept/ 权威页”） |
| `concept/03_advanced/03_proc_macros/32_macro_glossary.md` | 领域权威页（宏） | 保留；7 处定义对齐权威表（见 A.4） |
| `concept/06_ecosystem/03_design_patterns/84_design_patterns_glossary.md` | 领域权威页（设计模式） | 保留；1 处定义对齐 |
| `concept/06_ecosystem/11_domain_applications/59_wasm_glossary.md` | 领域权威页（WASM） | 保留；与权威表无同名冲突 |
| `content/safety_critical/09_reference/08_glossary_and_definitions.md` | 安全关键领域缩略语/对照表 | 保留（已链接权威表）；无冲突 |
| `knowledge/04_expert/safety_critical/09_reference/08_glossary_and_definitions.md` | 重定向 stub | 豁免 |
| `docs/research_notes/10_glossary.md` | 研究笔记术语表（698 行） | 修正 Rc/Send 反例措辞（见 A.4） |
| `crates/c01–c09,c11,c12/docs/tier_01_foundations/03_glossary.md`（11 个） | 重定向/占位 stub | 全部豁免（已指向 concept/ 权威页） |
| `crates/common/docs/glossary.md`、`crates/integration_tests/docs/glossary.md` | 占位 stub | 豁免 |
| `scripts/templates/crate_docs/glossary.md` | 模板 | 豁免 |

### A.2 权威表

`concept/00_meta/01_terminology/terminology_glossary.md` 确认为权威术语表，无需变更（状态 v3.2，184 条术语，已含权威来源声明）。

### A.3 新脚本 `scripts/check_glossary_alignment.py`

- 抽取权威表条目（`**中文** (English) [Lx] — 定义`），扫描全仓 `*glossary*`/`*术语表*` 文件，兼容 4 种格式：权威表 bullet 式、`**Term**:` + `- **定义**:` 多行式、`### Term (中文)` 标题式、中英对照表式。
- 同名术语（按英文/中文名归一化匹配，处理复数与 `/` 别名）比较**关键语义覆盖率**（权威定义 token 在候选定义中的召回率）：<0.5 → DIVERGENCE，<0.8 → WARNING；纯翻译表比较译名一致性（TRANSLATION）。
- 豁免：stub（占位/Quick links/待补充/正文<12 行）、archive/.kimi/book/tmp/target/vendor、templates；支持 `<!-- glossary-waive: 术语 -->` 领域特指义项豁免。
- 默认 exit 0；`--strict` 存在 DIVERGENCE/TRANSLATION 时 exit 1。已登记 `scripts/README.md` 与 `AGENTS.md` §5。

### A.4 首批差异处置（8 项 DIVERGENCE → 0）

1. **`docs/research_notes/10_glossary.md:259`**（任务指定）：`Rc 非 Send（多线程持会导致竞态）` → **`Rc 非 Send（引用计数非原子，跨线程共享会导致数据竞争）`**，并链接权威页 `concept/03_advanced/00_concurrency/17_send_sync_auto_traits.md`（该页表述：“引用计数非原子：并发 clone/drop 竞争计数”）。
2. **`32_macro_glossary.md`** 6 处定义补齐关键语义：声明宏（补“代码生成”）、过程宏（补“编译期操作 token 流”）、派生宏（补 `#[derive(...)]`）、属性宏（补 `#[...]` 形式与“过程宏”归类）、AST（补“源代码解析后/编译器前端输出”）、零成本抽象（补“不产生运行时开销”）。
3. **`32_macro_glossary.md` Pattern Matching**：宏领域特指义项（`macro_rules!` 参数匹配），与语言级义项合法不同 → 定义中注明区别并加 `glossary-waive` 豁免注释。
4. **`84_design_patterns_glossary.md` 零成本抽象**：补齐“高级语言特性编译后”的关键语义。

运行结果：`DIVERGENCE=0 WARNING=0 TRANSLATION=0`，`--strict` exit 0。

---

## 任务 B — MSRV 单一事实源

### B.1 事实源

根 `Cargo.toml` `[workspace.package] rust-version = "1.97.0"` 为唯一事实源；`.clippy.toml msrv = "1.97.0"`、`rust-toolchain.toml` 注释已一致（无需变更）。

### B.2 盘点结论

- **Cargo.toml**：全部 21 个 workspace 成员均为 `rust-version.workspace = true` ✅；`crates/c08_algorithms/fuzz`（1.97.0）一致。
- **豁免（非不一致）**：
  - `crates/c13_embedded/real-hardware-demos/{embassy,rtic}-demo`（rust-version 1.80）：在根 `exclude` 列表中，嵌入式硬件 demo 有独立工具链需求；
  - `examples/resolver_v3_practice`（成员 MSRV 1.70/1.84/1.97）：独立 workspace，混合 MSRV 是 resolver v3 MSRV-aware 行为的**有意演示**（见 CHANGELOG 3.x 记录）；
  - `examples/build_script_practice`、`examples/incremental_practice`、`exercises/rustlings_style/*`：独立 workspace，均已为 1.97.0。
- **文档中的“特性自某版本可用”**（如 `rust_1_90_stabilized.md` 的“对应 Rust 版本: 1.96.1+”、roadmap 中“特性集成（1.89/1.90）”、1.96.1 patch 说明）属特性版本而非 MSRV 声明，保留。
- **历史快照保留不改**：`crates/*/reports/RUST_190_*`、`rust_192_*_update_summary.md`、各 `CHANGELOG.md` 中的 1.89/1.90/1.92 记录是当时的真实状态，改动会伪造历史；脚本按文件名/目录规则豁免。

### B.3 真不一致修正（16 个文件）

| 文件 | 修正 |
|---|---|
| `crates/c09_design_pattern/implementation_roadmap.md` | MSRV/基线 1.90 → **1.97.0**（标题、TOC 锚点、§1.1、CI、验收标准等 15 处；保留“特性集成（1.89/1.90）”特性版本表述） |
| `crates/c09_design_pattern/09_design_patterns.md:1809` | MSRV 1.90 → 1.97.0 |
| `crates/c02_type_system/readme_rust_190.md` | Cargo.toml 示例 `rust-version = "1.90"` ×4 → 1.97.0 |
| `crates/c02_type_system/cargo_package_management_guide.md` | ×2（含 `# 最低 Rust 版本要求`）→ 1.97.0 |
| `crates/c02_type_system/best_practices_guide.md:961` | → 1.97.0 |
| `crates/c08_algorithms/CONTRIBUTING.md` | “1.89 特性对齐版”“Rust 版本: 1.89.0 或更高版本”等 5 处 → 1.97 |
| `crates/c07_process/completion_status.md:55` | `rust-version = "1.92"` → `rust-version.workspace = true（继承 workspace MSRV 1.97.0）` |
| `content/safety_critical/09_reference/02_checklists_and_templates.md:592` | 模板示例 `rust-version = "1.70" # MSRV` → 1.97.0 |
| `content/safety_critical/09_reference/17_toolchain_setup_guide.md:145` | 同上 → 1.97.0 |
| `content/safety_critical/01_mind_maps/03_rust_194_195_features_deep_dive.md:492` | 示例 `# 设置MSRV` 1.96 → 1.97.0 |
| `concept/07_future/04_research_and_experimental/03_evolution.md:244` | 字段示例 `# MSRV：最低编译器版本` 1.85 → 1.97.0 |
| `concept/06_ecosystem/01_cargo/64_cargo_manifest_reference.md:56` | 字段参考表示例值 1.70.0 → 1.97.0 |
| `concept/06_ecosystem/01_cargo/82_cargo_guide_practices.md:119` | 示例 1.70 → 1.97.0 |
| `concept/06_ecosystem/09_testing_and_quality/14_documentation.md:345` | 文档注释示例 MSRV 1.70.0 → 1.97.0 |
| `concept/03_advanced/03_proc_macros/31_production_grade_macro_development.md:48` | 保留 1.70.0（**Cargo Book 原文示例**），注释注明“示例值，摘自 Cargo Book 原文；本项目 MSRV 为 1.97.0” |
| `concept/06_ecosystem/05_systems_and_embedded/57_embedded_hal_1_0_migration.md:135` | 补归属：“MSRV 1.75” → “**Embassy** MSRV 1.75”（第三方运行时，非本项目声明） |

### B.4 新脚本 `scripts/check_msrv_consistency.py`

1. 解析根 `Cargo.toml` 的事实源版本与 `exclude` 列表；
2. 校验所有 Cargo.toml：workspace 成员必须 `rust-version.workspace = true` 或与根一致；豁免 exclude 路径与自带 `[workspace]` 的独立工作区（含其子成员）；
3. 校验活跃文档中的 MSRV **声明式**表述（`rust-version = "x"` 同行带 MSRV/最低注释、`MSRV x`、`x MSRV`、`最低 Rust 版本 x`、元数据式 `Rust 版本: x`；仅匹配 `1.x` 版本，跳过比较语义 `<`/`>=`、标题/TOC 行、假设性发布历史示例、第三方上下文行）；
4. 校验 `.clippy.toml msrv`。

- 默认 exit 0；`--strict` 存在 ERROR 时 exit 1。已登记 `scripts/README.md` 与 `AGENTS.md` §5。

运行结果：`ERROR=0 WARN=0 INFO(豁免)=16`，`--strict` exit 0。

---

## 验证

```bash
python scripts/check_glossary_alignment.py --strict   # exit 0
python scripts/check_msrv_consistency.py --strict     # exit 0
```

本次仅修改 Markdown 文档与新增 Python 脚本，未改动任何 `Cargo.toml` 或 Rust 源码，对 `cargo build/test` 无影响。未执行 git commit。
