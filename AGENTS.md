# Agent 协作指南：Rust 分层概念知识体系

> **作用域**：本文件适用于 `e:\_src\rust-lang` 及其所有子目录。当子目录存在更具体的 `AGENTS.md` 时，子目录规则优先。

---

## 1. 项目定位

这是一个**分层、可验证、可搜索**的 Rust 概念知识库，采用 **L0-L7 八层认知架构**。
核心目标不是“堆叠文档”，而是为每个 Rust 概念维护**单一、权威、可演进**的解释来源。

---

## 2. Canonical 规则：单一权威来源

任何 Rust 概念/主题必须只有一个**权威页（canonical page）**。其他位置只允许是以下三种形式之一：

| 形式 | 允许内容 | 禁止内容 |
|---|---|---|
| **权威页** | 完整概念解释、代码、反例、形式化、跨语言对比、工程实践 | 复制其他权威页内容 |
| **摘要/速查页** | 关键要点、链接到权威页、决策树、cheatsheet | 重复权威页的正文解释 |
| **重定向 stub** | 一句话说明 + `> **权威来源**: [concept/xxx.md](.)` 链接 | 保留重复正文 |

### 2.1 目录职责

| 目录 | 职责 | 是否可作为权威来源 |
|---|---|---|
| `concept/` | **权威概念层（L0-L7）**。每个 Rust 概念的唯一深度解释。 | ✅ 是 |
| `knowledge/` | 精简知识卡片、速查、学习入口。 | ❌ 否；只能摘要或重定向到 `concept/` |
| `docs/` | 指南、参考、实践项目、研究报告。 | ❌ 否；指南可保留操作步骤，概念解释必须链接到 `concept/` |
| `content/` | 专题深度内容套件（安全关键、生态深度、生产实践、学术研究）。 | ⚠️ 仅当 `concept/` 未覆盖时可作为该专题的权威页；否则必须链接 |
| `crates/` | 可编译代码示例与 workspace。`crates/*/docs/` 只保留与 crate 直接相关的独特内容。 | ❌ 概念解释不能放在这里 |
| `exercises/` | 练习题与答案。 | ❌ 不能替代概念解释 |
| `archive/` | 只读历史归档。内部文件不得与活跃目录重复。 | ❌ 不是权威来源 |
| `book/` | `mdbook build` 输出目录。除 `book/README.md` 外，不应提交到版本控制。 | ❌ 构建产物 |
| `tmp/` | 临时文件与缓存。不应提交到版本控制。 | ❌ 临时目录 |
| `vendor/` | 第三方 crate 的本地 vendor 副本（配合根 `Cargo.toml` 的 `[patch.crates-io]`），仅用于修复上游未发布的问题。上游修复发布后应移除对应 patch 与目录。 | ❌ 不是权威来源 |

### 2.2 如何判断权威页

1. 优先在 `concept/` 中按 L0-L7 层级查找对应主题。
2. 如果 `concept/` 已存在该主题，其他目录的重复文件必须改为重定向 stub 或摘要。
3. 如果 `concept/` 不存在但 `content/` 有专题深度文，可将 `content/` 文件作为该专题权威页，但需在 `concept/` 中创建链接或索引。
4. 禁止在多个目录中保留相同概念的完整正文。

---

## 3. 内容去重与合并政策

### 3.1 新增内容时

- **先查重**：运行 `python scripts/detect_content_overlap.py` 或手动搜索目标主题是否已存在。
- **不要复制**：如需在多个位置出现，创建重定向 stub，不要复制正文。
- **声明 canonical**：新增权威页应在文件顶部或元数据中注明其 canonical 地位。

### 3.2 修改内容时

- 如果修改的是非 `concept/` 文件，且该主题在 `concept/` 已有权威页，应：
  1. 将改动迁移到 `concept/` 的权威页；
  2. 将非权威文件改为摘要或重定向；
  3. 不要同时在两个位置维护相同内容。

### 3.3 发现重复时

按以下优先级合并：

1. `concept/` > `knowledge/` / `docs/` / `content/`
2. 较新、较完整、英文摘要/元数据齐全的版本优先
3. 保留有交叉引用、版本跟踪、Bloom 标签等元数据的版本
4. 被合并的文件保留路径，内容改为重定向 stub

### 3.4 `docs/` 去重政策

- `docs/` 中的指南、cheatsheet 可以保留操作步骤、决策树、示例和速查表。
- `docs/` 中**不得**重复已在 `concept/` 中存在的通用 Rust 概念解释；应通过链接指向 `concept/` 权威页。
- 编辑 `docs/` 文件时，如发现某节与 `concept/` 文件重复，应将该节迁移到 `concept/` 权威页，并在 `docs/` 中替换为 canonical 链接。

---

## 4. 文件命名与格式

- Markdown/脚本/目录名使用 `snake_case` 或 `number_prefix_snake_case`。
- 禁止中文文件名、空格、混合大小写（过渡期例外：`archive/` 历史文件、`.kimi/` 日期风格文件、`reports/` 日期风格文件、`.github/ISSUE_TEMPLATE/`）。
- 每个 `concept/` 文件应包含 `**EN**` 英文标题和 `**Summary**` 英文摘要。

### 4.0 序号与目录命名规则（2026-07-12 全库重编号后生效）

1. **序号语义**：一律为**目录内两位连续序号** `NN_`（01 起）；`00_` 保留给导览页/README。不再使用“层内全书章节号”。
2. **一级目录**：两位连续不跳号；删除目录后必须重排剩余目录。
3. **同目录禁同号**。删除文件后：小目录（<15 文件）重排；大目录（≥15）可留空号，但须在该目录 README 记录空号原因。
4. **专题系列**（如 `rust_1_9x_*` 版本追踪）可无序号，但须集中于同一目录并有 README 索引。
5. **quiz**：每层设 `NN_quizzes/` 目录收纳测验，不散落。
6. **crates/*/docs/**：仅允许 `tier_0N_*` 子目录 + `NN_` 文件；禁止 `viewNN`、散名、`*_final`/`*_expanded`/`*_supplement` 变体文件（内容并入主干后 stub 化或删除）。
7. 禁止双前缀（如 `06_20_`）与异形前缀（如 `1_2_`）；日期后缀仅限豁免目录（`reports/`、`.kimi/`、`archive/`）。
8. `concept/SUMMARY.md`、`knowledge/INDEX.md` 等导航文件的结构变更须与文件重命名同步；批量重命名统一使用 `scripts/plan_renumber.py`（生成映射 CSV，人工 review）+ `scripts/apply_renumber.py`（默认 dry-run，`--apply` 执行，自动双向重算相对链接并同步 JSON/YAML/KG 路径）。

### 4.1 `Cargo.toml` 规范

所有 workspace member 必须继承 workspace 元数据，禁止硬编码重复值：

```toml
[package]
name = "crate_name"
version.workspace = true
edition.workspace = true
rust-version.workspace = true
authors.workspace = true
license.workspace = true
repository.workspace = true
homepage.workspace = true
```

- `rust-version` 保持 `1.97.0`（本地 MSRV），文档版本号可单独维护为 `1.97.0+`。
- feature 名使用 `kebab-case`；避免使用 Rust 关键字（如 `async`）作为 feature 名。
- 已在 workspace dependencies 中声明的依赖，优先使用 `{ workspace = true }`。

### 4.2 `concept/` 文件元数据模板

```markdown
# 中文标题

**EN**: English Title
**Summary**: One-sentence English abstract.

> **Rust 版本**: 1.97.0+ (Edition 2024)
> **Bloom 层级**: Lx
> **权威来源**: 本文件为 `concept/` 权威页。

正文...
```

### 4.3 `knowledge/` 重定向 stub 模板

```markdown
# 中文标题

**EN**: English Title
**Summary**: One-sentence English abstract.

> **权威来源**: 本文件为学习入口 stub，完整概念解释请见：
> [`concept/xxx/xxx.md`](../../concept/xxx/xxx.md)
>
> 根据 AGENTS.md §2 Canonical 规则，通用 Rust 概念解释统一维护在 `concept/` 中；
> `knowledge/` 仅保留摘要、速查与链接。
```

### 4.4 `content/` 重定向 / 专题入口 stub 模板

```markdown
# 中文标题

**EN**: English Title
**Summary**: One-sentence English abstract.

> **权威来源**: 本文件为专题深度内容入口；通用 Rust 概念解释请见
> [`concept/xxx/xxx.md`](../../concept/xxx/xxx.md)。
> 若 `concept/` 已覆盖相同主题，本文仅保留应用场景、案例与决策树，不重复概念推导。
```

---

## 5. 常用命令

```bash
# 质量审计
python scripts/kb_auditor.py

# 内容重叠检测（关键！新增/修改前运行）
python scripts/detect_content_overlap.py

# 术语表对齐检查（以 concept/00_meta/01_terminology/01_terminology_glossary.md 为权威表）
python scripts/check_glossary_alignment.py --strict

# 内容完整性审计（TODO/待补充/占位标记 + 空章节量化，复核 reports/CONTENT_COMPLETENESS_CLEANUP_2026_07_12.md）
python scripts/audit_content_completeness.py --json tmp/completeness.json

# MSRV 单一事实源检查（根 Cargo.toml rust-version = 1.97.0 为唯一事实源）
python scripts/check_msrv_consistency.py --strict

# 死链检查（concept/ + docs/ + content/ + knowledge/）
python scripts/kb_auditor.py --link-check

# 构建验证
cargo build --workspace
cargo test --workspace

# mdbook 构建（输出到 book/，不应提交）
mdbook build

# 本地一键运行全部 23 个质量门（23 阻断 + 0 语义观察）
bash scripts/run_quality_gates.sh

# concept/ 代码块批量编译实测（阻断门 21，--strict 默认抽样；--with-deps 需先 cargo build --workspace）
python scripts/check_concept_code_blocks.py --sample 0 --with-deps --json tmp/cb.json --report reports/xxx.md

# 命名规范 lint（AGENTS.md §4.0：N1–N6；2026-07-14 转阻断门 18，--strict 仅卡 ERROR，WARN 不阻断）
python scripts/check_naming_convention.py --strict

# 安装 pre-commit hook（会在每次 commit 前自动跑重叠/i18n/死链检查）
bash scripts/git_hooks/install.sh
```

### 5.1 CI 质量门（23 项：23 阻断 + 0 语义观察）

所有合并到 `main`/`master` 的变更必须通过以下 **23 个阻断质量门**。语义观察门机制保留（见 §5.2）但当前 **0 个观察门**（2026-07-14 用户指示全部转阻断，4 门 --strict 实跑均 exit 0，见 `reports/GATE_FULL_BLOCKING_U1_2026_07_14.md`）：

**阻断门（23）**：

1. `cargo check --workspace`
2. `cargo test --workspace --quiet`
3. `cargo clippy --workspace -- -D warnings`
4. `cargo audit --no-fetch`
5. `cargo vet --locked`
6. `mdbook build`
7. `python scripts/kb_auditor.py`（死链：concept/ + docs/ + content/ + knowledge/；跨层/模板化 ⟹，EXIT 非 0 即阻断）
8. `python scripts/detect_content_overlap.py`
9. `python scripts/add_bilingual_annotations.py --mode check-only`
10. `mermaid` 语法检查（CI job；本地见 `scripts/run_quality_gates.sh`）
11. `python scripts/check_topology_quality.py --strict`（atlas 拓扑 T1–T6；2026-07-12 转正，见 §5.2）
12. `python scripts/check_kg_shapes.py --strict`（KG SHACL/形态；2026-07-12 转正）
13. `python scripts/check_canonical_uniqueness.py --strict`（concept 权威页唯一性；2026-07-12 转正）
14. `python scripts/concept_consistency_auditor.py --strict`（跨文件概念定义一致性；2026-07-12 转正）
15. `python scripts/detect_content_overlap_v2.py --budget 999999` + `python scripts/triage_overlap.py`（段落级重叠 v2；可处理项 MERGE+DOCS_INTERNAL 基线 0，超 0 即阻断；2026-07-12 转正，清零证据见 `reports/DEDUP_V2_ZERO_2026_07_12.md` 与 §5.2）
16. `python scripts/check_concept_authority_coverage.py --strict --include-crates`（concept 权威层国际化权威来源覆盖率：内容页 any=100%/none=0/核心 L1–L4 无 P0 缺口=0；`--include-crates` 附加 crates/*/docs 覆盖小节：crates 非 stub 内容页 64/64=100%，crates 缺口>0 亦阻断；2026-07-14 转正，R4 评估见 `reports/OBSERVE_GATE_PROMOTION_REVIEW_R4_2026_07_14.md`）
17. `python scripts/check_examples_compile.py --strict`（根 examples/ 游离示例编译保护；9 stdlib rustc 直编 + 3 依赖示例经 `examples/examples_check/` crate + 2 Cargo Script 豁免；2026-07-14 转正并**新增 CI job `examples-compile`**，此前仅本地脚本挂载）
18. `python scripts/check_naming_convention.py --strict`（命名规范 lint，AGENTS.md §4.0 N1–N6；扫描 concept/knowledge/docs/content/crates/*/docs；**--strict 仅卡 ERROR>0，WARN 不阻断**；基线 ERROR=0/WARN=54（2026-07-14 实测）；2026-07-14 转正）
19. `python scripts/check_quiz_system.py --strict`（测验体系一致性：quiz_registry.yaml 注册表核对、题型多样性≥3、难度标注率 100%、quiz↔concept 双向链接；--strict 时检查 1–3 失败即阻断，回链缺失仅统计；2026-07-14 转正）
20. `python scripts/check_metadata_consistency.py --strict`（元数据 D1–D6；D2 豁免 2 项 / D5 豁免 29 项（15 项 2026-07-12 + 14 项 2026-07-13 W0–W5 新建页逐文件复核）均已显式登记于检查器白名单并附理由；2026-07-13 另修复 NIGHTLY_RE 词边界误报；2026-07-14 复测 D1–D6 全 0、--strict exit 0，2026-07-14 转阻断）
21. `python scripts/check_concept_code_blocks.py --strict`（concept/ 代码块批量编译实测；提取 ```rust 块分类 10 桶，compile_fail 验证确实失败+E0xxx/editionNNNN 校验，std-only 候选 >300 分层抽样 rustc 1.97 --edition 2024 直编（自动包 fn main），`--with-deps` 用 target/debug/deps rmeta --extern 实测依赖块；“应过但失败/标注腐烂”>0 即 exit 1；2026-07-13 由附加小节提升为独立门，基线 `reports/CONCEPT_CODE_BLOCKS_BASELINE_2026_07_13.md`；2026-07-14 复测 rot=0、--strict 默认抽样 exit 0，2026-07-14 转阻断）
22. `python scripts/check_mindmap_coverage.py --strict`（思维表征覆盖：内容页 mindmap 覆盖率与反例节存在率，仅 concept/ 排除 00_meta/stub；--strict 基线 mindmap≥10%/反例≥40%，2026-07-14 实测 90.0%/84.4% exit 0；2026-07-14 转阻断）
23. `python scripts/semantic_health.py --strict`（综合语义健康分；grade=FAIL 时阻断；2026-07-14 实测 99.6 grade OK exit 0；聚合门，2026-07-14 转阻断）

**语义观察门（0，机制保留）**：

> 说明：观察门机制（默认 exit 0、warning 不阻断、达标后按 §5.2 转阻断）保留；2026-07-14 起当前 0 个观察门。新增观察门时在 `run_quality_gates.sh` 观察段与 `quality_gates.yml` 以 `continue-on-error: true` 挂载，命名后缀 `(observe)`。权威覆盖门（16）目标基线为 concept/ 真内容页 any=100%、none=0、核心 L1–L4 无 P0 缺口=0。

### 5.2 观察门机制说明（P3-7，2026-07-12 建立；当前 0 个在观察）

**当前状态**：2026-07-14 用户指示全部转阻断后，**23 门全阻断、0 个观察门**。机制保留以备将来新增观察门。

**转正规则**：任一语义观察门**连续 4 周（或连续 10 次 CI 运行）达标**，经评估后转为阻断门（在 `run_quality_gates.sh` 与 `quality_gates.yml` 中改为 `--strict` 且 `continue-on-error: false`）。转正前提：本地实跑 `--strict` 当前 exit=0。转正后若指标退化阻断 PR，按正常阻断门流程处置，不自动降级。

**各门基线状态（2026-07-14 更新：R4 评估后 authority coverage / examples compile / naming convention / quiz system 四门转阻断，见 `reports/OBSERVE_GATE_PROMOTION_REVIEW_R4_2026_07_14.md`；metadata consistency / concept code blocks / mindmap coverage / semantic health 四门同日转阻断，见 `reports/GATE_FULL_BLOCKING_U1_2026_07_14.md`；其余摘自 `reports/` 最新基线）**：

| 门 | 基线指标（2026-07-12） | --strict 实跑 | 状态 |
|---|---|:---:|---|
| topology quality | T1 套话率 0%（表头识别 bug 修复后）/ T2 高频关系 76.2% pass / T3 跳出 3.2%（6/189）且死端 0 / T4 定量 100% / T5=0 / T6=0 | exit 0 | ✅ **已转阻断** |
| KG SHACL | K1–K6 全 0（K1b 缺 bloomLevel=55，仅扣分不阻断） | exit 0 | ✅ **已转阻断** |
| canonical uniqueness | 0 处双权威页/同主题重复 | exit 0 | ✅ **已转阻断** |
| concept consistency | 0 错误级发现（decision trees 等跨文件引用全有效） | exit 0 | ✅ **已转阻断** |
| metadata consistency | D1–D6 全 0（2026-07-14 复测；D2 白名单 2 项与 D5 白名单 64 项均显式登记于检查器并公示于报告；前序 2026-07-14 早些时候 D5 曾回归 32，并行内容回填所致，已随回填清零） | exit 0（2026-07-14 复测） | ✅ **已转阻断**（2026-07-14，用户指示全部转阻断） |
| overlap v2 | 命中 559；可处理 MERGE=0 + DOCS_INTERNAL=0 = **0**（SERIES 115 白名单 / REVIEWED 444 已批量复核白名单 / REVIEW 0；54 对清零明细见 `reports/DEDUP_V2_ZERO_2026_07_12.md`，437 REVIEW 复核加固见 `reports/OVERLAP_REVIEW_SWEEP_2026_07_12.md`） | exit 0 | ✅ **已转阻断**（2026-07-12，可处理项基线 0） |
| naming convention | N1–N6：ERROR=0 / WARN=54（2026-07-14 实测，1821 文件/258 目录；WARN 较 07-12 基线 78 减 24；--strict 仅卡 ERROR>0，WARN 不阻断） | exit 0 | ✅ **已转阻断**（2026-07-14，R4 评估） |
| semantic health | 总分 99.6 grade OK（元数据 100.0 / 拓扑 98.4 / 去重 100.0 / KG 100.0；2026-07-14 复测同值） | exit 0 | ✅ **已转阻断**（2026-07-14，用户指示全部转阻断；聚合门） |
| authority coverage | 内容页 P0/P1/P2/any 全 100% / none=0 / 核心 L1–L4 无 P0 缺口=0（2026-07-12 补齐唯一 P2 缺口页）；`--include-crates` 扩展：crates docs 非 stub 内容页 64/64=100%，**stub canonical 链接 dead=0**（2026-07-14 W2 修复 163 处失效链接后复测）；2026-07-14 --strict --include-crates 实跑 exit 0 | exit 0 | ✅ **已转阻断**（2026-07-14，R4 评估，--strict --include-crates；W3 纳入 stub canonical 链接健康度） |
| examples compile | 14 游离示例：9 stdlib ✅ + 3 deps ✅（经 `examples/examples_check/` crate）+ 2 Cargo Script 豁免；失败 0；2026-07-14 --strict 实跑 exit 0 | exit 0 | ✅ **已转阻断**（2026-07-14，R4 评估；同步新增 CI job `examples-compile`） |
| concept code blocks | 4977 块分 10 桶；**2026-07-14 复测 rot=0**：candidate 抽样 300 pass/0 fail + compile_fail 822 ok/0 标注腐烂（--strict 默认抽样实跑 exit 0）；前序 R2b rot=1（双 main 对比块）已清零，详见 `reports/CODE_BLOCKS_R2B_2026_07_14.md` 与 `reports/CONCEPT_CODE_BLOCKS_BASELINE_2026_07_13.md` | exit 0（2026-07-14 复测） | ✅ **已转阻断**（2026-07-14，用户指示全部转阻断；--strict 默认抽样） |
| mindmap coverage | 内容页 404（已排除 quiz 评估页 21 + SUMMARY/sources/topic_index/1.98 骨架 5）：mindmap **404（100.0%）** / 反例 **399（98.8%）**（2026-07-14 复测；--strict 基线 mindmap≥10%/反例≥40%） | exit 0 | ✅ **已转阻断**（2026-07-14，用户指示全部转阻断；口径说明见 `scripts/check_mindmap_coverage.py`） |
| quiz system | 注册表 21 独立 quiz 全一致 / 题型均≥3 种 / 难度标注 309/309=100% / quiz→concept 21/21、concept→quiz 回链 21/21；2026-07-14 --strict 实跑 exit 0 | exit 0 | ✅ **已转阻断**（2026-07-14，R4 评估，--strict 检查 1–3 失败即阻断） |

**去重 v2 转阻断完成（P2-5 收尾，2026-07-12）**：v1（阻断门 8）报 1 对而 v2 报 552 对，v1 漏检属实；v2 可处理项 54 已于 2026-07-12 清零——autoverus 近克隆对（双向计数 2）按 canonical 裁定差异化改写（L4 `04_formal/04_model_checking/07_autoverus.md` 保留为概念权威页，L7 `07_future/03_preview_features/33_autoverus_preview.md` 改写为预览跟踪页），其余 52 对逐对人工复核后登记 SERIES 白名单（docs/05_practice 项目指南系列 48 对 + design_theory 子目录索引系列 4 对，证据注释见 `scripts/triage_overlap.py` `SERIES_PATH_RE`）。本门已转阻断：`run_quality_gates.sh` 与 `quality_gates.yml` 中可处理项（MERGE+DOCS_INTERNAL）> 0 即 exit 1，nightly 同步纳入 issue 触发条件。SERIES 白名单：`triage_overlap.py` 正则 + `SERIES_PATH_RE` 路径族 + 显式 `SERIES_PAIRS` 登记（2026-07-12 人工复核：c10 examples_collection/part2 分章、c02 readme_rust_189/190 版本系列、docs/05_practice 项目系列、design_theory 索引系列）。

---

## 6. 修改时必须遵守的红线

1. **不要** 在 `book/` 中直接修改内容（除 `book/README.md`）。
2. **不要** 将 `tmp/` 中的临时文件提交到版本控制。
3. **不要** 在 `archive/` 中创建新的活跃内容副本。
4. **不要** 在 `crates/*/docs/` 中复制通用概念解释；应链接到 `concept/`。
5. **新增重复内容必须被 CI 或人工 review 拦截**。
6. **禁止未经验证的“完成”声明**：任何“已完成/全部通过/100%”类结论必须引用可机器复核的证据（质量门报告、脚本输出、CI 记录），且必须覆盖全部 23 个阻断质量门（当前 0 个语义观察门；若将来新增观察门，亦须一并核对）；仅部分门通过不得宣称“质量门全部通过”。报告与观察门状态矛盾时，以观察门最新报告为准并勘误原报告。

---

## 7. 长期治理机制

| 机制 | 频率/触发条件 | 工具/负责人 |
|---|---|---|
| 内容重叠检测 | 每次 PR / 每周 | `scripts/detect_content_overlap.py` |
| 死链检查 | 每次大规模合并后 | `scripts/kb_auditor.py`（覆盖 concept/ + docs/ + content/ + knowledge/） |
| 归档审计 | 每季度 | 人工 + 脚本 |
| 版本页中心化管理 | Rust 新版本发布时 | `concept/07_future/rust_1_XX_*.md` |
| 版本新鲜度巡检 | 每周（手动，不挂 CI 门：网络依赖检查不适合阻断） | `scripts/check_authority_freshness.py` |
| 夜间质量报告 | 每天 | `.github/workflows/nightly_quality_report.yml` |
| pre-commit 检查 | 每次本地提交 | `scripts/git_hooks/pre-commit` |

---

**最后更新**：2026-07-14（已对齐 Rust 1.97.0 stable；23 门全阻断：23 阻断 + 0 观察）
