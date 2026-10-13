# T9 i18n 试点预研评估报告（mdbook-i18n-helpers / gettext）

- **日期**: 2026-10-13（只读预研，不实装、不修改项目文件、不 commit）
- **范围**: `G:\_src\rust-lang`（mdbook 0.5.3，`src = "concept"`，`language = "zh"`，约 800 concept 权威页，23 阻断门 + 5 观察门）
- **证据源**: `book.toml`、`concept/SUMMARY.md`（807 行）、`scripts/run_quality_gates.sh`（119 行）、`scripts/check_naming_convention.py`、`scripts/check_canonical_uniqueness.py`、`scripts/check_metadata_consistency.py`、`scripts/check_concept_numbering.py`、`scripts/add_bilingual_annotations.py`、`scripts/detect_content_overlap_v2.py`、`.github/workflows/mdbook_pages.yml`、`.github/workflows/quality_gates.yml`、crates.io API、google/mdbook-i18n-helpers（README/USAGE/CHANGELOG）。

---

## 1. mdbook-i18n-helpers 现状与 mdbook 0.5 兼容性

### 1.1 版本与兼容性结论

| 事实 | 证据 |
|---|---|
| 最新稳定版 **mdbook-i18n-helpers 0.4.0**（2025-11-27 发布，作者 qwandor/Andrew Walbran，Google 项目 mgeisler 主导） | crates.io API：`max_stable_version = 0.4.0`，14 个版本，累计下载 1,006,351，近期下载 113,976 |
| **0.4.0 已适配 mdbook 0.5**：依赖 `mdbook-driver ^0.5.0` / `mdbook-preprocessor ^0.5.0` / `mdbook-renderer ^0.5.0` | crates.io 0.4.0 依赖清单 |
| 0.4.0 的变更即 "Update to mdbook 0.5 by @ehuss"（PR #284，mdbook 维护者亲自适配） | i18n-helpers/CHANGELOG.md |
| 旧版 0.3.6（2025-02）钉 mdbook 0.4.44，**与本项目 mdbook 0.5.3 不兼容** | CHANGELOG 0.3.6 条目 |
| 本项目 `book.toml` 已按 0.5 适配（移除 `build-dir`/`copy-fonts`，注释明确 mdbook 0.5.3） | book.toml NOTE 2026-10-13 |

**结论：mdbook-i18n-helpers 0.4.0 与本项目 mdbook 0.5.3 兼容，且适配由 mdbook 上游维护者完成，兼容性风险低。** 必须用 0.4.0，不可用 0.3.x。

### 1.2 工具链（三个二进制，`cargo install mdbook-i18n-helpers` 一次装齐）

| 工具 | 角色 | 用法 |
|---|---|---|
| `mdbook-xgettext` | mdbook **renderer**：从 Markdown 提取原文生成 `messages.pot` | `MDBOOK_OUTPUT='{"xgettext": {}}' mdbook build -d po`；`{"xgettext":{"depth":"1"}}` 按章节拆分多个 POT；`output.xgettext.granularity` 控制行号取整以减少 PO 抖动 |
| `mdbook-gettext` | mdbook **preprocessor**：按 `book.language` 加载 `po/<lang>.po` 翻译书本；找不到对应 po 时原样输出（不翻译） | `book.toml` 加 `[preprocessor.gettext] after = ["links"]`；构建译文：`MDBOOK_BOOK__LANGUAGE=en mdbook build -d book/en` |
| `mdbook-i18n-normalize` | PO 文件规范化（升级 helpers 版本后一次性迁移，保留已有译文） | 版本升级后跑一次 |

配套 GNU gettext 工具：`msginit -i po/messages.pot -l en -o po/en.po`（初始化）、`msgmerge --update po/en.po po/messages.pot`（源文变更后增量更新，fuzzy 标记机制）。

**关于任务中提到的 "mdbook-md2po / po2md"**：mdbook-i18n-helpers 仓库中**不存在** `mdbook-md2po` 工具。`md2po`/`po2md` 是 **Translate Toolkit**（Python，translate-toolkit 3.19.x）的独立 Markdown↔PO 工具链，与 mdbook 无集成（不处理 SUMMARY.md 链接重写、不处理 mdbook 预处理产物如 `{{ #include }}`）。两条路线：
- **主路线（推荐）**：mdbook-xgettext + mdbook-gettext（mdbook 原生渲染器/预处理器，链接解析、include 展开、代码块只提取字符串字面量与注释——0.3.0 起的关键特性，对代码密集型 Rust 文档至关重要）。
- 备选：translate-toolkit md2po/po2md（把译文 .md 实体化落盘，与本项目 concept/ 门冲突面更大，见 §3）。

### 1.3 提取控制标记（实装时的关键机制）

- `<!-- i18n:skip -->` / `<!-- i18n:skip-start -->`…`<!-- i18n:skip-end -->`：跳过指定块（如整段代码块、元数据 blockquote）。
- `<!-- i18n:comment: XXX -->`：给 msgid 附加译者注释。
- 代码块默认只提取字符串字面量与行注释（0.3.0+），Rust 示例代码本体不进 PO——对本项目高度有利。
- 生产案例：Comprehensive Rust（Google 官方课程，多语言站点即此方案 + GitHub Actions 分语言构建 publish.yml）。

### 1.4 平台注意

- 三个二进制为 Rust 程序，Windows 可 `cargo install`；但 `msginit`/`msgmerge`（GNU gettext）Windows 原生不可用，需 WSL/MSYS gettext 包或 CI（ubuntu-latest，本项目 CI 全部 ubuntu）中执行。
- 本项目 `Cargo.lock` 不含 mdbook（mdbook 是外部 CLI，非 workspace 依赖）→ 安装 i18n-helpers 不影响 workspace 的 Cargo 门（check/test/clippy/audit/vet）。

---

## 2. 本项目适配性分析

### 2.1 页面头部样板对 gettext 提取的适配度

实测样板（`concept/01_foundation/00_start/00_start.md`，342 行）：文首为 blockquote 元数据块——`> **EN**: Getting Started with Rust`、`> **Summary**: …`、`> **Rust 版本**`、`> **权威来源**`、`> **前置/后置概念**`（含相对链接）、`> **来源**`（外链列表）。

- **适配点（高）**：本项目双语结构是「中文正文 + 头部 `**EN**`/`**Summary**` 英文字段」。gettext 方向恰好是 **zh→en**：msgid 为中文原文，msgstr 为英文译文；现有 `**EN**` 字段可直接作为**翻译记忆种子**（初始化 po 时人工/脚本预填 msgstr），显著降低冷启动成本。
- **摩擦点 1（提取噪音）**：mdbook-xgettext 会把整个 blockquote 元数据块当作可译消息提取（`**权威来源**: 本文件为 concept/ 权威页。` 等 800 页重复样板会进 PO）。缓解：实装时在样板块前加 `<!-- i18n:skip-start -->`/`skip-end`（需改源文件——试点阶段仅对试点页做，或接受样板 msgid 由 msgmerge 去重管理）。
- **摩擦点 2（msgid 语言）**：gettext 惯例是 msgid=英文源文；本项目 msgid=中文。技术上完全支持（Gettext 不要求源语言），但部分 PO 编辑器/MT 工具对非英文 msgid 的默认语言检测需手工指定 `Language: en` 头（msginit 已处理）。
- **摩擦点 3（元数据字段一致性）**：译文构建产物中头部字段（Bloom 层级/权威来源等）若被翻译，与 `check_metadata_consistency.py` 的 FIELD_RE（`^>\s*\*\*(.+?)\*\*\s*[:：]`）匹配的是**源文件**而非构建产物——只要译文不落盘进 concept/，此门完全不受影响（见 §3 场景 A）。

### 2.2 SUMMARY.md 多语言侧边栏方案

`concept/SUMMARY.md`（807 行）是单一导航清单，mdbook 无内建语言切换器。三个方案：

| 方案 | 做法 | 门风险 | 评价 |
|---|---|---|---|
| **A. 分语言独立构建（推荐）** | 主书 SUMMARY.md 不动；`MDBOOK_BOOK__LANGUAGE=en mdbook build -d book/en` 产出独立英文书；GitHub Pages 挂 `/en/` 子路径；语言切换用 `additional-js` 或页尾互链（Comprehensive Rust 模式） | 对 concept/ 内容门**零接触**；仅 mdbook_pages.yml 加 matrix job | 与 23 门兼容性最好 |
| B. 单 SUMMARY 双语条目 | SUMMARY.md 同时列 zh 与 en 副本条目 | 触发链接门/命名门/canonical 门（en 副本必须实体化进 src） | 不推荐 |
| C. po 化 SUMMARY | SUMMARY.md 本身进 PO，译文预处理器翻译侧边栏文本 | 需 `po/en.po` 含 SUMMARY 消息；mdbook-i18n-helpers 0.3.0 起支持 SUMMARY 内格式化 | 可与方案 A 组合（英文书侧边栏自动英文化），不新增 concept/ 文件 |

**推荐 A + C 组合**：英文书独立构建、侧边栏由 gettext 翻译，主书与 SUMMARY.md 源文件零改动。

### 2.3 既有先例

`concept/00_meta/04_navigation/14_learning_mvp_path_en.md`（292 行，英文 MVP 路径草案）是**已存在于 concept/ 内并通过全部 23 门的英文副本**——它在 `check_canonical_uniqueness.py` 的白名单中登记（该文件 185 行处显式列出路径）。这证明：(a) 门机制可以容纳受控英文副本；(b) 项目已有 zh/en 双页手工维护的痛点（该文件头部自注「部分链接可能与当前目录结构不一致，请以中文版为权威」）——正是 gettext 流水线要解决的问题。

---

## 3. 与 23 阻断门的兼容性风险清单（逐门评估）

前提区分两个场景：
- **场景 A（推荐实装形态）**：`po/` 目录置于仓库根（不在 `concept/` 内），译文只存在于构建产物 `book/en/`，**concept/ 内不落任何翻译副本**。
- **场景 B（高风险形态）**：用 po2md 之类把译文 `.md` 实体化写回 `concept/`（或 `concept/i18n/` 子目录）。

`run_quality_gates.sh` 全部 23 阻断门逐门评估：

| # | 门 | 场景 A | 场景 B | 冲突点说明 |
|---|---|---|---|---|
| 1-5 | Cargo Check/Test/Clippy/Audit/Vet | 无 | 无 | mdbook-i18n-helpers 经 `cargo install` 装到用户工具链，不进 workspace；`.po` 非 Rust 源 |
| 6 | mdbook Build | **中** | 中 | book.toml 加 `[preprocessor.gettext]` 后默认 `mdbook build`（language=zh、无 po/zh.po）应原样通过——需实跑验证；场景 B 中 SUMMARY 改动直接进此门 |
| 7 | KB Auditor Link Check | 低 | **中** | 场景 A 仅当 SUMMARY/页脚新增 en 互链时触发；场景 B 副本内相对链接全量受检 |
| 8 | Content Overlap v1 | 无 | **高** | zh/en 副本对被判近重复 |
| 9 | i18n Term Coverage（add_bilingual_annotations --mode check-only） | 无 | **高** | 该门 `rglob("*.md")` 扫整个 concept/；副本缺 EN/Summary 头或未标注术语即失败 |
| 10 | Mermaid Syntax Check | 无 | 低 | 副本含 mermaid 才受检 |
| 11 | Topology Quality (strict) | 低 | 中 | 副本新增节点/边扰动拓扑基线 |
| 12 | KG SHACL Validation (strict) | 无 | 中 | KG 从 concept 页抽取，副本污染图谱实体 |
| 13 | KG SHACL Real Engine Validation (strict) | 无 | 中 | 同上 |
| 14 | Canonical Uniqueness (strict) | 无 | **高** | zh/en 同主题对触发唯一性违规；需逐对登记白名单（先例：14_learning_mvp_path_en.md）；800 页规模下白名单不可维护 |
| 15 | Concept Consistency Audit (strict) | 无 | 中 | 副本参与一致性比对 |
| 16 | Concept Authority Coverage (strict) | 无 | 中 | 副本被计入权威页覆盖统计，稀释/扭曲覆盖率基线 |
| 17 | Examples Compile (strict) | 无 | 无 | 扫描 examples/，不涉 concept 译文 |
| 18 | Naming Convention (strict) | 低 | 中 | 门 SCAN_ROOTS=concept/knowledge/docs/content/crates/*/docs，根级 `po/` 不被扫（安全）；场景 B 副本须 `NN_snake_case`（`_en` 后缀合法，但禁 `*_final` 等变体后缀；CJK 文件名禁） |
| 19 | Quiz System (strict) | 无 | 低 | 副本无 quiz 反向链 |
| 20 | Metadata Consistency (strict) | 无 | **高** | 门 `glob concept/**/*.md`；副本缺 Bloom/版本/A-S-P/内容分级字段 → D1-D3 直接超阈值 |
| 21 | Concept Code Blocks (strict) | 无 | 中 | 副本内 rust 块被重复提取编译抽样，拉长门时长、可能引入标注腐烂误报 |
| 22 | Mindmap Coverage (strict) | 无 | 低 | mindmap≥10%/反例≥40% 比率基线被副本稀释 |
| 23 | Semantic Health (strict) | 无 | 中 | 全 concept 语义扫描纳入副本 |
| + | Content Overlap v2（脚本内联阻断，可处理项基线=0） | 无 | **高** | zh/en 近重复对判 MERGE → 可处理项 >0 直接阻断；SERIES 白名单机制（triage_overlap.py SERIES_PATH_RE）可登记但每对需人工复核证据 |

**风险计数**：
- 场景 A（推荐）：**0 高 / 2 中**（mdbook Build 配置变更、KB Auditor 互链）/ 4 低 / 17 无。
- 场景 B（副本进 concept/）：**5 高 / 10 中 / 3 低 / 5 无**——高冲突门：Overlap v1、Overlap v2、Canonical Uniqueness、i18n Term Coverage、Metadata Consistency。

**核心结论**：gettext 流水线的「PO 在 src 外、译文只在构建产物」形态与本项目门体系天然兼容；冲突全部来自「把译文 .md 写回 concept/」这一反模式。AGENTS.md §2 Canonical 单一权威规则与「只移动不删除」红线在场景 A 下完全不被触碰。

---

## 4. 试点目录选型建议

候选对比：

| 维度 | `concept/01_foundation/00_start/`（10 文件） | `concept/00_meta/04_navigation/`（15 文件） |
|---|---|---|
| 内容形态 | 概念权威页：正文+rust 代码块+决策树 mermaid+大量内/外链+完整元数据头——**对提取管线是完整压力测试** | 导航索引页：表格+链接清单为主，代码块少——测试覆盖不全（代码块提取、skip 标记等关键路径测不到） |
| 门暴露面（若试点出错需副本兜底） | 高：canonical/authority coverage/code blocks/mindmap 等门全涉及 | 低：导航页非概念权威页，已有 D2 白名单先例（13_foundations_gap_closure_index.md）与 en 副本先例（14_learning_mvp_path_en.md） |
| 翻译价值 | 最高：英文读者入口页、初学者旗舰 | 中：索引页翻译后信息密度低（大量链接锚文本重复） |
| 规模 | 00_start.md 342 行 + 9 页，PO 体量可控 | 02_career_landscape.md 等长文混杂，体量不均 |

**推荐：`concept/01_foundation/00_start/` 作为试点内容目录。** 理由：(1) 它是唯一能同时验证「正文提取、代码块只取字符串/注释、blockquote 元数据 skip 标记、内链在译文构建中的解析」四条关键路径的候选；(2) 场景 A 下它虽属权威页但**门暴露为零**（concept/ 内无任何新文件），其"门暴露面高"的劣势不成立；(3) 翻译价值最高，试点成果可直接服务英文读者；(4) 10 文件规模适中，单轮试点可完成。`04_navigation` 作为**备选/第二波**：其 14_*_en.md 先例证明若未来确需在 concept/ 内保留英文实体页，白名单机制可用，但不应作为 gettext 试点的落点。

---

## 5. 实装步骤草案（不执行）与回退方案

### 5.1 步骤草案（试点，约 1-2 人日）

1. **工具安装（项目外）**：`cargo install mdbook-i18n-helpers`（得 0.4.0）；Windows 本地另备 gettext（WSL/MSYS）或约定 POT/PO 操作只在 CI/WSL 执行。
2. **试点提取**：mdbook-xgettext 按 SUMMARY.md 全量提取——800 页全量 POT 不是试点目标。做法：在仓库外（scratch）建试点书壳：复制 book.toml + 仅含 00_start 章节的 SUMMARY.md + 符号链接/junction 指向 concept 内容目录，`MDBOOK_OUTPUT='{"xgettext":{"depth":"1"}}' mdbook build -d po` 产出分章 POT。仓库内正式化时再决定 `po/` 落点（建议仓库根 `po/`，`.gitignore` 只忽略 `po/messages.pot`，`po/en.po` 入库）。
3. **初始化英文 PO**：`msginit -i po/messages.pot -l en -o po/en.po`；用试点页现有 `**EN**`/`**Summary**` 字段脚本预填 msgstr（翻译记忆种子）。
4. **样板降噪**：对试点 10 页的头部 blockquote 加 `<!-- i18n:skip-start -->`/`skip-end`（这是试点唯一允许的源文件改动，纯注释行，不改内容语义，不违反「只移动不删除」）。
5. **译文构建**：book.toml 加 `[preprocessor.gettext] after = ["links"]`（可加 `optional = true` 降低默认构建风险）；`MDBOOK_BOOK__LANGUAGE=en mdbook build -d book/en` 本地验证渲染、链接、MathJax、mermaid。
6. **门回归**：跑 `scripts/run_quality_gates.sh` 全量，确认 23 门 exit 0（预期仅门 6 需观察）。
7. **CI 接入（试点通过后）**：mdbook_pages.yml 加 matrix：`MDBOOK_BOOK__LANGUAGE=en mdbook build -d book/en` + Pages 发布 `/en/`；quality_gates.yml 可选加「POT 新鲜度」观察门（`mdbook build -d po && git diff --exit-code po/` 变体）。
8. **翻译工作流**：源文变更 → `mdbook build -d po` → `msgmerge --update po/en.po po/messages.pot` → Poedit 清 fuzzy → 重建。

### 5.2 回退方案

- **触发条件**：门回归失败且当日不可修 / mdbook 0.5 与 helpers 出现兼容 bug / PO 维护成本超预估。
- **回退动作**：`git revert` book.toml 的 preprocessor 块与试点页 skip 注释；`po/` 目录整体删除或移入 `archive/`（遵守「只移动不删除」：移入 `archive/i18n_pilot_2026Q4/` 保留证据）。
- **回退安全性**：场景 A 不产生任何 concept/ 内容变更，回退即恢复原状，零数据损失；构建产物 `book/`、`book/en/` 本就不入库。
- **不可回退项**：无（试点不迁移既有 14_learning_mvp_path_en.md；该页保留现状，未来第二波再决定是否并入 PO 流程——若并入，按「只移动不删除」将其移 archive 需单独评审）。

### 5.3 遗留风险与观察项

1. 全量 POT（800 页）体量与 msgmerge 抖动：用 `granularity` 取整 + `depth` 分章缓解，试点期实测。
2. `mdbook build` 门在新增 preprocessor 后的行为需实跑确认（找不到 `po/zh.po` 时应 passthrough——USAGE 明示，但需本项目实证）。
3. Windows 本地 gettext 工具链缺口：约定 CI/WSL 为 POT/PO 操作环境。
4. 搜索索引：英文书独立构建会产生独立 searchindex（本项目已有 55MB 索引告警先例，`/en/` 子书体量小，可接受）。

---

## 6. 结论

- **可行性**：高。mdbook-i18n-helpers 0.4.0 与 mdbook 0.5.3 官方兼容；zh→en 方向与项目双语结构互补（EN 字段=翻译种子）。
- **门兼容**：推荐形态（po/ 在 src 外 + 分语言独立构建）下 23 门风险为 0 高/2 中；严禁把译文 .md 写回 concept/（该形态 5 高冲突门）。
- **试点目录**：`concept/01_foundation/00_start/`。
- **下一步**：按 §5.1 八步实装（先 scratch 壳验证提取，再决定 po/ 入库与 book.toml 改动），门回归通过后接 mdbook_pages.yml matrix。
