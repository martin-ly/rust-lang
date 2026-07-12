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

# 术语表对齐检查（以 concept/00_meta/01_terminology/terminology_glossary.md 为权威表）
python scripts/check_glossary_alignment.py --strict

# 内容完整性审计（TODO/待补充/占位标记 + 空章节量化，复核 reports/CONTENT_COMPLETENESS_CLEANUP_2026_07_12.md）
python scripts/audit_content_completeness.py --json tmp/completeness.json

# MSRV 单一事实源检查（根 Cargo.toml rust-version = 1.97.0 为唯一事实源）
python scripts/check_msrv_consistency.py --strict

# 死链检查
python scripts/kb_auditor.py --link-check
# 或根据项目实际命令调整

# 构建验证
cargo build --workspace
cargo test --workspace

# mdbook 构建（输出到 book/，不应提交）
mdbook build

# 本地一键运行全部 19 个质量门（14 阻断 + 5 语义观察）
bash scripts/run_quality_gates.sh

# 安装 pre-commit hook（会在每次 commit 前自动跑重叠/i18n/死链检查）
bash scripts/git_hooks/install.sh
```

### 5.1 CI 质量门（19 项：14 阻断 + 5 语义观察）

所有合并到 `main`/`master` 的变更必须通过以下 **14 个阻断质量门**；另有 **5 个语义观察门**（warning，不阻断，默认 exit 0，加 `--strict` 可转阻断）持续追踪语义健康：

**阻断门（14）**：

1. `cargo check --workspace`
2. `cargo test --workspace --quiet`
3. `cargo clippy --workspace -- -D warnings`
4. `cargo audit --no-fetch`
5. `cargo vet --locked`
6. `mdbook build`
7. `python scripts/kb_auditor.py`（死链/跨层/模板化 ⟹，EXIT 非 0 即阻断）
8. `python scripts/detect_content_overlap.py`
9. `python scripts/add_bilingual_annotations.py --mode check-only`
10. `mermaid` 语法检查（CI job；本地见 `scripts/run_quality_gates.sh`）
11. `python scripts/check_topology_quality.py --strict`（atlas 拓扑 T1–T6；2026-07-12 转正，见 §5.2）
12. `python scripts/check_kg_shapes.py --strict`（KG SHACL/形态；2026-07-12 转正）
13. `python scripts/check_canonical_uniqueness.py --strict`（concept 权威页唯一性；2026-07-12 转正）
14. `python scripts/concept_consistency_auditor.py --strict`（跨文件概念定义一致性；2026-07-12 转正）

**语义观察门（5，非阻断）**：
15. `python scripts/check_metadata_consistency.py`（元数据 D1–D6；D2=1/D5=17 未达标）
16. `python scripts/detect_content_overlap_v2.py --budget 999999`（段落级重叠 v2；可处理项 MERGE+DOCS_INTERNAL=53>0，超基线 WARN 升级判定见 `run_quality_gates.sh` 与 §5.2）
17. `python scripts/semantic_health.py`（综合语义健康分；grade=FAIL 时 --strict 才阻断）
18. `python scripts/check_concept_authority_coverage.py`（concept 权威层国际化权威来源覆盖率；--strict 已支持但当前 exit=1，见 §5.2）
19. `python scripts/check_examples_compile.py`（根 examples/ 游离示例编译保护；9 stdlib rustc 直编 + 3 依赖示例经 `examples/examples_check/` crate + 2 Cargo Script 豁免；2026-07-12 新增，P3-5）

> 说明：语义观察门用于“可机器复核的语义趋势”，不因单项退化阻断 PR；但当任一观察门指标显著恶化时，应在 PR 描述中说明原因与后续治理计划。权威覆盖门（18）目标基线为 concept/ 真内容页 any=100%、none=0、核心 L1–L4 无 P0 缺口=0。

### 5.2 观察门转正机制（P3-7，2026-07-12 建立）

**转正规则**：任一语义观察门**连续 4 周（或连续 10 次 CI 运行）达标**，经评估后转为阻断门（在 `run_quality_gates.sh` 与 `quality_gates.yml` 中改为 `--strict` 且 `continue-on-error: false`）。转正前提：本地实跑 `--strict` 当前 exit=0。转正后若指标退化阻断 PR，按正常阻断门流程处置，不自动降级。

**当前各观察门基线状态（2026-07-12，摘自 `reports/` 最新基线）**：

| 门 | 基线指标（2026-07-12） | --strict 实跑 | 状态 |
|---|---|:---:|---|
| topology quality | T1 套话率 1.1% / T2 高频关系 83.3% pass / T3 跳出 16.5% 且死端 0 / T4 定量 93.3% / T5=0 / T6=0 | exit 0 | ✅ **已转阻断** |
| KG SHACL | K1–K6 全 0（K1b 缺 bloomLevel=55，仅扣分不阻断） | exit 0 | ✅ **已转阻断** |
| canonical uniqueness | 0 处双权威页/同主题重复 | exit 0 | ✅ **已转阻断** |
| concept consistency | 0 错误级发现（decision trees 等跨文件引用全有效） | exit 0 | ✅ **已转阻断** |
| metadata consistency | D1=0 / D2=1 / D3=0 / D4=0 / D5=17 / D6=13（flagged 30/483） | exit 1 | ⏳ 维持观察（D2/D5 未达标） |
| overlap v2 | 命中 592；可处理 MERGE=4 + DOCS_INTERNAL=49 = **53**（SERIES 22 白名单 / REVIEW 517） | — | ⏳ 维持观察（可处理项>0；超基线 53 即 WARN 升级，归零后可转阻断 `--strict --budget 0`） |
| semantic health | 总分 90.3 grade OK（元数据 93.8 / 拓扑 90.7 / 去重 85.0 / KG 90） | exit 0 | ⏳ 维持观察（聚合门，待去重分量归零后再评估） |
| authority coverage | 内容页 any=99.5% / none=2 / 核心 L1–L4 无 P0 缺口=1（较 07-11 基线 any=100%/none=0/缺口=0 退化） | exit 1 | ⏳ 维持观察（--strict 已实现，达标后可转正） |
| examples compile | 14 游离示例：9 stdlib ✅ + 3 deps ✅（经 `examples/examples_check/` crate）+ 2 Cargo Script 豁免 | exit 0 | ⏳ 新增观察门（2026-07-12，P3-5；连续达标后可评估转正） |

**去重 v2 转阻断评估（P2-5，2026-07-12）**：v1（阻断门 8）报 1 对而 v2 报 592 对，v1 漏检属实；但 v2 当前可处理项 53>0（前序 P0-5 已处置 54 对后仍有存量），**暂不转阻断**。过渡方案：`run_quality_gates.sh` 中 v2 观察门由“计数报告”升级为“可处理项（MERGE+DOCS_INTERNAL）> 基线 53 即 WARN 升级提示”；可处理项归零后再转为阻断（`--strict --budget 0`）。

---

## 6. 修改时必须遵守的红线

1. **不要** 在 `book/` 中直接修改内容（除 `book/README.md`）。
2. **不要** 将 `tmp/` 中的临时文件提交到版本控制。
3. **不要** 在 `archive/` 中创建新的活跃内容副本。
4. **不要** 在 `crates/*/docs/` 中复制通用概念解释；应链接到 `concept/`。
5. **新增重复内容必须被 CI 或人工 review 拦截**。
6. **禁止未经验证的“完成”声明**：任何“已完成/全部通过/100%”类结论必须引用可机器复核的证据（质量门报告、脚本输出、CI 记录），且必须同时核对 14 阻断门与 5 语义观察门；仅阻断门通过不得宣称“质量门全部通过”。报告与观察门状态矛盾时，以观察门最新报告为准并勘误原报告。

---

## 7. 长期治理机制

| 机制 | 频率/触发条件 | 工具/负责人 |
|---|---|---|
| 内容重叠检测 | 每次 PR / 每周 | `scripts/detect_content_overlap.py` |
| 死链检查 | 每次大规模合并后 | `scripts/kb_auditor.py` |
| 归档审计 | 每季度 | 人工 + 脚本 |
| 版本页中心化管理 | Rust 新版本发布时 | `concept/07_future/rust_1_XX_*.md` |
| 夜间质量报告 | 每天 | `.github/workflows/nightly_quality_report.yml` |
| pre-commit 检查 | 每次本地提交 | `scripts/git_hooks/pre-commit` |

---

**最后更新**：2026-07-10（已对齐 Rust 1.97.0 stable）
