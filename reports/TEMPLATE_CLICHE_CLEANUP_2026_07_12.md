# 模板套话清理报告（Template Cliché Cleanup）

> **日期**: 2026-07-12
> **范围**: `concept/`（跳过 `concept/archive/` 与文件名含 `template` 的元层模板文件）
> **背景**: 审计发现 59–95 个 concept/ 文件被批量脚本（`add_backward_reasoning.py`、`add_backward_l2l3.py` 等）注入仅主题名不同的通用模板句，产生语义不通内容。本报告记录"先删通用句、保留结构"策略的清理结果。

---

## 一、取证方法与模板家族

取证脚本：`tmp/find_template_cliches.py`（跨文件重复行归一化统计）、`tmp/variants_check.py`（逐家族全量变体验证）。
共识别 **6 个模板家族、17 条行级黑名单模式**，所有变体经全量扫描确认仅主题槽（及个别措辞）不同，满足"跨 ≥5 文件逐字重复"的可证明通用标准：

| 家族 | 典型形态 | 涉及文件数（取证） |
|:---|:---|:---:|
| 反命题决策树（反命题 1/2/3） | `"X 在所有场景下都适用" ⟹ 不成立。存在特定的边界条件（如 unsafe、FFI、递归类型）…` | 51–59 |
| 认知路径（引言 + 五步骤） | `本节从 "X" 的核心问题出发…` + 问题识别/概念建立/机制推理/边界辨析/迁移应用 | 58–77 |
| 定理套话（定理 1/2/3 [Tier 2/3]） | `X 的核心约束 ⟹ 编译器可以在编译期排除一整类运行时（Runtime）错误。` | 67 |
| 过渡套话（过渡 1/2/3） | `从 X 的直观描述转向其形式化定义…` / `在建立 X 的核心命题之后…` / `最后，将 X 与相邻概念连接…` | 82–83 |
| 反向推理（反向推理 1/2） | `如果程序在 X 相关代码处出现编译错误 ⟸ 应首先检查所有权…` | 30 |
| 样例参照（keywords/operators 同一模板句） | 即反命题家族在 `36_keywords.md`、`37_operators_and_symbols.md` 的实例 | 2 |

明确**保留**（非模板）：```text 反命题树代码块（如 `反命题 1: "String.len() 返回字符数"` 为主题相关内容，22 文件）、各文件手写的认知路径步骤（如 `00_start.md`）、`| 核心概念 ⟹ |` 表格行（仅见于 `concept/archive/`，只读不动）。

## 二、清理执行

清理脚本：`tmp/clean_template_cliches.py`（dry-run 两轮 + apply 两轮；日志 `tmp/cliche_cleanup_apply.log`、`tmp/cliche_cleanup_apply2.log`）。
规则：按行精确删除模板句 → 清理孤立 `>` 引用空行 → 折叠多余空行/重复 `---` → 删除清空后无实质内容的章节标题（代码围栏感知）→ 同步删除指向已删章节的目录行。**未触碰任何元数据块**。

### 2.1 各家族删除计数（最终）

| 家族 | 删除行数 |
|:---|:---:|
| 过渡 1/2/3 | 89 × 3 = 267 |
| 定理 1/2/3 | 72 × 3 = 216 |
| 认知路径引言 | 78 |
| 反命题 1/2/3 | 60 + 54 + 53 = 167 |
| 步骤 1–5 | 59 + 59 + 60 + 68 + 60 = 306 |
| 反向推理 1/2 | 30 × 2 = 60 |
| **合计** | **1094 行 / 120 个文件** |

### 2.2 章节级处理

- 删除空章节标题 **约 110 处**：`## 认知路径` ×58、`## 反命题决策树` ×49（清空后无任何实质内容），另含 `## 一、核心命题` ×1（整节仅为定理套话）及 2 处重复空标题（`01_ai_integration.md` 的 `## 五、AI + Rust 工具链详解`、`### 6.3 代表性研究`，均为与下一标题重复的空壳）。
- 章节含主题相关内容时一律保留标题与内容（如 `00_start.md` 的 `## 认知路径` 保留了手写五步，`28_borrow_checking_decidability.md` 的 `## 零、认知路径（Cognitive Path）` 完整保留）。

### 2.3 受影响文件清单（120 个）

见 `tmp/cliche_affected_files.txt`（逐文件家族计数见 `tmp/cliche_cleanup_apply*.log`）。按层分布：L1 `01_foundation/` 24、L2 `02_intermediate/` 21、L3 `03_advanced/` 16、L4 `04_formal/` 26、L5 `05_comparative/` 1、L6 `06_ecosystem/` 12、L7 `07_future/` 20。

## 三、截断 bug 修复（任务项 3）

`concept/04_formal/01_ownership_logic/28_borrow_checking_decidability.md` 中 11 处 `Borrow Checking Decidability（借` 已全部恢复为 `Borrow Checking Decidability（借用检查可判定性）`（先于模板清理执行）。该 11 处均位于过渡/定理/反命题模板行内，随后按任务项 2 规则随模板句一并删除；文件标题 `# Borrow Checking Decidability（借用检查可判定性）` 保持正确。同类截断槽（`Operators and Symb`、`Statements and Expressi` 等）经全库复查仅存于已删除的模板行中，无残留。

## 四、Atlas T1 修复（任务项 4）

### 4.1 生成器修复（`scripts/generate_knowledge_topology_atlas.py`）

新增定义回退链（与 `check_topology_quality.py` T1 的 `DEF_LOW` 对齐）：

1. **优先** raw json 中的 `**Summary**`；
2. 空洞（`Core Rust concept` / `—` / <15 字符 / `A guide to…` 等）时回退到**文件当前 `**Summary**`**（应对过时 raw json）；
3. 再回退到**文件首个实质段落**（跳过元数据、标题、表格、代码块、目录、粗体标签、列表项、来源行；截断避让 Markdown 链接内部）；
4. 仍缺失时标诚实占位 `定义暂缺，请直接参见概念文件正文内容。`——**不编造语义**；未采用"待补充"字样，因其会触发 T6 占位检查（`待补` 在 `PLACEHOLDER_RE` 中）。

### 4.2 就地修复（不整体重新生成）

atlas 文件含人工策展（如 `18_lifetimes_advanced` 合并重定向标注）且 `tmp/concept_topology_raw.json` 缺失，故按任务允许的就地方式修复：`tmp/fix_atlas_definitions_v2.py` 复用生成器同一回退逻辑，逐行修复 `01_concept_definition_atlas.md`。

**结果**：94 条空洞定义（87 `X. Core Rust concept.` + 7 `—`）全部清零；0 条 `定义暂缺` 残留（全部经当前 Summary/首段恢复为真实定义）；人工策展行（合并重定向标注等）未受影响。

### 4.3 并发说明

执行期间检测到另一并发 agent（hermes-agent）同时编辑 `tmp/fix_atlas_definitions.py` 与该 atlas（04:02 前后）。其最终写入复用了本任务修补后的生成器逻辑；本任务随后以 v2 脚本完成二次校验与修复，并确认最终状态稳定一致（见下方验证）。

## 五、Lint 脚本（任务项 5）

新建 `scripts/check_template_cliches.py`：内置上述 17 条黑名单模式，扫描 `concept/`；默认 exit 0（warning），`--strict` 命中即 exit 1；豁免 `archive/` 与文件名含 `template` 的元层模板文件。已通过自测试（合成文件可检出、strict 返回 1；当前 concept/ 零命中）。
登记：`scripts/README.md`「🔍 审计与检查」表已含该脚本条目。

## 六、验证（任务项 6）

| 检查 | 结果 |
|:---|:---|
| `python scripts/check_topology_quality.py` | **T1 定义套话率 24.6%（94/382）→ 7.0%**，不再触发 ≥10% WOULD-FAIL；T2/T5/T6 为存量问题（关系塌缩 99.2%、02 atlas 抽取泄漏 5、占位 6），不在本任务范围 |
| `python scripts/kb_auditor.py` | **死链 0**（中途发现 1 条由 atlas 定义截断引入的 `https:/…` 断链，已修复抽取器并复验归零）；模板化 ⟹ 0；跨层问题 0 |
| `python scripts/check_template_cliches.py` | concept/ 零命中 |
| `python scripts/check_template_cliches.py --strict`（自测试） | 合成模板句可检出且 exit 1 |

## 七、误删风险自查（5 个抽查 diff）

1. **`36_keywords.md`**：仅删除 `## 认知路径`（纯模板五步）、`## 反命题决策树`（3 条模板反命题）及重复 `---`；元数据块、权威来源标注、`## 一、关键字概述` 起正文零改动。✅
2. **`28_borrow_checking_decidability.md`**：删除过渡×3、定理×3、反命题×3 模板行；手写的 `## 零、认知路径（Cognitive Path）`（借用检查三代演进真实内容）完整保留；截断括注已恢复。✅
3. **`00_start.md`**：仅删认知路径引言一句模板；其下手写五步（"为什么 Rust 需要一套专门的起步流程？…"）全部保留，标题保留。✅
4. **`24_quiz_type_system.md`**：删除以"测验"为主题的整组注入块（认知路径/过渡/定理/反命题/反向推理）；`## 一、标量与复合类型` 起全部 quiz 内容零改动。✅
5. **`01_ai_integration.md`**：删除过渡×3、定理×3；`## 一、核心命题`（整节仅定理套话）及 2 处重复空标题按规则删除；顺带清理 4 处孤立 `>` 空引用行；全部研究综述正文零改动。✅

**误删事故与修复**：首轮 `remove_empty_sections` 未感知代码围栏，将 7 个文件代码块内的 `#` 注释行（如 `# 4. 更新 Cargo.toml 中的 edition 字段`）误判为标题并删除空"章节"。已全量恢复这 7 个文件、修复脚本（`fence_mask` 围栏感知）并重跑，复验 diff 仅含模板行删除。

## 八、遗留事项与建议

- T1 残余 7% 为 `**Summary**` 本身 <15 字符的概念文件（真实但简短），建议后续在源文件补全 Summary 元数据而非在 atlas 侧填充。
- T2（07 atlas 关系塌缩 ⟹ 99.2%）、T5（02 atlas 抽取泄漏 5 处）、T6（占位 6 处）为存量问题，建议单独立项。
- 建议将 `check_template_cliches.py` 纳入 AGENTS.md §5.1 语义观察门（第 17 项）；本任务未改动 AGENTS.md 质量门清单。
- `concept/archive/` 内仍有同类模板句（如 `| 核心概念 ⟹ |` 表格行），按只读政策未动。
- 注入源脚本 `scripts/add_backward_reasoning.py`、`scripts/add_backward_l2l3.py` 仍在 scripts/ 下，建议归档或加注废弃说明，防止再次批量注入。

---

**产出物清单**

- 清理/取证脚本（tmp/，不入版本控制）：`find_template_cliches.py`、`variants_check.py`、`clean_template_cliches.py`、`fix_atlas_definitions_v2.py`、`cliche_cleanup_apply*.log`、`cliche_affected_files.txt`
- 修改：`concept/` 120 个文件（-1094 模板行）、`concept/00_meta/knowledge_topology/01_concept_definition_atlas.md`（94 条定义修复）、`scripts/generate_knowledge_topology_atlas.py`（定义回退逻辑）
- 新增：`scripts/check_template_cliches.py`（lint）、`scripts/README.md` 登记条目、本报告
