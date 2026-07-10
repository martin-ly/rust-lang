# 全局语义充分性批判审计与可持续推进计划

**日期**: 2026-07-11
**审计范围**: `e:\_src\rust-lang` 全项目（concept/knowledge/docs/content/crates，排除 archive/book/target/.git）
**工具链基线**: Rust 1.97.0 stable
**性质**: 批判性审计（critical audit），非"完成报告"
**审计方法**: 一手抽样（ownership、03/09 atlas、仪表盘、overlap 报告）+ 4 路并行只读量化审计（元数据一致性 / atlas 实质度 / 非 concept 目录重叠与空壳 / Rust 1.97 领域交叉）

> 本报告刻意避免"全部完成 / 10 门全过"式叙事。项目近期已有多份"完成报告"，但审计发现其中若干结论建立在**检查表层存在性**的质量门之上，未能触及**语义充分性、定义唯一性、推理闭环性、跨领域交叉建模**。本报告以可复核的数字与文件路径为证据。

---

## 0. 执行摘要

**一句话结论**：项目不是"全无实质"——核心 L1–L4 权威页（ownership 1897 行、type_system 3280、traits 3081、generics 3247、async 3445、unsafe 3428）确有深度；但存在**结构冗余与局部空洞并存、元数据自相矛盾、拓扑图谱退化为导航浅树、docs/ 以"假 stub 真正文"架空 canonical 规则、Rust 1.97 领域交叉语义严重不足、质量门只数数量不验语义**六类系统性问题。用户的"很多没有实质内容 / 语义不充分 / 缺领域交叉与边界"直觉**被数据证实**，且现有 10 大质量门**无法发现**这些问题。

**七维评分（1=差，5=好）**

| 维度 | 评分 | 关键证据 |
|---|:---:|---|
| 核心权威页实质深度 | 4 | 中位 504 行；L1–L4 主干页定义/矩阵/形式化/决策树/定理链/反例齐全 |
| 全局语义一致性（元数据） | 2 | Bloom↔层次定位 12 例同文件互斥；A/S/P↔Bloom 38.6% 脱节；版本号 3 例自矛盾；20.5% 字段重声明 |
| 概念定义/判定/推理/决策链 | 2 | atlas 平均实质度 2.2/5；定义列 55.8% 套话；推理图 0 条证明草图；判定树叶子大量 `[[见…]]` 跳出 |
| 决策树/图/领域层次可执行性 | 2 | 决策树深度≈5 且只是非问、无定量边界；07 层内映射 99.6% 边塌缩为同一 `⟹`；无闭环 |
| Canonical 单一权威来源落地 | 2.5 | knowledge/content/crates 合规（高）；docs/ 80.5%>150 行、419 篇"贴免责声明的完整正文"（低） |
| Rust 1.97 领域交叉与边界建模 | 2 | 31 项特性版本页单点罗列齐全，核心页零命中或仅横幅回链；零特性×特性交互；edition 2024 × 1.97 割裂 |
| 质量门对语义问题的敏感度 | 1 | 指标全为数量型（⟹≥270、反命题≥40、mermaid≥50）；无法检测定义唯一/推理闭环/版本交叉/decision-tree 可执行 |

---

## 1. 审计方法与数据口径（防"自夸"偏差）

1. **量化优先**：每结论附数字与文件路径，避免形容词判断。
2. **区分"存在性"与"充分性"**：现有质量门只验证前者（EN/Summary 有没有、mermaid 语法、链接死不死）；本审计验证后者（信息量、唯一无矛盾、闭环、可执行、跨领域一致）。
3. **四路独立审计交叉印证**：元数据一致性、atlas 实质度、非 concept 目录重叠、1.97 交叉语义由独立只读审计得出，结论相互印证（如 A/S/P 脱节在元数据审计与 atlas 审计中均出现）。
4. **承认反例**：明确记录"做得好的部分"（核心页深度、knowledge/content/crates 合规、theorem_registry 无残留冲突、kg_shapes.ttl 外部约束为真），避免一棍子打死。

---

## 2. 七大发现（现象 → 证据 → 为何质量门漏检 → 影响）

### 2.1 元数据自相矛盾：全局语义不一致的实锤

- **Bloom 层级 ↔ 层次定位同文件互斥 12 例（2.5%）**：`concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md` 第 17 行标 `层次定位: L1`、第 36 行标 `Bloom 层级: L2-L4`；同类：`02_borrowing.md`(L1 vs L2-L5)、`30_lifetimes_advanced.md`(L1-L3 vs L4-L5)、`01_traits.md`(L2 vs L3-L5)、`02_async.md`(L3 vs L4-L5)。
- **A/S/P 标记与 Bloom 脱节 124/321 = 38.6%**：基础概念被标高阶 P（评价/创造），如 `07_modules_and_items/12_functions.md`(P@L1-2)、`42_useful_development_tools.md`(P@L1-2)、`16_testing_basics.md`(A@L3-4)。
- **版本号同文件自矛盾 3 例**：`08_collections.md`(1.97.0+ 与 1.85.0 并存)、`rust_1_90_stabilized.md`、`rust_1_94_stabilized.md`；稳定层（剔除 07_future）仍有 **119 份（25.1%）** 夹带 nightly/preview/unstable 关键词；`24_async_closures.md` 仍标 1.85.0。
- **元数据膨胀与重声明**：文首 `>` 元数据块中位 20 行、51.5% 文件≥20 行；**97 份（20.5%）字段重声明**（Bloom 重复 37、`Rust 版本` 重复 69）；最冗长 `rust_1_98_preview.md`/`52_robotics.md` 50 行元数据，超过一个正文小节。
- **Summary 套话 44/474 = 9.3%**：集中在 `00_meta/*` 自动桩（`X. Core Rust concept.`）。

**为何质量门漏检**：i18n 检查只看 EN/Summary **是否存在**，不看信息量与一致性；没有任何门禁比对同一文件内两个层级字段、或跨文件版本语义。
**影响**：当"权威页"自身对"这是 L1 还是 L2-L4""这是结构还是评价""适用 1.85 还是 1.97"给出冲突答案时，下游所有 atlas/KG/学习路径都会继承矛盾，**全局语义一致性从源头受损**。

### 2.2 拓扑图谱 atlas = 导航索引 + 浅树，非可执行推理结构

`concept/00_meta/knowledge_topology/` 12 文件审计（平均实质度 2.2/5）：

| 文件 | 行数 | mermaid | 关键问题 |
|---:|---:|---:|---|
| 01 概念定义图 | 473 | 0 | 382 条目**定义列 55.8% 为模板套话**（`X: core Rust concepts…`、`Guide to NN`、`—`），仅 44.2% 有真定义 |
| 02 属性关系图 | 450 | 0 | 定理链列仅 8% 为真链、A/S/P 列 64% 为 `—`；4 处单元格泄漏 `> > [`/`> **`（抽取 bug） |
| 03 场景决策树 | 142 | 3 | 自述"navigational index，不重复正文"；3 树深度≈5，判定仅是非问、无定量边界 |
| 04 示例反例图 | 131 | 1 | 实质度 1/5，几无可执行反例结构 |
| 05 逻辑推理图 | 124 | 3 | **0 条"前提→推论→证明草图"**，全是 `X ⟹ Y + 一句说明 + 链接` |
| 07 层内映射图 | 314 | 0 | 244 条边 **99.6% 为同一符号 `⟹`**，承诺的等价/蕴含/依赖/互斥四类关系塌缩为共引邻接表 |
| 09 推理判定树 | 154 | 5 | 最好：23 根因节点/20 修复边，但仅 15 条真三元组（65%），5 条 `[[见…]]` 跳出、3 条有根因无修复（死端） |
| kg_ontology_v2 | 319 | 0 | 6 类全扁平 `subClassOf skos:Concept`、无 disjoint/axiom；SHACL 实质在外部 `kg_shapes.ttl`；`kg-validate`/`c13_semantic_web` **"待落地"不存在** |

- **无闭环**：12 文件无任一形成"问题→判定→推理→决策→验证"闭环；互引仅为"相关元页"导航列表；09 把"验证"外包给 Miri/Kani 链接；03/05/09 之间无共用节点 ID/无回边。
- **dangling-link 风险**：git 暂存区正将 `00_framework/03_bloom_taxonomy.md` 等去编号化重命名，而 01/02 atlas 表内仍链旧名。
- **可疑统计**：08 来源对齐图 L1 行 43 概念对每源恰为 43=100%，显为"层总数"而非逐源统计。

**为何质量门漏检**：mermaid 门禁只验**语法**不验**语义**；`kb_auditor` 数链接但不管叶子是否 `[[跳出]]`；`detect_content_overlap` 不触 atlas 内部"定义列套话率"。
**影响**：用户所要的"判断-判定-推理-决策"实质结构**目前不存在**——它们是目录索引与浅树，不能支撑可执行的推理、不能闭环验证、不能作为语义一致性的判定依据。

### 2.3 docs/ 是最大违规区："假 stub 真正文"架空 Canonical 规则

- docs/ 524 文件中 **80.5%（422）>150 行**；合规 stub（≤60 行且含"权威来源"）**仅 26（5.0%）**。
- **419/422 ≈ 99% 的 >150 行 docs 贴着"权威来源/归档提示/stub/archive redirect"免责声明，实为完整概念正文**——把 stub 标签贴在完整正文上以"形式上合规"。
- **160 篇（30.5%）** 含显式概念正文标记（`概念定义-属性`/`定理链`/`形式化定义`/`## 定义`）。重灾区：
  - `docs/research_notes/formal_methods/10_ownership_model.md` 3621 行（贴"归档"却含 Def3.1–4.5/定理/证明/CVE）
  - `10_borrow_checker_proof.md` 2386、`type_theory/10_type_system_foundations.md` 3958、`10_trait_system_formalization.md` 2037
  - `docs/02_reference/quick_reference/02_ownership_cheatsheet.md` 1005（含"概念定义-属性关系-解释论证/三大规则"）
  - `docs/05_guides/05_*_usage_guide.md` 多篇 1667–2524 行（Summary 自称 stub 实为全文）
- 对照：**knowledge/ 89% 为合规 stub、content/ 90% >300 行且有独特安全关键/生态深度、crates/*/docs/ 92% 为 stub+代码示例**——三者 Canonical 落地度高，证明问题集中在 docs/。

**为何质量门漏检**：`detect_content_overlap.py` 粒度为"标题（×1.5）+ 关键词集合 Jaccard（仅前 50 词），阈值 0.6"——①纯关键词 Jaccard，**"换说法重述"必然漏**；②标题权重高，docs 与 concept 题名不同即 `title_sim` 低（419 篇免责声明文因此逃过）；③50 词上限稀释长文；④**根本不扫 crates/**（571 篇零覆盖）；⑤stub 被排除→"假 stub 真正文"整体隐身。故 `CONTENT_OVERLAP_DETECTION_2026_07_11.md` 的"潜在重复对 0"是**工具粒度假象**，非事实。
**影响**：AGENTS.md §2 的 Canonical 规则在 docs/ **名存实亡**；同一概念在 concept/ 与 docs/ 各有一套可能冲突的正文，全局语义一致性无从保证。

### 2.4 Rust 1.97 领域交叉语义严重不足（评分 2/5，直击用户核心关切）

用户："Rust 1.97 的语义是由很多领域交叉和边界的"。审计证实项目**只做了单点罗列，未做交叉建模**：

| 1.97 特性 | 应交叉领域 | 状态 | 证据 |
|---|---|---|---|
| fallback `{float}`→f32 | 类型推断/检查 | **仅单点** | `27_type_checking_and_inference.md:114-166` 只讲 `{float}` 是 HM 变量，无 fallback 边界，末更 2026-06-21（早于 1.97） |
| `target_has_atomic_primitive_alignment` | 内存模型/atomics/类型布局 | **仅单点** | `29_memory_model.md` grep 0 命中；`11_atomics_and_memory_ordering.md` 仅元数据"1.97.0+" |
| v0 mangling | ABI/链接/debuginfo | **伪交叉** | `38_application_binary_interface.md` 仅横幅；`27_linkage.md` grep `mangling/linker/export_name/v0` **0 命中**（最该有却空白） |
| `linker_messages` lint | ABI/链接/lint | **仅单点** | 仅 `01_toolchain.md` 横幅 |
| pin! 阻止 deref coercion | Pin/Unpin/coercion/async | **仅单点** | `06_pin_unpin.md` 只到 1.68；`14_coercion_and_casting.md` grep pin!/1.97 0 命中 |
| Cargo `build.warnings` × `linker_messages` 不受 warnings 控制 | toolchain/lint | **伪交叉** | 关键边界仅版本页 §2.8 有 |
| `WSAESHUTDOWN`→BrokenPipe | 错误处理/平台 | **仅单点** | grep 仅版本页；`04_error_handling.md` 有横幅无 Windows/Unix ErrorKind 映射 |

- **零特性×特性交互**：fallback float × trait solver（`26_trait_solver_in_rustc.md` 只更到 solver flag）、pin! × Pin/Unpin × async、v0 mangling × debuginfo demangle × backtrace——均无。
- **Edition 2024 × 1.97 割裂**：372 文件 859 处"Edition 2024"绝大多数是元数据标签；edition 2024 的 `never type fallback` 与 1.97 的 `{float}→f32 fallback` **两个 fallback 机制未统一讨论**；edition 2024 默认 lint（`unsafe_op_in_unsafe_fn`）与 1.97 新 lint（`dead_code_pub_in_binary`/`linker_messages`/`varargs_without_pattern`）的 **lint-level 矩阵缺失**；`44_edition_guide.md` grep 1.97/fallback/linker 0 命中，末更 2026-05-22。
- **兼容性边界只在版本页表格罗列**：empty `export_name`、`f32:From<{float}>` future-compat、pin! coercion 未形成"受影响→迁移"判定树。

**为何质量门漏检**：版本对齐报告按"特性清单逐条 ✅ 已覆盖"，但"覆盖"=版本页有段落，**未要求核心概念页反向嵌入、未要求交互矩阵、未要求迁移判定树**。
**影响**：1.97 的语义被切割成 31 个孤岛，用户最需要理解的"这些变化在类型/内存/链接/异步/兼容性边界上如何相互作用"**完全缺席**。

### 2.5 质量门"全过"≠ 语义充分（评分 1/5）

`reports/kb_quality_dashboard.md` 的全局指标全是**数量型**：总定理链 ⟹ 2200、反命题 733、Mermaid 609、编译代码块 4571、前置/后置覆盖率 100%、模板化 ⟹ 0。无任何"语义"指标：

- 不检测**定义唯一且无矛盾**（2.1 的同文件互斥）
- 不检测**推理闭环**（2.2 的 0 证明草图、无回边）
- 不检测**决策树可执行**（叶子 `[[跳出]]`、无定量阈值、死端）
- 不检测**版本跨页/跨领域一致**（2.4 的单点罗列）
- 不检测**"假 stub 真正文"**（2.3 的 419 篇）
- "风险文件"仅列 6 个且全是"过渡段不足/反向推理不足"计数问题，**完全捕捉不到 2.1–2.4**。

**根因**：质量门被设计成"让报告好看"（数量达标即 ✅），而非"让语义正确"。这是"自报完成"文化得以延续的机制性原因。

### 2.6 历史先例印证风险

`reports/KG_V3_COMPLETION_2026_07_11.md` 自承：此前 `kg_data_v3.json` **"元数据声称 462 个概念但实际 entities 数组为空"**——即"声称有结构、实际无内容"在本项目**确有前科**。这要求后续所有"完成"声明必须附带**可机器复核的验收**，而非散文叙事。

### 2.7 做得好的部分（避免一棍子打死）

- 核心 L1–L4 权威页实质深度达标（2.1 已列行数与结构）。
- `theorem_registry.md` 机制有效：79 个 T- 编号剔除汇总表后**跨概念文件冲突 = 0**。
- knowledge/、content/、crates/*/docs/ 的 Canonical 落地度高（2.3 对照）。
- `kg_shapes.ttl`（外部）确有 5 个 NodeShape、约 25 条真约束；`kg_data_v3.json` 2.8MB 已填实。
- 09 推理判定树的 15 条真三元组、kg_tlo_alignment 的层级映射，是 atlas 中**最接近可执行**的部分，可作为改写样板。

---

## 3. 批判性意见（根因层）

1. **指标体系错配**：用"数量达标"代理"语义充分"，导致越优化数量、越偏离语义。应引入**语义质量门**（见 §4 P0）。
2. **生成脚本驱动内容**：01/02/07 atlas 由脚本从薄元数据半自动生成，元数据本身的矛盾（2.1）被放大成巨表；应"先修元数据、再生成图谱"，且生成器需加**套话/空定义/关系单一化**拒绝规则。
3. **Canonical 规则被免责声明架空**：docs/ 用"归档/stub/权威来源"标签包装完整正文，形式上合规、实质上双权威。需"标签 ≠ 内容"的实质判定（见 §4 P1）。
4. **版本治理缺交叉建模**：把"对齐 1.97"理解为"版本页列清单"，未要求核心页反向嵌入与交互矩阵。需建立"特性 → 领域 × 领域"反查机制（见 §4 P2）。
5. **闭环验证缺位**：判定-推理-决策-验证无共用节点 ID、无回边、无机器验证入口。需以 `kg_shapes.ttl` 为种子接入 CI（见 §4 P3）。
6. **"自报完成"文化**：完成报告应强制附"反例/未达标项/可复核命令"，否则视为未完成。

---

## 4. 可持续推进计划（分阶段，每项带可机器验证验收标准）

> 原则：**先治标准与门禁（让问题无法再次隐身），再批量修内容（让存量达标），最后接闭环验证（让语义可计算）**。所有验收标准均可由脚本产出数字，写入 `reports/` 留痕，纳入 `run_quality_gates.sh`。

### P0（立即，1 周）：建立"语义质量门"，让问题可检测、不可再隐身

| 任务 | 产出 | 验收标准（机器可查） |
|---|---|---|
| P0-1 元数据一致性检查器 | `scripts/check_metadata_consistency.py` | 扫 concept/：同文件 Bloom↔层次定位互斥=0；A/S/P↔Bloom 脱节<5%；字段重声明=0；版本号同文件自矛盾=0。当前基线写入报告 |
| P0-2 Summary/定义套话检测 | 扩展 `add_bilingual_annotations.py` 或新脚本 | Summary 模板句率<3%；atlas 定义列套话率<10%；输出黑名单样例 |
| P0-3 重叠检测升级 | `scripts/detect_content_overlap.py` v2 | 段落级（按 `##` 切片做 simhash/MinHash）+ 纳入 crates/ + 不豁免"贴免责声明"文件；重跑出报告，预期首次出现大量真实重复对 |
| P0-4 决策树/推理图语义 lint | `scripts/check_graph_semantics.py` | atlas 中 mermaid 叶子 `[[…]]` 跳出率<20%；判定节点须含定量/边界词；禁止"有根因无修复"死端；关系类型不得 100% 单一 `⟹` |
| P0-5 接入质量门 | `scripts/run_quality_gates.sh` + CI | 上述 4 项加入为第 11–14 门；初次允许 warning 模式（不阻断），2 周后转 error |

### P1（2–4 周）：Canonical 实质落地（主攻 docs/）

| 任务 | 产出 | 验收标准 |
|---|---|---|
| P1-1 docs/ 重复正文清单 | 基于 P0-3 的报告 | 列出 419 篇"假 stub 真正文"中实际与 concept/ 段落级重复者，按重复度排序 |
| P1-2 批量 stub 化 | 对确认重复者改 stub（一句话 + canonical 链接），独特内容迁回 concept/ | docs/ >150 行且含概念正文标记者从 160 → <20；dead link=0 |
| P1-3 重灾区专项 | `research_notes/formal_methods`、`type_theory`、`quick_reference`、`05_guides` 逐目录定"迁/并/留" | 每目录一份 `MIGRATION.md` 说明每篇去向 |
| P1-4 反"假 stub"lint | `kb_auditor` 增规则：贴 stub/归档标签却 >150 行或含正文标记即报警 | 误报率<5% |

### P2（2–3 周）：Rust 1.97 领域交叉语义建模（用户核心关切）

| 任务 | 产出 | 验收标准 |
|---|---|---|
| P2-1 特性×领域反查矩阵 | `concept/07_future/00_version_tracking/feature_domain_matrix_197.md` | 31 项特性 ×（语言/类型/内存/链接-ABI/异步/Cargo/std/平台/兼容）矩阵，每格指向核心页锚点或标"缺口" |
| P2-2 八大缺口补齐 | 见下表（Agent D 输出） | 每个核心页出现 1.97 交叉小节（非横幅），含代码/边界/迁移 |
| P2-3 特性×特性交互 | fallback float × trait solver、pin! × Pin/Unpin × async、v0 mangling × debuginfo × linker_messages 各 1 节 | 3 篇交互小节落地 |
| P2-4 Edition 2024 × 1.97 统一 | `never type fallback` 与 `{float}→f32 fallback` 统一讨论；edition 2024 默认 lint × 1.97 新 lint 的 lint-level 矩阵 | 1 个统一 fallback 小节 + 1 张 lint-level 矩阵 |
| P2-5 迁移判定树 | `concept/05_comparative/03_domain_comparisons/migration_197_decision_tree.md`（或 07_future） | empty `export_name` / `f32:From<{float}>` / pin! coercion 三类兼容性变化各一棵"受影响→迁移"判定树，叶子给迁移动作而非 `[[见…]]` |

**P2-2 八大补缺位置（优先级序）**

1. `03_advanced/04_ffi/27_linkage.md` — 补 v0 mangling × linker_messages × empty `export_name` × `link_section`/`link_name` 校验（现 0 命中，最严重）
2. `04_formal/00_type_theory/27_type_checking_and_inference.md` — 补 `{float}`→f32 fallback 边界、与 never type fallback 统一、× trait solver 默认值
3. `03_advanced/02_unsafe/29_memory_model.md` + `00_concurrency/11_atomics_and_memory_ordering.md` — 补 `target_has_atomic_primitive_alignment` 对齐语义 × `42_type_layout`/`repr(C)` 边界
4. `03_advanced/01_async/06_pin_unpin.md` + `01_foundation/02_type_system/14_coercion_and_casting.md` — 补 pin! 不再 deref coerce × Unpin auto trait × async
5. `04_formal/05_rustc_internals/38_application_binary_interface.md` — v0 横幅扩为 v0 × debuginfo demangle × linker_messages × backtrace 交互矩阵
6. `02_intermediate/00_traits/32_editions.md` + `07_future/01_edition_roadmap/44_edition_guide.md` — edition 2024 lint 默认值 × 1.97 新 lint 矩阵
7. `02_intermediate/03_error_handling/04_error_handling.md` — WSAESHUTDOWN→BrokenPipe 的 Windows/Unix `ErrorKind` 迁移判定
8. 迁移判定树页（同 P2-5）

### P3（3–4 周）：推理/判定/决策闭环化（让 atlas 从导航变结构）

| 任务 | 产出 | 验收标准 |
|---|---|---|
| P3-1 节点 ID 体系 | 为 03/05/09 atlas 的判定/根因/修复节点分配稳定 ID（如 `J-BORROW-01`） | 03/05/09 之间共享 ID，出现回边 |
| P3-2 判定定量阈值 | 03 决策树每个判定节点补定量/边界条件 | 纯是非问占比<50% |
| P3-3 推理证明草图 | 05 每条 `X ⟹ Y` 补"前提→推论→证明草图/反例" | 0 证明草图 → 核心定理 100% 有草图 |
| P3-4 SHACL 接入 CI | 把外部 `kg_shapes.ttl` 的 25 条约束接入 `kg-validate`（落地或替换为 pySHACL） | `kg_data_v3.json` 通过 SHACL 校验；CI 报错可读 |
| P3-5 闭环样板 | 以 09 的 15 条真三元组为样板，重写 03/05 各 2 棵为可执行闭环 | 至少 4 棵"问题→判定→推理→决策→验证"闭环树 |

### P4（持续）：治理与文化

| 任务 | 产出 | 验收标准 |
|---|---|---|
| P4-1 完成报告规范 | 模板强制含"未达标项/反例/可复核命令" | 新报告 100% 合规 |
| P4-2 仪表盘语义化 | `kb_quality_dashboard.md` 增加"语义健康"段（定义唯一率/推理闭环率/版本交叉率/假 stub 数） | 仪表盘出现上述 4 指标 |
| P4-3 月度回归 | 每月跑 P0–P3 全部脚本，趋势写入 `reports/` | 月度趋势图 |
| P4-4 pre-commit 强化 | `scripts/git_hooks/pre-commit` 加入 P0-1/P0-2 快速检查 | 提交前拦截元数据互斥与套话 |

---

## 5. 任务清单总览（优先级 / 依赖 / 验收）

| ID | 任务 | 优先级 | 依赖 | 估时 | 验收 |
|---|---|---|---|---|---|
| P0-1 | 元数据一致性检查器 | P0 | — | 1d | 互斥=0、脱节<5% |
| P0-2 | 套话检测 | P0 | — | 1d | Summary<3%、定义列<10% |
| P0-3 | 重叠检测 v2（段落级+扫 crates+不豁免免责声明） | P0 | — | 2d | 首跑出现真实重复对 |
| P0-4 | 图语义 lint | P0 | — | 1.5d | 跳出率<20%、无死端 |
| P0-5 | 接入质量门/CI | P0 | P0-1..4 | 0.5d | 14 门运行（先 warning） |
| P1-1..4 | docs/ Canonical 实质落地 | P1 | P0-3 | 1–2w | 概念正文 docs <20 篇 |
| P2-1..5 | 1.97 领域交叉建模 + 八缺口 | P1 | P0-1 | 2–3w | 八页各有交叉小节、31×9 矩阵 |
| P3-1..5 | 推理/判定/决策闭环 + SHACL | P2 | P0-4、P2 | 3–4w | ≥4 闭环树、SHACL 过 |
| P4-1..4 | 治理文化/仪表盘语义化 | P3 | P0–P3 | 持续 | 4 语义指标上线 |

---

## 6. 需用户确认的决策点（见对话）

本报告为分析与计划，**未修改任何项目文件**。请你确认：推进主线、是否同意新增语义质量门、atlas 处置策略、1.97 交叉补缺优先级与范围。确认后我再进入实际改动。

---

**报告状态**: 待用户确认后进入 P0 实施。
