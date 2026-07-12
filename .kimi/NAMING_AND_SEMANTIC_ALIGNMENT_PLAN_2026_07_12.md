# 命名体系与语义完整性对齐计划(2026-07-12)

> **触发**: 用户批评①"很多文件的命名、序号、分类都比较乱";②"从语义标准评价,内容仍缺少系统化、完整性和充分性"。
> **输入证据**: 全项目命名/序号/分类体系审计(只读,逐目录实测)+ 当日语义整改终态(语义健康 93.6 OK、权威覆盖 100%)。
> **性质**: 批判性评价 + 整改计划,**待用户确认后执行**。

---

## 0. 当日已完成的语义整改基线(供对照)

语义健康 **64.5 → 93.6(OK)**;权威覆盖 P0/P1/P2 全 100%;元数据 flagged 242→30;空章节 420→0;TODO 标记 -82.5%;判定表 6→31 页;6 个新权威页(Send/Sync、const generics、GAT、取消安全、async/unsafe 边界全景);14 阻断门 + 5 观察门。**但命名体系与深层语义完整性仍是未清偿的债。**

---

## 1. 批判性评价

### 1.1 命名/序号/分类:用户批评完全成立,且比观感更严重

**根因:concept/ 现行序号不是"目录内序号",而是历史遗留的"层内全书章节号"**,物理上按主题目录切分后,每个目录内序号支离破碎:

| 证据 | 现状 |
|---|---|
| 三套编号 regime 混用 | 层内章节号(主流)/目录内局部序号(process_ipc、networking)/无序号(version_tracking、00_framework 21 文件) |
| 层内同号冲突 | **L1 有 6 处、L4 有 1 处、L6 有 17 处同号双文件**(59–87 新批次与旧批次撞号:wasm×3、算法×5、cargo×9 等) |
| 目录序号缺口 | 02_intermediate 缺 08_(文件已删目录悬空)、07_future 缺 02_——删除后未重排 |
| SUMMARY 乱序 | **54 处序号倒挂**(L7 预览特性段几乎全程乱序)+ **3 处结构损坏**(2 条目错挂顶级、版本跟踪段缩进混乱夹游离 blockquote)+ 1 个真实内容页(33_safety_tags_in_formal)**漏收** |
| docs/ 顶层 | 4 组编号重复(01_core+01_learning、03_guides+03_practice、04_research+04_thinking、07_future 空壳+07_project);根目录散落 15 个文件(含 1.8MB 的 link_check_report);两个 guides 目录主题重叠 |
| docs/12_research_notes | 147 个 `10_` 扁平前缀;`formal_methods` 与 `formal_modules` 疑似同义目录并存;档级号 10/20/30…70 混用 |
| knowledge/ | 01_fundamentals 教学顺序**倒挂**(borrowing 在 ownership 前);async 同号双文件;INDEX.md 过期(仍称 Rust 1.95、73 篇);与 content/ 两个镜像目录(safety_critical 100% 结构镜像、deep_dives 同名不同内容) |
| crates/*/docs | **五套体系并存**(c07:01–14+跳号+view01–05+tier_01–04+散名文件);c05 两套 01–05 全撞号;c10 tier_04 全撞号;*_supplement/*_final/*_expanded 变体泛滥 |
| quizzes 体系 | L1 有专目录(文件号 24–33 章节号残留)、L2 目录仅 1 文件、L3–L6 quiz 散落主题目录、L7 无 quiz |

**批判**: 这是典型的"多批次生成、无统一编号契约"熵增。乱序不只是审美问题——SUMMARY 3 处结构损坏直接影响 mdbook 导航正确性,L6 的 17 处撞号让"按号引用"完全不可靠,knowledge 的教学顺序倒挂误导学习者。

### 1.2 语义系统化/完整性/充分性:当日整改后有实质改善,但仍有 6 类缺口

| 维度 | 已达标(当日) | 仍缺口 |
|---|---|---|
| 系统化 | taxonomy.yaml、KG layer/domain 100%、决策树 YAML、关联区块统一、判定表 31 页 | quizzes 体系不统一;equivalentTo/instanceOf/appliesTo 三种关系仍零实例;311 个 KG 实体 zh 标签是英文占位 |
| 完整性 | 空章节 0、TODO -82.5%、权威覆盖 100%、版本声明 96.5% | **20 个 Reference 摘译薄页(实质占比 33–43%)**;~16 页带"综述级—待补充代码"徽标;6 文件 9 处代码块内 `todo!()`;exercises L4–L7 空白 |
| 充分性 | 6 个新交叉/边界权威页、判定森林、边界全景 | 交叉页仍缺:drop×并发/async、FFI 布局契约收敛、async 错误处理;判定表目标 50 页(现 31);L4 Reference 摘译页与 L1 同名页的深度落差未弥合 |
| 一致性 | D1/D3/D4=0、D2=1、canonical 唯一性门通过 | knowledge INDEX 过期;content↔knowledge 镜像权威侧未裁定;docs 04_research 3 对同主题双文件未并 |
| 可验证性 | 19 门 CI(14 阻断+5 观察) | 命名规范无机器检查(撞号/乱序无门);SUMMARY 手工维护(审计建议脚本生成) |
| 国际化权威对齐 | P0/P1/P2 = 100%(机器验证) | 外链腐烂治理进行中(07-09 基线 97 条已清,复扫新发现 ~76 个 404 处置中) |

---

## 2. 整改计划(待确认)

### 阶段 N0 — 止血(半天,无重命名)

| # | 任务 | 验收 |
|---|---|---|
| N0-1 | SUMMARY.md 修 3 处结构损坏(错挂顶级条目、版本段缩进)、补收 33_safety_tags_in_formal、全节按序号重排(54 处倒挂归零) | mdbook build ✅;倒挂检测脚本 0 |
| N0-2 | 删除/合并 9 组冗余:31_safety_tags_preview stub、18_lifetimes_advanced stub、20_borrowsanitizer 旧页、docs 06_toolchain 2 个重复、04_research 3 对双文件、knowledge async/rust_1_95 双文件 | 各门不转红;canonical uniqueness ✅ |
| N0-3 | knowledge/01_fundamentals 重排教学序(ownership→borrowing→lifetimes→iterators)+ INDEX.md 更新 | 顺序正确;INDEX 链接有效 |
| N0-4 | docs 根 15 散落文件归位(10_* → 07_project/06_toolchain/04_research;link_check_report → reports/) | 根目录仅留 README/master_index |
| N0-5 | 新建 `scripts/check_naming_convention.py`(目录内序号唯一、目录号连续、SUMMARY 序号倒挂检测、禁双前缀/异形前缀)接入观察门 | --strict 当前仅报已知项 |

### 阶段 N1 — concept/ 全层重编号(主工程,~401 文件,分 8 层逐层 PR)

| # | 任务 |
|---|---|
| N1-1 | 写 `scripts/maintenance/plan_renumber.py`(只读生成 old→new 映射 CSV,按 SUMMARY 阅读序→目录内 01.. 连续,00 留给导览)与 `apply_renumber.py`(git mv + 全仓相对链接按双向位置重算 + concept_kb/kg_data/taxonomy/atlas 内嵌路径同步 + SUMMARY 重排) |
| N1-2 | 执行顺序:L5(19 文件零冲突)→ L2/L3 → L1 → L4 → L7 → L6(115 条目+17 撞号,最复杂);每层独立验证(14 阻断门全绿 + 死链 0 + KG SHACL ✅) |
| N1-3 | 目录缺口补齐:02_intermediate/09_quizzes→08_quizzes、07_future 03/04 前移补 02 缺;quizzes 体系统一(每层 NN_quizzes/ 置末,散落 quiz 归位) |
| N1-4 | AGENTS.md §4 写入统一命名规则(序号语义唯一化、目录号连续、禁双前缀/异形前缀、专题系列集中+索引、SUMMARY 脚本生成化) |

### 阶段 N2 — docs/knowledge/crates 对齐(1–2 周)

| # | 任务 |
|---|---|
| N2-1 | docs 顶层重编号(01_learning→08、04_thinking→10、删 07_future 空壳、07_project→07_meta_project);03_guides vs 05_guides 按裁定处置(**待确认 D3**) |
| N2-2 | research_notes 147 文件归组连续编号(formal_methods/type_theory/software_design_theory/alignment_reports/organization/tutorials/cheatsheets;formal_modules 并入 formal_methods/module_system) |
| N2-3 | knowledge 镜像裁定(**待确认 D4**):deep_dives 与 safety_critical 的权威侧;async 双文件合并;emerging 双文件合并 |
| N2-4 | crates/*/docs 统一(tier_0N + 内连续号;删 *_supplement/*_final 变体;c05/c07/c10 撞号合并;c01 异形前缀修正) |

### 阶段 N3 — 语义完整性深化(与 N1/N2 可并行)

| # | 任务 |
|---|---|
| N3-1 | 20 个 Reference 摘译薄页 enrichment(实质占比 33–43% → ≥60%:补机制解释、与形式化页的推导链接、示例) |
| N3-2 | 3 个剩余交叉权威页:drop×并发/async 边界、FFI 布局契约收敛(合并 ABI/repr 分散内容)、async 错误处理(取消×错误×超时) |
| N3-3 | KG 关系第三类实例化:equivalentTo/instanceOf/appliesTo 各 ≥5(有依据才标);311 zh 标签译名回填 |
| N3-4 | 16 页"综述级—待补充代码"徽标页补可编译示例;6 文件 9 处代码块 todo!() 消除;判定表 31→50 页 |
| N3-5 | exercises L4–L7 扩展(形式化验证/跨语言/生态/前沿各 ≥3 题) |
| N3-6 | 外链腐烂收尾(剩余 ~76 个 404 处置,进行中) |

### 建议节奏

- N0 先做(半天,收益最大风险最低);N1 是主工程,每层独立 PR 独立验证;N2/N3 并行;
- 每阶段验收:14 阻断门全绿 + 语义健康不退化(当前 93.6)+ 死链 0;
- 全程遵守 AGENTS.md 红线 6:完成声明必须附机器验证。

---

## 3. 用户确认的决策点（2026-07-12 已确认）

| # | 决策点 | 裁定 |
|---|---|---|
| D1 | 序号语义 | ✅ **目录内两位连续序号**（~401 文件重命名，分 8 层逐层 PR，脚本化+全量验证） |
| D2 | 删后策略 | ✅ 小目录（<15）重排、大目录留空号+README 记录 |
| D3 | 03/05_guides | ✅ 保留两目录仅改编号 |
| D4 | 镜像权威侧 | ✅ content/ 权威、knowledge 转 stub（AGENTS §2.1） |
| D5 | 执行规模 | ✅ N0→N3 全量 |

---

**生成时间**: 2026-07-12
**关联文档**: `.kimi/CRITICAL_SEMANTIC_AUDIT_AND_SUSTAINABLE_PLAN_2026_07_12.md`(P0–P3 已完成)、`reports/` 当日 15+ 份整改报告

---

## 执行完成记录（2026-07-12）

**状态：N0→N2 全部完成，全 20 门通过（14 阻断 + 6 观察），semantic health 93.5 OK（meta 96.2 / topo 90.7 / dedup 84.7 / kg 100）。**

- N0 止血：SUMMARY 补收 2 文件 + 结构修复 3 处；删 3 个遗留 stub（31_safety_tags_preview、18_lifetimes_advanced、20_borrowsanitizer_preview）；docs 三对同主题合并（~430 行独特内容迁移）；knowledge 两对合并；borrow_sanitizer 双权威裁定。
- N1 重编号：concept 384 文件 + docs 517 文件/32 目录 + knowledge 7 文件 + crates 245 项，全量目录内 NN_ 连续序号；链接重写 ≥9531 处（dry-run 统计，concept 阶段 ~1.2 万处日志被覆盖）；终态死链 0、跨层 0。
- 工具：`scripts/plan_renumber.py` / `apply_renumber.py`（两阶段移动 + 相对链接双向重算 + JSON/KG 同步 + 目录改名支持）/ `plan_renumber_phase2.py`；`scripts/check_naming_convention.py` 接入为第 20 门（观察）。
- 治理：AGENTS.md §4.0 命名规则生效；kb_auditor 跨层检查改为按真实目录层级判定（重编号鲁棒）；20 文件补真实向下引用；crates 变体 13 stub + 4 删除；v2 SERIES 白名单加固；KG 2 个失效 ex:path 修复。
- 报告：`reports/NAMING_RENUMBER_COMPLETION_2026_07_12.md`。

**遗留（N3/后续）**：v2 可处置项 54（MERGE 5 + DOCS_INTERNAL 49，归零后可转 --strict）；无序号系列目录 WARN 85（命名 lint 观察）；`04_guides`/`08_guides` 命名歧义；crates 非 tier 子目录（c01_ownership/ 等）待改 tier_05_*；knowledge INDEX 旧统计数字（代码行数）未重算。

## 第二轮深化完成记录（2026-07-12 午后）

**状态：四线并行全部完成，全 20 门 exit 0，semantic health 93.5→97.2（meta 96.0 / topo 93.3 / dedup 100.0 / kg 100.0）。**

- 线 A 命名收尾：docs/08_guides→08_usage_guides（33 文件/328 处链接）；crates 5 个非 tier 目录改 tier_05_*；10 个 rust_194_updates 补 README 索引；snippets 豁免登记；knowledge INDEX 统计重算（stub 化后实测口径）；命名 lint WARN 85→78（剩余均为已裁定豁免）。
- 线 B 国际权威复核：覆盖门 any=100%/none=0 未退化；concept 内 1133 条权威外链复测，真实失效 2 条已修（spec.rust-lang.org→RFC Book、secure-code-guidelines→ANSSI）；1.97 release notes 逐条比对 0 缺口；1.98 周期新合并 RFC 补 4 条（#3955/#3928/#3808/#3946）；学术新刊补 3 篇（Kani/verify-rust-std/Safety Tags 审计）。报告 reports/INTERNATIONAL_AUTHORITY_REVERIFY_2026_07_12.md。
- 线 C KG 关系实例化：equivalentTo 9 / instanceOf 18 / appliesTo 14（零→41 条类型化边，全附 evidence）；T3 jump 31/188→21/189；kg_links.json 重新生成并修 5 条陈旧路径。新脚本 scripts/type_kg_semantic_edges.py（可复跑）。范畴节点缺口 9 项登记待补。
- 线 D v2 去重清零：54 可处置项→0（autoverus 真近克隆对差异化改写为预览跟踪页；52 对系列结构相似登记 SERIES_PATH_RE 白名单附证据）；**v2 门转阻断**（15 阻断+5 观察=20 门），CI/nightly/AGENTS 同步。报告 reports/DEDUP_V2_ZERO_2026_07_12.md。

**遗留（非阻断）**：命名 lint WARN 78（已裁定豁免项）；KG 范畴节点缺口 9 项（Vec/Tokio/Send/Sync 等实体未建）；REVIEW 级相似对 437（观察，非可处置）。
