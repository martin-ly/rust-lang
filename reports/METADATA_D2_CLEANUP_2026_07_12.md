# 元数据一致性 D2 专项清理报告

**日期**: 2026-07-12
**范围**: `concept/`（排除 archive），规则 D2（A/S/P 标记与 Bloom 层级脱节：A→L1-2，S→L2-4，P→L4-7）
**工具**: `scripts/check_metadata_consistency.py`（warning 模式）；修复脚本 `tmp/fix_d2.py`
**基线**: `reports/METADATA_CONSISTENCY_BASELINE_2026-07-12.{md,json}`（D1/D3/D5 清理后：D2=97，基=296）

## 一、总体结果

| 规则 | 基线 | 最终 | 目标 | 达成 |
|---|:---:|:---:|:---:|:---:|
| D2 A/S/P 标记与 Bloom 脱节 | 97 | **1** | <10 | ✅（0.3% of base 296，远低于 strict 阈值 5%）|
| D1 Bloom ↔ 层次定位/层级 互斥 | 0 | **0** | 不回退 | ✅ |
| D3 关键字段重声明 | 0 | **0** | 不回退 | ✅ |
| D5 稳定层 nightly 残留 | 18 | 17 | 不回退 | ✅（见 §五 注记）|

## 二、判定依据

A/S/P 语义以 `concept/00_meta/03_audit/asp_marking_guide.md` 为权威：

- **A — Application**：语法回忆 / API 应用 / 代码构造（Bloom 记忆+应用，L1-2）
- **S — Structure**：心智模型 / 解释推理 / 模式识别（Bloom 理解+分析，L2-4）
- **P — Procedure**：系统方法 / 调试策略 / 选型决策（Bloom 评价+创造，L4-7）
- 组合标记**首字母为主导标记**（guide §2.2 主导原则）；检查器只解析首字母。
- 层级递增原则：L1 以 A/S 为主，L4 以 S/P 为主，L6 以 P 为主。

逐文件结合「内容分级 + 受众 + 定位字段 + 目录层级」裁定修复方向。

## 三、修复计数与方向分布

共修复 **96 文件**，保留 1 个合法特例。

### 3.1 改 Bloom（21 文件）——A/S/P 标记正确，Bloom 区间偏窄

| 子类 | 文件数 | 规则 |
|---|:---:|---|
| F2 向下扩展至 L2（应用层） | 18 | A 主导的 how-to/参考/API 应用页（如 `08_collections` L3-L4→L2-L4、`01_toolchain`/`03_core_crates` L3-L6→L2-L6、`09_cargo_script` L3-L5→L2-L5、`33_macro_faq` L4-L5→L2-L5）。语义与 D1 清理的「Bloom 覆盖内容深度至架构层」一致，**只扩展不收缩**，高端不变故 D1 交集保持 |
| F4 覆盖分析-评价跨度 | 3 | guide 明确标为 **S** 的对比分析页（`03_paradigm_matrix`、`01_rust_vs_cpp`、`02_rust_vs_go`），Bloom L5→L4-L5（对比分析天然跨越「分析+评价」） |

### 3.2 改 A/S/P（75 文件）——Bloom 正确，标记脱节

| 子类 | 文件数 | 规则 |
|---|:---:|---|
| F3 单标记更正 P→A | 17 | P（Practice）标记的初学者/中级 how-to 与参考页：cargo 指南系列（61-66、76、78、80-85 共 14 个）、`42_useful_development_tools`、`77_rustdoc_196_changes`、`79_development_tools`。内容是工具使用/速查（A），不是策略决策（P） |
| F3 单标记更正 P→S | 4 | 机制解释页：`60_cargo_dependency_resolution`（“为什么选这个版本”）、`71_compiler_testing`（rustc 测试体系讲解）、`50_nightly_rust`（发布流程理解）、`27_linkage`（链接语义） |
| F1 组合重排 A+P→P+A | 10 | 策略/决策主导的专家页（process_ipc 系列 5 个、`36_ownership_performance_optimization`、`28_devops_and_ci_cd`、`37_pattern_selection_best_practices`、`12_testing_strategies`、`20_licensing_and_compliance`），组合字母集合不变，仅将主导标记前置 |
| F1 组合重排 A+S→S+A | 16 | 分析/机制/对比主导页（如 `27_web_frameworks`、`08_wasi`、`44_edition_guide`、`37_rpitit_preview`、`24_autoverus` 等） |
| F1 组合重排 A+S+P→S+A+P | 26 | 分析主导的综述/专家页（design_patterns、domain_applications、04_formal、07_future 等系列），符合 guide「L6 以 S/P 为主」 |
| F1 组合重排 S+P→P+S | 1 | `30_system_composability`（Bloom L5-L6，系统设计决策主导） |
| F1 非标准标记更正 | 1 | `16_cpp_rust_surface_features` 的 `C+A — Comparison + Application` 不在 A/S/P 体系内，改为 `S+A — Structure + Application`（对比分析主导） |

> 注：F1 重排顺带修正了原文 `ApplicationStructure` / `ApplicationProcedure` 等缺空格的拼写粘连，组合字母集合与含义不变。

## 四、剩余特例清单（D2=1）

| 文件 | 状态 | 理由 |
|---|---|---|
| `concept/00_meta/04_navigation/foundations_gap_closure_index.md` | 保留 | D1 清理（规则 B）已将其 Bloom 裁定为 `L0（导航索引）`——L0 元信息/导航页**没有认知技能内容**，A/S/P 三维标记体系（A→L1-2 起）对 L0 页天然不适用；任何标记都无法与 Bloom {0} 相交。属规则不适用的合法特例，建议后续在检查器中对 Bloom={0} 文件豁免 D2（留给检查器专项任务） |

## 五、约束遵守与验证

| 约束 | 结果 |
|---|---|
| 不动 D1 已修复的 层次定位/层级 字段 | ✅ 96 文件全部只改 `Bloom 层级` 或 `A/S/P 标记` 单行；Bloom 只扩展（高端不变），D1 复跑仍为 0 |
| 不动 D5 保留文件的 nightly 表述 | ✅ `09_cargo_script`、`10_public_private_deps` 两个 D5 保留文件仅改元数据行，正文 nightly 相关表述未触碰，复跑仍在 D5 清单中 |
| 行尾 | ✅ 修复脚本字节级读写、逐行保留原行尾；96 个文件当前均为 LF（与 `.gitattributes` 的 `*.md text eol=lf` 及 `.editorconfig` 一致；LF 状态为前序 D1/D3/D5 清理文本模式写回所致，本任务未引入行尾变化，git diff 无行尾噪声） |
| 改动最小化 | ✅ 每文件恰好 1 行元数据改动 |
| 每批修复后重跑检查器 | ✅ 本任务修复完成时：D1=0、D2=1、D3=0、D4=1（既有合法特例）、D5=17、D6=12（scanned=482）。最终复核：D1=0、**D2=1**、D3=0、D4=0、D5=17、D6=13（scanned=483）——D4/D6/扫描数波动来自工作区其他在途任务的并发改动，与本任务（仅改 Bloom/A-S-P 行）无关 |
| git commit | 未执行（按任务要求） |

**注记（D5 18→17）**：`33_rust_release_process.md` 在基线生成后被工作区其他在途任务从 `02_intermediate/00_traits/` 移至 `07_future/00_version_tracking/`（D5 白名单目录），故不再计入 D5；与本任务无关，未触碰该文件。

**注记（路径漂移）**：基线 JSON 中 `concept/03_advanced/02_process_ipc/`（7 文件）已在工作区重命名为 `08_process_ipc/`，修复按当前路径执行。

## 六、遗留建议（非本任务范围）

1. **检查器 D2 豁免 Bloom={0}**：导航索引类页面（L0）不应参与 A/S/P-Bloom 映射判定，可在 `check_metadata_consistency.py` 的 D2 分支加 `if 0 in b: skip`。
2. **D4 剩余 1 例**（`40_generic_associated_types.md` 版本字段含历史说明）沿用 D1/D3/D5 报告 §六 的建议，留给 D4 专项。
3. `tmp/fix_d2.py` 为临时修复脚本，含完整 96 文件决策表，可供复核；不提交版本控制。
