# 链接有效性检查报告

> **Bloom 层级**: L2-L3 (理解/应用)

> **[来源: 💡 自动生成 — scripts/link_checker.py]**

## 统计

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]** · **[来源: [TRPL](https://doc.rust-lang.org/book/)]**

| 类别 | 数量 |
|:---|:---:|
| 总链接数 | 64071 |
| 有效链接 | 54155 |
| 损坏链接 | 3736 |
| 外部链接 | 6167 |
| 仅锚点链接 | 47007 |

## 损坏链接清单（按问题类型分组）

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]** · **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

### 锚点不存在 (3100个)

| 源文件 | 链接文本 | 链接路径 | 问题 |
|:---|:---|:---|:---|
| docs\00_master_index.md | 文档中心 - 主索引 | `#文档中心---主索引` | 同文件锚点不存在: #文档中心---主索引 |
| docs\03_2026_international_authoritative_alignment_report.md | 1.1 Tree Borrows - PLDI 2025 Distinguished Paper | `#11-tree-borrows---pldi-2025-distinguished-paper` | 同文件锚点不存在: #11-tree-borrows---pldi-2025-distinguished-paper |
| docs\03_2026_international_authoritative_alignment_report.md | 1.2 Miri: Practical UB Detection - POPL 2026 | `#12-miri-practical-ub-detection---popl-2026` | 同文件锚点不存在: #12-miri-practical-ub-detection---popl-2026 |
| docs\03_2026_international_authoritative_alignment_report.md | 2.1 Rust 2024 Edition - 已稳定发布 | `#21-rust-2024-edition---已稳定发布` | 同文件锚点不存在: #21-rust-2024-edition---已稳定发布 |
| docs\03_2026_international_authoritative_alignment_report.md | 2.2 Rust 1.95.0 - 即将发布 | `#22-rust-1950---即将发布` | 同文件锚点不存在: #22-rust-1950---即将发布 |
| docs\03_2026_international_authoritative_alignment_report.md | 3.1 Linux内核 - Rust永久采用 | `#31-linux内核---rust永久采用` | 同文件锚点不存在: #31-linux内核---rust永久采用 |
| docs\AUTHORITATIVE_SOURCES_AND_CITATIONS.md | 1. `array_windows` - 切片迭代方法 | `#1-array_windows---切片迭代方法` | 同文件锚点不存在: #1-array_windows---切片迭代方法 |
| docs\AUTHORITATIVE_SOURCES_AND_CITATIONS.md | **维护说明**: 本文档应随Rust生态更新而更新，确保所有引用来源保持最新和准确 | `#维护说明-本文档应随rust生态更新而更新确保所有引用来源保持最新和准确` | 同文件锚点不存在: #维护说明-本文档应随rust生态更新而更新确保所有引用来源保持最新和准确 |
| docs\01_cargo_build_optimization.md | ⚙️ 环境变量配置 | `#️-环境变量配置` | 同文件锚点不存在: #️-环境变量配置 |
| docs\01_cargo_build_optimization.md | 🛠️ 推荐工具 | `#️-推荐工具` | 同文件锚点不存在: #️-推荐工具 |
| docs\01_cargo_build_optimization.md | ⚠️ 注意事项 | `#️-注意事项` | 同文件锚点不存在: #️-注意事项 |
| docs\MIGRATION_GUIDE_2026.md | lazy\_static → LazyLock | `#lazy_static--lazylock` | 同文件锚点不存在: #lazy_static--lazylock |
| docs\MIGRATION_GUIDE_2026.md | async-trait → 原生async trait | `#async-trait--原生async-trait` | 同文件锚点不存在: #async-trait--原生async-trait |
| docs\MIGRATION_GUIDE_2026.md | 生成器 → gen关键字 | `#生成器--gen关键字` | 同文件锚点不存在: #生成器--gen关键字 |
| docs\MIGRATION_GUIDE_2026.md | **详细指南**: 2026\_RUST\_ECOSYSTEM\_COMPREHENSIVE\_REVIEW.md | `#详细指南-2026_rust_ecosystem_comprehensive_reviewmd` | 同文件锚点不存在: #详细指南-2026_rust_ecosystem_comprehensive_reviewmd |
| docs\04_rust_language_feature_comprehensive_inventory_2026.md | 00.2 缺失项热力图 (A \\ B) | `#002-缺失项热力图-a--b` | 同文件锚点不存在: #002-缺失项热力图-a--b |
| docs\04_rust_language_feature_comprehensive_inventory_2026.md | 🔴 P0 — 语言核心层（1.95.0 已稳定，认知必需） | `#-p0--语言核心层1950-已稳定认知必需` | 同文件锚点不存在: #-p0--语言核心层1950-已稳定认知必需 |
| docs\04_rust_language_feature_comprehensive_inventory_2026.md | 🔴 P0 — 异步范式层（改变编程心智模型） | `#-p0--异步范式层改变编程心智模型` | 同文件锚点不存在: #-p0--异步范式层改变编程心智模型 |
| docs\04_rust_language_feature_comprehensive_inventory_2026.md | 🟡 P1 — 系统与网络层 | `#-p1--系统与网络层` | 同文件锚点不存在: #-p1--系统与网络层 |
| docs\04_rust_language_feature_comprehensive_inventory_2026.md | 🟢 P2 — 类型系统与工具链层 | `#-p2--类型系统与工具链层` | 同文件锚点不存在: #-p2--类型系统与工具链层 |
| docs\04_rust_language_feature_comprehensive_inventory_2026.md | 00.3 冗余/过时项热力图 (B \\ A) | `#003-冗余过时项热力图-b--a` | 同文件锚点不存在: #003-冗余过时项热力图-b--a |
| docs\04_rust_language_feature_comprehensive_inventory_2026.md | 05.3 1.95+ 新增特性深度梳理：Atomic\*::update / try\_update | `#053-195-新增特性深度梳理atomicupdate--try_update` | 同文件锚点不存在: #053-195-新增特性深度梳理atomicupdate--try_update |
| docs\04_rust_language_feature_comprehensive_inventory_2026.md | 07.4 前沿缺口：eBPF + Rust (Aya) | `#074-前沿缺口ebpf--rust-aya` | 同文件锚点不存在: #074-前沿缺口ebpf--rust-aya |
| docs\04_rust_language_feature_comprehensive_inventory_2026.md | *项目 MSRV: 1.96.0+ (Edition 2024)* | `#项目-msrv-1950-edition-2024` | 同文件锚点不存在: #项目-msrv-1950-edition-2024 |
| docs\10_terminology_standard.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\10_terminology_standard.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\00_meta\ANNUAL_REVIEW_TEMPLATE.md | 1️⃣ 对称差分析更新 | `#1️⃣-对称差分析更新` | 同文件锚点不存在: #1️⃣-对称差分析更新 |
| docs\00_meta\ANNUAL_REVIEW_TEMPLATE.md | 2️⃣ 国际权威来源覆盖度评估 | `#2️⃣-国际权威来源覆盖度评估` | 同文件锚点不存在: #2️⃣-国际权威来源覆盖度评估 |
| docs\00_meta\ANNUAL_REVIEW_TEMPLATE.md | 3️⃣ 项目健康度指标 | `#3️⃣-项目健康度指标` | 同文件锚点不存在: #3️⃣-项目健康度指标 |
| docs\00_meta\ANNUAL_REVIEW_TEMPLATE.md | 4️⃣ 社区与协作 | `#4️⃣-社区与协作` | 同文件锚点不存在: #4️⃣-社区与协作 |
| docs\00_meta\ANNUAL_REVIEW_TEMPLATE.md | 5️⃣ 下一年度路线图建议 | `#5️⃣-下一年度路线图建议` | 同文件锚点不存在: #5️⃣-下一年度路线图建议 |
| docs\00_meta\ANNUAL_REVIEW_TEMPLATE.md | 6️⃣ 年度总结 | `#6️⃣-年度总结` | 同文件锚点不存在: #6️⃣-年度总结 |
| docs\00_meta\00_content_reconstruction_plan_2026.md | 模块 6: 反例集（Counterexamples \& Anti-patterns） | `#模块-6-反例集counterexamples--anti-patterns` | 同文件锚点不存在: #模块-6-反例集counterexamples--anti-patterns |
| docs\00_meta\00_content_reconstruction_plan_2026.md | **状态**: 待确认 | `#状态-待确认` | 同文件锚点不存在: #状态-待确认 |
| docs\00_meta\00_critical_evaluation_and_improvement_plan.md | **下次评价时间**: 2026-04-18 | `#下次评价时间-2026-04-18` | 同文件锚点不存在: #下次评价时间-2026-04-18 |
| docs\00_meta\00_docs_final_organization_report.md | **状态**: ✅ **Docs目录整理完成** | `#状态--docs目录整理完成` | 同文件锚点不存在: #状态--docs目录整理完成 |
| docs\00_meta\00_docs_reorganization_complete.md | ✅ **重组完成** - docs目录已清晰组织 | `#-重组完成---docs目录已清晰组织` | 同文件锚点不存在: #-重组完成---docs目录已清晰组织 |
| docs\00_meta\DOCUMENTATION_DIVISION_OF_LABOR.md | 2.1 `knowledge/` — 面向学习者的分层教程 | `#21-knowledge--面向学习者的分层教程` | 同文件锚点不存在: #21-knowledge--面向学习者的分层教程 |
| docs\00_meta\DOCUMENTATION_DIVISION_OF_LABOR.md | 2.2 `docs/05_guides/` — 面向开发者的专题查阅指南 | `#22-docs05_guides--面向开发者的专题查阅指南` | 同文件锚点不存在: #22-docs05_guides--面向开发者的专题查阅指南 |
| docs\00_meta\DOCUMENTATION_DIVISION_OF_LABOR.md | 2.3 `docs/02_reference/` — 速查卡与边界特例 | `#23-docs02_reference--速查卡与边界特例` | 同文件锚点不存在: #23-docs02_reference--速查卡与边界特例 |
| docs\00_meta\DOCUMENTATION_DIVISION_OF_LABOR.md | 2.4 `docs/research_notes/` — 学术与形式化内容 | `#24-docsresearch_notes--学术与形式化内容` | 同文件锚点不存在: #24-docsresearch_notes--学术与形式化内容 |
| docs\00_meta\DOCUMENTATION_DIVISION_OF_LABOR.md | 2.5 `docs/content/` — 进阶生态与场景化内容 | `#25-docscontent--进阶生态与场景化内容` | 同文件锚点不存在: #25-docscontent--进阶生态与场景化内容 |
| docs\00_meta\QUARTERLY_SYNC_CHECKLIST.md | 1️⃣ Rust 官方生态更新 | `#1️⃣-rust-官方生态更新` | 同文件锚点不存在: #1️⃣-rust-官方生态更新 |
| docs\00_meta\QUARTERLY_SYNC_CHECKLIST.md | 2️⃣ 国际权威来源覆盖度 | `#2️⃣-国际权威来源覆盖度` | 同文件锚点不存在: #2️⃣-国际权威来源覆盖度 |
| docs\00_meta\QUARTERLY_SYNC_CHECKLIST.md | Google / Microsoft / AWS 官方更新 | `#google--microsoft--aws-官方更新` | 同文件锚点不存在: #google--microsoft--aws-官方更新 |
| docs\00_meta\QUARTERLY_SYNC_CHECKLIST.md | 3️⃣ 项目内容同步 | `#3️⃣-项目内容同步` | 同文件锚点不存在: #3️⃣-项目内容同步 |
| docs\00_meta\QUARTERLY_SYNC_CHECKLIST.md | 4️⃣ 技术债务评估 | `#4️⃣-技术债务评估` | 同文件锚点不存在: #4️⃣-技术债务评估 |
| docs\00_meta\QUARTERLY_SYNC_CHECKLIST.md | 5️⃣ 归档与总结 | `#5️⃣-归档与总结` | 同文件锚点不存在: #5️⃣-归档与总结 |
| docs\00_meta\rust_feature_tracking_template.md | *本模板基于 2026-05-08 的对称差分析报告创建。* | `#本模板基于-2026-05-08-的对称差分析报告创建` | 同文件锚点不存在: #本模板基于-2026-05-08-的对称差分析报告创建 |
| docs\00_meta\RUST_VERSION_ALIGNMENT_CHECKLIST.md | 1️⃣ Rust 新版本发布跟踪 | `#1️⃣-rust-新版本发布跟踪` | 同文件锚点不存在: #1️⃣-rust-新版本发布跟踪 |
| docs\00_meta\RUST_VERSION_ALIGNMENT_CHECKLIST.md | 2️⃣ Edition 兼容性检查 | `#2️⃣-edition-兼容性检查` | 同文件锚点不存在: #2️⃣-edition-兼容性检查 |
| docs\00_meta\RUST_VERSION_ALIGNMENT_CHECKLIST.md | 3️⃣ MSRV 更新评估 | `#3️⃣-msrv-更新评估` | 同文件锚点不存在: #3️⃣-msrv-更新评估 |
| docs\00_meta\RUST_VERSION_ALIGNMENT_CHECKLIST.md | 4️⃣ 废弃特性迁移计划 | `#4️⃣-废弃特性迁移计划` | 同文件锚点不存在: #4️⃣-废弃特性迁移计划 |
| docs\00_meta\RUST_VERSION_ALIGNMENT_CHECKLIST.md | 5️⃣ 新特性集成机会 | `#5️⃣-新特性集成机会` | 同文件锚点不存在: #5️⃣-新特性集成机会 |
| docs\00_meta\RUST_VERSION_ALIGNMENT_CHECKLIST.md | 6️⃣ 检查结果汇总 | `#6️⃣-检查结果汇总` | 同文件锚点不存在: #6️⃣-检查结果汇总 |
| docs\00_meta\TEMPLATE_CONCEPT_DOC.md | 模块 6: 反例集（Counterexamples \& Anti-patterns） | `#模块-6-反例集counterexamples--anti-patterns` | 同文件锚点不存在: #模块-6-反例集counterexamples--anti-patterns |
| docs\00_meta\TEMPLATE_CONCEPT_DOC.md | **最后更新**: 2026-05-09 | `#最后更新-2026-05-09` | 同文件锚点不存在: #最后更新-2026-05-09 |
| docs\00_meta\analysis\RUST_2026_PROJECT_GOALS_MONTHLY_TRACKING.md | Rust 2026 Project Goals — 月度跟踪报告 | `#rust-2026-project-goals--月度跟踪报告` | 同文件锚点不存在: #rust-2026-project-goals--月度跟踪报告 |
| docs\00_meta\analysis\RUST_2026_PROJECT_GOALS_MONTHLY_TRACKING.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\00_meta\analysis\RUST_2026_PROJECT_GOALS_MONTHLY_TRACKING.md | 🔴 P0 — 紧急（高影响力 + 官方里程碑临近或社区需求迫切） | `#-p0--紧急高影响力--官方里程碑临近或社区需求迫切` | 同文件锚点不存在: #-p0--紧急高影响力--官方里程碑临近或社区需求迫切 |
| docs\00_meta\analysis\RUST_2026_PROJECT_GOALS_MONTHLY_TRACKING.md | 🟡 P1 — 重要（中等影响力 + 持续社区关注） | `#-p1--重要中等影响力--持续社区关注` | 同文件锚点不存在: #-p1--重要中等影响力--持续社区关注 |
| docs\00_meta\analysis\RUST_2026_PROJECT_GOALS_MONTHLY_TRACKING.md | 🟢 P2 — 规划（长期价值 + 资源允许时推进） | `#-p2--规划长期价值--资源允许时推进` | 同文件锚点不存在: #-p2--规划长期价值--资源允许时推进 |
| docs\00_meta\analysis\RUST_2026_PROJECT_GOALS_MONTHLY_TRACKING.md | Rust 2026 Project Goals — 月度跟踪报告 | `#rust-2026-project-goals--月度跟踪报告` | 同文件锚点不存在: #rust-2026-project-goals--月度跟踪报告 |
| docs\00_meta\analysis\RUST_2026_PROJECT_GOALS_MONTHLY_TRACKING.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\00_meta\analysis\RUST_2026_PROJECT_GOALS_MONTHLY_TRACKING.md | 🔴 P0 — 紧急（高影响力 + 官方里程碑临近或社区需求迫切） | `#-p0--紧急高影响力--官方里程碑临近或社区需求迫切` | 同文件锚点不存在: #-p0--紧急高影响力--官方里程碑临近或社区需求迫切 |
| docs\00_meta\analysis\RUST_2026_PROJECT_GOALS_MONTHLY_TRACKING.md | 🟡 P1 — 重要（中等影响力 + 持续社区关注） | `#-p1--重要中等影响力--持续社区关注` | 同文件锚点不存在: #-p1--重要中等影响力--持续社区关注 |
| docs\00_meta\analysis\RUST_2026_PROJECT_GOALS_MONTHLY_TRACKING.md | 🟢 P2 — 规划（长期价值 + 资源允许时推进） | `#-p2--规划长期价值--资源允许时推进` | 同文件锚点不存在: #-p2--规划长期价值--资源允许时推进 |
| docs\00_meta\analysis\RUST_GLOBAL_ALIGNMENT_SYMMETRIC_DIFFERENCE_ANALYSIS_2026.md | 4.1 交集 (A intersect B) - 已对齐内容 | `#41-交集-a-intersect-b---已对齐内容` | 同文件锚点不存在: #41-交集-a-intersect-b---已对齐内容 |
| docs\00_meta\analysis\RUST_GLOBAL_ALIGNMENT_SYMMETRIC_DIFFERENCE_ANALYSIS_2026.md | 4.2 项目独有优势 (A - B) - 差异化资产 | `#42-项目独有优势-a---b---差异化资产` | 同文件锚点不存在: #42-项目独有优势-a---b---差异化资产 |
| docs\00_meta\analysis\RUST_GLOBAL_ALIGNMENT_SYMMETRIC_DIFFERENCE_ANALYSIS_2026.md | 4.3 项目缺失内容 (B - A) - 待补齐差距 (重点) | `#43-项目缺失内容-b---a---待补齐差距-重点` | 同文件锚点不存在: #43-项目缺失内容-b---a---待补齐差距-重点 |
| docs\00_meta\analysis\RUST_GLOBAL_ALIGNMENT_SYMMETRIC_DIFFERENCE_ANALYSIS_2026.md | P0 - 紧急缺失 (6项) | `#p0---紧急缺失-6项` | 同文件锚点不存在: #p0---紧急缺失-6项 |
| docs\00_meta\analysis\RUST_GLOBAL_ALIGNMENT_SYMMETRIC_DIFFERENCE_ANALYSIS_2026.md | P1 - 重要缺失 (12项) | `#p1---重要缺失-12项` | 同文件锚点不存在: #p1---重要缺失-12项 |
| docs\00_meta\analysis\RUST_GLOBAL_ALIGNMENT_SYMMETRIC_DIFFERENCE_ANALYSIS_2026.md | P2 - 扩展缺失 (12项) | `#p2---扩展缺失-12项` | 同文件锚点不存在: #p2---扩展缺失-12项 |
| docs\00_meta\analysis\RUST_GLOBAL_ALIGNMENT_SYMMETRIC_DIFFERENCE_ANALYSIS_2026.md | 阶段一: 版本迁移与基础夯实 (2026-04 ~ 2026-05, 4周) | `#阶段一-版本迁移与基础夯实-2026-04--2026-05-4周` | 同文件锚点不存在: #阶段一-版本迁移与基础夯实-2026-04--2026-05-4周 |
| docs\00_meta\analysis\RUST_GLOBAL_ALIGNMENT_SYMMETRIC_DIFFERENCE_ANALYSIS_2026.md | 阶段二: 2024 Edition 新特性专题 (2026-05 ~ 2026-06, 6周) | `#阶段二-2024-edition-新特性专题-2026-05--2026-06-6周` | 同文件锚点不存在: #阶段二-2024-edition-新特性专题-2026-05--2026-06-6周 |
| docs\00_meta\analysis\RUST_GLOBAL_ALIGNMENT_SYMMETRIC_DIFFERENCE_ANALYSIS_2026.md | 阶段三: 生产级工程实践 (2026-06 ~ 2026-08, 8周) | `#阶段三-生产级工程实践-2026-06--2026-08-8周` | 同文件锚点不存在: #阶段三-生产级工程实践-2026-06--2026-08-8周 |
| docs\00_meta\analysis\RUST_GLOBAL_ALIGNMENT_SYMMETRIC_DIFFERENCE_ANALYSIS_2026.md | 阶段四: 系统级与底层拓展 (2026-08 ~ 2026-10, 8周) | `#阶段四-系统级与底层拓展-2026-08--2026-10-8周` | 同文件锚点不存在: #阶段四-系统级与底层拓展-2026-08--2026-10-8周 |
| docs\00_meta\analysis\RUST_GLOBAL_ALIGNMENT_SYMMETRIC_DIFFERENCE_ANALYSIS_2026.md | 阶段五: 前沿技术与学术研究 (2026-10 ~ 2026-12, 8周) | `#阶段五-前沿技术与学术研究-2026-10--2026-12-8周` | 同文件锚点不存在: #阶段五-前沿技术与学术研究-2026-10--2026-12-8周 |
| docs\00_meta\analysis\RUST_GLOBAL_ALIGNMENT_SYMMETRIC_DIFFERENCE_ANALYSIS_2026.md | 阶段六: 练习体系与认证对接 (2026-12 ~ 2027-02, 8周) | `#阶段六-练习体系与认证对接-2026-12--2027-02-8周` | 同文件锚点不存在: #阶段六-练习体系与认证对接-2026-12--2027-02-8周 |
| docs\00_meta\analysis\RUST_GLOBAL_ALIGNMENT_SYMMETRIC_DIFFERENCE_ANALYSIS_2026.md | *本报告由全面梳理生成，需与用户确认后进入执行阶段。* | `#本报告由全面梳理生成需与用户确认后进入执行阶段` | 同文件锚点不存在: #本报告由全面梳理生成需与用户确认后进入执行阶段 |
| docs\00_meta\analysis\RUST_GLOBAL_ALIGNMENT_SYMMETRIC_DIFFERENCE_ANALYSIS_2026_05.md | 🔴 P0 — 紧急（标签错误 + 特性缺失） | `#-p0--紧急标签错误--特性缺失` | 同文件锚点不存在: #-p0--紧急标签错误--特性缺失 |
| docs\00_meta\analysis\RUST_GLOBAL_ALIGNMENT_SYMMETRIC_DIFFERENCE_ANALYSIS_2026_05.md | 🟡 P1 — 重要（内容缺失） | `#-p1--重要内容缺失` | 同文件锚点不存在: #-p1--重要内容缺失 |
| docs\00_meta\analysis\RUST_GLOBAL_ALIGNMENT_SYMMETRIC_DIFFERENCE_ANALYSIS_2026_05.md | 🟢 P2 — 扩展 | `#-p2--扩展` | 同文件锚点不存在: #-p2--扩展 |
| docs\00_meta\history\2026_reorganization.md | **状态**: ✅ 重组完成 | `#状态--重组完成` | 同文件锚点不存在: #状态--重组完成 |
| docs\00_meta\history\00_project_reorganization_plan.md | **验证**: 完成后全面检查 | `#验证-完成后全面检查` | 同文件锚点不存在: #验证-完成后全面检查 |
| docs\01_core\README.md | 2. 借用与引用 (Borrowing \& References) | `#2-借用与引用-borrowing--references` | 同文件锚点不存在: #2-借用与引用-borrowing--references |
| docs\01_learning\CROSS_MODULE_LEARNING_ROADMAP_2025_10_25.md | 🗺️ 7 条定制化学习路径 | `#️-7-条定制化学习路径` | 同文件锚点不存在: #️-7-条定制化学习路径 |
| docs\01_learning\CROSS_MODULE_LEARNING_ROADMAP_2025_10_25.md | C01 所有权与借用 → 1.96 并发安全 | `#c01-所有权与借用--196-并发安全` | 同文件锚点不存在: #c01-所有权与借用--196-并发安全 |
| docs\01_learning\CROSS_MODULE_LEARNING_ROADMAP_2025_10_25.md | C04 泛型 → async Fn Trait (≥1.85, Ed 2024) | `#c04-泛型--async-fn-trait-185-ed-2024` | 同文件锚点不存在: #c04-泛型--async-fn-trait-185-ed-2024 |
| docs\01_learning\CROSS_MODULE_LEARNING_ROADMAP_2025_10_25.md | C05 线程 → 1.96 线程改进 | `#c05-线程--196-线程改进` | 同文件锚点不存在: #c05-线程--196-线程改进 |
| docs\01_learning\CROSS_MODULE_LEARNING_ROADMAP_2025_10_25.md | C08 算法 → isqrt (≥1.84) | `#c08-算法--isqrt-184` | 同文件锚点不存在: #c08-算法--isqrt-184 |
| docs\01_learning\CROSS_MODULE_NAVIGATION.md | 🗺️ 学习路线图 | `#️-学习路线图` | 同文件锚点不存在: #️-学习路线图 |
| docs\01_learning\CROSS_MODULE_NAVIGATION.md | 核心概念 → 源码 → 文档 → 实践 | `#核心概念--源码--文档--实践` | 同文件锚点不存在: #核心概念--源码--文档--实践 |
| docs\01_learning\CROSS_MODULE_NAVIGATION.md | **状态**: ✅ 100% 完成 | `#状态--100-完成` | 同文件锚点不存在: #状态--100-完成 |
| docs\01_learning\LEARNING_PATH_GUIDE_2025_10_24.md | 🗺️ 推荐学习路径 | `#️-推荐学习路径` | 同文件锚点不存在: #️-推荐学习路径 |
| docs\01_learning\LEARNING_PATH_GUIDE_2025_10_24.md | 🛠️ 实践项目建议 | `#️-实践项目建议` | 同文件锚点不存在: #️-实践项目建议 |
| docs\01_learning\LEARNING_PATH_PLANNING.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\01_learning\LEARNING_PATH_PLANNING.md | **最后更新**: 2026-05-08 (Rust 1.95+ 持续更新) | `#最后更新-2026-05-08-rust-195-持续更新` | 同文件锚点不存在: #最后更新-2026-05-08-rust-195-持续更新 |
| docs\01_learning\LEARNING_PATH_PLANNING.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\01_learning\LEARNING_PATH_PLANNING.md | **最后更新**: 2026-05-08 (Rust 1.95+ 持续更新) | `#最后更新-2026-05-08-rust-195-持续更新` | 同文件锚点不存在: #最后更新-2026-05-08-rust-195-持续更新 |
| docs\01_learning\LFRS_CERTIFICATION_MAPPING.md | 考点 10: 并发（线程 / 通道 / async） | `#考点-10-并发线程--通道--async` | 同文件锚点不存在: #考点-10-并发线程--通道--async |
| docs\01_learning\01_mdbook_quiz_guide.md | **最后更新**: 2026-05-08 (Rust 1.95+ 持续更新) | `#最后更新-2026-05-08-rust-195-持续更新` | 同文件锚点不存在: #最后更新-2026-05-08-rust-195-持续更新 |
| docs\01_learning\OFFICIAL_RESOURCES_MAPPING.md | 模块 → 官方章节映射 | `#模块--官方章节映射` | 同文件锚点不存在: #模块--官方章节映射 |
| docs\01_learning\OFFICIAL_RESOURCES_MAPPING.md | 路径一：新手入门路径（零基础 → 能写简单项目） | `#路径一新手入门路径零基础--能写简单项目` | 同文件锚点不存在: #路径一新手入门路径零基础--能写简单项目 |
| docs\01_learning\OFFICIAL_RESOURCES_MAPPING.md | 路径二：中级进阶路径（能写项目 → 深入理解） | `#路径二中级进阶路径能写项目--深入理解` | 同文件锚点不存在: #路径二中级进阶路径能写项目--深入理解 |
| docs\01_learning\OFFICIAL_RESOURCES_MAPPING.md | 路径三：高级专家路径（深入原理 → 形式化理解） | `#路径三高级专家路径深入原理--形式化理解` | 同文件锚点不存在: #路径三高级专家路径深入原理--形式化理解 |
| docs\01_learning\OFFICIAL_RESOURCES_MAPPING.md | 在线课程资源映射（edX + Coursera） | `#在线课程资源映射edx--coursera` | 同文件锚点不存在: #在线课程资源映射edx--coursera |
| docs\02_reference\CROSS_LANGUAGE_COMPARISON.md | Haskell（二级来源，Trait / 类型系统对标） | `#haskell二级来源trait--类型系统对标` | 同文件锚点不存在: #haskell二级来源trait--类型系统对标 |
| docs\02_reference\CROSS_LANGUAGE_COMPARISON.md | 所有权唯一性定理 | `../research_notes/formal_methods/ownership_model.md#定理-2-所有权唯一性` | 锚点不存在: #定理-2-所有权唯一性 |
| docs\02_reference\CROSS_LANGUAGE_COMPARISON.md | 内存安全定理 | `../research_notes/formal_methods/ownership_model.md#定理-3-内存安全框架` | 锚点不存在: #定理-3-内存安全框架 |
| docs\02_reference\EDGE_CASES_AND_SPECIAL_CASES.md | 空 HashMap / BTreeMap | `#空-hashmap--btreemap` | 同文件锚点不存在: #空-hashmap--btreemap |
| docs\02_reference\EDGE_CASES_AND_SPECIAL_CASES.md | 零个线程 / 空任务列表 | `#零个线程--空任务列表` | 同文件锚点不存在: #零个线程--空任务列表 |
| docs\02_reference\EDGE_CASES_AND_SPECIAL_CASES.md | ownership_model | `../research_notes/formal_methods/ownership_model.md#示例-8-复杂所有权场景---结构体字段移动` | 锚点不存在: #示例-8-复杂所有权场景---结构体字段移动 |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0382 - 使用已移动的值 | `#e0382---使用已移动的值` | 同文件锚点不存在: #e0382---使用已移动的值 |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0383 - 部分移动 | `#e0383---部分移动` | 同文件锚点不存在: #e0383---部分移动 |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0499 - 重复可变借用 | `#e0499---重复可变借用` | 同文件锚点不存在: #e0499---重复可变借用 |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0502 - 可变与不可变借用共存 | `#e0502---可变与不可变借用共存` | 同文件锚点不存在: #e0502---可变与不可变借用共存 |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0503 - 使用已移动的值（在借用后） | `#e0503---使用已移动的值在借用后` | 同文件锚点不存在: #e0503---使用已移动的值在借用后 |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0505 - 在借用时移动 | `#e0505---在借用时移动` | 同文件锚点不存在: #e0505---在借用时移动 |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0506 - 在借用时赋值 | `#e0506---在借用时赋值` | 同文件锚点不存在: #e0506---在借用时赋值 |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0507 - 从借用内容中移出 | `#e0507---从借用内容中移出` | 同文件锚点不存在: #e0507---从借用内容中移出 |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0508 - 从数组/元组中移出 | `#e0508---从数组元组中移出` | 同文件锚点不存在: #e0508---从数组元组中移出 |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0277 - Trait 约束不满足 | `#e0277---trait-约束不满足` | 同文件锚点不存在: #e0277---trait-约束不满足 |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0282 - 需要类型标注 | `#e0282---需要类型标注` | 同文件锚点不存在: #e0282---需要类型标注 |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0283 - 类型标注不足 | `#e0283---类型标注不足` | 同文件锚点不存在: #e0283---类型标注不足 |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0308 - 类型不匹配 | `#e0308---类型不匹配` | 同文件锚点不存在: #e0308---类型不匹配 |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0308 - 返回值类型不匹配 | `#e0308---返回值类型不匹配` | 同文件锚点不存在: #e0308---返回值类型不匹配 |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0106 - 需要生命周期标注 | `#e0106---需要生命周期标注` | 同文件锚点不存在: #e0106---需要生命周期标注 |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0107 - 生命周期参数数量不匹配 | `#e0107---生命周期参数数量不匹配` | 同文件锚点不存在: #e0107---生命周期参数数量不匹配 |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0597 - 生命周期不足 | `#e0597---生命周期不足` | 同文件锚点不存在: #e0597---生命周期不足 |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0310 - 参数生命周期不足 | `#e0310---参数生命周期不足` | 同文件锚点不存在: #e0310---参数生命周期不足 |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0495 - 生命周期不匹配 | `#e0495---生命周期不匹配` | 同文件锚点不存在: #e0495---生命周期不匹配 |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0381 - 使用未初始化变量 | `#e0381---使用未初始化变量` | 同文件锚点不存在: #e0381---使用未初始化变量 |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0384 - 对不可变变量赋值 | `#e0384---对不可变变量赋值` | 同文件锚点不存在: #e0384---对不可变变量赋值 |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0004 - 非穷尽模式匹配 | `#e0004---非穷尽模式匹配` | 同文件锚点不存在: #e0004---非穷尽模式匹配 |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0005 - 不可反驳模式 | `#e0005---不可反驳模式` | 同文件锚点不存在: #e0005---不可反驳模式 |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0297 - 模式绑定不匹配 | `#e0297---模式绑定不匹配` | 同文件锚点不存在: #e0297---模式绑定不匹配 |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0424 - self 使用错误 | `#e0424---self-使用错误` | 同文件锚点不存在: #e0424---self-使用错误 |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0425 - 未找到函数/变量 | `#e0425---未找到函数变量` | 同文件锚点不存在: #e0425---未找到函数变量 |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0554 - 未知特性 | `#e0554---未知特性` | 同文件锚点不存在: #e0554---未知特性 |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0432 - 未解析的导入 | `#e0432---未解析的导入` | 同文件锚点不存在: #e0432---未解析的导入 |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0433 - 未找到 crate | `#e0433---未找到-crate` | 同文件锚点不存在: #e0433---未找到-crate |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0463 - 找不到 crate | `#e0463---找不到-crate` | 同文件锚点不存在: #e0463---找不到-crate |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0603 - 私有模块 | `#e0603---私有模块` | 同文件锚点不存在: #e0603---私有模块 |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0596 - 无法借用不可变变量为可变 | `#e0596---无法借用不可变变量为可变` | 同文件锚点不存在: #e0596---无法借用不可变变量为可变 |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0599 - 未找到方法 | `#e0599---未找到方法` | 同文件锚点不存在: #e0599---未找到方法 |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0609 - 未找到字段 | `#e0609---未找到字段` | 同文件锚点不存在: #e0609---未找到字段 |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0614 - 类型不能进行此操作 | `#e0614---类型不能进行此操作` | 同文件锚点不存在: #e0614---类型不能进行此操作 |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0616 - 私有字段 | `#e0616---私有字段` | 同文件锚点不存在: #e0616---私有字段 |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0201 - 重复的 Trait 实现 | `#e0201---重复的-trait-实现` | 同文件锚点不存在: #e0201---重复的-trait-实现 |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0323 - 错误的方法签名 | `#e0323---错误的方法签名` | 同文件锚点不存在: #e0323---错误的方法签名 |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0392 - 参数未使用 | `#e0392---参数未使用` | 同文件锚点不存在: #e0392---参数未使用 |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0275 - Trait 解析无限递归 | `#e0275---trait-解析无限递归` | 同文件锚点不存在: #e0275---trait-解析无限递归 |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0373 - 闭包生命周期问题 | `#e0373---闭包生命周期问题` | 同文件锚点不存在: #e0373---闭包生命周期问题 |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0378 - Send/Sync 约束不满足 | `#e0378---sendsync-约束不满足` | 同文件锚点不存在: #e0378---sendsync-约束不满足 |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0700 - 异步块中借用 | `#e0700---异步块中借用` | 同文件锚点不存在: #e0700---异步块中借用 |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0733 - 递归异步函数 | `#e0733---递归异步函数` | 同文件锚点不存在: #e0733---递归异步函数 |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0252 - 名称冲突 | `#e0252---名称冲突` | 同文件锚点不存在: #e0252---名称冲突 |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0301 - 可变与不可变模式 | `#e0301---可变与不可变模式` | 同文件锚点不存在: #e0301---可变与不可变模式 |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0446 - 私有类型在公共接口 | `#e0446---私有类型在公共接口` | 同文件锚点不存在: #e0446---私有类型在公共接口 |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0515 - 返回局部变量的引用 | `#e0515---返回局部变量的引用` | 同文件锚点不存在: #e0515---返回局部变量的引用 |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0521 - 借用数据逃逸 | `#e0521---借用数据逃逸` | 同文件锚点不存在: #e0521---借用数据逃逸 |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0658 - 不稳定特性 | `#e0658---不稳定特性` | 同文件锚点不存在: #e0658---不稳定特性 |
| docs\02_reference\ERROR_CODE_MAPPING.md | E0689 - 整数类型后缀 | `#e0689---整数类型后缀` | 同文件锚点不存在: #e0689---整数类型后缀 |
| docs\02_reference\ERROR_CODE_MAPPING.md | W0001 - 未使用的变量 | `#w0001---未使用的变量` | 同文件锚点不存在: #w0001---未使用的变量 |
| docs\02_reference\ERROR_CODE_MAPPING.md | W0002 - 未使用的导入 | `#w0002---未使用的导入` | 同文件锚点不存在: #w0002---未使用的导入 |
| docs\02_reference\ERROR_CODE_MAPPING.md | W0003 - 不可达代码 | `#w0003---不可达代码` | 同文件锚点不存在: #w0003---不可达代码 |
| docs\02_reference\ERROR_CODE_MAPPING.md | W0004 - 未使用的 mut | `#w0004---未使用的-mut` | 同文件锚点不存在: #w0004---未使用的-mut |
| docs\02_reference\ERROR_CODE_MAPPING.md | W0005 - 死代码 | `#w0005---死代码` | 同文件锚点不存在: #w0005---死代码 |
| docs\02_reference\ERROR_CODE_MAPPING.md | W0006 - 未处理的 Result | `#w0006---未处理的-result` | 同文件锚点不存在: #w0006---未处理的-result |
| docs\02_reference\ERROR_CODE_MAPPING.md | **状态**: ✅ 深度整合完成 | `#状态--深度整合完成` | 同文件锚点不存在: #状态--深度整合完成 |
| docs\02_reference\platform_support_matrix.md | 一、Rust 1.95.0 新增 / 变更的平台支持 | `#一rust-1950-新增--变更的平台支持` | 同文件锚点不存在: #一rust-1950-新增--变更的平台支持 |
| docs\02_reference\platform_support_matrix.md | Tier 1（保证可用 + 主机工具 + CI 测试） | `#tier-1保证可用--主机工具--ci-测试` | 同文件锚点不存在: #tier-1保证可用--主机工具--ci-测试 |
| docs\02_reference\platform_support_matrix.md | Tier 2 with Host Tools（交叉编译 + 主机工具） | `#tier-2-with-host-tools交叉编译--主机工具` | 同文件锚点不存在: #tier-2-with-host-tools交叉编译--主机工具 |
| docs\02_reference\platform_support_matrix.md | 三、嵌入式 / 裸机开发注意事项 | `#三嵌入式--裸机开发注意事项` | 同文件锚点不存在: #三嵌入式--裸机开发注意事项 |
| docs\02_reference\STANDARD_LIBRARY_COMPREHENSIVE_ANALYSIS_2025_12_25.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\02_reference\STANDARD_LIBRARY_COMPREHENSIVE_ANALYSIS_2025_12_25.md | 1.4 Rust 1.93.0 标准库新特性 🆕 | `#14-rust-1930-标准库新特性-` | 同文件锚点不存在: #14-rust-1930-标准库新特性- |
| docs\02_reference\STANDARD_LIBRARY_COMPREHENSIVE_ANALYSIS_2025_12_25.md | 1.5 Rust 1.93.0 标准库行为变更 ⚠️ | `#15-rust-1930-标准库行为变更-️` | 同文件锚点不存在: #15-rust-1930-标准库行为变更-️ |
| docs\02_reference\STANDARD_LIBRARY_COMPREHENSIVE_ANALYSIS_2025_12_25.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\02_reference\STANDARD_LIBRARY_COMPREHENSIVE_ANALYSIS_2025_12_25.md | 1.4 Rust 1.93.0 标准库新特性 🆕 | `#14-rust-1930-标准库新特性-` | 同文件锚点不存在: #14-rust-1930-标准库新特性- |
| docs\02_reference\STANDARD_LIBRARY_COMPREHENSIVE_ANALYSIS_2025_12_25.md | 1.5 Rust 1.93.0 标准库行为变更 ⚠️ | `#15-rust-1930-标准库行为变更-️` | 同文件锚点不存在: #15-rust-1930-标准库行为变更-️ |
| docs\02_reference\quick_reference\ai_ml_cheatsheet.md | 🤖 Rust AI/ML 速查卡 | `#-rust-aiml-速查卡` | 同文件锚点不存在: #-rust-aiml-速查卡 |
| docs\02_reference\quick_reference\ai_ml_cheatsheet.md | 📑 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\02_reference\quick_reference\ai_ml_cheatsheet.md | 反例 4: 内存泄漏 - 循环引用张量缓存 | `#反例-4-内存泄漏---循环引用张量缓存` | 同文件锚点不存在: #反例-4-内存泄漏---循环引用张量缓存 |
| docs\02_reference\quick_reference\ai_ml_cheatsheet.md | 反例 5: 边界情况 - 空张量操作 | `#反例-5-边界情况---空张量操作` | 同文件锚点不存在: #反例-5-边界情况---空张量操作 |
| docs\02_reference\quick_reference\ai_ml_cheatsheet.md | **最后更新**: 2026-05-08 (AI/ML 场景深度整合) | `#最后更新-2026-05-08-aiml-场景深度整合` | 同文件锚点不存在: #最后更新-2026-05-08-aiml-场景深度整合 |
| docs\02_reference\quick_reference\ai_ml_cheatsheet.md | 🤖 Rust AI/ML 速查卡 | `#-rust-aiml-速查卡` | 同文件锚点不存在: #-rust-aiml-速查卡 |
| docs\02_reference\quick_reference\ai_ml_cheatsheet.md | 📑 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\02_reference\quick_reference\ai_ml_cheatsheet.md | 反例 4: 内存泄漏 - 循环引用张量缓存 | `#反例-4-内存泄漏---循环引用张量缓存` | 同文件锚点不存在: #反例-4-内存泄漏---循环引用张量缓存 |
| docs\02_reference\quick_reference\ai_ml_cheatsheet.md | 反例 5: 边界情况 - 空张量操作 | `#反例-5-边界情况---空张量操作` | 同文件锚点不存在: #反例-5-边界情况---空张量操作 |
| docs\02_reference\quick_reference\ai_ml_cheatsheet.md | **最后更新**: 2026-05-08 (AI/ML 场景深度整合) | `#最后更新-2026-05-08-aiml-场景深度整合` | 同文件锚点不存在: #最后更新-2026-05-08-aiml-场景深度整合 |
| docs\02_reference\quick_reference\algorithms_cheatsheet.md | 算法与数据结构快速参考卡片 | `#算法与数据结构快速参考卡片` | 同文件锚点不存在: #算法与数据结构快速参考卡片 |
| docs\02_reference\quick_reference\algorithms_cheatsheet.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\02_reference\quick_reference\algorithms_cheatsheet.md | 示例 3: 动态规划 - 最长公共子序列 | `#示例-3-动态规划---最长公共子序列` | 同文件锚点不存在: #示例-3-动态规划---最长公共子序列 |
| docs\02_reference\quick_reference\algorithms_cheatsheet.md | **最后更新**: 2026-05-08 (算法场景深度整合) | `#最后更新-2026-05-08-算法场景深度整合` | 同文件锚点不存在: #最后更新-2026-05-08-算法场景深度整合 |
| docs\02_reference\quick_reference\algorithms_cheatsheet.md | 算法与数据结构快速参考卡片 | `#算法与数据结构快速参考卡片` | 同文件锚点不存在: #算法与数据结构快速参考卡片 |
| docs\02_reference\quick_reference\algorithms_cheatsheet.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\02_reference\quick_reference\algorithms_cheatsheet.md | 示例 3: 动态规划 - 最长公共子序列 | `#示例-3-动态规划---最长公共子序列` | 同文件锚点不存在: #示例-3-动态规划---最长公共子序列 |
| docs\02_reference\quick_reference\algorithms_cheatsheet.md | **最后更新**: 2026-05-08 (算法场景深度整合) | `#最后更新-2026-05-08-算法场景深度整合` | 同文件锚点不存在: #最后更新-2026-05-08-算法场景深度整合 |
| docs\02_reference\quick_reference\02_algorithm_decision_cheatsheet.md | **最后更新**: 2026-05-08 | `#最后更新-2026-05-08` | 同文件锚点不存在: #最后更新-2026-05-08 |
| docs\02_reference\quick_reference\02_assert_matches_guide.md | `assert_matches!` / `debug_assert_matches!` 速查指南 | `#assert_matches--debug_assert_matches-速查指南` | 同文件锚点不存在: #assert_matches--debug_assert_matches-速查指南 |
| docs\02_reference\quick_reference\02_assert_matches_guide.md | 与 `assert!` + `matches!` 的关系 | `#与-assert--matches-的关系` | 同文件锚点不存在: #与-assert--matches-的关系 |
| docs\02_reference\quick_reference\async_patterns.md | ⚡ Rust 异步编程速查卡 | `#-rust-异步编程速查卡` | 同文件锚点不存在: #-rust-异步编程速查卡 |
| docs\02_reference\quick_reference\async_patterns.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\02_reference\quick_reference\async_patterns.md | 🏗️ 运行时对比 | `#️-运行时对比` | 同文件锚点不存在: #️-运行时对比 |
| docs\02_reference\quick_reference\async_patterns.md | 模式 1: Arc + Mutex | `#模式-1-arc--mutex` | 同文件锚点不存在: #模式-1-arc--mutex |
| docs\02_reference\quick_reference\async_patterns.md | 模式 2: Arc + RwLock（读多写少） | `#模式-2-arc--rwlock读多写少` | 同文件锚点不存在: #模式-2-arc--rwlock读多写少 |
| docs\02_reference\quick_reference\async_patterns.md | ⚠️ 常见陷阱 | `#️-常见陷阱` | 同文件锚点不存在: #️-常见陷阱 |
| docs\02_reference\quick_reference\async_patterns.md | ⚠️ 边界情况 | `#️-边界情况` | 同文件锚点不存在: #️-边界情况 |
| docs\02_reference\quick_reference\async_patterns.md | **状态**: ✅ 深度整合完成 | `#状态--深度整合完成` | 同文件锚点不存在: #状态--深度整合完成 |
| docs\02_reference\quick_reference\async_patterns.md | ⚡ Rust 异步编程速查卡 | `#-rust-异步编程速查卡` | 同文件锚点不存在: #-rust-异步编程速查卡 |
| docs\02_reference\quick_reference\async_patterns.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\02_reference\quick_reference\async_patterns.md | 🏗️ 运行时对比 | `#️-运行时对比` | 同文件锚点不存在: #️-运行时对比 |
| docs\02_reference\quick_reference\async_patterns.md | 模式 1: Arc + Mutex | `#模式-1-arc--mutex` | 同文件锚点不存在: #模式-1-arc--mutex |
| docs\02_reference\quick_reference\async_patterns.md | 模式 2: Arc + RwLock（读多写少） | `#模式-2-arc--rwlock读多写少` | 同文件锚点不存在: #模式-2-arc--rwlock读多写少 |
| docs\02_reference\quick_reference\async_patterns.md | ⚠️ 常见陷阱 | `#️-常见陷阱` | 同文件锚点不存在: #️-常见陷阱 |
| docs\02_reference\quick_reference\async_patterns.md | ⚠️ 边界情况 | `#️-边界情况` | 同文件锚点不存在: #️-边界情况 |
| docs\02_reference\quick_reference\async_patterns.md | **状态**: ✅ 深度整合完成 | `#状态--深度整合完成` | 同文件锚点不存在: #状态--深度整合完成 |
| docs\02_reference\quick_reference\cargo_cheatsheet.md | 📦 Cargo 速查卡 {#-cargo-速查卡} | `#-cargo-速查卡--cargo-速查卡` | 同文件锚点不存在: #-cargo-速查卡--cargo-速查卡 |
| docs\02_reference\quick_reference\cargo_cheatsheet.md | ⚙️ 配置文件 {#️-配置文件} | `#️-配置文件-️-配置文件` | 同文件锚点不存在: #️-配置文件-️-配置文件 |
| docs\02_reference\quick_reference\cargo_cheatsheet.md | 🛠️ 常用工具 {#️-常用工具} | `#️-常用工具-️-常用工具` | 同文件锚点不存在: #️-常用工具-️-常用工具 |
| docs\02_reference\quick_reference\cargo_cheatsheet.md | **状态**: ✅ 深度整合完成 | `#状态--深度整合完成` | 同文件锚点不存在: #状态--深度整合完成 |
| docs\02_reference\quick_reference\cargo_cheatsheet.md | 📦 Cargo 速查卡 {#-cargo-速查卡} | `#-cargo-速查卡--cargo-速查卡` | 同文件锚点不存在: #-cargo-速查卡--cargo-速查卡 |
| docs\02_reference\quick_reference\cargo_cheatsheet.md | ⚙️ 配置文件 {#️-配置文件} | `#️-配置文件-️-配置文件` | 同文件锚点不存在: #️-配置文件-️-配置文件 |
| docs\02_reference\quick_reference\cargo_cheatsheet.md | 🛠️ 常用工具 {#️-常用工具} | `#️-常用工具-️-常用工具` | 同文件锚点不存在: #️-常用工具-️-常用工具 |
| docs\02_reference\quick_reference\cargo_cheatsheet.md | **状态**: ✅ 深度整合完成 | `#状态--深度整合完成` | 同文件锚点不存在: #状态--深度整合完成 |
| docs\02_reference\quick_reference\closures_cheatsheet.md | **最后更新**: 2026-05-08 (闭包场景深度整合) | `#最后更新-2026-05-08-闭包场景深度整合` | 同文件锚点不存在: #最后更新-2026-05-08-闭包场景深度整合 |
| docs\02_reference\quick_reference\collections_iterators_cheatsheet.md | 📦 Rust 集合与迭代器速查卡 | `#-rust-集合与迭代器速查卡` | 同文件锚点不存在: #-rust-集合与迭代器速查卡 |
| docs\02_reference\quick_reference\collections_iterators_cheatsheet.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\02_reference\quick_reference\collections_iterators_cheatsheet.md | 🗺️ HashMap（哈希映射） | `#️-hashmap哈希映射` | 同文件锚点不存在: #️-hashmap哈希映射 |
| docs\02_reference\quick_reference\collections_iterators_cheatsheet.md | 🍽️ 迭代器消费者 | `#️-迭代器消费者` | 同文件锚点不存在: #️-迭代器消费者 |
| docs\02_reference\quick_reference\collections_iterators_cheatsheet.md | Rust 1.95+ `array_windows()` - 零开销固定大小窗口 | `#rust-195-array_windows---零开销固定大小窗口` | 同文件锚点不存在: #rust-195-array_windows---零开销固定大小窗口 |
| docs\02_reference\quick_reference\collections_iterators_cheatsheet.md | 🎯 **掌握集合与迭代器，高效处理数据！** | `#-掌握集合与迭代器高效处理数据` | 同文件锚点不存在: #-掌握集合与迭代器高效处理数据 |
| docs\02_reference\quick_reference\collections_iterators_cheatsheet.md | 📦 Rust 集合与迭代器速查卡 | `#-rust-集合与迭代器速查卡` | 同文件锚点不存在: #-rust-集合与迭代器速查卡 |
| docs\02_reference\quick_reference\collections_iterators_cheatsheet.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\02_reference\quick_reference\collections_iterators_cheatsheet.md | 🗺️ HashMap（哈希映射） | `#️-hashmap哈希映射` | 同文件锚点不存在: #️-hashmap哈希映射 |
| docs\02_reference\quick_reference\collections_iterators_cheatsheet.md | 🍽️ 迭代器消费者 | `#️-迭代器消费者` | 同文件锚点不存在: #️-迭代器消费者 |
| docs\02_reference\quick_reference\collections_iterators_cheatsheet.md | Rust 1.95+ `array_windows()` - 零开销固定大小窗口 | `#rust-195-array_windows---零开销固定大小窗口` | 同文件锚点不存在: #rust-195-array_windows---零开销固定大小窗口 |
| docs\02_reference\quick_reference\collections_iterators_cheatsheet.md | 🎯 **掌握集合与迭代器，高效处理数据！** | `#-掌握集合与迭代器高效处理数据` | 同文件锚点不存在: #-掌握集合与迭代器高效处理数据 |
| docs\02_reference\quick_reference\control_flow_functions_cheatsheet.md | 🔄 Rust 控制流与函数速查卡 | `#-rust-控制流与函数速查卡` | 同文件锚点不存在: #-rust-控制流与函数速查卡 |
| docs\02_reference\quick_reference\control_flow_functions_cheatsheet.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\02_reference\quick_reference\control_flow_functions_cheatsheet.md | ⚠️ 边界情况 | `#️-边界情况` | 同文件锚点不存在: #️-边界情况 |
| docs\02_reference\quick_reference\control_flow_functions_cheatsheet.md | **状态**: ✅ 深度整合完成 | `#状态--深度整合完成` | 同文件锚点不存在: #状态--深度整合完成 |
| docs\02_reference\quick_reference\control_flow_functions_cheatsheet.md | 🔄 Rust 控制流与函数速查卡 | `#-rust-控制流与函数速查卡` | 同文件锚点不存在: #-rust-控制流与函数速查卡 |
| docs\02_reference\quick_reference\control_flow_functions_cheatsheet.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\02_reference\quick_reference\control_flow_functions_cheatsheet.md | ⚠️ 边界情况 | `#️-边界情况` | 同文件锚点不存在: #️-边界情况 |
| docs\02_reference\quick_reference\control_flow_functions_cheatsheet.md | **状态**: ✅ 深度整合完成 | `#状态--深度整合完成` | 同文件锚点不存在: #状态--深度整合完成 |
| docs\02_reference\quick_reference\error_handling_cheatsheet.md | ⚠️ Rust 错误处理速查卡 | `#️-rust-错误处理速查卡` | 同文件锚点不存在: #️-rust-错误处理速查卡 |
| docs\02_reference\quick_reference\error_handling_cheatsheet.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\02_reference\quick_reference\error_handling_cheatsheet.md | 模式 3: ? 操作符 | `#模式-3--操作符` | 同文件锚点不存在: #模式-3--操作符 |
| docs\02_reference\quick_reference\error_handling_cheatsheet.md | anyhow - 灵活的错误处理 | `#anyhow---灵活的错误处理` | 同文件锚点不存在: #anyhow---灵活的错误处理 |
| docs\02_reference\quick_reference\error_handling_cheatsheet.md | thiserror - 自定义错误类型 | `#thiserror---自定义错误类型` | 同文件锚点不存在: #thiserror---自定义错误类型 |
| docs\02_reference\quick_reference\error_handling_cheatsheet.md | 反例 2: 在非 Result 返回类型函数中使用 ? | `#反例-2-在非-result-返回类型函数中使用-` | 同文件锚点不存在: #反例-2-在非-result-返回类型函数中使用- |
| docs\02_reference\quick_reference\error_handling_cheatsheet.md | 生产场景 1：批量任务处理（超时 + 错误阈值） | `#生产场景-1批量任务处理超时--错误阈值` | 同文件锚点不存在: #生产场景-1批量任务处理超时--错误阈值 |
| docs\02_reference\quick_reference\error_handling_cheatsheet.md | 📚 相关资源 | `#-相关资源-1` | 同文件锚点不存在: #-相关资源-1 |
| docs\02_reference\quick_reference\error_handling_cheatsheet.md | ⚠️ 边界情况 | `#️-边界情况` | 同文件锚点不存在: #️-边界情况 |
| docs\02_reference\quick_reference\error_handling_cheatsheet.md | 边界 2:  panic 恢复 | `#边界-2--panic-恢复` | 同文件锚点不存在: #边界-2--panic-恢复 |
| docs\02_reference\quick_reference\error_handling_cheatsheet.md | **Rust 版本**: 1.96.0+ (Edition 2024) | `#rust-版本-1950-edition-2024` | 同文件锚点不存在: #rust-版本-1950-edition-2024 |
| docs\02_reference\quick_reference\error_handling_cheatsheet.md | ⚠️ Rust 错误处理速查卡 | `#️-rust-错误处理速查卡` | 同文件锚点不存在: #️-rust-错误处理速查卡 |
| docs\02_reference\quick_reference\error_handling_cheatsheet.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\02_reference\quick_reference\error_handling_cheatsheet.md | 模式 3: ? 操作符 | `#模式-3--操作符` | 同文件锚点不存在: #模式-3--操作符 |
| docs\02_reference\quick_reference\error_handling_cheatsheet.md | anyhow - 灵活的错误处理 | `#anyhow---灵活的错误处理` | 同文件锚点不存在: #anyhow---灵活的错误处理 |
| docs\02_reference\quick_reference\error_handling_cheatsheet.md | thiserror - 自定义错误类型 | `#thiserror---自定义错误类型` | 同文件锚点不存在: #thiserror---自定义错误类型 |
| docs\02_reference\quick_reference\error_handling_cheatsheet.md | 反例 2: 在非 Result 返回类型函数中使用 ? | `#反例-2-在非-result-返回类型函数中使用-` | 同文件锚点不存在: #反例-2-在非-result-返回类型函数中使用- |
| docs\02_reference\quick_reference\error_handling_cheatsheet.md | 生产场景 1：批量任务处理（超时 + 错误阈值） | `#生产场景-1批量任务处理超时--错误阈值` | 同文件锚点不存在: #生产场景-1批量任务处理超时--错误阈值 |
| docs\02_reference\quick_reference\error_handling_cheatsheet.md | 📚 相关资源 | `#-相关资源-1` | 同文件锚点不存在: #-相关资源-1 |
| docs\02_reference\quick_reference\error_handling_cheatsheet.md | ⚠️ 边界情况 | `#️-边界情况` | 同文件锚点不存在: #️-边界情况 |
| docs\02_reference\quick_reference\error_handling_cheatsheet.md | 边界 2:  panic 恢复 | `#边界-2--panic-恢复` | 同文件锚点不存在: #边界-2--panic-恢复 |
| docs\02_reference\quick_reference\error_handling_cheatsheet.md | **Rust 版本**: 1.96.0+ (Edition 2024) | `#rust-版本-1950-edition-2024` | 同文件锚点不存在: #rust-版本-1950-edition-2024 |
| docs\02_reference\quick_reference\generics_cheatsheet.md | 🔷 Rust 泛型编程速查卡 | `#-rust-泛型编程速查卡` | 同文件锚点不存在: #-rust-泛型编程速查卡 |
| docs\02_reference\quick_reference\generics_cheatsheet.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\02_reference\quick_reference\generics_cheatsheet.md | 📚 相关资源 | `#-相关资源-1` | 同文件锚点不存在: #-相关资源-1 |
| docs\02_reference\quick_reference\generics_cheatsheet.md | ⚠️ 边界情况 | `#️-边界情况` | 同文件锚点不存在: #️-边界情况 |
| docs\02_reference\quick_reference\generics_cheatsheet.md | **状态**: ✅ 深度整合完成 | `#状态--深度整合完成` | 同文件锚点不存在: #状态--深度整合完成 |
| docs\02_reference\quick_reference\generics_cheatsheet.md | 🔷 Rust 泛型编程速查卡 | `#-rust-泛型编程速查卡` | 同文件锚点不存在: #-rust-泛型编程速查卡 |
| docs\02_reference\quick_reference\generics_cheatsheet.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\02_reference\quick_reference\generics_cheatsheet.md | 📚 相关资源 | `#-相关资源-1` | 同文件锚点不存在: #-相关资源-1 |
| docs\02_reference\quick_reference\generics_cheatsheet.md | ⚠️ 边界情况 | `#️-边界情况` | 同文件锚点不存在: #️-边界情况 |
| docs\02_reference\quick_reference\generics_cheatsheet.md | **状态**: ✅ 深度整合完成 | `#状态--深度整合完成` | 同文件锚点不存在: #状态--深度整合完成 |
| docs\02_reference\quick_reference\generics_cheatsheet.md | 生命周期速查卡 | `./type_system.md#生命周期` | 锚点不存在: #生命周期 |
| docs\02_reference\quick_reference\modules_cheatsheet.md | 📦 Rust 模块系统速查卡 | `#-rust-模块系统速查卡` | 同文件锚点不存在: #-rust-模块系统速查卡 |
| docs\02_reference\quick_reference\modules_cheatsheet.md | 🛤️ 路径系统 | `#️-路径系统` | 同文件锚点不存在: #️-路径系统 |
| docs\02_reference\quick_reference\modules_cheatsheet.md | ⚠️ 边界情况 | `#️-边界情况` | 同文件锚点不存在: #️-边界情况 |
| docs\02_reference\quick_reference\modules_cheatsheet.md | **状态**: ✅ 深度整合完成 | `#状态--深度整合完成` | 同文件锚点不存在: #状态--深度整合完成 |
| docs\02_reference\quick_reference\network_programming_cheatsheet.md | 网络编程快速参考卡片 | `#网络编程快速参考卡片` | 同文件锚点不存在: #网络编程快速参考卡片 |
| docs\02_reference\quick_reference\network_programming_cheatsheet.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\02_reference\quick_reference\network_programming_cheatsheet.md | **状态**: ✅ 深度整合完成 | `#状态--深度整合完成` | 同文件锚点不存在: #状态--深度整合完成 |
| docs\02_reference\quick_reference\network_programming_cheatsheet.md | 网络编程快速参考卡片 | `#网络编程快速参考卡片` | 同文件锚点不存在: #网络编程快速参考卡片 |
| docs\02_reference\quick_reference\network_programming_cheatsheet.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\02_reference\quick_reference\network_programming_cheatsheet.md | **状态**: ✅ 深度整合完成 | `#状态--深度整合完成` | 同文件锚点不存在: #状态--深度整合完成 |
| docs\02_reference\quick_reference\ownership_cheatsheet.md | 🦀 所有权系统速查卡 | `#-所有权系统速查卡` | 同文件锚点不存在: #-所有权系统速查卡 |
| docs\02_reference\quick_reference\ownership_cheatsheet.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\02_reference\quick_reference\ownership_cheatsheet.md | 🏗️ 智能指针速查 | `#️-智能指针速查` | 同文件锚点不存在: #️-智能指针速查 |
| docs\02_reference\quick_reference\ownership_cheatsheet.md | `Box<T>` - 堆分配 | `#boxt---堆分配` | 同文件锚点不存在: #boxt---堆分配 |
| docs\02_reference\quick_reference\ownership_cheatsheet.md | `Rc<T>` - 引用计数（单线程） | `#rct---引用计数单线程` | 同文件锚点不存在: #rct---引用计数单线程 |
| docs\02_reference\quick_reference\ownership_cheatsheet.md | `Arc<T>` - 原子引用计数（多线程） | `#arct---原子引用计数多线程` | 同文件锚点不存在: #arct---原子引用计数多线程 |
| docs\02_reference\quick_reference\ownership_cheatsheet.md | `RefCell<T>` - 内部可变性（单线程） | `#refcellt---内部可变性单线程` | 同文件锚点不存在: #refcellt---内部可变性单线程 |
| docs\02_reference\quick_reference\ownership_cheatsheet.md | `Mutex<T>` - 互斥锁（多线程） | `#mutext---互斥锁多线程` | 同文件锚点不存在: #mutext---互斥锁多线程 |
| docs\02_reference\quick_reference\ownership_cheatsheet.md | ⚠️ 低效模式 | `#️-低效模式` | 同文件锚点不存在: #️-低效模式 |
| docs\02_reference\quick_reference\ownership_cheatsheet.md | ⚠️ 边界情况 | `#️-边界情况` | 同文件锚点不存在: #️-边界情况 |
| docs\02_reference\quick_reference\ownership_cheatsheet.md | **状态**: ✅ 深度整合完成 | `#状态--深度整合完成` | 同文件锚点不存在: #状态--深度整合完成 |
| docs\02_reference\quick_reference\ownership_cheatsheet.md | 🦀 所有权系统速查卡 | `#-所有权系统速查卡` | 同文件锚点不存在: #-所有权系统速查卡 |
| docs\02_reference\quick_reference\ownership_cheatsheet.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\02_reference\quick_reference\ownership_cheatsheet.md | 🏗️ 智能指针速查 | `#️-智能指针速查` | 同文件锚点不存在: #️-智能指针速查 |
| docs\02_reference\quick_reference\ownership_cheatsheet.md | `Box<T>` - 堆分配 | `#boxt---堆分配` | 同文件锚点不存在: #boxt---堆分配 |
| docs\02_reference\quick_reference\ownership_cheatsheet.md | `Rc<T>` - 引用计数（单线程） | `#rct---引用计数单线程` | 同文件锚点不存在: #rct---引用计数单线程 |
| docs\02_reference\quick_reference\ownership_cheatsheet.md | `Arc<T>` - 原子引用计数（多线程） | `#arct---原子引用计数多线程` | 同文件锚点不存在: #arct---原子引用计数多线程 |
| docs\02_reference\quick_reference\ownership_cheatsheet.md | `RefCell<T>` - 内部可变性（单线程） | `#refcellt---内部可变性单线程` | 同文件锚点不存在: #refcellt---内部可变性单线程 |
| docs\02_reference\quick_reference\ownership_cheatsheet.md | `Mutex<T>` - 互斥锁（多线程） | `#mutext---互斥锁多线程` | 同文件锚点不存在: #mutext---互斥锁多线程 |
| docs\02_reference\quick_reference\ownership_cheatsheet.md | ⚠️ 低效模式 | `#️-低效模式` | 同文件锚点不存在: #️-低效模式 |
| docs\02_reference\quick_reference\ownership_cheatsheet.md | ⚠️ 边界情况 | `#️-边界情况` | 同文件锚点不存在: #️-边界情况 |
| docs\02_reference\quick_reference\ownership_cheatsheet.md | **状态**: ✅ 深度整合完成 | `#状态--深度整合完成` | 同文件锚点不存在: #状态--深度整合完成 |
| docs\02_reference\quick_reference\ownership_cheatsheet.md | 生命周期速查卡 | `./type_system.md#生命周期` | 锚点不存在: #生命周期 |
| docs\02_reference\quick_reference\ownership_cheatsheet.md | 借用检查器速查卡 | `./ownership_cheatsheet.md#借用规则` | 锚点不存在: #借用规则 |
| docs\02_reference\quick_reference\02_pin_cheatsheet.md | **最后更新**: 2026-05-08 | `#最后更新-2026-05-08` | 同文件锚点不存在: #最后更新-2026-05-08 |
| docs\02_reference\quick_reference\process_management_cheatsheet.md | 进程管理快速参考卡片 | `#进程管理快速参考卡片` | 同文件锚点不存在: #进程管理快速参考卡片 |
| docs\02_reference\quick_reference\process_management_cheatsheet.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\02_reference\quick_reference\process_management_cheatsheet.md | **状态**: ✅ 深度整合完成 | `#状态--深度整合完成` | 同文件锚点不存在: #状态--深度整合完成 |
| docs\02_reference\quick_reference\process_management_cheatsheet.md | 进程管理快速参考卡片 | `#进程管理快速参考卡片` | 同文件锚点不存在: #进程管理快速参考卡片 |
| docs\02_reference\quick_reference\process_management_cheatsheet.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\02_reference\quick_reference\process_management_cheatsheet.md | **状态**: ✅ 深度整合完成 | `#状态--深度整合完成` | 同文件锚点不存在: #状态--深度整合完成 |
| docs\02_reference\quick_reference\README.md | Rust 快速参考指南 {#-rust-快速参考指南} | `#rust-快速参考指南--rust-快速参考指南` | 同文件锚点不存在: #rust-快速参考指南--rust-快速参考指南 |
| docs\02_reference\quick_reference\README.md | 15. 进程管理速查卡 ⭐ NEW | `#15-进程管理速查卡--new` | 同文件锚点不存在: #15-进程管理速查卡--new |
| docs\02_reference\quick_reference\README.md | 16. 网络编程速查卡 ⭐ NEW | `#16-网络编程速查卡--new` | 同文件锚点不存在: #16-网络编程速查卡--new |
| docs\02_reference\quick_reference\README.md | 17. 算法与数据结构速查卡 ⭐ NEW | `#17-算法与数据结构速查卡--new` | 同文件锚点不存在: #17-算法与数据结构速查卡--new |
| docs\02_reference\quick_reference\README.md | 18. 设计模式速查卡 ⭐ NEW | `#18-设计模式速查卡--new` | 同文件锚点不存在: #18-设计模式速查卡--new |
| docs\02_reference\quick_reference\README.md | 19. WASM 速查卡 ⭐ NEW | `#19-wasm-速查卡--new` | 同文件锚点不存在: #19-wasm-速查卡--new |
| docs\02_reference\quick_reference\README.md | 20. AI/ML 速查卡 ⭐ NEW | `#20-aiml-速查卡--new` | 同文件锚点不存在: #20-aiml-速查卡--new |
| docs\02_reference\quick_reference\README.md | **状态**: ✅ 深度整合完成 | `#状态--深度整合完成` | 同文件锚点不存在: #状态--深度整合完成 |
| docs\02_reference\quick_reference\rust_195_features_cheatsheet.md | 原子操作 — `update` / `try_update` | `#原子操作--update--try_update` | 同文件锚点不存在: #原子操作--update--try_update |
| docs\02_reference\quick_reference\rust_195_features_cheatsheet.md | 集合 — 获取可变引用的插入操作 | `#集合--获取可变引用的插入操作` | 同文件锚点不存在: #集合--获取可变引用的插入操作 |
| docs\02_reference\quick_reference\rust_195_features_cheatsheet.md | 裸指针 — 不安全转引用 | `#裸指针--不安全转引用` | 同文件锚点不存在: #裸指针--不安全转引用 |
| docs\02_reference\quick_reference\rust_195_features_cheatsheet.md | 布局计算 — `Layout` 新 API | `#布局计算--layout-新-api` | 同文件锚点不存在: #布局计算--layout-新-api |
| docs\02_reference\quick_reference\rust_195_features_cheatsheet.md | 提示 — `cold_path` | `#提示--cold_path` | 同文件锚点不存在: #提示--cold_path |
| docs\02_reference\quick_reference\rust_195_features_cheatsheet.md | 布尔转换 — `TryFrom<{integer}>` | `#布尔转换--tryfrominteger` | 同文件锚点不存在: #布尔转换--tryfrominteger |
| docs\02_reference\quick_reference\rust_195_features_cheatsheet.md | `--remap-path-scope` 稳定化 | `#--remap-path-scope-稳定化` | 同文件锚点不存在: #--remap-path-scope-稳定化 |
| docs\02_reference\quick_reference\smart_pointers_cheatsheet.md | 🎯 Rust 智能指针速查卡 | `#-rust-智能指针速查卡` | 同文件锚点不存在: #-rust-智能指针速查卡 |
| docs\02_reference\quick_reference\smart_pointers_cheatsheet.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\02_reference\quick_reference\smart_pointers_cheatsheet.md | 📦 `Box<T>` - 堆分配 | `#-boxt---堆分配` | 同文件锚点不存在: #-boxt---堆分配 |
| docs\02_reference\quick_reference\smart_pointers_cheatsheet.md | 🔗 `Rc<T>` - 引用计数（单线程） | `#-rct---引用计数单线程` | 同文件锚点不存在: #-rct---引用计数单线程 |
| docs\02_reference\quick_reference\smart_pointers_cheatsheet.md | 🔗 `Arc<T>` - 原子引用计数（多线程） | `#-arct---原子引用计数多线程` | 同文件锚点不存在: #-arct---原子引用计数多线程 |
| docs\02_reference\quick_reference\smart_pointers_cheatsheet.md | 🔓 `RefCell<T>` - 内部可变性（单线程） | `#-refcellt---内部可变性单线程` | 同文件锚点不存在: #-refcellt---内部可变性单线程 |
| docs\02_reference\quick_reference\smart_pointers_cheatsheet.md | 🔒 `Mutex<T>` - 互斥锁（多线程） | `#-mutext---互斥锁多线程` | 同文件锚点不存在: #-mutext---互斥锁多线程 |
| docs\02_reference\quick_reference\smart_pointers_cheatsheet.md | 🔓 `RwLock<T>` - 读写锁（多线程） | `#-rwlockt---读写锁多线程` | 同文件锚点不存在: #-rwlockt---读写锁多线程 |
| docs\02_reference\quick_reference\smart_pointers_cheatsheet.md | 🔗 `Weak<T>` - 弱引用 | `#-weakt---弱引用` | 同文件锚点不存在: #-weakt---弱引用 |
| docs\02_reference\quick_reference\smart_pointers_cheatsheet.md | `Rc<RefCell<T>>` - 单线程内部可变性 | `#rcrefcellt---单线程内部可变性` | 同文件锚点不存在: #rcrefcellt---单线程内部可变性 |
| docs\02_reference\quick_reference\smart_pointers_cheatsheet.md | `Arc<Mutex<T>>` - 多线程共享可变数据 | `#arcmutext---多线程共享可变数据` | 同文件锚点不存在: #arcmutext---多线程共享可变数据 |
| docs\02_reference\quick_reference\smart_pointers_cheatsheet.md | `Arc<RwLock<T>>` - 多线程读写锁 | `#arcrwlockt---多线程读写锁` | 同文件锚点不存在: #arcrwlockt---多线程读写锁 |
| docs\02_reference\quick_reference\smart_pointers_cheatsheet.md | `Rc<RefCell<Vec<T>>>` - 共享可变向量 | `#rcrefcellvect---共享可变向量` | 同文件锚点不存在: #rcrefcellvect---共享可变向量 |
| docs\02_reference\quick_reference\smart_pointers_cheatsheet.md | 🎯 **掌握智能指针，灵活管理内存！** | `#-掌握智能指针灵活管理内存` | 同文件锚点不存在: #-掌握智能指针灵活管理内存 |
| docs\02_reference\quick_reference\smart_pointers_cheatsheet.md | 🎯 Rust 智能指针速查卡 | `#-rust-智能指针速查卡` | 同文件锚点不存在: #-rust-智能指针速查卡 |
| docs\02_reference\quick_reference\smart_pointers_cheatsheet.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\02_reference\quick_reference\smart_pointers_cheatsheet.md | 📦 `Box<T>` - 堆分配 | `#-boxt---堆分配` | 同文件锚点不存在: #-boxt---堆分配 |
| docs\02_reference\quick_reference\smart_pointers_cheatsheet.md | 🔗 `Rc<T>` - 引用计数（单线程） | `#-rct---引用计数单线程` | 同文件锚点不存在: #-rct---引用计数单线程 |
| docs\02_reference\quick_reference\smart_pointers_cheatsheet.md | 🔗 `Arc<T>` - 原子引用计数（多线程） | `#-arct---原子引用计数多线程` | 同文件锚点不存在: #-arct---原子引用计数多线程 |
| docs\02_reference\quick_reference\smart_pointers_cheatsheet.md | 🔓 `RefCell<T>` - 内部可变性（单线程） | `#-refcellt---内部可变性单线程` | 同文件锚点不存在: #-refcellt---内部可变性单线程 |
| docs\02_reference\quick_reference\smart_pointers_cheatsheet.md | 🔒 `Mutex<T>` - 互斥锁（多线程） | `#-mutext---互斥锁多线程` | 同文件锚点不存在: #-mutext---互斥锁多线程 |
| docs\02_reference\quick_reference\smart_pointers_cheatsheet.md | 🔓 `RwLock<T>` - 读写锁（多线程） | `#-rwlockt---读写锁多线程` | 同文件锚点不存在: #-rwlockt---读写锁多线程 |
| docs\02_reference\quick_reference\smart_pointers_cheatsheet.md | 🔗 `Weak<T>` - 弱引用 | `#-weakt---弱引用` | 同文件锚点不存在: #-weakt---弱引用 |
| docs\02_reference\quick_reference\smart_pointers_cheatsheet.md | `Rc<RefCell<T>>` - 单线程内部可变性 | `#rcrefcellt---单线程内部可变性` | 同文件锚点不存在: #rcrefcellt---单线程内部可变性 |
| docs\02_reference\quick_reference\smart_pointers_cheatsheet.md | `Arc<Mutex<T>>` - 多线程共享可变数据 | `#arcmutext---多线程共享可变数据` | 同文件锚点不存在: #arcmutext---多线程共享可变数据 |
| docs\02_reference\quick_reference\smart_pointers_cheatsheet.md | `Arc<RwLock<T>>` - 多线程读写锁 | `#arcrwlockt---多线程读写锁` | 同文件锚点不存在: #arcrwlockt---多线程读写锁 |
| docs\02_reference\quick_reference\smart_pointers_cheatsheet.md | `Rc<RefCell<Vec<T>>>` - 共享可变向量 | `#rcrefcellvect---共享可变向量` | 同文件锚点不存在: #rcrefcellvect---共享可变向量 |
| docs\02_reference\quick_reference\smart_pointers_cheatsheet.md | 🎯 **掌握智能指针，灵活管理内存！** | `#-掌握智能指针灵活管理内存` | 同文件锚点不存在: #-掌握智能指针灵活管理内存 |
| docs\02_reference\quick_reference\strings_formatting_cheatsheet.md | 📝 Rust 字符串与格式化速查卡 | `#-rust-字符串与格式化速查卡` | 同文件锚点不存在: #-rust-字符串与格式化速查卡 |
| docs\02_reference\quick_reference\strings_formatting_cheatsheet.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\02_reference\quick_reference\strings_formatting_cheatsheet.md | ✂️ 字符串操作 | `#️-字符串操作` | 同文件锚点不存在: #️-字符串操作 |
| docs\02_reference\quick_reference\strings_formatting_cheatsheet.md | String ↔ \&str | `#string--str` | 同文件锚点不存在: #string--str |
| docs\02_reference\quick_reference\strings_formatting_cheatsheet.md | 🖨️ 格式化输出 | `#️-格式化输出` | 同文件锚点不存在: #️-格式化输出 |
| docs\02_reference\quick_reference\strings_formatting_cheatsheet.md | 反例 4: format!  panic 导致的拒绝服务 | `#反例-4-format--panic-导致的拒绝服务` | 同文件锚点不存在: #反例-4-format--panic-导致的拒绝服务 |
| docs\02_reference\quick_reference\strings_formatting_cheatsheet.md | **状态**: ✅ 深度整合完成 | `#状态--深度整合完成` | 同文件锚点不存在: #状态--深度整合完成 |
| docs\02_reference\quick_reference\strings_formatting_cheatsheet.md | 📝 Rust 字符串与格式化速查卡 | `#-rust-字符串与格式化速查卡` | 同文件锚点不存在: #-rust-字符串与格式化速查卡 |
| docs\02_reference\quick_reference\strings_formatting_cheatsheet.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\02_reference\quick_reference\strings_formatting_cheatsheet.md | ✂️ 字符串操作 | `#️-字符串操作` | 同文件锚点不存在: #️-字符串操作 |
| docs\02_reference\quick_reference\strings_formatting_cheatsheet.md | String ↔ \&str | `#string--str` | 同文件锚点不存在: #string--str |
| docs\02_reference\quick_reference\strings_formatting_cheatsheet.md | 🖨️ 格式化输出 | `#️-格式化输出` | 同文件锚点不存在: #️-格式化输出 |
| docs\02_reference\quick_reference\strings_formatting_cheatsheet.md | 反例 4: format!  panic 导致的拒绝服务 | `#反例-4-format--panic-导致的拒绝服务` | 同文件锚点不存在: #反例-4-format--panic-导致的拒绝服务 |
| docs\02_reference\quick_reference\strings_formatting_cheatsheet.md | **状态**: ✅ 深度整合完成 | `#状态--深度整合完成` | 同文件锚点不存在: #状态--深度整合完成 |
| docs\02_reference\quick_reference\testing_cheatsheet.md | 🧪 Rust 测试速查卡 | `#-rust-测试速查卡` | 同文件锚点不存在: #-rust-测试速查卡 |
| docs\02_reference\quick_reference\testing_cheatsheet.md | 🛠️ 测试工具和库 | `#️-测试工具和库` | 同文件锚点不存在: #️-测试工具和库 |
| docs\02_reference\quick_reference\testing_cheatsheet.md | **状态**: ✅ 深度整合完成 | `#状态--深度整合完成` | 同文件锚点不存在: #状态--深度整合完成 |
| docs\02_reference\quick_reference\threads_concurrency_cheatsheet.md | 🔀 Rust 线程与并发速查卡 | `#-rust-线程与并发速查卡` | 同文件锚点不存在: #-rust-线程与并发速查卡 |
| docs\02_reference\quick_reference\threads_concurrency_cheatsheet.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\02_reference\quick_reference\threads_concurrency_cheatsheet.md | 反例 2: 死锁 - 重复获取同一 Mutex | `#反例-2-死锁---重复获取同一-mutex` | 同文件锚点不存在: #反例-2-死锁---重复获取同一-mutex |
| docs\02_reference\quick_reference\threads_concurrency_cheatsheet.md | 📚 相关资源 | `#-相关资源-1` | 同文件锚点不存在: #-相关资源-1 |
| docs\02_reference\quick_reference\threads_concurrency_cheatsheet.md | **状态**: ✅ 深度整合完成 | `#状态--深度整合完成` | 同文件锚点不存在: #状态--深度整合完成 |
| docs\02_reference\quick_reference\threads_concurrency_cheatsheet.md | 🔀 Rust 线程与并发速查卡 | `#-rust-线程与并发速查卡` | 同文件锚点不存在: #-rust-线程与并发速查卡 |
| docs\02_reference\quick_reference\threads_concurrency_cheatsheet.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\02_reference\quick_reference\threads_concurrency_cheatsheet.md | 反例 2: 死锁 - 重复获取同一 Mutex | `#反例-2-死锁---重复获取同一-mutex` | 同文件锚点不存在: #反例-2-死锁---重复获取同一-mutex |
| docs\02_reference\quick_reference\threads_concurrency_cheatsheet.md | 📚 相关资源 | `#-相关资源-1` | 同文件锚点不存在: #-相关资源-1 |
| docs\02_reference\quick_reference\threads_concurrency_cheatsheet.md | **状态**: ✅ 深度整合完成 | `#状态--深度整合完成` | 同文件锚点不存在: #状态--深度整合完成 |
| docs\02_reference\quick_reference\type_system.md | 🔷 Rust 类型系统速查卡 | `#-rust-类型系统速查卡` | 同文件锚点不存在: #-rust-类型系统速查卡 |
| docs\02_reference\quick_reference\type_system.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\02_reference\quick_reference\type_system.md | 🏗️ Trait 系统 | `#️-trait-系统` | 同文件锚点不存在: #️-trait-系统 |
| docs\02_reference\quick_reference\type_system.md | 协变（Covariant）- \&T | `#协变covariant--t` | 同文件锚点不存在: #协变covariant--t |
| docs\02_reference\quick_reference\type_system.md | 逆变（Contravariant）- fn(T) | `#逆变contravariant--fnt` | 同文件锚点不存在: #逆变contravariant--fnt |
| docs\02_reference\quick_reference\type_system.md | 不变（Invariant）- \&mut T | `#不变invariant--mut-t` | 同文件锚点不存在: #不变invariant--mut-t |
| docs\02_reference\quick_reference\type_system.md | Debug \& Display | `#debug--display` | 同文件锚点不存在: #debug--display |
| docs\02_reference\quick_reference\type_system.md | Clone \& Copy | `#clone--copy` | 同文件锚点不存在: #clone--copy |
| docs\02_reference\quick_reference\type_system.md | PartialEq \& Eq | `#partialeq--eq` | 同文件锚点不存在: #partialeq--eq |
| docs\02_reference\quick_reference\type_system.md | PartialOrd \& Ord | `#partialord--ord` | 同文件锚点不存在: #partialord--ord |
| docs\02_reference\quick_reference\type_system.md | ⚠️ 边界情况 | `#️-边界情况` | 同文件锚点不存在: #️-边界情况 |
| docs\02_reference\quick_reference\type_system.md | **状态**: ✅ 深度整合完成 | `#状态--深度整合完成` | 同文件锚点不存在: #状态--深度整合完成 |
| docs\02_reference\quick_reference\type_system.md | 🔷 Rust 类型系统速查卡 | `#-rust-类型系统速查卡` | 同文件锚点不存在: #-rust-类型系统速查卡 |
| docs\02_reference\quick_reference\type_system.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\02_reference\quick_reference\type_system.md | 🏗️ Trait 系统 | `#️-trait-系统` | 同文件锚点不存在: #️-trait-系统 |
| docs\02_reference\quick_reference\type_system.md | 协变（Covariant）- \&T | `#协变covariant--t` | 同文件锚点不存在: #协变covariant--t |
| docs\02_reference\quick_reference\type_system.md | 逆变（Contravariant）- fn(T) | `#逆变contravariant--fnt` | 同文件锚点不存在: #逆变contravariant--fnt |
| docs\02_reference\quick_reference\type_system.md | 不变（Invariant）- \&mut T | `#不变invariant--mut-t` | 同文件锚点不存在: #不变invariant--mut-t |
| docs\02_reference\quick_reference\type_system.md | Debug \& Display | `#debug--display` | 同文件锚点不存在: #debug--display |
| docs\02_reference\quick_reference\type_system.md | Clone \& Copy | `#clone--copy` | 同文件锚点不存在: #clone--copy |
| docs\02_reference\quick_reference\type_system.md | PartialEq \& Eq | `#partialeq--eq` | 同文件锚点不存在: #partialeq--eq |
| docs\02_reference\quick_reference\type_system.md | PartialOrd \& Ord | `#partialord--ord` | 同文件锚点不存在: #partialord--ord |
| docs\02_reference\quick_reference\type_system.md | ⚠️ 边界情况 | `#️-边界情况` | 同文件锚点不存在: #️-边界情况 |
| docs\02_reference\quick_reference\type_system.md | **状态**: ✅ 深度整合完成 | `#状态--深度整合完成` | 同文件锚点不存在: #状态--深度整合完成 |
| docs\02_reference\quick_reference\wasm_cheatsheet.md | WASM 快速参考卡片 | `#wasm-快速参考卡片` | 同文件锚点不存在: #wasm-快速参考卡片 |
| docs\02_reference\quick_reference\wasm_cheatsheet.md | **状态**: ✅ 深度整合完成 | `#状态--深度整合完成` | 同文件锚点不存在: #状态--深度整合完成 |
| docs\02_reference\quick_reference\wasm_cheatsheet.md | WASM 快速参考卡片 | `#wasm-快速参考卡片` | 同文件锚点不存在: #wasm-快速参考卡片 |
| docs\02_reference\quick_reference\wasm_cheatsheet.md | **状态**: ✅ 深度整合完成 | `#状态--深度整合完成` | 同文件锚点不存在: #状态--深度整合完成 |
| docs\03_guides\03_async_closures_deep_dive.md | 2.3 关键区别：AsyncFn vs Fn + Future | `#23-关键区别asyncfn-vs-fn--future` | 同文件锚点不存在: #23-关键区别asyncfn-vs-fn--future |
| docs\03_guides\CXX_INTEROP_GUIDE.md | C++ 互操作指南（cxx + bindgen） | `#c-互操作指南cxx--bindgen` | 同文件锚点不存在: #c-互操作指南cxx--bindgen |
| docs\03_guides\03_fuzzing_guide.md | c08\_algorithms —— 解析器模糊测试 | `#c08_algorithms--解析器模糊测试` | 同文件锚点不存在: #c08_algorithms--解析器模糊测试 |
| docs\03_guides\03_let_chains_guide.md | 2.3 不能用 `\|\|` 混合 let | `#23-不能用--混合-let` | 同文件锚点不存在: #23-不能用--混合-let |
| docs\03_guides\03_let_chains_guide.md | 3.1 嵌套 if let → 扁平 let chains | `#31-嵌套-if-let--扁平-let-chains` | 同文件锚点不存在: #31-嵌套-if-let--扁平-let-chains |
| docs\03_guides\03_libp2p_guide.md | Multiaddr —— 统一的地址格式 | `#multiaddr--统一的地址格式` | 同文件锚点不存在: #multiaddr--统一的地址格式 |
| docs\03_guides\03_libp2p_guide.md | PeerId —— 去中心化身份 | `#peerid--去中心化身份` | 同文件锚点不存在: #peerid--去中心化身份 |
| docs\03_guides\03_quic_http3_guide.md | QUIC / HTTP/3 指南 | `#quic--http3-指南` | 同文件锚点不存在: #quic--http3-指南 |
| docs\03_guides\03_quic_http3_guide.md | HTTP/3 客户端（h3 + quinn） | `#http3-客户端h3--quinn` | 同文件锚点不存在: #http3-客户端h3--quinn |
| docs\03_guides\RUST_FOR_LINUX_GUIDE.md | 与 eBPF + Rust 的关系 | `#与-ebpf--rust-的关系` | 同文件锚点不存在: #与-ebpf--rust-的关系 |
| docs\03_practice\CROSS_MODULE_PRACTICAL_PROJECTS_2025_10_25.md | **状态**: ✅ 可用 | `#状态--可用` | 同文件锚点不存在: #状态--可用 |
| docs\03_practice\03_project_03_calculator.md | 完整参考实现位于: `examples/calculator/` | `#完整参考实现位于-examplescalculator` | 同文件锚点不存在: #完整参考实现位于-examplescalculator |
| docs\03_practice\03_project_04_password_generator.md | 完整参考实现位于: `examples/password-generator/` | `#完整参考实现位于-examplespassword-generator` | 同文件锚点不存在: #完整参考实现位于-examplespassword-generator |
| docs\03_practice\03_project_05_text_statistics.md | 完整参考实现位于: `examples/text-statistics/` | `#完整参考实现位于-examplestext-statistics` | 同文件锚点不存在: #完整参考实现位于-examplestext-statistics |
| docs\03_practice\03_project_06_concurrent_downloader.md | 完整参考实现位于: `examples/concurrent-downloader/` | `#完整参考实现位于-examplesconcurrent-downloader` | 同文件锚点不存在: #完整参考实现位于-examplesconcurrent-downloader |
| docs\03_practice\03_project_07_chat_server.md | 完整参考实现位于: `examples/chat-server/` | `#完整参考实现位于-exampleschat-server` | 同文件锚点不存在: #完整参考实现位于-exampleschat-server |
| docs\03_practice\03_project_08_cache_system.md | 完整参考实现位于: `examples/cache-system/` | `#完整参考实现位于-examplescache-system` | 同文件锚点不存在: #完整参考实现位于-examplescache-system |
| docs\03_practice\03_project_09_log_parser.md | 完整参考实现位于: `examples/log-parser/` | `#完整参考实现位于-exampleslog-parser` | 同文件锚点不存在: #完整参考实现位于-exampleslog-parser |
| docs\03_practice\03_project_10_data_pipeline.md | 完整参考实现位于: `examples/data-pipeline/` | `#完整参考实现位于-examplesdata-pipeline` | 同文件锚点不存在: #完整参考实现位于-examplesdata-pipeline |
| docs\03_practice\03_project_11_web_server.md | 完整参考实现位于: `examples/web-server/` | `#完整参考实现位于-examplesweb-server` | 同文件锚点不存在: #完整参考实现位于-examplesweb-server |
| docs\03_practice\03_project_12_wasm_app.md | 完整参考实现位于: `examples/wasm-app/` | `#完整参考实现位于-exampleswasm-app` | 同文件锚点不存在: #完整参考实现位于-exampleswasm-app |
| docs\03_practice\03_project_13_database_engine.md | 完整参考实现位于: `examples/database-engine/` | `#完整参考实现位于-examplesdatabase-engine` | 同文件锚点不存在: #完整参考实现位于-examplesdatabase-engine |
| docs\03_practice\03_project_14_async_runtime.md | 完整参考实现位于: `examples/async-runtime/` | `#完整参考实现位于-examplesasync-runtime` | 同文件锚点不存在: #完整参考实现位于-examplesasync-runtime |
| docs\03_practice\03_project_15_distributed_system.md | 完整参考实现位于: `examples/distributed-kv/` | `#完整参考实现位于-examplesdistributed-kv` | 同文件锚点不存在: #完整参考实现位于-examplesdistributed-kv |
| docs\04_research\04_ng_trait_solver.md | C. 改进的 Coherence / Specialization 支持 | `#c-改进的-coherence--specialization-支持` | 同文件锚点不存在: #c-改进的-coherence--specialization-支持 |
| docs\04_research\RUST_FOR_LINUX.md | 六、与 Ferrocene / 安全关键系统的关联 | `#六与-ferrocene--安全关键系统的关联` | 同文件锚点不存在: #六与-ferrocene--安全关键系统的关联 |
| docs\04_research\VERUSBELT_PLDI_2026.md | ⚖️ 与相关工作的对比 | `#️-与相关工作的对比` | 同文件锚点不存在: #️-与相关工作的对比 |
| docs\04_thinking\APPLICATIONS_ANALYSIS_VIEW.md | **最后更新**: 2026-05-08 (Rust 1.95+ 持续更新) | `#最后更新-2026-05-08-rust-195-持续更新` | 同文件锚点不存在: #最后更新-2026-05-08-rust-195-持续更新 |
| docs\04_thinking\DECISION_GRAPH_NETWORK.md | Rust 决策图网 / Decision Graph Network | `#rust-决策图网--decision-graph-network` | 同文件锚点不存在: #rust-决策图网--decision-graph-network |
| docs\04_thinking\DECISION_GRAPH_NETWORK.md | **最后更新**: 2026-05-08 (Rust 1.95+ 持续更新) | `#最后更新-2026-05-08-rust-195-持续更新` | 同文件锚点不存在: #最后更新-2026-05-08-rust-195-持续更新 |
| docs\04_thinking\DECISION_GRAPH_NETWORK.md | Rust 决策图网 / Decision Graph Network | `#rust-决策图网--decision-graph-network` | 同文件锚点不存在: #rust-决策图网--decision-graph-network |
| docs\04_thinking\DECISION_GRAPH_NETWORK.md | **最后更新**: 2026-05-08 (Rust 1.95+ 持续更新) | `#最后更新-2026-05-08-rust-195-持续更新` | 同文件锚点不存在: #最后更新-2026-05-08-rust-195-持续更新 |
| docs\04_thinking\MIND_MAP_COLLECTION.md | 🗺️ 核心概念思维导图 {#️-核心概念思维导图} | `#️-核心概念思维导图-️-核心概念思维导图` | 同文件锚点不存在: #️-核心概念思维导图-️-核心概念思维导图 |
| docs\04_thinking\MIND_MAP_COLLECTION.md | **最后更新**: 2026-05-08 (Rust 1.95+ 持续更新) | `#最后更新-2026-05-08-rust-195-持续更新` | 同文件锚点不存在: #最后更新-2026-05-08-rust-195-持续更新 |
| docs\04_thinking\MIND_MAP_COLLECTION.md | 🗺️ 核心概念思维导图 {#️-核心概念思维导图} | `#️-核心概念思维导图-️-核心概念思维导图` | 同文件锚点不存在: #️-核心概念思维导图-️-核心概念思维导图 |
| docs\04_thinking\MIND_MAP_COLLECTION.md | **最后更新**: 2026-05-08 (Rust 1.95+ 持续更新) | `#最后更新-2026-05-08-rust-195-持续更新` | 同文件锚点不存在: #最后更新-2026-05-08-rust-195-持续更新 |
| docs\04_thinking\MULTI_DIMENSIONAL_CONCEPT_MATRIX.md | ⚠️ Rust 1.93 行为变更影响（性能矩阵补充） {#️-rust-193-行为变更影响性能矩阵补充} | `#️-rust-193-行为变更影响性能矩阵补充-️-rust-193-行为变更影响性能矩阵补充` | 同文件锚点不存在: #️-rust-193-行为变更影响性能矩阵补充-️-rust-193-行为变更影响性能矩阵补充 |
| docs\04_thinking\MULTI_DIMENSIONAL_CONCEPT_MATRIX.md | 🛡️ 安全性对比矩阵 {#️-安全性对比矩阵} | `#️-安全性对比矩阵-️-安全性对比矩阵` | 同文件锚点不存在: #️-安全性对比矩阵-️-安全性对比矩阵 |
| docs\04_thinking\MULTI_DIMENSIONAL_CONCEPT_MATRIX.md | **最后更新**: 2026-05-08 (Rust 1.95+ 持续更新) | `#最后更新-2026-05-08-rust-195-持续更新` | 同文件锚点不存在: #最后更新-2026-05-08-rust-195-持续更新 |
| docs\04_thinking\MULTI_DIMENSIONAL_CONCEPT_MATRIX.md | ⚠️ Rust 1.93 行为变更影响（性能矩阵补充） {#️-rust-193-行为变更影响性能矩阵补充} | `#️-rust-193-行为变更影响性能矩阵补充-️-rust-193-行为变更影响性能矩阵补充` | 同文件锚点不存在: #️-rust-193-行为变更影响性能矩阵补充-️-rust-193-行为变更影响性能矩阵补充 |
| docs\04_thinking\MULTI_DIMENSIONAL_CONCEPT_MATRIX.md | 🛡️ 安全性对比矩阵 {#️-安全性对比矩阵} | `#️-安全性对比矩阵-️-安全性对比矩阵` | 同文件锚点不存在: #️-安全性对比矩阵-️-安全性对比矩阵 |
| docs\04_thinking\MULTI_DIMENSIONAL_CONCEPT_MATRIX.md | **最后更新**: 2026-05-08 (Rust 1.95+ 持续更新) | `#最后更新-2026-05-08-rust-195-持续更新` | 同文件锚点不存在: #最后更新-2026-05-08-rust-195-持续更新 |
| docs\04_thinking\PROOF_GRAPH_NETWORK.md | Rust 证明图网 / Proof Graph Network | `#rust-证明图网--proof-graph-network` | 同文件锚点不存在: #rust-证明图网--proof-graph-network |
| docs\04_thinking\PROOF_GRAPH_NETWORK.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\04_thinking\PROOF_GRAPH_NETWORK.md | 🛡️ 内存安全证明树 | `#️-内存安全证明树` | 同文件锚点不存在: #️-内存安全证明树 |
| docs\04_thinking\PROOF_GRAPH_NETWORK.md | 组合1: MaybeUninit + 调用追踪 | `#组合1-maybeuninit--调用追踪` | 同文件锚点不存在: #组合1-maybeuninit--调用追踪 |
| docs\04_thinking\PROOF_GRAPH_NETWORK.md | 组合2: 关联类型多边界 + 自动特征 | `#组合2-关联类型多边界--自动特征` | 同文件锚点不存在: #组合2-关联类型多边界--自动特征 |
| docs\04_thinking\PROOF_GRAPH_NETWORK.md | **最后更新**: 2026-05-08 (Rust 1.95+ 持续更新) | `#最后更新-2026-05-08-rust-195-持续更新` | 同文件锚点不存在: #最后更新-2026-05-08-rust-195-持续更新 |
| docs\04_thinking\PROOF_GRAPH_NETWORK.md | Rust 证明图网 / Proof Graph Network | `#rust-证明图网--proof-graph-network` | 同文件锚点不存在: #rust-证明图网--proof-graph-network |
| docs\04_thinking\PROOF_GRAPH_NETWORK.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\04_thinking\PROOF_GRAPH_NETWORK.md | 🛡️ 内存安全证明树 | `#️-内存安全证明树` | 同文件锚点不存在: #️-内存安全证明树 |
| docs\04_thinking\PROOF_GRAPH_NETWORK.md | 组合1: MaybeUninit + 调用追踪 | `#组合1-maybeuninit--调用追踪` | 同文件锚点不存在: #组合1-maybeuninit--调用追踪 |
| docs\04_thinking\PROOF_GRAPH_NETWORK.md | 组合2: 关联类型多边界 + 自动特征 | `#组合2-关联类型多边界--自动特征` | 同文件锚点不存在: #组合2-关联类型多边界--自动特征 |
| docs\04_thinking\PROOF_GRAPH_NETWORK.md | **最后更新**: 2026-05-08 (Rust 1.95+ 持续更新) | `#最后更新-2026-05-08-rust-195-持续更新` | 同文件锚点不存在: #最后更新-2026-05-08-rust-195-持续更新 |
| docs\04_thinking\THINKING_REPRESENTATION_METHODS.md | Rust 思维表征方式文档 / Thinking Representation Methods Documentation | `#rust-思维表征方式文档--thinking-representation-methods-documentation` | 同文件锚点不存在: #rust-思维表征方式文档--thinking-representation-methods-documentation |
| docs\04_thinking\THINKING_REPRESENTATION_METHODS.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\04_thinking\THINKING_REPRESENTATION_METHODS.md | 🗺️ 1. 思维导图 (Mind Map) | `#️-1-思维导图-mind-map` | 同文件锚点不存在: #️-1-思维导图-mind-map |
| docs\04_thinking\THINKING_REPRESENTATION_METHODS.md | 3.9.1 借用 ↔ 所有权转换树 | `#391-借用--所有权转换树` | 同文件锚点不存在: #391-借用--所有权转换树 |
| docs\04_thinking\THINKING_REPRESENTATION_METHODS.md | 3.9.2 Option ↔ Result 转换树 | `#392-option--result-转换树` | 同文件锚点不存在: #392-option--result-转换树 |
| docs\04_thinking\THINKING_REPRESENTATION_METHODS.md | **最后更新**: 2026-05-08 (Rust 1.95+ 持续更新) | `#最后更新-2026-05-08-rust-195-持续更新` | 同文件锚点不存在: #最后更新-2026-05-08-rust-195-持续更新 |
| docs\04_thinking\THINKING_REPRESENTATION_METHODS.md | Rust 思维表征方式文档 / Thinking Representation Methods Documentation | `#rust-思维表征方式文档--thinking-representation-methods-documentation` | 同文件锚点不存在: #rust-思维表征方式文档--thinking-representation-methods-documentation |
| docs\04_thinking\THINKING_REPRESENTATION_METHODS.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\04_thinking\THINKING_REPRESENTATION_METHODS.md | 🗺️ 1. 思维导图 (Mind Map) | `#️-1-思维导图-mind-map` | 同文件锚点不存在: #️-1-思维导图-mind-map |
| docs\04_thinking\THINKING_REPRESENTATION_METHODS.md | 3.9.1 借用 ↔ 所有权转换树 | `#391-借用--所有权转换树` | 同文件锚点不存在: #391-借用--所有权转换树 |
| docs\04_thinking\THINKING_REPRESENTATION_METHODS.md | 3.9.2 Option ↔ Result 转换树 | `#392-option--result-转换树` | 同文件锚点不存在: #392-option--result-转换树 |
| docs\04_thinking\THINKING_REPRESENTATION_METHODS.md | **最后更新**: 2026-05-08 (Rust 1.95+ 持续更新) | `#最后更新-2026-05-08-rust-195-持续更新` | 同文件锚点不存在: #最后更新-2026-05-08-rust-195-持续更新 |
| docs\05_guides\ADVANCED_TOPICS_DEEP_DIVE.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\05_guides\ADVANCED_TOPICS_DEEP_DIVE.md | **状态**: ✅ 深度整合完成 | `#状态--深度整合完成` | 同文件锚点不存在: #状态--深度整合完成 |
| docs\05_guides\ADVANCED_TOPICS_DEEP_DIVE.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\05_guides\ADVANCED_TOPICS_DEEP_DIVE.md | **状态**: ✅ 深度整合完成 | `#状态--深度整合完成` | 同文件锚点不存在: #状态--深度整合完成 |
| docs\05_guides\AI_RUST_ECOSYSTEM_GUIDE.md | AI + Rust 生态指南 | `#ai--rust-生态指南` | 同文件锚点不存在: #ai--rust-生态指南 |
| docs\05_guides\AI_RUST_ECOSYSTEM_GUIDE.md | 路径 C：AI + Rust 双轨 | `#路径-cai--rust-双轨` | 同文件锚点不存在: #路径-cai--rust-双轨 |
| docs\05_guides\AI_RUST_ECOSYSTEM_GUIDE.md | **状态**: ✅ 深度整合完成 | `#状态--深度整合完成` | 同文件锚点不存在: #状态--深度整合完成 |
| docs\05_guides\ALGORITHMS_USAGE_GUIDE.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\05_guides\ALGORITHMS_USAGE_GUIDE.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\05_guides\ASYNC_PROGRAMMING_USAGE_GUIDE.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\05_guides\ASYNC_PROGRAMMING_USAGE_GUIDE.md | ControlFlow 与 Try  trait 集成 | `#controlflow-与-try--trait-集成` | 同文件锚点不存在: #controlflow-与-try--trait-集成 |
| docs\05_guides\ASYNC_PROGRAMMING_USAGE_GUIDE.md | 🏗️ 异步编程模式（5+ 完整示例） | `#️-异步编程模式5-完整示例` | 同文件锚点不存在: #️-异步编程模式5-完整示例 |
| docs\05_guides\ASYNC_PROGRAMMING_USAGE_GUIDE.md | **最后更新**: 2026-05-08 | `#最后更新-2026-05-08` | 同文件锚点不存在: #最后更新-2026-05-08 |
| docs\05_guides\ASYNC_PROGRAMMING_USAGE_GUIDE.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\05_guides\ASYNC_PROGRAMMING_USAGE_GUIDE.md | ControlFlow 与 Try  trait 集成 | `#controlflow-与-try--trait-集成` | 同文件锚点不存在: #controlflow-与-try--trait-集成 |
| docs\05_guides\ASYNC_PROGRAMMING_USAGE_GUIDE.md | 🏗️ 异步编程模式（5+ 完整示例） | `#️-异步编程模式5-完整示例` | 同文件锚点不存在: #️-异步编程模式5-完整示例 |
| docs\05_guides\ASYNC_PROGRAMMING_USAGE_GUIDE.md | **最后更新**: 2026-05-08 | `#最后更新-2026-05-08` | 同文件锚点不存在: #最后更新-2026-05-08 |
| docs\05_guides\BEST_PRACTICES.md | Rust 项目最佳实践指南 | `#rust-项目最佳实践指南` | 同文件锚点不存在: #rust-项目最佳实践指南 |
| docs\05_guides\BEST_PRACTICES.md | 📑 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\05_guides\BEST_PRACTICES.md | 1. array\_windows - 零开销滑动窗口 | `#1-array_windows---零开销滑动窗口` | 同文件锚点不存在: #1-array_windows---零开销滑动窗口 |
| docs\05_guides\BEST_PRACTICES.md | 2. ControlFlow - 清晰的提前终止语义 | `#2-controlflow---清晰的提前终止语义` | 同文件锚点不存在: #2-controlflow---清晰的提前终止语义 |
| docs\05_guides\BEST_PRACTICES.md | 3. LazyLock/LazyCell - 延迟初始化优化 | `#3-lazylocklazycell---延迟初始化优化` | 同文件锚点不存在: #3-lazylocklazycell---延迟初始化优化 |
| docs\05_guides\BEST_PRACTICES.md | 4. 数学常量 - 精确计算 | `#4-数学常量---精确计算` | 同文件锚点不存在: #4-数学常量---精确计算 |
| docs\05_guides\BEST_PRACTICES.md | 1. isqrt - 整数平方根运算 | `#1-isqrt---整数平方根运算` | 同文件锚点不存在: #1-isqrt---整数平方根运算 |
| docs\05_guides\BEST_PRACTICES.md | 2. HashMap::get\_disjoint\_mut - 安全并行访问 | `#2-hashmapget_disjoint_mut---安全并行访问` | 同文件锚点不存在: #2-hashmapget_disjoint_mut---安全并行访问 |
| docs\05_guides\BEST_PRACTICES.md | 3. async Fn Trait - 异步抽象改进 | `#3-async-fn-trait---异步抽象改进` | 同文件锚点不存在: #3-async-fn-trait---异步抽象改进 |
| docs\05_guides\BEST_PRACTICES.md | 4. Vec::pop\_if - 条件弹出 | `#4-vecpop_if---条件弹出` | 同文件锚点不存在: #4-vecpop_if---条件弹出 |
| docs\05_guides\BEST_PRACTICES.md | **状态**: ✅ 持续更新 | `#状态--持续更新` | 同文件锚点不存在: #状态--持续更新 |
| docs\05_guides\BEST_PRACTICES.md | Rust 项目最佳实践指南 | `#rust-项目最佳实践指南` | 同文件锚点不存在: #rust-项目最佳实践指南 |
| docs\05_guides\BEST_PRACTICES.md | 📑 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\05_guides\BEST_PRACTICES.md | 1. array\_windows - 零开销滑动窗口 | `#1-array_windows---零开销滑动窗口` | 同文件锚点不存在: #1-array_windows---零开销滑动窗口 |
| docs\05_guides\BEST_PRACTICES.md | 2. ControlFlow - 清晰的提前终止语义 | `#2-controlflow---清晰的提前终止语义` | 同文件锚点不存在: #2-controlflow---清晰的提前终止语义 |
| docs\05_guides\BEST_PRACTICES.md | 3. LazyLock/LazyCell - 延迟初始化优化 | `#3-lazylocklazycell---延迟初始化优化` | 同文件锚点不存在: #3-lazylocklazycell---延迟初始化优化 |
| docs\05_guides\BEST_PRACTICES.md | 4. 数学常量 - 精确计算 | `#4-数学常量---精确计算` | 同文件锚点不存在: #4-数学常量---精确计算 |
| docs\05_guides\BEST_PRACTICES.md | 1. isqrt - 整数平方根运算 | `#1-isqrt---整数平方根运算` | 同文件锚点不存在: #1-isqrt---整数平方根运算 |
| docs\05_guides\BEST_PRACTICES.md | 2. HashMap::get\_disjoint\_mut - 安全并行访问 | `#2-hashmapget_disjoint_mut---安全并行访问` | 同文件锚点不存在: #2-hashmapget_disjoint_mut---安全并行访问 |
| docs\05_guides\BEST_PRACTICES.md | 3. async Fn Trait - 异步抽象改进 | `#3-async-fn-trait---异步抽象改进` | 同文件锚点不存在: #3-async-fn-trait---异步抽象改进 |
| docs\05_guides\BEST_PRACTICES.md | 4. Vec::pop\_if - 条件弹出 | `#4-vecpop_if---条件弹出` | 同文件锚点不存在: #4-vecpop_if---条件弹出 |
| docs\05_guides\BEST_PRACTICES.md | **状态**: ✅ 持续更新 | `#状态--持续更新` | 同文件锚点不存在: #状态--持续更新 |
| docs\05_guides\CLI_APPLICATIONS_GUIDE.md | 1. 使用 `?` 操作符传播错误 | `#1-使用--操作符传播错误` | 同文件锚点不存在: #1-使用--操作符传播错误 |
| docs\05_guides\CLI_APPLICATIONS_GUIDE.md | **状态**: ✅ 深度整合完成 | `#状态--深度整合完成` | 同文件锚点不存在: #状态--深度整合完成 |
| docs\05_guides\CLI_APPLICATIONS_GUIDE.md | 超时处理 | `#错误处理最佳实践` | 同文件锚点不存在: #错误处理最佳实践 |
| docs\05_guides\CONTROL_FLOW_FUNCTIONS_USAGE_GUIDE.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\05_guides\CONTROL_FLOW_FUNCTIONS_USAGE_GUIDE.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\05_guides\CROSS_MODULE_INTEGRATION_EXAMPLES.md | 场景3: 嵌入式 + 云端协同 | `#场景3-嵌入式--云端协同` | 同文件锚点不存在: #场景3-嵌入式--云端协同 |
| docs\05_guides\CROSS_MODULE_INTEGRATION_EXAMPLES.md | **状态**: ✅ 深度整合完成 | `#状态--深度整合完成` | 同文件锚点不存在: #状态--深度整合完成 |
| docs\05_guides\CROSS_MODULE_INTEGRATION_EXAMPLES.md | 场景3: 嵌入式 + 云端协同 | `#场景3-嵌入式--云端协同` | 同文件锚点不存在: #场景3-嵌入式--云端协同 |
| docs\05_guides\CROSS_MODULE_INTEGRATION_EXAMPLES.md | **状态**: ✅ 深度整合完成 | `#状态--深度整合完成` | 同文件锚点不存在: #状态--深度整合完成 |
| docs\05_guides\CXX_RUST_INTEROP_EVALUATION.md | C++ ↔ Rust 互操作评估 | `#c--rust-互操作评估` | 同文件锚点不存在: #c--rust-互操作评估 |
| docs\05_guides\CXX_RUST_INTEROP_EVALUATION.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\05_guides\CXX_RUST_INTEROP_EVALUATION.md | **相关文档**: Rust for Linux 工具链指南 | `#相关文档-rust-for-linux-工具链指南` | 同文件锚点不存在: #相关文档-rust-for-linux-工具链指南 |
| docs\05_guides\CXX_RUST_INTEROP_EVALUATION.md | C++ ↔ Rust 互操作评估 | `#c--rust-互操作评估` | 同文件锚点不存在: #c--rust-互操作评估 |
| docs\05_guides\CXX_RUST_INTEROP_EVALUATION.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\05_guides\CXX_RUST_INTEROP_EVALUATION.md | **相关文档**: Rust for Linux 工具链指南 | `#相关文档-rust-for-linux-工具链指南` | 同文件锚点不存在: #相关文档-rust-for-linux-工具链指南 |
| docs\05_guides\DESIGN_PATTERNS_USAGE_GUIDE.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\05_guides\DESIGN_PATTERNS_USAGE_GUIDE.md | **最后更新**: 2026-05-08 | `#最后更新-2026-05-08` | 同文件锚点不存在: #最后更新-2026-05-08 |
| docs\05_guides\DESIGN_PATTERNS_USAGE_GUIDE.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\05_guides\DESIGN_PATTERNS_USAGE_GUIDE.md | **最后更新**: 2026-05-08 | `#最后更新-2026-05-08` | 同文件锚点不存在: #最后更新-2026-05-08 |
| docs\05_guides\EMBEDDED_RUST_GUIDE.md | **状态**: ✅ 深度整合完成 | `#状态--深度整合完成` | 同文件锚点不存在: #状态--深度整合完成 |
| docs\05_guides\FINAL_DOCUMENTATION_COMPLETION_GUIDE.md | 📚 文档完善最终指南 - 2026-01-27 {#-文档完善最终指南---2026-01-27} | `#-文档完善最终指南---2026-01-27--文档完善最终指南---2026-01-27` | 同文件锚点不存在: #-文档完善最终指南---2026-01-27--文档完善最终指南---2026-01-27 |
| docs\05_guides\FINAL_DOCUMENTATION_COMPLETION_GUIDE.md | **状态**: ✅✅✅ **100% 深度整合完成** | `#状态--100-深度整合完成` | 同文件锚点不存在: #状态--100-深度整合完成 |
| docs\05_guides\FINAL_DOCUMENTATION_COMPLETION_GUIDE.md | 📚 文档完善最终指南 - 2026-01-27 {#-文档完善最终指南---2026-01-27} | `#-文档完善最终指南---2026-01-27--文档完善最终指南---2026-01-27` | 同文件锚点不存在: #-文档完善最终指南---2026-01-27--文档完善最终指南---2026-01-27 |
| docs\05_guides\FINAL_DOCUMENTATION_COMPLETION_GUIDE.md | **状态**: ✅✅✅ **100% 深度整合完成** | `#状态--100-深度整合完成` | 同文件锚点不存在: #状态--100-深度整合完成 |
| docs\05_guides\FINAL_DOCUMENTATION_COMPLETION_GUIDE.md | 可选后续 | `#3-可选后续非阻塞-100` | 同文件锚点不存在: #3-可选后续非阻塞-100 |
| docs\05_guides\FORMAL_VERIFICATION_INTEGRATION_GUIDE.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\05_guides\FORMAL_VERIFICATION_INTEGRATION_GUIDE.md | 🧪 Miri - 内存安全验证 | `#-miri---内存安全验证` | 同文件锚点不存在: #-miri---内存安全验证 |
| docs\05_guides\FORMAL_VERIFICATION_INTEGRATION_GUIDE.md | 🔍 Kani - 模型检查 | `#-kani---模型检查` | 同文件锚点不存在: #-kani---模型检查 |
| docs\05_guides\FORMAL_VERIFICATION_INTEGRATION_GUIDE.md | 📐 Prusti - 契约编程 | `#-prusti---契约编程` | 同文件锚点不存在: #-prusti---契约编程 |
| docs\05_guides\FORMAL_VERIFICATION_INTEGRATION_GUIDE.md | **状态**: ✅ 生产就绪 | `#状态--生产就绪` | 同文件锚点不存在: #状态--生产就绪 |
| docs\05_guides\FORMAL_VERIFICATION_INTEGRATION_GUIDE.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\05_guides\FORMAL_VERIFICATION_INTEGRATION_GUIDE.md | 🧪 Miri - 内存安全验证 | `#-miri---内存安全验证` | 同文件锚点不存在: #-miri---内存安全验证 |
| docs\05_guides\FORMAL_VERIFICATION_INTEGRATION_GUIDE.md | 🔍 Kani - 模型检查 | `#-kani---模型检查` | 同文件锚点不存在: #-kani---模型检查 |
| docs\05_guides\FORMAL_VERIFICATION_INTEGRATION_GUIDE.md | 📐 Prusti - 契约编程 | `#-prusti---契约编程` | 同文件锚点不存在: #-prusti---契约编程 |
| docs\05_guides\FORMAL_VERIFICATION_INTEGRATION_GUIDE.md | **状态**: ✅ 生产就绪 | `#状态--生产就绪` | 同文件锚点不存在: #状态--生产就绪 |
| docs\05_guides\INLINE_ASSEMBLY_GUIDE.md | **状态**: ✅ 深度整合完成 | `#状态--深度整合完成` | 同文件锚点不存在: #状态--深度整合完成 |
| docs\05_guides\MACRO_SYSTEM_USAGE_GUIDE.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\05_guides\MACRO_SYSTEM_USAGE_GUIDE.md | ⚠️ 宏的常见陷阱与调试技巧 | `#️-宏的常见陷阱与调试技巧` | 同文件锚点不存在: #️-宏的常见陷阱与调试技巧 |
| docs\05_guides\MACRO_SYSTEM_USAGE_GUIDE.md | **状态**: ✅ 深度整合完成 | `#状态--深度整合完成` | 同文件锚点不存在: #状态--深度整合完成 |
| docs\05_guides\MACRO_SYSTEM_USAGE_GUIDE.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\05_guides\MACRO_SYSTEM_USAGE_GUIDE.md | ⚠️ 宏的常见陷阱与调试技巧 | `#️-宏的常见陷阱与调试技巧` | 同文件锚点不存在: #️-宏的常见陷阱与调试技巧 |
| docs\05_guides\MACRO_SYSTEM_USAGE_GUIDE.md | **状态**: ✅ 深度整合完成 | `#状态--深度整合完成` | 同文件锚点不存在: #状态--深度整合完成 |
| docs\05_guides\MIRI_PRACTICAL_GUIDE.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\05_guides\MIRI_PRACTICAL_GUIDE.md | ⚙️ 安装与运行 | `#️-安装与运行` | 同文件锚点不存在: #️-安装与运行 |
| docs\05_guides\MIRI_PRACTICAL_GUIDE.md | ✍️ 编写 Miri 友好测试的实战流程 | `#️-编写-miri-友好测试的实战流程` | 同文件锚点不存在: #️-编写-miri-友好测试的实战流程 |
| docs\05_guides\MIRI_PRACTICAL_GUIDE.md | ⚠️ Miri 的局限性 | `#️-miri-的局限性` | 同文件锚点不存在: #️-miri-的局限性 |
| docs\05_guides\MIRI_PRACTICAL_GUIDE.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\05_guides\MIRI_PRACTICAL_GUIDE.md | ⚙️ 安装与运行 | `#️-安装与运行` | 同文件锚点不存在: #️-安装与运行 |
| docs\05_guides\MIRI_PRACTICAL_GUIDE.md | ✍️ 编写 Miri 友好测试的实战流程 | `#️-编写-miri-友好测试的实战流程` | 同文件锚点不存在: #️-编写-miri-友好测试的实战流程 |
| docs\05_guides\MIRI_PRACTICAL_GUIDE.md | ⚠️ Miri 的局限性 | `#️-miri-的局限性` | 同文件锚点不存在: #️-miri-的局限性 |
| docs\05_guides\PERFORMANCE_TESTING_REPORT.md | **状态**: ✅ 深度整合完成 | `#状态--深度整合完成` | 同文件锚点不存在: #状态--深度整合完成 |
| docs\05_guides\PERFORMANCE_TESTING_REPORT.md | **状态**: ✅ 深度整合完成 | `#状态--深度整合完成` | 同文件锚点不存在: #状态--深度整合完成 |
| docs\05_guides\PERFORMANCE_TUNING_GUIDE.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\05_guides\PERFORMANCE_TUNING_GUIDE.md | 1. `array_windows()` - 零开销滑动窗口迭代 | `#1-array_windows---零开销滑动窗口迭代` | 同文件锚点不存在: #1-array_windows---零开销滑动窗口迭代 |
| docs\05_guides\PERFORMANCE_TUNING_GUIDE.md | 2. `ControlFlow<B, C>` - 流控制的零成本抽象 | `#2-controlflowb-c---流控制的零成本抽象` | 同文件锚点不存在: #2-controlflowb-c---流控制的零成本抽象 |
| docs\05_guides\PERFORMANCE_TUNING_GUIDE.md | **最后更新**: 2026-05-08 (深度整合 Rust 1.95+ 语义) | `#最后更新-2026-05-08-深度整合-rust-195-语义` | 同文件锚点不存在: #最后更新-2026-05-08-深度整合-rust-195-语义 |
| docs\05_guides\PERFORMANCE_TUNING_GUIDE.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\05_guides\PERFORMANCE_TUNING_GUIDE.md | 1. `array_windows()` - 零开销滑动窗口迭代 | `#1-array_windows---零开销滑动窗口迭代` | 同文件锚点不存在: #1-array_windows---零开销滑动窗口迭代 |
| docs\05_guides\PERFORMANCE_TUNING_GUIDE.md | 2. `ControlFlow<B, C>` - 流控制的零成本抽象 | `#2-controlflowb-c---流控制的零成本抽象` | 同文件锚点不存在: #2-controlflowb-c---流控制的零成本抽象 |
| docs\05_guides\PERFORMANCE_TUNING_GUIDE.md | **最后更新**: 2026-05-08 (深度整合 Rust 1.95+ 语义) | `#最后更新-2026-05-08-深度整合-rust-195-语义` | 同文件锚点不存在: #最后更新-2026-05-08-深度整合-rust-195-语义 |
| docs\05_guides\05_rust_196_guides_index.md | **负责人**: 系统化梳理团队 | `#负责人-系统化梳理团队` | 同文件锚点不存在: #负责人-系统化梳理团队 |
| docs\05_guides\05_rust_196_guides_index.md | isqrt 最佳实践 | `./BEST_PRACTICES.md#rust-196-最佳实践` | 锚点不存在: #rust-196-最佳实践 |
| docs\05_guides\TESTING_COVERAGE_GUIDE.md | **状态**: ✅ 深度整合完成 | `#状态--深度整合完成` | 同文件锚点不存在: #状态--深度整合完成 |
| docs\05_guides\TESTING_COVERAGE_GUIDE.md | **状态**: ✅ 深度整合完成 | `#状态--深度整合完成` | 同文件锚点不存在: #状态--深度整合完成 |
| docs\05_guides\THREADS_CONCURRENCY_USAGE_GUIDE.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\05_guides\THREADS_CONCURRENCY_USAGE_GUIDE.md | 🛡️ 并发安全代码示例（5+ 模式） | `#️-并发安全代码示例5-模式` | 同文件锚点不存在: #️-并发安全代码示例5-模式 |
| docs\05_guides\THREADS_CONCURRENCY_USAGE_GUIDE.md | ⚠️ 数据竞争案例与解决方案 | `#️-数据竞争案例与解决方案` | 同文件锚点不存在: #️-数据竞争案例与解决方案 |
| docs\05_guides\THREADS_CONCURRENCY_USAGE_GUIDE.md | 生产场景 2: 单线程延迟初始化 + 可变更新 | `#生产场景-2-单线程延迟初始化--可变更新` | 同文件锚点不存在: #生产场景-2-单线程延迟初始化--可变更新 |
| docs\05_guides\THREADS_CONCURRENCY_USAGE_GUIDE.md | **状态**: ✅ 完整实现 | `#状态--完整实现` | 同文件锚点不存在: #状态--完整实现 |
| docs\05_guides\THREADS_CONCURRENCY_USAGE_GUIDE.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\05_guides\THREADS_CONCURRENCY_USAGE_GUIDE.md | 🛡️ 并发安全代码示例（5+ 模式） | `#️-并发安全代码示例5-模式` | 同文件锚点不存在: #️-并发安全代码示例5-模式 |
| docs\05_guides\THREADS_CONCURRENCY_USAGE_GUIDE.md | ⚠️ 数据竞争案例与解决方案 | `#️-数据竞争案例与解决方案` | 同文件锚点不存在: #️-数据竞争案例与解决方案 |
| docs\05_guides\THREADS_CONCURRENCY_USAGE_GUIDE.md | 生产场景 2: 单线程延迟初始化 + 可变更新 | `#生产场景-2-单线程延迟初始化--可变更新` | 同文件锚点不存在: #生产场景-2-单线程延迟初始化--可变更新 |
| docs\05_guides\THREADS_CONCURRENCY_USAGE_GUIDE.md | **状态**: ✅ 完整实现 | `#状态--完整实现` | 同文件锚点不存在: #状态--完整实现 |
| docs\05_guides\TROUBLESHOOTING_GUIDE.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\05_guides\TROUBLESHOOTING_GUIDE.md | **状态**: ✅ 深度整合完成 | `#状态--深度整合完成` | 同文件锚点不存在: #状态--深度整合完成 |
| docs\05_guides\TROUBLESHOOTING_GUIDE.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\05_guides\TROUBLESHOOTING_GUIDE.md | **状态**: ✅ 深度整合完成 | `#状态--深度整合完成` | 同文件锚点不存在: #状态--深度整合完成 |
| docs\05_guides\TYPE_SYSTEM_USAGE_GUIDE.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\05_guides\TYPE_SYSTEM_USAGE_GUIDE.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\05_guides\UNSAFE_FIELDS_PREVIEW.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\05_guides\UNSAFE_FIELDS_PREVIEW.md | ⚖️ 与当前 `unsafe` 块的对比 | `#️-与当前-unsafe-块的对比` | 同文件锚点不存在: #️-与当前-unsafe-块的对比 |
| docs\05_guides\UNSAFE_FIELDS_PREVIEW.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\05_guides\UNSAFE_FIELDS_PREVIEW.md | ⚖️ 与当前 `unsafe` 块的对比 | `#️-与当前-unsafe-块的对比` | 同文件锚点不存在: #️-与当前-unsafe-块的对比 |
| docs\05_guides\UNSAFE_RUST_GUIDE.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\05_guides\UNSAFE_RUST_GUIDE.md | ⚠️ 未定义行为 (UB) 案例 | `#️-未定义行为-ub-案例` | 同文件锚点不存在: #️-未定义行为-ub-案例 |
| docs\05_guides\UNSAFE_RUST_GUIDE.md | 🛡️ 安全抽象原则 | `#️-安全抽象原则` | 同文件锚点不存在: #️-安全抽象原则 |
| docs\05_guides\UNSAFE_RUST_GUIDE.md | **状态**: ✅ 深度整合完成 | `#状态--深度整合完成` | 同文件锚点不存在: #状态--深度整合完成 |
| docs\05_guides\UNSAFE_RUST_GUIDE.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\05_guides\UNSAFE_RUST_GUIDE.md | ⚠️ 未定义行为 (UB) 案例 | `#️-未定义行为-ub-案例` | 同文件锚点不存在: #️-未定义行为-ub-案例 |
| docs\05_guides\UNSAFE_RUST_GUIDE.md | 🛡️ 安全抽象原则 | `#️-安全抽象原则` | 同文件锚点不存在: #️-安全抽象原则 |
| docs\05_guides\UNSAFE_RUST_GUIDE.md | **状态**: ✅ 深度整合完成 | `#状态--深度整合完成` | 同文件锚点不存在: #状态--深度整合完成 |
| docs\05_guides\WASM_USAGE_GUIDE.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\05_guides\WASM_USAGE_GUIDE.md | **最后更新**: 2026-05-08 | `#最后更新-2026-05-08` | 同文件锚点不存在: #最后更新-2026-05-08 |
| docs\05_guides\WASM_USAGE_GUIDE.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\05_guides\WASM_USAGE_GUIDE.md | **最后更新**: 2026-05-08 | `#最后更新-2026-05-08` | 同文件锚点不存在: #最后更新-2026-05-08 |
| docs\05_guides\workflow\01_workflow_theory.md | 14. 工作流理论与形式化模型 | `#14-工作流理论与形式化模型` | 同文件锚点不存在: #14-工作流理论与形式化模型 |
| docs\05_guides\workflow\01_workflow_theory.md | **状态**: ✅ 深度整合完成 | `#状态--深度整合完成` | 同文件锚点不存在: #状态--深度整合完成 |
| docs\06_toolchain\01_compiler_features.md | 📊 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\06_toolchain\01_compiler_features.md | **最后更新**: 2026-05-08 (添加 1.95+ 引用) | `#最后更新-2026-05-08-添加-195-引用` | 同文件锚点不存在: #最后更新-2026-05-08-添加-195-引用 |
| docs\06_toolchain\01_compiler_features.md | 📊 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\06_toolchain\01_compiler_features.md | **最后更新**: 2026-05-08 (添加 1.95+ 引用) | `#最后更新-2026-05-08-添加-195-引用` | 同文件锚点不存在: #最后更新-2026-05-08-添加-195-引用 |
| docs\06_toolchain\01_compiler_features.md | Rust 历史版本文档索引 | `../README.md#相关资源` | 锚点不存在: #相关资源 |
| docs\06_toolchain\03_rustdoc_advanced.md | 📊 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\06_toolchain\03_rustdoc_advanced.md | ⚠️ 避免 | `#️-避免` | 同文件锚点不存在: #️-避免 |
| docs\06_toolchain\03_rustdoc_advanced.md | **最后更新**: 2026-05-08 (添加 1.95+ 引用) | `#最后更新-2026-05-08-添加-195-引用` | 同文件锚点不存在: #最后更新-2026-05-08-添加-195-引用 |
| docs\06_toolchain\03_rustdoc_advanced.md | 📊 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\06_toolchain\03_rustdoc_advanced.md | ⚠️ 避免 | `#️-避免` | 同文件锚点不存在: #️-避免 |
| docs\06_toolchain\03_rustdoc_advanced.md | **最后更新**: 2026-05-08 (添加 1.95+ 引用) | `#最后更新-2026-05-08-添加-195-引用` | 同文件锚点不存在: #最后更新-2026-05-08-添加-195-引用 |
| docs\06_toolchain\03_rustdoc_advanced.md | Rust 历史版本文档索引 | `../README.md#相关资源` | 锚点不存在: #相关资源 |
| docs\06_toolchain\05_rust_1.93_vs_1.92_comparison.md | Rust 1.93 vs 1.92 全面对比分析 | `#rust-193-vs-192-全面对比分析` | 同文件锚点不存在: #rust-193-vs-192-全面对比分析 |
| docs\06_toolchain\05_rust_1.93_vs_1.92_comparison.md | 📑 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\06_toolchain\05_rust_1.93_vs_1.92_comparison.md | **下次更新**：Rust 1.94 发布时 | `#下次更新rust-194-发布时` | 同文件锚点不存在: #下次更新rust-194-发布时 |
| docs\06_toolchain\05_rust_1.93_vs_1.92_comparison.md | Rust 1.93 vs 1.92 全面对比分析 | `#rust-193-vs-192-全面对比分析` | 同文件锚点不存在: #rust-193-vs-192-全面对比分析 |
| docs\06_toolchain\05_rust_1.93_vs_1.92_comparison.md | 📑 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\06_toolchain\05_rust_1.93_vs_1.92_comparison.md | **下次更新**：Rust 1.94 发布时 | `#下次更新rust-194-发布时` | 同文件锚点不存在: #下次更新rust-194-发布时 |
| docs\06_toolchain\07_rust_1.93_full_changelog.md | Rust 1.93 完整变更清单 | `#rust-193-完整变更清单` | 同文件锚点不存在: #rust-193-完整变更清单 |
| docs\06_toolchain\07_rust_1.93_full_changelog.md | cargo tree --format 长格式 | `#cargo-tree---format-长格式` | 同文件锚点不存在: #cargo-tree---format-长格式 |
| docs\06_toolchain\07_rust_1.93_full_changelog.md | cargo clean --workspace | `#cargo-clean---workspace` | 同文件锚点不存在: #cargo-clean---workspace |
| docs\06_toolchain\07_rust_1.93_full_changelog.md | **状态**: ✅ 深度整合完成 | `#状态--深度整合完成` | 同文件锚点不存在: #状态--深度整合完成 |
| docs\06_toolchain\09_rust_1.93_compatibility_deep_dive.md | Rust 1.93 兼容性深度解析 | `#rust-193-兼容性深度解析` | 同文件锚点不存在: #rust-193-兼容性深度解析 |
| docs\06_toolchain\09_rust_1.93_compatibility_deep_dive.md | **状态**: ✅ 深度整合完成 | `#状态--深度整合完成` | 同文件锚点不存在: #状态--深度整合完成 |
| docs\06_toolchain\11_rust_1.93_cargo_rustdoc_changes.md | Rust 1.93 Cargo 与 Rustdoc 变更详解 | `#rust-193-cargo-与-rustdoc-变更详解` | 同文件锚点不存在: #rust-193-cargo-与-rustdoc-变更详解 |
| docs\06_toolchain\11_rust_1.93_cargo_rustdoc_changes.md | cargo tree --format 长格式 | `#cargo-tree---format-长格式` | 同文件锚点不存在: #cargo-tree---format-长格式 |
| docs\06_toolchain\11_rust_1.93_cargo_rustdoc_changes.md | cargo clean --workspace | `#cargo-clean---workspace` | 同文件锚点不存在: #cargo-clean---workspace |
| docs\06_toolchain\11_rust_1.93_cargo_rustdoc_changes.md | **状态**: ✅ 深度整合完成 | `#状态--深度整合完成` | 同文件锚点不存在: #状态--深度整合完成 |
| docs\06_toolchain\06_14_rust_1_95_nightly_preview.md | 1. `-Zinstrument-mcount` | `#1--zinstrument-mcount` | 同文件锚点不存在: #1--zinstrument-mcount |
| docs\06_toolchain\06_14_rust_1_95_nightly_preview.md | 2. `-Cdebuginfo-compression` | `#2--cdebuginfo-compression` | 同文件锚点不存在: #2--cdebuginfo-compression |
| docs\06_toolchain\06_14_rust_1_95_nightly_preview.md | **最后更新**: 2026-05-08 (添加 1.95+ 引用) | `#最后更新-2026-05-08-添加-195-引用` | 同文件锚点不存在: #最后更新-2026-05-08-添加-195-引用 |
| docs\06_toolchain\06_19_rust_1_96_features.md | Rust 1.95 & 1.96 特性详解 | `#rust-195--196-特性详解含版本勘误` | 同文件锚点不存在: #rust-195--196-特性详解含版本勘误 |
| docs\06_toolchain\06_cargo_script_guide.md | Cargo Script / Frontmatter 指南 | `#cargo-script--frontmatter-指南` | 同文件锚点不存在: #cargo-script--frontmatter-指南 |
| docs\06_toolchain\CRANELIFT_BACKEND_GUIDE.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\06_toolchain\CRANELIFT_BACKEND_GUIDE.md | ⏱️ 为什么 Cranelift 重要 | `#️-为什么-cranelift-重要` | 同文件锚点不存在: #️-为什么-cranelift-重要 |
| docs\06_toolchain\CRANELIFT_BACKEND_GUIDE.md | ⚙️ 安装与配置 | `#️-安装与配置` | 同文件锚点不存在: #️-安装与配置 |
| docs\06_toolchain\CRANELIFT_BACKEND_GUIDE.md | ⚖️ LLVM vs Cranelift 对比 | `#️-llvm-vs-cranelift-对比` | 同文件锚点不存在: #️-llvm-vs-cranelift-对比 |
| docs\06_toolchain\CRANELIFT_BACKEND_GUIDE.md | ✅ 何时使用 vs 🚫 何时不使用 | `#-何时使用-vs--何时不使用` | 同文件锚点不存在: #-何时使用-vs--何时不使用 |
| docs\06_toolchain\CRANELIFT_BACKEND_GUIDE.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\06_toolchain\CRANELIFT_BACKEND_GUIDE.md | ⏱️ 为什么 Cranelift 重要 | `#️-为什么-cranelift-重要` | 同文件锚点不存在: #️-为什么-cranelift-重要 |
| docs\06_toolchain\CRANELIFT_BACKEND_GUIDE.md | ⚙️ 安装与配置 | `#️-安装与配置` | 同文件锚点不存在: #️-安装与配置 |
| docs\06_toolchain\CRANELIFT_BACKEND_GUIDE.md | ⚖️ LLVM vs Cranelift 对比 | `#️-llvm-vs-cranelift-对比` | 同文件锚点不存在: #️-llvm-vs-cranelift-对比 |
| docs\06_toolchain\CRANELIFT_BACKEND_GUIDE.md | ✅ 何时使用 vs 🚫 何时不使用 | `#-何时使用-vs--何时不使用` | 同文件锚点不存在: #-何时使用-vs--何时不使用 |
| docs\06_toolchain\RUST_FOR_LINUX_TOOLING_GUIDE.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\06_toolchain\RUST_FOR_LINUX_TOOLING_GUIDE.md | **相关文档**: C++ ↔ Rust 互操作评估 | `#相关文档-c--rust-互操作评估` | 同文件锚点不存在: #相关文档-c--rust-互操作评估 |
| docs\06_toolchain\RUST_FOR_LINUX_TOOLING_GUIDE.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\06_toolchain\RUST_FOR_LINUX_TOOLING_GUIDE.md | **相关文档**: C++ ↔ Rust 互操作评估 | `#相关文档-c--rust-互操作评估` | 同文件锚点不存在: #相关文档-c--rust-互操作评估 |
| docs\06_toolchain\TOML_V11_CARGO_GUIDE.md | 6.1 ✅ 推荐做法 | `#61--推荐做法` | 同文件锚点不存在: #61--推荐做法 |
| docs\06_toolchain\TOML_V11_CARGO_GUIDE.md | 6.2 ❌ 避免的做法 | `#62--避免的做法` | 同文件锚点不存在: #62--避免的做法 |
| docs\07_future\rust_project_goals_2026_matrix.md | 一、旗舰主题映射（Flagship Themes → 项目内容） | `#一旗舰主题映射flagship-themes--项目内容` | 同文件锚点不存在: #一旗舰主题映射flagship-themes--项目内容 |
| docs\07_future\rust_project_goals_2026_matrix.md | 🔴 P0 — 立即创建（完全缺失，2026 年稳定化目标） | `#-p0--立即创建完全缺失2026-年稳定化目标` | 同文件锚点不存在: #-p0--立即创建完全缺失2026-年稳定化目标 |
| docs\07_future\rust_project_goals_2026_matrix.md | 🟡 P1 — 补充深化（部分覆盖，需升级） | `#-p1--补充深化部分覆盖需升级` | 同文件锚点不存在: #-p1--补充深化部分覆盖需升级 |
| docs\07_future\rust_project_goals_2026_matrix.md | 🟢 P2 — 跟踪观察（nightly / 长期演进） | `#-p2--跟踪观察nightly--长期演进` | 同文件锚点不存在: #-p2--跟踪观察nightly--长期演进 |
| docs\07_project\ALIGNMENT_KNOWLEDGE_CRITICAL_EVALUATION_2026_02.md | 对齐知识批判性评估 - 重定向 | `#对齐知识批判性评估---重定向` | 同文件锚点不存在: #对齐知识批判性评估---重定向 |
| docs\07_project\ALIGNMENT_KNOWLEDGE_CRITICAL_EVALUATION_2026_02.md | **最后更新**: 2026-05-08 (Rust 1.95+ 持续更新) | `#最后更新-2026-05-08-rust-195-持续更新` | 同文件锚点不存在: #最后更新-2026-05-08-rust-195-持续更新 |
| docs\07_project\07_completion_status.md | ⚠️ 已知问题 | `#️-已知问题` | 同文件锚点不存在: #️-已知问题 |
| docs\07_project\07_completion_status.md | **更新流程**: 每轮扩展后由执行代理同步更新 | `#更新流程-每轮扩展后由执行代理同步更新` | 同文件锚点不存在: #更新流程-每轮扩展后由执行代理同步更新 |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | 🔗 文档交叉引用指南 {#-文档交叉引用指南} | `#-文档交叉引用指南--文档交叉引用指南` | 同文件锚点不存在: #-文档交叉引用指南--文档交叉引用指南 |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | 🗺️ 文档网络总览 {#️-文档网络总览} | `#️-文档网络总览-️-文档网络总览` | 同文件锚点不存在: #️-文档网络总览-️-文档网络总览 |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | C01 - 所有权与借用 | `#c01---所有权与借用` | 同文件锚点不存在: #c01---所有权与借用 |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | C02 - 类型系统 | `#c02---类型系统` | 同文件锚点不存在: #c02---类型系统 |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | C03 - 控制流与函数 | `#c03---控制流与函数` | 同文件锚点不存在: #c03---控制流与函数 |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | C04 - 泛型编程 | `#c04---泛型编程` | 同文件锚点不存在: #c04---泛型编程 |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | C05 - 线程与并发 | `#c05---线程与并发` | 同文件锚点不存在: #c05---线程与并发 |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | C06 - 异步编程 | `#c06---异步编程` | 同文件锚点不存在: #c06---异步编程 |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | C07 - 进程管理 | `#c07---进程管理` | 同文件锚点不存在: #c07---进程管理 |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | C08 - 算法与数据结构 | `#c08---算法与数据结构` | 同文件锚点不存在: #c08---算法与数据结构 |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | C09 - 设计模式 | `#c09---设计模式` | 同文件锚点不存在: #c09---设计模式 |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | C10 - 网络编程 | `#c10---网络编程` | 同文件锚点不存在: #c10---网络编程 |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | C11 - 宏系统 | `#c11---宏系统` | 同文件锚点不存在: #c11---宏系统 |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | C12 - WASM | `#c12---wasm` | 同文件锚点不存在: #c12---wasm |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | 速查卡 ↔ 指南映射 | `#速查卡--指南映射` | 同文件锚点不存在: #速查卡--指南映射 |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | 速查卡 ↔ 研究笔记映射 | `#速查卡--研究笔记映射` | 同文件锚点不存在: #速查卡--研究笔记映射 |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | **最后更新**: 2026-05-08 (Rust 1.95+ 持续更新) | `#最后更新-2026-05-08-rust-195-持续更新` | 同文件锚点不存在: #最后更新-2026-05-08-rust-195-持续更新 |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | 🔗 文档交叉引用指南 {#-文档交叉引用指南} | `#-文档交叉引用指南--文档交叉引用指南` | 同文件锚点不存在: #-文档交叉引用指南--文档交叉引用指南 |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | 🗺️ 文档网络总览 {#️-文档网络总览} | `#️-文档网络总览-️-文档网络总览` | 同文件锚点不存在: #️-文档网络总览-️-文档网络总览 |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | C01 - 所有权与借用 | `#c01---所有权与借用` | 同文件锚点不存在: #c01---所有权与借用 |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | C02 - 类型系统 | `#c02---类型系统` | 同文件锚点不存在: #c02---类型系统 |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | C03 - 控制流与函数 | `#c03---控制流与函数` | 同文件锚点不存在: #c03---控制流与函数 |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | C04 - 泛型编程 | `#c04---泛型编程` | 同文件锚点不存在: #c04---泛型编程 |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | C05 - 线程与并发 | `#c05---线程与并发` | 同文件锚点不存在: #c05---线程与并发 |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | C06 - 异步编程 | `#c06---异步编程` | 同文件锚点不存在: #c06---异步编程 |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | C07 - 进程管理 | `#c07---进程管理` | 同文件锚点不存在: #c07---进程管理 |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | C08 - 算法与数据结构 | `#c08---算法与数据结构` | 同文件锚点不存在: #c08---算法与数据结构 |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | C09 - 设计模式 | `#c09---设计模式` | 同文件锚点不存在: #c09---设计模式 |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | C10 - 网络编程 | `#c10---网络编程` | 同文件锚点不存在: #c10---网络编程 |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | C11 - 宏系统 | `#c11---宏系统` | 同文件锚点不存在: #c11---宏系统 |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | C12 - WASM | `#c12---wasm` | 同文件锚点不存在: #c12---wasm |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | 速查卡 ↔ 指南映射 | `#速查卡--指南映射` | 同文件锚点不存在: #速查卡--指南映射 |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | 速查卡 ↔ 研究笔记映射 | `#速查卡--研究笔记映射` | 同文件锚点不存在: #速查卡--研究笔记映射 |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | **最后更新**: 2026-05-08 (Rust 1.95+ 持续更新) | `#最后更新-2026-05-08-rust-195-持续更新` | 同文件锚点不存在: #最后更新-2026-05-08-rust-195-持续更新 |
| docs\07_project\DOCUMENTATION_THEME_ORGANIZATION_PLAN.md | 文档主题梳理规划 - 重定向 | `#文档主题梳理规划---重定向` | 同文件锚点不存在: #文档主题梳理规划---重定向 |
| docs\07_project\DOCUMENTATION_THEME_ORGANIZATION_PLAN.md | **最后更新**: 2026-05-08 (Rust 1.95+ 持续更新) | `#最后更新-2026-05-08-rust-195-持续更新` | 同文件锚点不存在: #最后更新-2026-05-08-rust-195-持续更新 |
| docs\07_project\07_extension_deepening_plan_2026.md | **版本**: v1.0 | `#版本-v10` | 同文件锚点不存在: #版本-v10 |
| docs\07_project\INTERNATIONAL_BENCHMARK_CRITICAL_EVALUATION_2026_02.md | 国际化对标批判性评估 - 重定向 | `#国际化对标批判性评估---重定向` | 同文件锚点不存在: #国际化对标批判性评估---重定向 |
| docs\07_project\INTERNATIONAL_BENCHMARK_CRITICAL_EVALUATION_2026_02.md | **最后更新**: 2026-05-08 (Rust 1.95+ 持续更新) | `#最后更新-2026-05-08-rust-195-持续更新` | 同文件锚点不存在: #最后更新-2026-05-08-rust-195-持续更新 |
| docs\07_project\KNOWLEDGE_STRUCTURE_FRAMEWORK.md | Rust 知识结构框架文档 | `#rust-知识结构框架文档` | 同文件锚点不存在: #rust-知识结构框架文档 |
| docs\07_project\KNOWLEDGE_STRUCTURE_FRAMEWORK.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\07_project\KNOWLEDGE_STRUCTURE_FRAMEWORK.md | 🗺️ 思维表征方式 | `#️-思维表征方式` | 同文件锚点不存在: #️-思维表征方式 |
| docs\07_project\KNOWLEDGE_STRUCTURE_FRAMEWORK.md | **最后更新**: 2026-05-08 (Rust 1.95+ 持续更新) | `#最后更新-2026-05-08-rust-195-持续更新` | 同文件锚点不存在: #最后更新-2026-05-08-rust-195-持续更新 |
| docs\07_project\KNOWLEDGE_STRUCTURE_FRAMEWORK.md | Rust 知识结构框架文档 | `#rust-知识结构框架文档` | 同文件锚点不存在: #rust-知识结构框架文档 |
| docs\07_project\KNOWLEDGE_STRUCTURE_FRAMEWORK.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\07_project\KNOWLEDGE_STRUCTURE_FRAMEWORK.md | 🗺️ 思维表征方式 | `#️-思维表征方式` | 同文件锚点不存在: #️-思维表征方式 |
| docs\07_project\KNOWLEDGE_STRUCTURE_FRAMEWORK.md | **最后更新**: 2026-05-08 (Rust 1.95+ 持续更新) | `#最后更新-2026-05-08-rust-195-持续更新` | 同文件锚点不存在: #最后更新-2026-05-08-rust-195-持续更新 |
| docs\07_project\MODULE_1.93_ADAPTATION_STATUS.md | C01–C12 1.93 适配状态 - 重定向 | `#c01c12-193-适配状态---重定向` | 同文件锚点不存在: #c01c12-193-适配状态---重定向 |
| docs\07_project\MODULE_1.93_ADAPTATION_STATUS.md | **最后更新**: 2026-05-08 (Rust 1.95+ 持续更新) | `#最后更新-2026-05-08-rust-195-持续更新` | 同文件锚点不存在: #最后更新-2026-05-08-rust-195-持续更新 |
| docs\07_project\MODULE_KNOWLEDGE_STRUCTURE_GUIDE.md | 模块知识结构补充指南 | `#模块知识结构补充指南` | 同文件锚点不存在: #模块知识结构补充指南 |
| docs\07_project\MODULE_KNOWLEDGE_STRUCTURE_GUIDE.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\07_project\MODULE_KNOWLEDGE_STRUCTURE_GUIDE.md | 🗺️ 思维表征方式补充 | `#️-思维表征方式补充` | 同文件锚点不存在: #️-思维表征方式补充 |
| docs\07_project\MODULE_KNOWLEDGE_STRUCTURE_GUIDE.md | **最后更新**: 2026-05-08 (Rust 1.95+ 持续更新) | `#最后更新-2026-05-08-rust-195-持续更新` | 同文件锚点不存在: #最后更新-2026-05-08-rust-195-持续更新 |
| docs\07_project\MODULE_KNOWLEDGE_STRUCTURE_GUIDE.md | 模块知识结构补充指南 | `#模块知识结构补充指南` | 同文件锚点不存在: #模块知识结构补充指南 |
| docs\07_project\MODULE_KNOWLEDGE_STRUCTURE_GUIDE.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\07_project\MODULE_KNOWLEDGE_STRUCTURE_GUIDE.md | 🗺️ 思维表征方式补充 | `#️-思维表征方式补充` | 同文件锚点不存在: #️-思维表征方式补充 |
| docs\07_project\MODULE_KNOWLEDGE_STRUCTURE_GUIDE.md | **最后更新**: 2026-05-08 (Rust 1.95+ 持续更新) | `#最后更新-2026-05-08-rust-195-持续更新` | 同文件锚点不存在: #最后更新-2026-05-08-rust-195-持续更新 |
| docs\07_project\ONE_PAGE_SUMMARY_TEMPLATE.md | 一页纸总结模板 - 重定向 | `#一页纸总结模板---重定向` | 同文件锚点不存在: #一页纸总结模板---重定向 |
| docs\07_project\ONE_PAGE_SUMMARY_TEMPLATE.md | **最后更新**: 2026-05-08 (Rust 1.95+ 持续更新) | `#最后更新-2026-05-08-rust-195-持续更新` | 同文件锚点不存在: #最后更新-2026-05-08-rust-195-持续更新 |
| docs\07_project\PROJECT_ARCHITECTURE_GUIDE.md | 项目架构指南 | `#项目架构指南` | 同文件锚点不存在: #项目架构指南 |
| docs\07_project\PROJECT_ARCHITECTURE_GUIDE.md | 🏗️ 项目结构 | `#️-项目结构` | 同文件锚点不存在: #️-项目结构 |
| docs\07_project\PROJECT_ARCHITECTURE_GUIDE.md | 📑 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\07_project\PROJECT_ARCHITECTURE_GUIDE.md | **最后更新**: 2026-05-08 (Rust 1.95+ 持续更新) | `#最后更新-2026-05-08-rust-195-持续更新` | 同文件锚点不存在: #最后更新-2026-05-08-rust-195-持续更新 |
| docs\07_project\PROJECT_ARCHITECTURE_GUIDE.md | 项目架构指南 | `#项目架构指南` | 同文件锚点不存在: #项目架构指南 |
| docs\07_project\PROJECT_ARCHITECTURE_GUIDE.md | 🏗️ 项目结构 | `#️-项目结构` | 同文件锚点不存在: #️-项目结构 |
| docs\07_project\PROJECT_ARCHITECTURE_GUIDE.md | 📑 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\07_project\PROJECT_ARCHITECTURE_GUIDE.md | **最后更新**: 2026-05-08 (Rust 1.95+ 持续更新) | `#最后更新-2026-05-08-rust-195-持续更新` | 同文件锚点不存在: #最后更新-2026-05-08-rust-195-持续更新 |
| docs\07_project\07_project_critical_evaluation_report_2026_02.md | **最后更新**: 2026-05-08 (Rust 1.95+ 持续更新) | `#最后更新-2026-05-08-rust-195-持续更新` | 同文件锚点不存在: #最后更新-2026-05-08-rust-195-持续更新 |
| docs\07_project\RUST_RELEASE_TRACKING_CHECKLIST.md | Rust 新版本发布追踪 Checklist - 重定向 | `#rust-新版本发布追踪-checklist---重定向` | 同文件锚点不存在: #rust-新版本发布追踪-checklist---重定向 |
| docs\07_project\RUST_RELEASE_TRACKING_CHECKLIST.md | **最后更新**: 2026-05-08 (Rust 1.95+ 持续更新) | `#最后更新-2026-05-08-rust-195-持续更新` | 同文件锚点不存在: #最后更新-2026-05-08-rust-195-持续更新 |
| docs\archive\2026_03_reorganization\PROJECT_STRUCTURE.md | crates/ - 学习模块 | `#crates---学习模块` | 同文件锚点不存在: #crates---学习模块 |
| docs\archive\2026_03_reorganization\PROJECT_STRUCTURE.md | 🏗️ 模块标准结构 | `#️-模块标准结构` | 同文件锚点不存在: #️-模块标准结构 |
| docs\archive\2026_03_reorganization\PROJECT_STRUCTURE.md | guides/ - 学习指南 | `#guides---学习指南` | 同文件锚点不存在: #guides---学习指南 |
| docs\archive\2026_03_reorganization\PROJECT_STRUCTURE.md | docs/ - 跨模块文档与指南 | `#docs---跨模块文档与指南` | 同文件锚点不存在: #docs---跨模块文档与指南 |
| docs\archive\2026_03_reorganization\PROJECT_STRUCTURE.md | scripts/ - 脚本工具 | `#scripts---脚本工具` | 同文件锚点不存在: #scripts---脚本工具 |
| docs\archive\2026_03_reorganization\PROJECT_STRUCTURE.md | examples/ - 根级综合示例 | `#examples---根级综合示例` | 同文件锚点不存在: #examples---根级综合示例 |
| docs\archive\2026_03_reorganization\PROJECT_STRUCTURE.md | tests/ - 集成测试 | `#tests---集成测试` | 同文件锚点不存在: #tests---集成测试 |
| docs\archive\2026_03_reorganization\PROJECT_STRUCTURE.md | exercises/ - 练习入口 | `#exercises---练习入口` | 同文件锚点不存在: #exercises---练习入口 |
| docs\archive\2026_05_historical_docs\13_rust_1.94_preview.md | Rust 1.94 预览与特性追踪 | `#rust-194-预览与特性追踪` | 同文件锚点不存在: #rust-194-预览与特性追踪 |
| docs\archive\2026_05_historical_docs\13_rust_1.94_preview.md | 1. rustdoc `--merge` 选项 | `#1-rustdoc---merge-选项` | 同文件锚点不存在: #1-rustdoc---merge-选项 |
| docs\archive\2026_05_historical_docs\15_rust_1.94_comprehensive_guide.md | 1. `ControlFlow::ok()` - 控制流简化 | `#1-controlflowok---控制流简化` | 同文件锚点不存在: #1-controlflowok---控制流简化 |
| docs\archive\2026_05_historical_docs\15_rust_1.94_comprehensive_guide.md | 2. `int_format_into` - 高性能格式化 | `#2-int_format_into---高性能格式化` | 同文件锚点不存在: #2-int_format_into---高性能格式化 |
| docs\archive\2026_05_historical_docs\15_rust_1.94_comprehensive_guide.md | 4. `RefCell::try_map` - 安全内部可变性 | `#4-refcelltry_map---安全内部可变性` | 同文件锚点不存在: #4-refcelltry_map---安全内部可变性 |
| docs\archive\2026_05_historical_docs\15_rust_1.94_comprehensive_guide.md | 5. `proc_macro_value` - 宏增强 | `#5-proc_macro_value---宏增强` | 同文件锚点不存在: #5-proc_macro_value---宏增强 |
| docs\archive\2026_05_historical_docs\15_rust_1.94_comprehensive_guide.md | 2. rustdoc `--merge` 选项 | `#2-rustdoc---merge-选项` | 同文件锚点不存在: #2-rustdoc---merge-选项 |
| docs\archive\2026_05_historical_docs\16_rust_1.94_release_notes.md | Rust 1.94.0 发布说明 / Release Notes | `#rust-1940-发布说明--release-notes` | 同文件锚点不存在: #rust-1940-发布说明--release-notes |
| docs\archive\2026_05_historical_docs\16_rust_1.94_release_notes.md | 1. `array_windows` - 零开销抽象 | `#1-array_windows---零开销抽象` | 同文件锚点不存在: #1-array_windows---零开销抽象 |
| docs\archive\2026_05_historical_docs\16_rust_1.94_release_notes.md | 2. `LazyLock::get()` - 热路径优化 | `#2-lazylockget---热路径优化` | 同文件锚点不存在: #2-lazylockget---热路径优化 |
| docs\archive\2026_05_historical_docs\16_rust_1.94_release_notes.md | 3. `ControlFlow` - 迭代器短路优化 | `#3-controlflow---迭代器短路优化` | 同文件锚点不存在: #3-controlflow---迭代器短路优化 |
| docs\archive\2026_05_historical_docs\16_rust_1.94_release_notes.md | 4. 数学常量 - 精确计算 | `#4-数学常量---精确计算` | 同文件锚点不存在: #4-数学常量---精确计算 |
| docs\archive\2026_05_historical_docs\RUST_194_COMPREHENSIVE_GUIDE.md | 在所有权模块中 - 安全地分析数据序列 | `#在所有权模块中---安全地分析数据序列` | 同文件锚点不存在: #在所有权模块中---安全地分析数据序列 |
| docs\archive\2026_05_historical_docs\RUST_194_COMPREHENSIVE_GUIDE.md | 在类型系统模块中 - 类型安全的窗口分析 | `#在类型系统模块中---类型安全的窗口分析` | 同文件锚点不存在: #在类型系统模块中---类型安全的窗口分析 |
| docs\archive\2026_05_historical_docs\RUST_194_COMPREHENSIVE_GUIDE.md | 在控制流模块中 - 状态机转换检测 | `#在控制流模块中---状态机转换检测` | 同文件锚点不存在: #在控制流模块中---状态机转换检测 |
| docs\archive\2026_05_historical_docs\rust_194_features_cheatsheet.md | Rust 1.95+ 特性速查卡 / Rust 1.94 Features Cheatsheet | `#rust-195-特性速查卡--rust-194-features-cheatsheet` | 同文件锚点不存在: #rust-195-特性速查卡--rust-194-features-cheatsheet |
| docs\archive\2026_05_historical_docs\rust_194_features_cheatsheet.md | 2. LazyCell \& LazyLock 新方法 | `#2-lazycell--lazylock-新方法` | 同文件锚点不存在: #2-lazycell--lazylock-新方法 |
| docs\archive\2026_05_historical_docs\rust_194_features_cheatsheet.md | Rust 1.95+ 特性速查 - 完整版 | `#rust-195-特性速查---完整版` | 同文件锚点不存在: #rust-195-特性速查---完整版 |
| docs\archive\deprecated_20260318\00_rust_2024_edition_learning_impact.md | Rust 2024 Edition 学习影响 | `#rust-2024-edition-学习影响` | 同文件锚点不存在: #rust-2024-edition-学习影响 |
| docs\archive\deprecated_20260318\01_safe_23_catalog.md | 23 种安全设计模型索引 | `#23-种安全设计模型索引` | 同文件锚点不存在: #23-种安全设计模型索引 |
| docs\archive\deprecated_20260318\02_cargo_workspace_guide.md | 11.1 大型多 crate 项目 - 完整配置 | `#111-大型多-crate-项目---完整配置` | 同文件锚点不存在: #111-大型多-crate-项目---完整配置 |
| docs\archive\deprecated_20260318\02_cargo_workspace_guide.md | 11.2 微服务架构 - 完整示例 | `#112-微服务架构---完整示例` | 同文件锚点不存在: #112-微服务架构---完整示例 |
| docs\archive\deprecated_20260318\02_cargo_workspace_guide.md | ⚠️ 常见陷阱 | `#️-常见陷阱` | 同文件锚点不存在: #️-常见陷阱 |
| docs\archive\deprecated_20260318\03_semantic_boundary_map.md | 语义边界图 | `#语义边界图` | 同文件锚点不存在: #语义边界图 |
| docs\archive\deprecated_20260318\03_semantic_boundary_map.md | 示例 5：领域逻辑 + 持久化 | `#示例-5领域逻辑--持久化` | 同文件锚点不存在: #示例-5领域逻辑--持久化 |
| docs\archive\deprecated_20260318\03_semantic_boundary_map.md | 场景 8：跨线程缓存（Flyweight + Arc） | `#场景-8跨线程缓存flyweight--arc` | 同文件锚点不存在: #场景-8跨线程缓存flyweight--arc |
| docs\archive\deprecated_20260318\04_rust_1.91_vs_1.90_comparison.md | 2) Cargo 原生支持 `cargo publish --workspace` | `#2-cargo-原生支持-cargo-publish---workspace` | 同文件锚点不存在: #2-cargo-原生支持-cargo-publish---workspace |
| docs\archive\deprecated_20260318\04_rust_1.91_vs_1.90_comparison.md | 📊 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\archive\deprecated_20260318\05-02-rust-vs-cpp.md | 11.1 C++ → Rust 思维转换 | `#111-c--rust-思维转换` | 同文件锚点不存在: #111-c--rust-思维转换 |
| docs\archive\deprecated_20260318\05-runtime-semantics.md | 8.2.1 ? 运算符语义 | `#821--运算符语义` | 同文件锚点不存在: #821--运算符语义 |
| docs\archive\deprecated_20260318\05_workflow_models.md | 工作流执行引擎重构设计与实现 | `#工作流执行引擎重构设计与实现` | 同文件锚点不存在: #工作流执行引擎重构设计与实现 |
| docs\archive\deprecated_20260318\06_rust_1.93_compatibility_notes.md | Rust 1.93 兼容性注意事项 | `#rust-193-兼容性注意事项` | 同文件锚点不存在: #rust-193-兼容性注意事项 |
| docs\archive\deprecated_20260318\06_rust_1.93_compatibility_notes.md | 1. ... 函数参数（可变参数） | `#1--函数参数可变参数` | 同文件锚点不存在: #1--函数参数可变参数 |
| docs\archive\deprecated_20260318\2026_RUST_ECOSYSTEM_COMPREHENSIVE_REVIEW.md | 🏗️ 2026年推荐架构模式 | `#️-2026年推荐架构模式` | 同文件锚点不存在: #️-2026年推荐架构模式 |
| docs\archive\deprecated_20260318\2026_RUST_ECOSYSTEM_COMPREHENSIVE_REVIEW.md | ⚠️ 过时内容识别 | `#️-过时内容识别` | 同文件锚点不存在: #️-过时内容识别 |
| docs\archive\deprecated_20260318\ANTI_PATTERN_TEMPLATE.md | Rust 反模式速查卡 | `#rust-反模式速查卡` | 同文件锚点不存在: #rust-反模式速查卡 |
| docs\archive\deprecated_20260318\ANTI_PATTERN_TEMPLATE.md | 十四、完整示例：场景 → 反模式 → 正确写法 | `#十四完整示例场景--反模式--正确写法` | 同文件锚点不存在: #十四完整示例场景--反模式--正确写法 |
| docs\archive\deprecated_20260318\async-trait-formal-analysis.md | 定义 PROBLEM-1 ( 原生限制 ) | `#定义-problem-1--原生限制-` | 同文件锚点不存在: #定义-problem-1--原生限制- |
| docs\archive\deprecated_20260318\async-trait-formal-analysis.md | 定义 PROBLEM-2 ( RPITIT限制 ) | `#定义-problem-2--rpitit限制-` | 同文件锚点不存在: #定义-problem-2--rpitit限制- |
| docs\archive\deprecated_20260318\async-trait-formal-analysis.md | 定义 TRANSFORM-1 ( 转换规则 ) | `#定义-transform-1--转换规则-` | 同文件锚点不存在: #定义-transform-1--转换规则- |
| docs\archive\deprecated_20260318\async-trait-formal-analysis.md | 定义 TRANSFORM-2 ( 具体实现转换 ) | `#定义-transform-2--具体实现转换-` | 同文件锚点不存在: #定义-transform-2--具体实现转换- |
| docs\archive\deprecated_20260318\async-trait-formal-analysis.md | 定义 SEND-1 ( Send要求 ) | `#定义-send-1--send要求-` | 同文件锚点不存在: #定义-send-1--send要求- |
| docs\archive\deprecated_20260318\async-trait-formal-analysis.md | 定义 SEND-2 ( Send传播 ) | `#定义-send-2--send传播-` | 同文件锚点不存在: #定义-send-2--send传播- |
| docs\archive\deprecated_20260318\async-trait-formal-analysis.md | 定理 SEND-T1 ( 自动推断 ) | `#定理-send-t1--自动推断-` | 同文件锚点不存在: #定理-send-t1--自动推断- |
| docs\archive\deprecated_20260318\async-trait-formal-analysis.md | 定义 LIFETIME-1 ( 隐式生命周期 ) | `#定义-lifetime-1--隐式生命周期-` | 同文件锚点不存在: #定义-lifetime-1--隐式生命周期- |
| docs\archive\deprecated_20260318\async-trait-formal-analysis.md | 定理 LIFETIME-T1 ( 生命周期保留 ) | `#定理-lifetime-t1--生命周期保留-` | 同文件锚点不存在: #定理-lifetime-t1--生命周期保留- |
| docs\archive\deprecated_20260318\async-trait-formal-analysis.md | 定理 ASYNC\_TRAIT-T1 ( 语义保持 ) | `#定理-async_trait-t1--语义保持-` | 同文件锚点不存在: #定理-async_trait-t1--语义保持- |
| docs\archive\deprecated_20260318\async-trait-formal-analysis.md | 定理 ASYNC\_TRAIT-T2 ( 开销边界 ) | `#定理-async_trait-t2--开销边界-` | 同文件锚点不存在: #定理-async_trait-t2--开销边界- |
| docs\archive\deprecated_20260318\axum-formal-analysis.md | 定义 ROUTE-1 ( 路由类型 ) | `#定义-route-1--路由类型-` | 同文件锚点不存在: #定义-route-1--路由类型- |
| docs\archive\deprecated_20260318\axum-formal-analysis.md | 定义 ROUTE-2 ( 路径参数 ) | `#定义-route-2--路径参数-` | 同文件锚点不存在: #定义-route-2--路径参数- |
| docs\archive\deprecated_20260318\axum-formal-analysis.md | 定理 ROUTE-T1 ( 类型安全 ) | `#定理-route-t1--类型安全-` | 同文件锚点不存在: #定理-route-t1--类型安全- |
| docs\archive\deprecated_20260318\axum-formal-analysis.md | 定义 EXTRACTOR-1 ( FromRequest trait ) | `#定义-extractor-1--fromrequest-trait-` | 同文件锚点不存在: #定义-extractor-1--fromrequest-trait- |
| docs\archive\deprecated_20260318\axum-formal-analysis.md | 定义 EXTRACTOR-2 ( 提取器组合 ) | `#定义-extractor-2--提取器组合-` | 同文件锚点不存在: #定义-extractor-2--提取器组合- |
| docs\archive\deprecated_20260318\axum-formal-analysis.md | 定理 EXTRACTOR-T1 ( 独立性 ) | `#定理-extractor-t1--独立性-` | 同文件锚点不存在: #定理-extractor-t1--独立性- |
| docs\archive\deprecated_20260318\axum-formal-analysis.md | 定义 TOWER-1 ( Service trait ) | `#定义-tower-1--service-trait-` | 同文件锚点不存在: #定义-tower-1--service-trait- |
| docs\archive\deprecated_20260318\axum-formal-analysis.md | 定义 TOWER-2 ( 中间件链 ) | `#定义-tower-2--中间件链-` | 同文件锚点不存在: #定义-tower-2--中间件链- |
| docs\archive\deprecated_20260318\axum-formal-analysis.md | 定理 TOWER-T1 ( 组合性 ) | `#定理-tower-t1--组合性-` | 同文件锚点不存在: #定理-tower-t1--组合性- |
| docs\archive\deprecated_20260318\axum-formal-analysis.md | 定义 STATE-1 ( 共享状态 ) | `#定义-state-1--共享状态-` | 同文件锚点不存在: #定义-state-1--共享状态- |
| docs\archive\deprecated_20260318\axum-formal-analysis.md | 定义 STATE-2 ( 状态注入 ) | `#定义-state-2--状态注入-` | 同文件锚点不存在: #定义-state-2--状态注入- |
| docs\archive\deprecated_20260318\axum-formal-analysis.md | 定理 STATE-T1 ( 线程安全 ) | `#定理-state-t1--线程安全-` | 同文件锚点不存在: #定理-state-t1--线程安全- |
| docs\archive\deprecated_20260318\axum-formal-analysis.md | 定理 AXUM-T1 ( 编译时路由验证 ) | `#定理-axum-t1--编译时路由验证-` | 同文件锚点不存在: #定理-axum-t1--编译时路由验证- |
| docs\archive\deprecated_20260318\axum-formal-analysis.md | 定理 AXUM-T2 ( 零成本抽象 ) | `#定理-axum-t2--零成本抽象-` | 同文件锚点不存在: #定理-axum-t2--零成本抽象- |
| docs\archive\deprecated_20260318\design_patterns_cheatsheet.md | 设计模式快速参考卡片 | `#设计模式快速参考卡片` | 同文件锚点不存在: #设计模式快速参考卡片 |
| docs\archive\deprecated_20260318\EDITION_2024_COMPREHENSIVE_GUIDE.md | ⚠️ 破坏性变更 | `#️-破坏性变更` | 同文件锚点不存在: #️-破坏性变更 |
| docs\archive\deprecated_20260318\FFI_PRACTICAL_GUIDE.md | 2. bindgen - C/C++ → Rust | `#2-bindgen---cc--rust` | 同文件锚点不存在: #2-bindgen---cc--rust |
| docs\archive\deprecated_20260318\FFI_PRACTICAL_GUIDE.md | 3. cbindgen - Rust → C/C++ | `#3-cbindgen---rust--cc` | 同文件锚点不存在: #3-cbindgen---rust--cc |
| docs\archive\deprecated_20260318\FFI_PRACTICAL_GUIDE.md | 4. wasm-bindgen - Rust → Web | `#4-wasm-bindgen---rust--web` | 同文件锚点不存在: #4-wasm-bindgen---rust--web |
| docs\archive\deprecated_20260318\macros_cheatsheet.md | 🔧 Rust 宏系统速查卡 | `#-rust-宏系统速查卡` | 同文件锚点不存在: #-rust-宏系统速查卡 |
| docs\archive\deprecated_20260318\MIND_REPRESENTATION_COMPLETION_PLAN.md | 思维表征完善计划：思维导图、矩阵、证明树、决策树、应用树 | `#思维表征完善计划思维导图矩阵证明树决策树应用树` | 同文件锚点不存在: #思维表征完善计划思维导图矩阵证明树决策树应用树 |
| docs\archive\deprecated_20260318\PRODUCTION_PROJECT_EXAMPLES.md | 项目 1: CLI 工具 - 高性能日志分析器 | `#项目-1-cli-工具---高性能日志分析器` | 同文件锚点不存在: #项目-1-cli-工具---高性能日志分析器 |
| docs\archive\deprecated_20260318\RUST_194_MIGRATION_GUIDE.md | ⚠️ 破坏性变更 | `#️-破坏性变更` | 同文件锚点不存在: #️-破坏性变更 |
| docs\archive\deprecated_20260318\RUST_194_STDLIB_API_GUIDE.md | CARGO\_BIN\_EXE\_ at Runtime | `#cargo_bin_exe_-at-runtime` | 同文件锚点不存在: #cargo_bin_exe_-at-runtime |
| docs\archive\deprecated_20260318\sea-orm-formal-analysis.md | 定义 ENTITY-1 ( 实体结构 ) | `#定义-entity-1--实体结构-` | 同文件锚点不存在: #定义-entity-1--实体结构- |
| docs\archive\deprecated_20260318\sea-orm-formal-analysis.md | 定义 ENTITY-2 ( 主键约束 ) | `#定义-entity-2--主键约束-` | 同文件锚点不存在: #定义-entity-2--主键约束- |
| docs\archive\deprecated_20260318\sea-orm-formal-analysis.md | 定理 ENTITY-T1 ( 标识唯一性 ) | `#定理-entity-t1--标识唯一性-` | 同文件锚点不存在: #定理-entity-t1--标识唯一性- |
| docs\archive\deprecated_20260318\sea-orm-formal-analysis.md | 定义 QUERY-1 ( 查询构建器 ) | `#定义-query-1--查询构建器-` | 同文件锚点不存在: #定义-query-1--查询构建器- |
| docs\archive\deprecated_20260318\sea-orm-formal-analysis.md | 定义 QUERY-2 ( 类型检查 ) | `#定义-query-2--类型检查-` | 同文件锚点不存在: #定义-query-2--类型检查- |
| docs\archive\deprecated_20260318\sea-orm-formal-analysis.md | 定理 QUERY-T1 ( 编译时类型安全 ) | `#定理-query-t1--编译时类型安全-` | 同文件锚点不存在: #定理-query-t1--编译时类型安全- |
| docs\archive\deprecated_20260318\sea-orm-formal-analysis.md | 定义 REL-1 ( 关系类型 ) | `#定义-rel-1--关系类型-` | 同文件锚点不存在: #定义-rel-1--关系类型- |
| docs\archive\deprecated_20260318\sea-orm-formal-analysis.md | 定义 REL-2 ( 外键约束 ) | `#定义-rel-2--外键约束-` | 同文件锚点不存在: #定义-rel-2--外键约束- |
| docs\archive\deprecated_20260318\sea-orm-formal-analysis.md | 定理 REL-T1 ( 引用完整性 ) | `#定理-rel-t1--引用完整性-` | 同文件锚点不存在: #定理-rel-t1--引用完整性- |
| docs\archive\deprecated_20260318\sea-orm-formal-analysis.md | 定义 MIGRATION-1 ( 迁移操作 ) | `#定义-migration-1--迁移操作-` | 同文件锚点不存在: #定义-migration-1--迁移操作- |
| docs\archive\deprecated_20260318\sea-orm-formal-analysis.md | 定理 MIGRATION-T1 ( 可逆性 ) | `#定理-migration-t1--可逆性-` | 同文件锚点不存在: #定理-migration-t1--可逆性- |
| docs\archive\deprecated_20260318\sea-orm-formal-analysis.md | 定理 ORM-T1 ( SQL注入防护 ) | `#定理-orm-t1--sql注入防护-` | 同文件锚点不存在: #定理-orm-t1--sql注入防护- |
| docs\archive\deprecated_20260318\sea-orm-formal-analysis.md | 定理 ORM-T2 ( 连接池安全 ) | `#定理-orm-t2--连接池安全-` | 同文件锚点不存在: #定理-orm-t2--连接池安全- |
| docs\archive\reports\RUST_1.91_FEATURES_COMPREHENSIVE.md | Rust 1.91 特性全面文档 | `#rust-191-特性全面文档` | 同文件锚点不存在: #rust-191-特性全面文档 |
| docs\archive\reports\formal_system_reports\DOCUMENTATION_ENHANCEMENT_REPORT_2025_09_27.md | Rust 形式化工程系统文档完善报告 | `#rust-形式化工程系统文档完善报告` | 同文件锚点不存在: #rust-形式化工程系统文档完善报告 |
| docs\archive\reports\formal_system_reports\FORMAL_PROOFS_2025_11_11.md | Rust 形式化论证集合 2025-11-11 | `#rust-形式化论证集合-2025-11-11` | 同文件锚点不存在: #rust-形式化论证集合-2025-11-11 |
| docs\archive\reports\formal_system_reports\KNOWLEDGE_GRAPH_2025_11_11.md | Rust 形式化工程体系知识图谱 2025-11-11 | `#rust-形式化工程体系知识图谱-2025-11-11` | 同文件锚点不存在: #rust-形式化工程体系知识图谱-2025-11-11 |
| docs\archive\reports\formal_system_reports\KNOWLEDGE_GRAPH_2025_11_11.md | 理论基础 → 工具链生态 | `#理论基础--工具链生态` | 同文件锚点不存在: #理论基础--工具链生态 |
| docs\archive\reports\formal_system_reports\KNOWLEDGE_GRAPH_2025_11_11.md | 工具链生态 → 应用领域 | `#工具链生态--应用领域` | 同文件锚点不存在: #工具链生态--应用领域 |
| docs\archive\reports\formal_system_reports\KNOWLEDGE_GRAPH_2025_11_11.md | 应用领域 → 研究前沿 | `#应用领域--研究前沿` | 同文件锚点不存在: #应用领域--研究前沿 |
| docs\archive\reports\formal_system_reports\KNOWLEDGE_GRAPH_2025_11_11.md | 🗺️ 学习路径图谱 | `#️-学习路径图谱` | 同文件锚点不存在: #️-学习路径图谱 |
| docs\archive\reports\formal_system_reports\KNOWLEDGE_GRAPH_2025_11_11.md | 路径1：理论基础 → 实践应用 | `#路径1理论基础--实践应用` | 同文件锚点不存在: #路径1理论基础--实践应用 |
| docs\archive\reports\formal_system_reports\KNOWLEDGE_GRAPH_2025_11_11.md | 路径2：工具链 → 工程实践 | `#路径2工具链--工程实践` | 同文件锚点不存在: #路径2工具链--工程实践 |
| docs\archive\reports\formal_system_reports\KNOWLEDGE_GRAPH_2025_11_11.md | 路径3：研究前沿 → 创新应用 | `#路径3研究前沿--创新应用` | 同文件锚点不存在: #路径3研究前沿--创新应用 |
| docs\archive\rust-ownership-chinese\comprehensive_analysis_c_go_rust.md | Rust (原子操作 + 类型安全) | `#rust-原子操作--类型安全` | 同文件锚点不存在: #rust-原子操作--类型安全 |
| docs\archive\rust-ownership-chinese\FAQ.md | Rust所有权与可判定性 - 常见问题 | `#rust所有权与可判定性---常见问题` | 同文件锚点不存在: #rust所有权与可判定性---常见问题 |
| docs\archive\rust-ownership-chinese\README.md | 🛠️ 代码库 | `#️-代码库` | 同文件锚点不存在: #️-代码库 |
| docs\archive\rust-ownership-chinese\扩展主题：Pin与Unpin深度分析.md | 方法3: pin! 宏 ( nightly ) | `#方法3-pin-宏--nightly-` | 同文件锚点不存在: #方法3-pin-宏--nightly- |
| docs\archive\rust-ownership-chinese\推进计划与任务分解.md | 🗓️ 第一阶段：基础完善（第1-3个月） | `#️-第一阶段基础完善第1-3个月` | 同文件锚点不存在: #️-第一阶段基础完善第1-3个月 |
| docs\archive\rust-ownership-chinese\推进计划与任务分解.md | 🗓️ 第二阶段：深度扩展（第4-6个月） | `#️-第二阶段深度扩展第4-6个月` | 同文件锚点不存在: #️-第二阶段深度扩展第4-6个月 |
| docs\archive\rust-ownership-chinese\推进计划与任务分解.md | 🗓️ 第三阶段：综合完善（第7-9个月） | `#️-第三阶段综合完善第7-9个月` | 同文件锚点不存在: #️-第三阶段综合完善第7-9个月 |
| docs\archive\rust-ownership-chinese\推进计划与任务分解.md | 🗓️ 第四阶段：长期维护（第10-12个月） | `#️-第四阶段长期维护第10-12个月` | 同文件锚点不存在: #️-第四阶段长期维护第10-12个月 |
| docs\archive\rust-ownership-chinese\改进实施计划.md | 🗓️ 实施阶段 | `#️-实施阶段` | 同文件锚点不存在: #️-实施阶段 |
| docs\archive\rust-ownership-chinese\文档索引与关联指南.md | §2.1 所有权转移 | `#212-所有权转移语义` | 同文件锚点不存在: #212-所有权转移语义 |
| docs\archive\rust-ownership-chinese\文档索引与关联指南.md | Jung et al. (2018) | `./REFERENCES.md#rustbelt` | 锚点不存在: #rustbelt |
| docs\archive\rust-ownership-chinese\guides\complete-formal-proofs.md | 2. 类型安全性定理（Progress + Preservation） | `#2-类型安全性定理progress--preservation` | 同文件锚点不存在: #2-类型安全性定理progress--preservation |
| docs\archive\rust-ownership-chinese\guides\complete-formal-proofs.md | 情况 1：变量 $e = x$ | `#情况-1变量-e--x` | 同文件锚点不存在: #情况-1变量-e--x |
| docs\archive\rust-ownership-chinese\guides\complete-formal-proofs.md | 情况 2：借用 $e = \&x$ | `#情况-2借用-e--x` | 同文件锚点不存在: #情况-2借用-e--x |
| docs\archive\rust-ownership-chinese\guides\complete-formal-proofs.md | 情况 3：可变借用 $e = \&mut x$ | `#情况-3可变借用-e--mut-x` | 同文件锚点不存在: #情况-3可变借用-e--mut-x |
| docs\archive\rust-ownership-chinese\guides\complete-formal-proofs.md | 情况 4：赋值 $e = \*e\_1 = e\_2$ | `#情况-4赋值-e--e_1--e_2` | 同文件锚点不存在: #情况-4赋值-e--e_1--e_2 |
| docs\archive\rust-ownership-chinese\guides\complete-formal-proofs.md | 情况 5：let绑定 $e = \\text{let } x = e\_1 \\text{ in } e\_2$ | `#情况-5let绑定-e--textlet--x--e_1-text-in--e_2` | 同文件锚点不存在: #情况-5let绑定-e--textlet--x--e_1-text-in--e_2 |
| docs\archive\rust-ownership-chinese\guides\complete-formal-proofs.md | 引理 2.3.1（代入引理 / Substitution Lemma） | `#引理-231代入引理--substitution-lemma` | 同文件锚点不存在: #引理-231代入引理--substitution-lemma |
| docs\archive\rust-ownership-chinese\guides\creusot-tutorial.md | 6.2  traits 规范 | `#62--traits-规范` | 同文件锚点不存在: #62--traits-规范 |
| docs\archive\rust-ownership-chinese\guides\zero-cost-abstraction-proof.md | 2.2 生成的汇编对比 (x86\_64, -O3) | `#22-生成的汇编对比-x86_64--o3` | 同文件锚点不存在: #22-生成的汇编对比-x86_64--o3 |
| docs\archive\rust-ownership-chinese\papers\aeneas-translation-formalization.md | 2. 翻译函数 ⟦·⟧: Rust MIR → LLBC | `#2-翻译函数--rust-mir--llbc` | 同文件锚点不存在: #2-翻译函数--rust-mir--llbc |
| docs\archive\rust-ownership-chinese\papers\stacked-tree-borrows-formal-semantics.md | 规则 4：使用引用（use tag）- 读操作 | `#规则-4使用引用use-tag--读操作` | 同文件锚点不存在: #规则-4使用引用use-tag--读操作 |
| docs\archive\rust-ownership-chinese\papers\stacked-tree-borrows-formal-semantics.md | 规则 5：使用引用（use tag）- 写操作 | `#规则-5使用引用use-tag--写操作` | 同文件锚点不存在: #规则-5使用引用use-tag--写操作 |
| docs\archive\rust-ownership-chinese\papers\stacked-tree-borrows-formal-semantics.md | 规则 1：Active → Frozen（创建子节点） | `#规则-1active--frozen创建子节点` | 同文件锚点不存在: #规则-1active--frozen创建子节点 |
| docs\archive\rust-ownership-chinese\papers\stacked-tree-borrows-formal-semantics.md | 规则 2：Frozen → Disabled（父节点写入） | `#规则-2frozen--disabled父节点写入` | 同文件锚点不存在: #规则-2frozen--disabled父节点写入 |
| docs\archive\temp\QUICK_REFERENCE.md | 🚀 Rust 快速参考 (Quick Reference) | `#-rust-快速参考-quick-reference` | 同文件锚点不存在: #-rust-快速参考-quick-reference |
| docs\archive\temp\swap\RUST_190_FAQ.md | ❓ Rust 1.90 升级 FAQ | `#-rust-190-升级-faq` | 同文件锚点不存在: #-rust-190-升级-faq |
| docs\archive\version_reports\RUST_192_EXAMPLE_COMPATIBILITY_REPORT.md | Rust 1.92.0 / 1.93.0 示例代码兼容性验证报告 | `#rust-1920--1930-示例代码兼容性验证报告` | 同文件锚点不存在: #rust-1920--1930-示例代码兼容性验证报告 |
| docs\archive\version_reports\RUST_192_EXAMPLE_COMPATIBILITY_REPORT.md | 2.2 C01 - 所有权和借用作用域 | `#22-c01---所有权和借用作用域` | 同文件锚点不存在: #22-c01---所有权和借用作用域 |
| docs\archive\version_reports\RUST_192_EXAMPLE_COMPATIBILITY_REPORT.md | 2.3 C02 - 类型系统 | `#23-c02---类型系统` | 同文件锚点不存在: #23-c02---类型系统 |
| docs\archive\version_reports\RUST_192_EXAMPLE_COMPATIBILITY_REPORT.md | 2.4 C03 - 控制流和函数 | `#24-c03---控制流和函数` | 同文件锚点不存在: #24-c03---控制流和函数 |
| docs\archive\version_reports\RUST_192_EXAMPLE_COMPATIBILITY_REPORT.md | 2.5 C04 - 泛型 | `#25-c04---泛型` | 同文件锚点不存在: #25-c04---泛型 |
| docs\archive\version_reports\RUST_192_EXAMPLE_COMPATIBILITY_REPORT.md | 2.6 C05 - 线程和并发 | `#26-c05---线程和并发` | 同文件锚点不存在: #26-c05---线程和并发 |
| docs\archive\version_reports\RUST_192_EXAMPLE_COMPATIBILITY_REPORT.md | 2.7 C06 - 异步编程 | `#27-c06---异步编程` | 同文件锚点不存在: #27-c06---异步编程 |
| docs\archive\version_reports\RUST_192_EXAMPLE_COMPATIBILITY_REPORT.md | 2.8 C07 - 进程管理 | `#28-c07---进程管理` | 同文件锚点不存在: #28-c07---进程管理 |
| docs\archive\version_reports\RUST_192_EXAMPLE_COMPATIBILITY_REPORT.md | 2.9 C08 - 算法 | `#29-c08---算法` | 同文件锚点不存在: #29-c08---算法 |
| docs\archive\version_reports\RUST_192_EXAMPLE_COMPATIBILITY_REPORT.md | 2.10 C09 - 设计模式 | `#210-c09---设计模式` | 同文件锚点不存在: #210-c09---设计模式 |
| docs\archive\version_reports\RUST_192_EXAMPLE_COMPATIBILITY_REPORT.md | 2.11 C10 - 网络编程 | `#211-c10---网络编程` | 同文件锚点不存在: #211-c10---网络编程 |
| docs\archive\version_reports\RUST_192_EXAMPLE_COMPATIBILITY_REPORT.md | 2.12 C11 - 宏系统 | `#212-c11---宏系统` | 同文件锚点不存在: #212-c11---宏系统 |
| docs\archive\version_reports\RUST_192_EXAMPLE_COMPATIBILITY_REPORT.md | 2.13 C12 - WebAssembly | `#213-c12---webassembly` | 同文件锚点不存在: #213-c12---webassembly |
| docs\archive\version_reports\RUST_192_EXAMPLE_COMPATIBILITY_REPORT.md | ⚠️ 需要更新的示例 | `#️-需要更新的示例` | 同文件锚点不存在: #️-需要更新的示例 |
| docs\archive\version_reports\RUST_192_FEATURES_ALIGNMENT.md | Rust 1.92.0 / 1.93.0 特性对齐文档 / Rust Features Alignment | `#rust-1920--1930-特性对齐文档--rust-features-alignment` | 同文件锚点不存在: #rust-1920--1930-特性对齐文档--rust-features-alignment |
| docs\archive\version_reports\RUST_192_FEATURES_ALIGNMENT.md | 5.1.1 展开表默认启用（Unwind Tables with `-Cpanic=abort`） | `#511-展开表默认启用unwind-tables-with--cpanicabort` | 同文件锚点不存在: #511-展开表默认启用unwind-tables-with--cpanicabort |
| docs\archive\version_reports\RUST_192_THINKING_REPRESENTATION_COMPREHENSIVE.md | Rust 1.92.0 思维表征方式综合文档 / Comprehensive Thinking Representation Methods | `#rust-1920-思维表征方式综合文档--comprehensive-thinking-representation-methods` | 同文件锚点不存在: #rust-1920-思维表征方式综合文档--comprehensive-thinking-representation-methods |
| docs\archive\version_reports\RUST_192_THINKING_REPRESENTATION_COMPREHENSIVE.md | 🗺️ 1. 思维导图 (Mind Map) | `#️-1-思维导图-mind-map` | 同文件锚点不存在: #️-1-思维导图-mind-map |
| docs\content\CONTENT_CRATES_MAPPING.md | 🗺️ 映射关系概览 | `#️-映射关系概览` | 同文件锚点不存在: #️-映射关系概览 |
| docs\content\CONTENT_CRATES_MAPPING.md | content/emerging/ → C04 + C11 | `#contentemerging--c04--c11` | 同文件锚点不存在: #contentemerging--c04--c11 |
| docs\content\CONTENT_CRATES_MAPPING.md | content/ecosystem/ → C05 + C06 + C10 | `#contentecosystem--c05--c06--c10` | 同文件锚点不存在: #contentecosystem--c05--c06--c10 |
| docs\content\CONTENT_CRATES_MAPPING.md | content/production/ → C07 + C12 | `#contentproduction--c07--c12` | 同文件锚点不存在: #contentproduction--c07--c12 |
| docs\content\CONTENT_CRATES_MAPPING.md | content/academic/ → C01 + C04 | `#contentacademic--c01--c04` | 同文件锚点不存在: #contentacademic--c01--c04 |
| docs\content\CONTENT_CRATES_MAPPING.md | content/scenarios/ → C09 + C10 | `#contentscenarios--c09--c10` | 同文件锚点不存在: #contentscenarios--c09--c10 |
| docs\content\CONTENT_CRATES_MAPPING.md | **状态**: ✅ 100% 完成 | `#状态--100-完成` | 同文件锚点不存在: #状态--100-完成 |
| docs\content\academic\coq_formalization_guide.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\content\academic\coq_formalization_guide.md | 🏗️ 基础设置 | `#️-基础设置` | 同文件锚点不存在: #️-基础设置 |
| docs\content\academic\coq_formalization_guide.md | **状态**: ✅ 100% 完成 | `#状态--100-完成` | 同文件锚点不存在: #状态--100-完成 |
| docs\content\academic\coq_formalization_guide.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\content\academic\coq_formalization_guide.md | 🏗️ 基础设置 | `#️-基础设置` | 同文件锚点不存在: #️-基础设置 |
| docs\content\academic\coq_formalization_guide.md | **状态**: ✅ 100% 完成 | `#状态--100-完成` | 同文件锚点不存在: #状态--100-完成 |
| docs\content\academic\README.md | 🛠️ 验证工具 | `#️-验证工具` | 同文件锚点不存在: #️-验证工具 |
| docs\content\academic\README.md | **状态**: 🔄 持续整合学术前沿 | `#状态--持续整合学术前沿` | 同文件锚点不存在: #状态--持续整合学术前沿 |
| docs\content\academic\tree_borrows_authoritative_guide.md | Tree Borrows 权威指南 / Tree Borrows Authoritative Guide | `#tree-borrows-权威指南--tree-borrows-authoritative-guide` | 同文件锚点不存在: #tree-borrows-权威指南--tree-borrows-authoritative-guide |
| docs\content\academic\tree_borrows_authoritative_guide.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\content\academic\tree_borrows_authoritative_guide.md | **状态**: ✅ 权威指南 v1.0 | `#状态--权威指南-v10` | 同文件锚点不存在: #状态--权威指南-v10 |
| docs\content\academic\tree_borrows_authoritative_guide.md | Tree Borrows 权威指南 / Tree Borrows Authoritative Guide | `#tree-borrows-权威指南--tree-borrows-authoritative-guide` | 同文件锚点不存在: #tree-borrows-权威指南--tree-borrows-authoritative-guide |
| docs\content\academic\tree_borrows_authoritative_guide.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\content\academic\tree_borrows_authoritative_guide.md | **状态**: ✅ 权威指南 v1.0 | `#状态--权威指南-v10` | 同文件锚点不存在: #状态--权威指南-v10 |
| docs\content\academic\tree_borrows_guide.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\content\academic\tree_borrows_guide.md | **状态**: 🔄 学术前沿跟踪中 | `#状态--学术前沿跟踪中` | 同文件锚点不存在: #状态--学术前沿跟踪中 |
| docs\content\academic\tree_borrows_guide.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\content\academic\tree_borrows_guide.md | **状态**: 🔄 学术前沿跟踪中 | `#状态--学术前沿跟踪中` | 同文件锚点不存在: #状态--学术前沿跟踪中 |
| docs\content\ecosystem\README.md | 🗄️ 数据库 | `#️-数据库` | 同文件锚点不存在: #️-数据库 |
| docs\content\ecosystem\README.md | **状态**: 🔄 持续扩充中 | `#状态--持续扩充中` | 同文件锚点不存在: #状态--持续扩充中 |
| docs\content\ecosystem\async_runtimes\tokio_deep_dive.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\content\ecosystem\async_runtimes\tokio_deep_dive.md | 🏗️ 架构设计 | `#️-架构设计` | 同文件锚点不存在: #️-架构设计 |
| docs\content\ecosystem\async_runtimes\tokio_deep_dive.md | **状态**: ✅ 100% 完成 | `#状态--100-完成` | 同文件锚点不存在: #状态--100-完成 |
| docs\content\ecosystem\async_runtimes\tokio_deep_dive.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\content\ecosystem\async_runtimes\tokio_deep_dive.md | 🏗️ 架构设计 | `#️-架构设计` | 同文件锚点不存在: #️-架构设计 |
| docs\content\ecosystem\async_runtimes\tokio_deep_dive.md | **状态**: ✅ 100% 完成 | `#状态--100-完成` | 同文件锚点不存在: #状态--100-完成 |
| docs\content\ecosystem\database\sea_orm_deep_dive.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\content\ecosystem\database\sea_orm_deep_dive.md | 🏗️ 架构设计 | `#️-架构设计` | 同文件锚点不存在: #️-架构设计 |
| docs\content\ecosystem\database\sea_orm_deep_dive.md | **状态**: ✅ 已完成 | `#状态--已完成` | 同文件锚点不存在: #状态--已完成 |
| docs\content\ecosystem\database\sea_orm_deep_dive.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\content\ecosystem\database\sea_orm_deep_dive.md | 🏗️ 架构设计 | `#️-架构设计` | 同文件锚点不存在: #️-架构设计 |
| docs\content\ecosystem\database\sea_orm_deep_dive.md | **状态**: ✅ 已完成 | `#状态--已完成` | 同文件锚点不存在: #状态--已完成 |
| docs\content\ecosystem\database\sqlx_deep_dive.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\content\ecosystem\database\sqlx_deep_dive.md | 🏗️ 架构设计 | `#️-架构设计` | 同文件锚点不存在: #️-架构设计 |
| docs\content\ecosystem\database\sqlx_deep_dive.md | **状态**: ✅ 已完成 | `#状态--已完成` | 同文件锚点不存在: #状态--已完成 |
| docs\content\ecosystem\database\sqlx_deep_dive.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\content\ecosystem\database\sqlx_deep_dive.md | 🏗️ 架构设计 | `#️-架构设计` | 同文件锚点不存在: #️-架构设计 |
| docs\content\ecosystem\database\sqlx_deep_dive.md | **状态**: ✅ 已完成 | `#状态--已完成` | 同文件锚点不存在: #状态--已完成 |
| docs\content\ecosystem\web_frameworks\axum_deep_dive.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\content\ecosystem\web_frameworks\axum_deep_dive.md | 🏗️ 架构设计 | `#️-架构设计` | 同文件锚点不存在: #️-架构设计 |
| docs\content\ecosystem\web_frameworks\axum_deep_dive.md | **状态**: ✅ 已完成 | `#状态--已完成` | 同文件锚点不存在: #状态--已完成 |
| docs\content\ecosystem\web_frameworks\axum_deep_dive.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\content\ecosystem\web_frameworks\axum_deep_dive.md | 🏗️ 架构设计 | `#️-架构设计` | 同文件锚点不存在: #️-架构设计 |
| docs\content\ecosystem\web_frameworks\axum_deep_dive.md | **状态**: ✅ 已完成 | `#状态--已完成` | 同文件锚点不存在: #状态--已完成 |
| docs\content\emerging\async_closures.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\content\emerging\async_closures.md | ⚠️ 注意事项 | `#️-注意事项` | 同文件锚点不存在: #️-注意事项 |
| docs\content\emerging\async_closures.md | **状态**: 🧪 不稳定特性，需要 nightly | `#状态--不稳定特性需要-nightly` | 同文件锚点不存在: #状态--不稳定特性需要-nightly |
| docs\content\emerging\async_closures.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\content\emerging\async_closures.md | ⚠️ 注意事项 | `#️-注意事项` | 同文件锚点不存在: #️-注意事项 |
| docs\content\emerging\async_closures.md | **状态**: 🧪 不稳定特性，需要 nightly | `#状态--不稳定特性需要-nightly` | 同文件锚点不存在: #状态--不稳定特性需要-nightly |
| docs\content\emerging\generic_const_exprs.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\content\emerging\generic_const_exprs.md | ⚠️ 限制与注意事项 | `#️-限制与注意事项` | 同文件锚点不存在: #️-限制与注意事项 |
| docs\content\emerging\generic_const_exprs.md | **状态**: 🧪 不稳定特性，需要 nightly | `#状态--不稳定特性需要-nightly` | 同文件锚点不存在: #状态--不稳定特性需要-nightly |
| docs\content\emerging\generic_const_exprs.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\content\emerging\generic_const_exprs.md | ⚠️ 限制与注意事项 | `#️-限制与注意事项` | 同文件锚点不存在: #️-限制与注意事项 |
| docs\content\emerging\generic_const_exprs.md | **状态**: 🧪 不稳定特性，需要 nightly | `#状态--不稳定特性需要-nightly` | 同文件锚点不存在: #状态--不稳定特性需要-nightly |
| docs\content\emerging\README.md | **状态**: 🔄 持续跟踪更新 | `#状态--持续跟踪更新` | 同文件锚点不存在: #状态--持续跟踪更新 |
| docs\content\emerging\rust_1_95_preview.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\content\emerging\rust_1_95_preview.md | **状态**: 🧪 Beta 预览 | `#状态--beta-预览` | 同文件锚点不存在: #状态--beta-预览 |
| docs\content\emerging\rust_1_95_preview.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\content\emerging\rust_1_95_preview.md | **状态**: 🧪 Beta 预览 | `#状态--beta-预览` | 同文件锚点不存在: #状态--beta-预览 |
| docs\content\production\kubernetes_deployment_guide.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\content\production\kubernetes_deployment_guide.md | 🏗️ 基础架构 | `#️-基础架构` | 同文件锚点不存在: #️-基础架构 |
| docs\content\production\kubernetes_deployment_guide.md | ☸️ Kubernetes 配置 | `#️-kubernetes-配置` | 同文件锚点不存在: #️-kubernetes-配置 |
| docs\content\production\kubernetes_deployment_guide.md | 🛡️ 安全性 | `#️-安全性` | 同文件锚点不存在: #️-安全性 |
| docs\content\production\kubernetes_deployment_guide.md | **状态**: ✅ 100% 完成 | `#状态--100-完成` | 同文件锚点不存在: #状态--100-完成 |
| docs\content\production\kubernetes_deployment_guide.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\content\production\kubernetes_deployment_guide.md | 🏗️ 基础架构 | `#️-基础架构` | 同文件锚点不存在: #️-基础架构 |
| docs\content\production\kubernetes_deployment_guide.md | ☸️ Kubernetes 配置 | `#️-kubernetes-配置` | 同文件锚点不存在: #️-kubernetes-配置 |
| docs\content\production\kubernetes_deployment_guide.md | 🛡️ 安全性 | `#️-安全性` | 同文件锚点不存在: #️-安全性 |
| docs\content\production\kubernetes_deployment_guide.md | **状态**: ✅ 100% 完成 | `#状态--100-完成` | 同文件锚点不存在: #状态--100-完成 |
| docs\content\production\README.md | OpenTelemetry + Jaeger | `#opentelemetry--jaeger` | 同文件锚点不存在: #opentelemetry--jaeger |
| docs\content\production\README.md | 🛡️ 可靠性 | `#️-可靠性` | 同文件锚点不存在: #️-可靠性 |
| docs\content\production\README.md | **状态**: 🔄 持续完善中 | `#状态--持续完善中` | 同文件锚点不存在: #状态--持续完善中 |
| docs\content\representations\10_knowledge_representation_matrix.md | 📊 表征类型 × 概念领域矩阵 | `#-表征类型--概念领域矩阵` | 同文件锚点不存在: #-表征类型--概念领域矩阵 |
| docs\content\representations\10_knowledge_representation_matrix.md | 🗺️ 思维导图索引 | `#️-思维导图索引` | 同文件锚点不存在: #️-思维导图索引 |
| docs\content\representations\10_knowledge_representation_matrix.md | **状态**: 🔄 85% 完成，持续扩充中 | `#状态--85-完成持续扩充中` | 同文件锚点不存在: #状态--85-完成持续扩充中 |
| docs\content\scenarios\10_web_application_scenarios.md | **状态**: ✅ 100% 完成 | `#状态--100-完成` | 同文件锚点不存在: #状态--100-完成 |
| docs\research_notes\00_COMPREHENSIVE_SUMMARY.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\00_ORGANIZATION_AND_NAVIGATION.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\100_PERCENT_COMPLETION_VERIFICATION.md | 1. 形式化定义验证 ✅ | `#1-形式化定义验证-` | 同文件锚点不存在: #1-形式化定义验证- |
| docs\research_notes\100_PERCENT_COMPLETION_VERIFICATION.md | 2. 公理系统验证 ✅ | `#2-公理系统验证-` | 同文件锚点不存在: #2-公理系统验证- |
| docs\research_notes\100_PERCENT_COMPLETION_VERIFICATION.md | 3. 定理证明验证 ✅ | `#3-定理证明验证-` | 同文件锚点不存在: #3-定理证明验证- |
| docs\research_notes\100_PERCENT_COMPLETION_VERIFICATION.md | 4. 思维表征验证 ✅ | `#4-思维表征验证-` | 同文件锚点不存在: #4-思维表征验证- |
| docs\research_notes\100_PERCENT_COMPLETION_VERIFICATION.md | 思维导图 (11/15 = 73%) | `#思维导图-1115--73` | 同文件锚点不存在: #思维导图-1115--73 |
| docs\research_notes\100_PERCENT_COMPLETION_VERIFICATION.md | 矩阵系统 (9/12 = 75%) | `#矩阵系统-912--75` | 同文件锚点不存在: #矩阵系统-912--75 |
| docs\research_notes\100_PERCENT_COMPLETION_VERIFICATION.md | 决策树 (9/10 = 90%) | `#决策树-910--90` | 同文件锚点不存在: #决策树-910--90 |
| docs\research_notes\100_PERCENT_COMPLETION_VERIFICATION.md | 应用树 (8/8 = 100%) | `#应用树-88--100` | 同文件锚点不存在: #应用树-88--100 |
| docs\research_notes\100_PERCENT_COMPLETION_VERIFICATION.md | 5. 工具对接验证 ✅ | `#5-工具对接验证-` | 同文件锚点不存在: #5-工具对接验证- |
| docs\research_notes\100_PERCENT_COMPLETION_VERIFICATION.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\ACTUAL_COMPLETION_STATUS_2026_02_28.md | 1. 核心形式化文档 ✅ 基本完成 | `#1-核心形式化文档--基本完成` | 同文件锚点不存在: #1-核心形式化文档--基本完成 |
| docs\research_notes\ACTUAL_COMPLETION_STATUS_2026_02_28.md | 2. 类型理论文档 ✅ 基本完成 | `#2-类型理论文档--基本完成` | 同文件锚点不存在: #2-类型理论文档--基本完成 |
| docs\research_notes\ACTUAL_COMPLETION_STATUS_2026_02_28.md | 3. 软件设计理论 ✅ 基本完成 | `#3-软件设计理论--基本完成` | 同文件锚点不存在: #3-软件设计理论--基本完成 |
| docs\research_notes\ACTUAL_COMPLETION_STATUS_2026_02_28.md | 3.2 工作流模型 ✅ 完成 | `#32-工作流模型--完成` | 同文件锚点不存在: #32-工作流模型--完成 |
| docs\research_notes\ACTUAL_COMPLETION_STATUS_2026_02_28.md | 3.3 执行模型 ✅ 完成 | `#33-执行模型--完成` | 同文件锚点不存在: #33-执行模型--完成 |
| docs\research_notes\ACTUAL_COMPLETION_STATUS_2026_02_28.md | 3.4 组合工程 ✅ 完成 | `#34-组合工程--完成` | 同文件锚点不存在: #34-组合工程--完成 |
| docs\research_notes\ACTUAL_COMPLETION_STATUS_2026_02_28.md | 3.5 边界系统 ✅ 完成 | `#35-边界系统--完成` | 同文件锚点不存在: #35-边界系统--完成 |
| docs\research_notes\ACTUAL_COMPLETION_STATUS_2026_02_28.md | 4. 思维表征 ✅ 基本完成 | `#4-思维表征--基本完成` | 同文件锚点不存在: #4-思维表征--基本完成 |
| docs\research_notes\ACTUAL_COMPLETION_STATUS_2026_02_28.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\AENEAS_INTEGRATION_PLAN.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\research_notes\AENEAS_INTEGRATION_PLAN.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\AENEAS_INTEGRATION_PLAN.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\research_notes\AENEAS_INTEGRATION_PLAN.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\APPLICATION_TREES.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\research_notes\APPLICATION_TREES.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\APPLICATION_TREES.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\research_notes\APPLICATION_TREES.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\ARGUMENTATION_CHAIN_AND_FLOW.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\ARGUMENTATION_CHAIN_AND_FLOW.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\ARGUMENTATION_GAP_INDEX.md | 论证缺口与设计理由综合索引 | `#论证缺口与设计理由综合索引` | 同文件锚点不存在: #论证缺口与设计理由综合索引 |
| docs\research_notes\ARGUMENTATION_GAP_INDEX.md | 🗺️ 思维表征覆盖矩阵 {#️-思维表征覆盖矩阵} | `#️-思维表征覆盖矩阵-️-思维表征覆盖矩阵` | 同文件锚点不存在: #️-思维表征覆盖矩阵-️-思维表征覆盖矩阵 |
| docs\research_notes\ARGUMENTATION_GAP_INDEX.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\ARGUMENTATION_GAP_INDEX.md | 论证缺口与设计理由综合索引 | `#论证缺口与设计理由综合索引` | 同文件锚点不存在: #论证缺口与设计理由综合索引 |
| docs\research_notes\ARGUMENTATION_GAP_INDEX.md | 🗺️ 思维表征覆盖矩阵 {#️-思维表征覆盖矩阵} | `#️-思维表征覆盖矩阵-️-思维表征覆盖矩阵` | 同文件锚点不存在: #️-思维表征覆盖矩阵-️-思维表征覆盖矩阵 |
| docs\research_notes\ARGUMENTATION_GAP_INDEX.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\AUTHORITATIVE_ALIGNMENT_GUIDE.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\AUTHORITATIVE_ALIGNMENT_GUIDE.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\10_authoritative_alignment_status.md | 权威内容对齐状态报告 | `#权威内容对齐状态报告` | 同文件锚点不存在: #权威内容对齐状态报告 |
| docs\research_notes\10_authoritative_alignment_status.md | 一致性差异 (📝 扩展) | `#一致性差异--扩展` | 同文件锚点不存在: #一致性差异--扩展 |
| docs\research_notes\10_authoritative_alignment_status.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\10_authoritative_content_alignment_report.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\BEST_PRACTICES.md | ✍️ 编写最佳实践 {#️-编写最佳实践} | `#️-编写最佳实践-️-编写最佳实践` | 同文件锚点不存在: #️-编写最佳实践-️-编写最佳实践 |
| docs\research_notes\BEST_PRACTICES.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\BEST_PRACTICES.md | ✍️ 编写最佳实践 {#️-编写最佳实践} | `#️-编写最佳实践-️-编写最佳实践` | 同文件锚点不存在: #️-编写最佳实践-️-编写最佳实践 |
| docs\research_notes\BEST_PRACTICES.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\10_cargo_194_features.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\CLASSIFICATION.md | 研究笔记分类体系 | `#研究笔记分类体系` | 同文件锚点不存在: #研究笔记分类体系 |
| docs\research_notes\CLASSIFICATION.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | 代码-文档-形式化完整映射 | `#代码-文档-形式化完整映射` | 同文件锚点不存在: #代码-文档-形式化完整映射 |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | 代码-文档-形式化完整映射 | `#代码-文档-形式化完整映射` | 同文件锚点不存在: #代码-文档-形式化完整映射 |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C01 所有权 | `../02_reference/quick_reference/ownership_cheatsheet.md#移动语义` | 锚点不存在: #移动语义 |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C01 函数参数 | `../02_reference/quick_reference/ownership_cheatsheet.md#函数参数` | 锚点不存在: #函数参数 |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C01 借用 | `../02_reference/quick_reference/ownership_cheatsheet.md#引用与借用` | 锚点不存在: #引用与借用 |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C01 生命周期 | `../02_reference/quick_reference/ownership_cheatsheet.md#生命周期` | 锚点不存在: #生命周期 |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C01 结构体生命周期 | `../02_reference/quick_reference/ownership_cheatsheet.md#生命周期标注` | 锚点不存在: #生命周期标注 |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C04 Trait Bound | `../02_reference/quick_reference/generics_cheatsheet.md#trait-bound` | 锚点不存在: #trait-bound |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C04 Trait 定义 | `../02_reference/quick_reference/generics_cheatsheet.md#定义-trait` | 锚点不存在: #定义-trait |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C04 Trait 实现 | `../02_reference/quick_reference/generics_cheatsheet.md#实现-trait` | 锚点不存在: #实现-trait |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C05 线程 | `../02_reference/quick_reference/threads_concurrency_cheatsheet.md#创建线程` | 锚点不存在: #创建线程 |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C05 Arc + Mutex | `../02_reference/quick_reference/threads_concurrency_cheatsheet.md#共享状态并发` | 锚点不存在: #共享状态并发 |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C06 异步 | `../02_reference/quick_reference/async_patterns.md#async-函数` | 锚点不存在: #async-函数 |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C06 任务调度 | `../02_reference/quick_reference/async_patterns.md#任务调度` | 锚点不存在: #任务调度 |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C02 Vec | `../02_reference/quick_reference/type_system.md#vec` | 锚点不存在: #vec |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C02 HashMap | `../02_reference/quick_reference/type_system.md#hashmap` | 锚点不存在: #hashmap |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C02 String | `../02_reference/quick_reference/type_system.md#string` | 锚点不存在: #string |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C07 I/O | `../02_reference/quick_reference/collections_iterators_cheatsheet.md#读取文件` | 锚点不存在: #读取文件 |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C07 进程 | `../02_reference/quick_reference/process_management_cheatsheet.md#运行外部命令` | 锚点不存在: #运行外部命令 |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | 定理 2 - 所有权唯一性 | `./formal_methods/ownership_model.md#定理-2-所有权唯一性` | 锚点不存在: #定理-2-所有权唯一性 |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | 引理 1 - 资源释放 | `./formal_methods/ownership_model.md#引理-1-资源释放` | 锚点不存在: #引理-1-资源释放 |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | 定理 3 - Copy 语义 | `./formal_methods/ownership_model.md#定理-3-copy-语义` | 锚点不存在: #定理-3-copy-语义 |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | 规则 1 - 借用规则 | `./formal_methods/borrow_checker_proof.md#规则-1-借用规则` | 锚点不存在: #规则-1-借用规则 |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | 引理 2 - 切片有效性 | `./formal_methods/borrow_checker_proof.md#引理-2-切片有效性` | 锚点不存在: #引理-2-切片有效性 |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | 规则 3 - 生命周期包含 | `./formal_methods/lifetime_formalization.md#规则-3-生命周期包含` | 锚点不存在: #规则-3-生命周期包含 |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | 定理 LF-T1 - 生命周期传递 | `./formal_methods/lifetime_formalization.md#定理-lf-t1-生命周期传递` | 锚点不存在: #定理-lf-t1-生命周期传递 |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | 0, infinity) \| [定义 - 静态生命周期 | `./formal_methods/lifetime_formalization.md#定义-静态生命周期` | 锚点不存在: #定义-静态生命周期 |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | 类型规则 - Trait Bound | `./type_theory/type_system_foundations.md#类型规则-trait-bound` | 锚点不存在: #类型规则-trait-bound |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | 类型规则 - Trait 实现 | `./type_theory/type_system_foundations.md#类型规则-trait-实现` | 锚点不存在: #类型规则-trait-实现 |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | 类型规则 - Trait 对象 | `./type_theory/type_system_foundations.md#类型规则-trait-对象` | 锚点不存在: #类型规则-trait-对象 |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | 定理 C-T1 - Arc 安全 | `./formal_methods/send_sync_formalization.md#定理-c-t1-arc-安全` | 锚点不存在: #定理-c-t1-arc-安全 |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | 定理 C-T2 - Mutex 互斥 | `./formal_methods/send_sync_formalization.md#定理-c-t2-mutex-互斥` | 锚点不存在: #定理-c-t2-mutex-互斥 |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | 定理 C-T3 - 读写锁 | `./formal_methods/send_sync_formalization.md#定理-c-t3-读写锁` | 锚点不存在: #定理-c-t3-读写锁 |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | 定义 - Send | `./formal_methods/send_sync_formalization.md#定义-send` | 锚点不存在: #定义-send |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | 定义 - Sync | `./formal_methods/send_sync_formalization.md#定义-sync` | 锚点不存在: #定义-sync |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | 定义 - 异步函数 | `./formal_methods/async_state_machine.md#定义-异步函数` | 锚点不存在: #定义-异步函数 |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | 定理 A-T1 - Await 正确性 | `./formal_methods/async_state_machine.md#定理-a-t1-await-正确性` | 锚点不存在: #定理-a-t1-await-正确性 |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | 定理 A-T2 - Pin 安全性 | `./formal_methods/async_state_machine.md#定理-a-t2-pin-安全性` | 锚点不存在: #定理-a-t2-pin-安全性 |
| docs\research_notes\COGNITIVE_ARGUMENTATION_FRAMEWORK.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\10_comprehensive_project_report.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\COMPREHENSIVE_SYSTEMATIC_OVERVIEW.md | 🗺️ 思维表征方式全索引 {#️-思维表征方式全索引} | `#️-思维表征方式全索引-️-思维表征方式全索引` | 同文件锚点不存在: #️-思维表征方式全索引-️-思维表征方式全索引 |
| docs\research_notes\COMPREHENSIVE_SYSTEMATIC_OVERVIEW.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\COMPREHENSIVE_SYSTEMATIC_OVERVIEW.md | 🗺️ 思维表征方式全索引 {#️-思维表征方式全索引} | `#️-思维表征方式全索引-️-思维表征方式全索引` | 同文件锚点不存在: #️-思维表征方式全索引-️-思维表征方式全索引 |
| docs\research_notes\COMPREHENSIVE_SYSTEMATIC_OVERVIEW.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\COMPREHENSIVE_SYSTEMATIC_OVERVIEW.md | 概念-公理-定理映射表 | `#-概念-公理-定理映射表` | 同文件锚点不存在: #-概念-公理-定理映射表 |
| docs\research_notes\COMPREHENSIVE_SYSTEMATIC_OVERVIEW.md | 论证要素规范 | `FORMAL_PROOF_SYSTEM_GUIDE.md#-论证要素规范` | 锚点不存在: #-论证要素规范 |
| docs\research_notes\COMPREHENSIVE_SYSTEMATIC_OVERVIEW.md | 反例索引 | `#️-反例索引` | 同文件锚点不存在: #️-反例索引 |
| docs\research_notes\COMPREHENSIVE_SYSTEMATIC_OVERVIEW.md | FORMAL_PROOF_SYSTEM_GUIDE | `FORMAL_PROOF_SYSTEM_GUIDE.md#️-反例索引` | 锚点不存在: #️-反例索引 |
| docs\research_notes\COMPREHENSIVE_SYSTEMATIC_REVIEW_AND_100_PERCENT_PLAN.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\research_notes\COMPREHENSIVE_SYSTEMATIC_REVIEW_AND_100_PERCENT_PLAN.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\10_comprehensive_task_orchestration_100_percent.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\COMPREHENSIVE_TASK_ORCHESTRATION_2026_03_01.md | A类：归档占位文件 (6个) - 需清理或补充 | `#a类归档占位文件-6个---需清理或补充` | 同文件锚点不存在: #a类归档占位文件-6个---需清理或补充 |
| docs\research_notes\COMPREHENSIVE_TASK_ORCHESTRATION_2026_03_01.md | Phase 5: Coq骨架与L3证明 (5天 - 可选) | `#phase-5-coq骨架与l3证明-5天---可选` | 同文件锚点不存在: #phase-5-coq骨架与l3证明-5天---可选 |
| docs\research_notes\COMPREHENSIVE_TASK_ORCHESTRATION_2026_03_01.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\CONCEPT_AXIOM_THEOREM_MATRIX.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\10_concept_comparison_tables.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\CONCEPT_HIERARCHY_FRAMEWORK.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\CONCEPT_HIERARCHY_FRAMEWORK.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\CONCEPT_RELATIONSHIP_NETWORK.md | L1 元概念 → 文档 | `#l1-元概念--文档` | 同文件锚点不存在: #l1-元概念--文档 |
| docs\research_notes\CONCEPT_RELATIONSHIP_NETWORK.md | L2 核心概念 → 文档 | `#l2-核心概念--文档` | 同文件锚点不存在: #l2-核心概念--文档 |
| docs\research_notes\CONCEPT_RELATIONSHIP_NETWORK.md | L3 具体概念 → 文档 | `#l3-具体概念--文档` | 同文件锚点不存在: #l3-具体概念--文档 |
| docs\research_notes\CONCEPT_RELATIONSHIP_NETWORK.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\CONCEPT_RELATIONSHIP_NETWORK.md | L1 元概念 → 文档 | `#l1-元概念--文档` | 同文件锚点不存在: #l1-元概念--文档 |
| docs\research_notes\CONCEPT_RELATIONSHIP_NETWORK.md | L2 核心概念 → 文档 | `#l2-核心概念--文档` | 同文件锚点不存在: #l2-核心概念--文档 |
| docs\research_notes\CONCEPT_RELATIONSHIP_NETWORK.md | L3 具体概念 → 文档 | `#l3-具体概念--文档` | 同文件锚点不存在: #l3-具体概念--文档 |
| docs\research_notes\CONCEPT_RELATIONSHIP_NETWORK.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\CONCURRENCY_CHEATSHEET.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\CONST_EVAL_FORMALIZATION.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\research_notes\CONST_EVAL_FORMALIZATION.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\CONST_EVAL_FORMALIZATION.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\research_notes\CONST_EVAL_FORMALIZATION.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\CONTENT_ENHANCEMENT.md | 研究笔记内容完善指南 | `#研究笔记内容完善指南` | 同文件锚点不存在: #研究笔记内容完善指南 |
| docs\research_notes\CONTENT_ENHANCEMENT.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\CONTENT_ENHANCEMENT.md | 研究笔记内容完善指南 | `#研究笔记内容完善指南` | 同文件锚点不存在: #研究笔记内容完善指南 |
| docs\research_notes\CONTENT_ENHANCEMENT.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\CONTENT_ENHANCEMENT.md | QUALITY_CHECKLIST | `QUALITY_CHECKLIST.md#概念定义-属性关系-解释论证-层次化` | 锚点不存在: #概念定义-属性关系-解释论证-层次化 |
| docs\research_notes\CONTRIBUTING.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\CONTRIBUTING.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\COQ_ISABELLE_PROOF_SCAFFOLDING.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\COQ_OF_RUST_INTEGRATION_PLAN.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\CORE_FEATURES_FULL_CHAIN.md | Rust 核心特性完整链：定义→示例→论证→证明 | `#rust-核心特性完整链定义示例论证证明` | 同文件锚点不存在: #rust-核心特性完整链定义示例论证证明 |
| docs\research_notes\CORE_FEATURES_FULL_CHAIN.md | 13. ? 操作符 | `#13--操作符` | 同文件锚点不存在: #13--操作符 |
| docs\research_notes\CORE_FEATURES_FULL_CHAIN.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\CORE_FEATURES_FULL_CHAIN.md | Rust 核心特性完整链：定义→示例→论证→证明 | `#rust-核心特性完整链定义示例论证证明` | 同文件锚点不存在: #rust-核心特性完整链定义示例论证证明 |
| docs\research_notes\CORE_FEATURES_FULL_CHAIN.md | 13. ? 操作符 | `#13--操作符` | 同文件锚点不存在: #13--操作符 |
| docs\research_notes\CORE_FEATURES_FULL_CHAIN.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\CORE_THEOREMS_EN_SUMMARY.md | Core Theorems — English Summary | `#core-theorems--english-summary` | 同文件锚点不存在: #core-theorems--english-summary |
| docs\research_notes\CORE_THEOREMS_EN_SUMMARY.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\CORE_THEOREMS_FULL_PROOFS.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\CORE_THEOREMS_FULL_PROOFS.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\COUNTER_EXAMPLES_COMPENDIUM.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\CROSS_REFERENCE_INDEX.md | � 跨文档映射网络 - 核心索引 {#-跨文档映射网络---核心索引} | `#-跨文档映射网络---核心索引--跨文档映射网络---核心索引` | 同文件锚点不存在: #-跨文档映射网络---核心索引--跨文档映射网络---核心索引 |
| docs\research_notes\CROSS_REFERENCE_INDEX.md | 🗺️ 文档网络概览 {#️-文档网络概览} | `#️-文档网络概览-️-文档网络概览` | 同文件锚点不存在: #️-文档网络概览-️-文档网络概览 |
| docs\research_notes\CROSS_REFERENCE_INDEX.md | formal\_methods ↔ 其他文档 | `#formal_methods--其他文档` | 同文件锚点不存在: #formal_methods--其他文档 |
| docs\research_notes\CROSS_REFERENCE_INDEX.md | type\_theory ↔ 其他文档 | `#type_theory--其他文档` | 同文件锚点不存在: #type_theory--其他文档 |
| docs\research_notes\CROSS_REFERENCE_INDEX.md | software\_design\_theory ↔ 其他文档 | `#software_design_theory--其他文档` | 同文件锚点不存在: #software_design_theory--其他文档 |
| docs\research_notes\CROSS_REFERENCE_INDEX.md | 速查卡 ↔ 指南/研究笔记 | `#速查卡--指南研究笔记` | 同文件锚点不存在: #速查卡--指南研究笔记 |
| docs\research_notes\CROSS_REFERENCE_INDEX.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\CROSS_REFERENCE_INDEX.md | 🔗 跨文档映射网络 - 核心索引 {#-跨文档映射网络---核心索引} | `#-跨文档映射网络---核心索引--跨文档映射网络---核心索引` | 同文件锚点不存在: #-跨文档映射网络---核心索引--跨文档映射网络---核心索引 |
| docs\research_notes\CROSS_REFERENCE_INDEX.md | 🗺️ 文档网络概览 {#️-文档网络概览} | `#️-文档网络概览-️-文档网络概览` | 同文件锚点不存在: #️-文档网络概览-️-文档网络概览 |
| docs\research_notes\CROSS_REFERENCE_INDEX.md | formal\_methods ↔ 其他文档 | `#formal_methods--其他文档` | 同文件锚点不存在: #formal_methods--其他文档 |
| docs\research_notes\CROSS_REFERENCE_INDEX.md | type\_theory ↔ 其他文档 | `#type_theory--其他文档` | 同文件锚点不存在: #type_theory--其他文档 |
| docs\research_notes\CROSS_REFERENCE_INDEX.md | software\_design\_theory ↔ 其他文档 | `#software_design_theory--其他文档` | 同文件锚点不存在: #software_design_theory--其他文档 |
| docs\research_notes\CROSS_REFERENCE_INDEX.md | 速查卡 ↔ 指南/研究笔记 | `#速查卡--指南研究笔记` | 同文件锚点不存在: #速查卡--指南研究笔记 |
| docs\research_notes\CROSS_REFERENCE_INDEX.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\DESIGN_MECHANISM_RATIONALE.md | Rust 设计机制论证：理由与完整论证 | `#rust-设计机制论证理由与完整论证` | 同文件锚点不存在: #rust-设计机制论证理由与完整论证 |
| docs\research_notes\DESIGN_MECHANISM_RATIONALE.md | ⏱️ 生命周期：为何需要显式标注？ {#️-生命周期为何需要显式标注} | `#️-生命周期为何需要显式标注-️-生命周期为何需要显式标注` | 同文件锚点不存在: #️-生命周期为何需要显式标注-️-生命周期为何需要显式标注 |
| docs\research_notes\DESIGN_MECHANISM_RATIONALE.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\DESIGN_MECHANISM_RATIONALE.md | Rust 设计机制论证：理由与完整论证 | `#rust-设计机制论证理由与完整论证` | 同文件锚点不存在: #rust-设计机制论证理由与完整论证 |
| docs\research_notes\DESIGN_MECHANISM_RATIONALE.md | ⏱️ 生命周期：为何需要显式标注？ {#️-生命周期为何需要显式标注} | `#️-生命周期为何需要显式标注-️-生命周期为何需要显式标注` | 同文件锚点不存在: #️-生命周期为何需要显式标注-️-生命周期为何需要显式标注 |
| docs\research_notes\DESIGN_MECHANISM_RATIONALE.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\DISTRIBUTED_ARCHITECTURE_DECISION_TREE.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\DISTRIBUTED_CONCEPT_MINDMAP.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\DISTRIBUTED_PATTERNS_MATRIX.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\DISTRIBUTED_PATTERN_MATRIX.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\research_notes\DISTRIBUTED_PATTERN_MATRIX.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\DISTRIBUTED_PATTERN_MATRIX.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\research_notes\DISTRIBUTED_PATTERN_MATRIX.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\10_domain_analysis_framework.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\10_domain_analysis_framework.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\10_error_handling_cheatsheet.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\EXAMPLE.md | 研究笔记示例 | `#研究笔记示例` | 同文件锚点不存在: #研究笔记示例 |
| docs\research_notes\EXAMPLE.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\EXAMPLE.md | 研究笔记示例 | `#研究笔记示例` | 同文件锚点不存在: #研究笔记示例 |
| docs\research_notes\EXAMPLE.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\EXECUTABLE_SEMANTICS_ROADMAP.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\FAQ.md | ✍️ 贡献相关问题 {#️-贡献相关问题} | `#️-贡献相关问题-️-贡献相关问题` | 同文件锚点不存在: #️-贡献相关问题-️-贡献相关问题 |
| docs\research_notes\FAQ.md | 🛠️ 工具使用问题 {#️-工具使用问题} | `#️-工具使用问题-️-工具使用问题` | 同文件锚点不存在: #️-工具使用问题-️-工具使用问题 |
| docs\research_notes\FAQ.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\FAQ.md | ✍️ 贡献相关问题 {#️-贡献相关问题} | `#️-贡献相关问题-️-贡献相关问题` | 同文件锚点不存在: #️-贡献相关问题-️-贡献相关问题 |
| docs\research_notes\FAQ.md | 🛠️ 工具使用问题 {#️-工具使用问题} | `#️-工具使用问题-️-工具使用问题` | 同文件锚点不存在: #️-工具使用问题-️-工具使用问题 |
| docs\research_notes\FAQ.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\FAQ.md | 工具使用指南 - Coq | `./TOOLS_GUIDE.md#coq` | 锚点不存在: #coq |
| docs\research_notes\FAQ_COMPREHENSIVE.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\FAQ_COMPREHENSIVE.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\FEATURE_TEMPLATE.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\FINAL_100_PERCENT_COMPLETION_CERTIFICATION.md | 内容完整性验证 ✅ | `#内容完整性验证-` | 同文件锚点不存在: #内容完整性验证- |
| docs\research_notes\FINAL_100_PERCENT_COMPLETION_CERTIFICATION.md | 文档质量验证 ✅ | `#文档质量验证-` | 同文件锚点不存在: #文档质量验证- |
| docs\research_notes\FINAL_100_PERCENT_COMPLETION_CERTIFICATION.md | Phase 0: 审计清理 ✅ | `#phase-0-审计清理-` | 同文件锚点不存在: #phase-0-审计清理- |
| docs\research_notes\FINAL_100_PERCENT_COMPLETION_CERTIFICATION.md | Phase 1: 核心增强 ✅ | `#phase-1-核心增强-` | 同文件锚点不存在: #phase-1-核心增强- |
| docs\research_notes\FINAL_100_PERCENT_COMPLETION_CERTIFICATION.md | Phase 2: 设计模式 ✅ | `#phase-2-设计模式-` | 同文件锚点不存在: #phase-2-设计模式- |
| docs\research_notes\FINAL_100_PERCENT_COMPLETION_CERTIFICATION.md | Phase 3: 思维表征 ✅ | `#phase-3-思维表征-` | 同文件锚点不存在: #phase-3-思维表征- |
| docs\research_notes\FINAL_100_PERCENT_COMPLETION_CERTIFICATION.md | Phase 4: 实用内容 ✅ | `#phase-4-实用内容-` | 同文件锚点不存在: #phase-4-实用内容- |
| docs\research_notes\FINAL_100_PERCENT_COMPLETION_CERTIFICATION.md | Phase 5: 补充完善 ✅ | `#phase-5-补充完善-` | 同文件锚点不存在: #phase-5-补充完善- |
| docs\research_notes\FINAL_100_PERCENT_COMPLETION_CERTIFICATION.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\FINAL_100_PERCENT_COMPLETION_REPORT.md | 一、核心形式化文档 (6篇) ✅ | `#一核心形式化文档-6篇-` | 同文件锚点不存在: #一核心形式化文档-6篇- |
| docs\research_notes\FINAL_100_PERCENT_COMPLETION_REPORT.md | 二、类型理论文档 (5篇) ✅ | `#二类型理论文档-5篇-` | 同文件锚点不存在: #二类型理论文档-5篇- |
| docs\research_notes\FINAL_100_PERCENT_COMPLETION_REPORT.md | 三、软件设计理论 (42篇) ✅ | `#三软件设计理论-42篇-` | 同文件锚点不存在: #三软件设计理论-42篇- |
| docs\research_notes\FINAL_100_PERCENT_COMPLETION_REPORT.md | 四、思维表征 (48个) ✅ | `#四思维表征-48个-` | 同文件锚点不存在: #四思维表征-48个- |
| docs\research_notes\FINAL_100_PERCENT_COMPLETION_REPORT.md | 五、教程与参考 (10篇) ✅ | `#五教程与参考-10篇-` | 同文件锚点不存在: #五教程与参考-10篇- |
| docs\research_notes\FINAL_100_PERCENT_COMPLETION_REPORT.md | 六、索引与框架 (15篇) ✅ | `#六索引与框架-15篇-` | 同文件锚点不存在: #六索引与框架-15篇- |
| docs\research_notes\FINAL_100_PERCENT_COMPLETION_REPORT.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\FINAL_100_PERCENT_COMPLETION_REPORT_2026_02_28.md | 一、核心形式化文档 (11篇) ✅ | `#一核心形式化文档-11篇-` | 同文件锚点不存在: #一核心形式化文档-11篇- |
| docs\research_notes\FINAL_100_PERCENT_COMPLETION_REPORT_2026_02_28.md | 二、软件设计理论 (42篇) ✅ | `#二软件设计理论-42篇-` | 同文件锚点不存在: #二软件设计理论-42篇- |
| docs\research_notes\FINAL_100_PERCENT_COMPLETION_REPORT_2026_02_28.md | 三、思维表征 (48个) ✅ | `#三思维表征-48个-` | 同文件锚点不存在: #三思维表征-48个- |
| docs\research_notes\FINAL_100_PERCENT_COMPLETION_REPORT_2026_02_28.md | 四、教程与参考 (10篇) ✅ | `#四教程与参考-10篇-` | 同文件锚点不存在: #四教程与参考-10篇- |
| docs\research_notes\FINAL_100_PERCENT_COMPLETION_REPORT_2026_02_28.md | 五、索引与框架 (15篇) ✅ | `#五索引与框架-15篇-` | 同文件锚点不存在: #五索引与框架-15篇- |
| docs\research_notes\FINAL_100_PERCENT_COMPLETION_REPORT_2026_02_28.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\FINAL_COMPLETION_PROGRESS_REPORT_2026_02_28.md | Phase 0: 全面审计与清理 ✅ | `#phase-0-全面审计与清理-` | 同文件锚点不存在: #phase-0-全面审计与清理- |
| docs\research_notes\FINAL_COMPLETION_PROGRESS_REPORT_2026_02_28.md | Phase 1-4: 文档扩展 ✅ | `#phase-1-4-文档扩展-` | 同文件锚点不存在: #phase-1-4-文档扩展- |
| docs\research_notes\FINAL_COMPLETION_PROGRESS_REPORT_2026_02_28.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\FINAL_VERIFICATION_CHECKLIST.md | 一、文档完整性验证 ✅ | `#一文档完整性验证-` | 同文件锚点不存在: #一文档完整性验证- |
| docs\research_notes\FINAL_VERIFICATION_CHECKLIST.md | 二、内容质量验证 ✅ | `#二内容质量验证-` | 同文件锚点不存在: #二内容质量验证- |
| docs\research_notes\FINAL_VERIFICATION_CHECKLIST.md | 三、功能性验证 ✅ | `#三功能性验证-` | 同文件锚点不存在: #三功能性验证- |
| docs\research_notes\FINAL_VERIFICATION_CHECKLIST.md | 四、统计验证 ✅ | `#四统计验证-` | 同文件锚点不存在: #四统计验证- |
| docs\research_notes\FINAL_VERIFICATION_CHECKLIST.md | 五、最终检查 ✅ | `#五最终检查-` | 同文件锚点不存在: #五最终检查- |
| docs\research_notes\FINAL_VERIFICATION_CHECKLIST.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\FORMAL_ARGUMENTATION_COMPLETION_REPORT.md | 一、逻辑基础 (2篇) ✅ | `#一逻辑基础-2篇-` | 同文件锚点不存在: #一逻辑基础-2篇- |
| docs\research_notes\FORMAL_ARGUMENTATION_COMPLETION_REPORT.md | 二、程序语义 (2篇) ✅ | `#二程序语义-2篇-` | 同文件锚点不存在: #二程序语义-2篇- |
| docs\research_notes\FORMAL_ARGUMENTATION_COMPLETION_REPORT.md | 三、证明技术 (2篇) ✅ | `#三证明技术-2篇-` | 同文件锚点不存在: #三证明技术-2篇- |
| docs\research_notes\FORMAL_ARGUMENTATION_COMPLETION_REPORT.md | 四、方法学 (3篇) ✅ | `#四方法学-3篇-` | 同文件锚点不存在: #四方法学-3篇- |
| docs\research_notes\FORMAL_ARGUMENTATION_COMPLETION_REPORT.md | 理论 → Rust映射 | `#理论--rust映射` | 同文件锚点不存在: #理论--rust映射 |
| docs\research_notes\FORMAL_ARGUMENTATION_COMPLETION_REPORT.md | **最后更新**: 2026-03-14 | `#最后更新-2026-03-14` | 同文件锚点不存在: #最后更新-2026-03-14 |
| docs\research_notes\FORMAL_CONCEPTS_ENCYCLOPEDIA.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\FORMAL_FULL_MODEL_EN_SUMMARY.md | Rust Formal Full Model — English Summary | `#rust-formal-full-model--english-summary` | 同文件锚点不存在: #rust-formal-full-model--english-summary |
| docs\research_notes\FORMAL_FULL_MODEL_EN_SUMMARY.md | Axiom → Composition Theorem DAG (Pillars 1+3) | `#axiom--composition-theorem-dag-pillars-13` | 同文件锚点不存在: #axiom--composition-theorem-dag-pillars-13 |
| docs\research_notes\FORMAL_FULL_MODEL_EN_SUMMARY.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\FORMAL_FULL_MODEL_OVERVIEW.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\FORMAL_FULL_MODEL_OVERVIEW.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\FORMAL_LANGUAGE_AND_PROOFS.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\10_formal_methods_master_index.md | 应用树 (8/8) ✅ 完成 | `#应用树-88--完成` | 同文件锚点不存在: #应用树-88--完成 |
| docs\research_notes\10_formal_methods_master_index.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\FORMAL_PROOF_CRITICAL_ANALYSIS_AND_PLAN_2026_02.md | 形式化证明批判性分析与计划 2026-02 | `#形式化证明批判性分析与计划-2026-02` | 同文件锚点不存在: #形式化证明批判性分析与计划-2026-02 |
| docs\research_notes\FORMAL_PROOF_CRITICAL_ANALYSIS_AND_PLAN_2026_02.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\FORMAL_PROOF_SYSTEM_GUIDE.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\FORMAL_VERIFICATION_GUIDE.md | 🛠️ 工具选择 {#️-工具选择} | `#️-工具选择-️-工具选择` | 同文件锚点不存在: #️-工具选择-️-工具选择 |
| docs\research_notes\FORMAL_VERIFICATION_GUIDE.md | 工具链扩展任务（Rust → 证明助手） | `#工具链扩展任务rust--证明助手` | 同文件锚点不存在: #工具链扩展任务rust--证明助手 |
| docs\research_notes\FORMAL_VERIFICATION_GUIDE.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\FORMAL_VERIFICATION_GUIDE.md | 🛠️ 工具选择 {#️-工具选择} | `#️-工具选择-️-工具选择` | 同文件锚点不存在: #️-工具选择-️-工具选择 |
| docs\research_notes\FORMAL_VERIFICATION_GUIDE.md | 工具链扩展任务（Rust → 证明助手） | `#工具链扩展任务rust--证明助手` | 同文件锚点不存在: #工具链扩展任务rust--证明助手 |
| docs\research_notes\FORMAL_VERIFICATION_GUIDE.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\GETTING_STARTED.md | ✍️ 第四步：创建研究笔记 {#️-第四步创建研究笔记} | `#️-第四步创建研究笔记-️-第四步创建研究笔记` | 同文件锚点不存在: #️-第四步创建研究笔记-️-第四步创建研究笔记 |
| docs\research_notes\GETTING_STARTED.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\GETTING_STARTED.md | ✍️ 第四步：创建研究笔记 {#️-第四步创建研究笔记} | `#️-第四步创建研究笔记-️-第四步创建研究笔记` | 同文件锚点不存在: #️-第四步创建研究笔记-️-第四步创建研究笔记 |
| docs\research_notes\GETTING_STARTED.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\GLOSSARY.md | 🔬 类型理论术语（A–V） {#a-1} | `#-类型理论术语av-a-1` | 同文件锚点不存在: #-类型理论术语av-a-1 |
| docs\research_notes\GLOSSARY.md | 🛠️ 工具术语 {#️-工具术语} | `#️-工具术语-️-工具术语` | 同文件锚点不存在: #️-工具术语-️-工具术语 |
| docs\research_notes\GLOSSARY.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\GLOSSARY.md | 🔬 类型理论术语（A–V） {#a-1} | `#-类型理论术语av-a-1` | 同文件锚点不存在: #-类型理论术语av-a-1 |
| docs\research_notes\GLOSSARY.md | 🛠️ 工具术语 {#️-工具术语} | `#️-工具术语-️-工具术语` | 同文件锚点不存在: #️-工具术语-️-工具术语 |
| docs\research_notes\GLOSSARY.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\GLOSSARY.md | 工具使用指南 - Coq | `./TOOLS_GUIDE.md#coq` | 锚点不存在: #coq |
| docs\research_notes\GLOSSARY.md | 工具使用指南 - Lean | `./TOOLS_GUIDE.md#lean` | 锚点不存在: #lean |
| docs\research_notes\HIERARCHICAL_MAPPING_AND_SUMMARY.md | 二、概念族 ↔ 文档 ↔ Def/Axiom/定理 映射表 | `#二概念族--文档--defaxiom定理-映射表` | 同文件锚点不存在: #二概念族--文档--defaxiom定理-映射表 |
| docs\research_notes\HIERARCHICAL_MAPPING_AND_SUMMARY.md | 三、文档 ↔ 思维表征 映射表 | `#三文档--思维表征-映射表` | 同文件锚点不存在: #三文档--思维表征-映射表 |
| docs\research_notes\HIERARCHICAL_MAPPING_AND_SUMMARY.md | 3.1 按文档 → 思维表征 | `#31-按文档--思维表征` | 同文件锚点不存在: #31-按文档--思维表征 |
| docs\research_notes\HIERARCHICAL_MAPPING_AND_SUMMARY.md | 3.2 按思维表征 → 文档（入口） | `#32-按思维表征--文档入口` | 同文件锚点不存在: #32-按思维表征--文档入口 |
| docs\research_notes\HIERARCHICAL_MAPPING_AND_SUMMARY.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\HIERARCHICAL_MAPPING_AND_SUMMARY.md | 二、概念族 ↔ 文档 ↔ Def/Axiom/定理 映射表 | `#二概念族--文档--defaxiom定理-映射表` | 同文件锚点不存在: #二概念族--文档--defaxiom定理-映射表 |
| docs\research_notes\HIERARCHICAL_MAPPING_AND_SUMMARY.md | 三、文档 ↔ 思维表征 映射表 | `#三文档--思维表征-映射表` | 同文件锚点不存在: #三文档--思维表征-映射表 |
| docs\research_notes\HIERARCHICAL_MAPPING_AND_SUMMARY.md | 3.1 按文档 → 思维表征 | `#31-按文档--思维表征` | 同文件锚点不存在: #31-按文档--思维表征 |
| docs\research_notes\HIERARCHICAL_MAPPING_AND_SUMMARY.md | 3.2 按思维表征 → 文档（入口） | `#32-按思维表征--文档入口` | 同文件锚点不存在: #32-按思维表征--文档入口 |
| docs\research_notes\HIERARCHICAL_MAPPING_AND_SUMMARY.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\INCREMENTAL_UPDATE_FLOW.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\INCREMENTAL_UPDATE_FLOW.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\INDEX.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\INTERNATIONAL_FORMAL_VERIFICATION_INDEX.md | 国际 Rust 形式化验证成果对标索引 | `#国际-rust-形式化验证成果对标索引` | 同文件锚点不存在: #国际-rust-形式化验证成果对标索引 |
| docs\research_notes\INTERNATIONAL_FORMAL_VERIFICATION_INDEX.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\INTERVIEW_QUESTIONS_COLLECTION.md | ⭐ 基础题 | `#-基础题-1` | 同文件锚点不存在: #-基础题-1 |
| docs\research_notes\INTERVIEW_QUESTIONS_COLLECTION.md | ⭐⭐ 进阶题 | `#-进阶题-1` | 同文件锚点不存在: #-进阶题-1 |
| docs\research_notes\INTERVIEW_QUESTIONS_COLLECTION.md | ⭐⭐⭐ 高级题 | `#-高级题-1` | 同文件锚点不存在: #-高级题-1 |
| docs\research_notes\INTERVIEW_QUESTIONS_COLLECTION.md | ⭐⭐⭐⭐ 专家题 | `#-专家题-1` | 同文件锚点不存在: #-专家题-1 |
| docs\research_notes\INTERVIEW_QUESTIONS_COLLECTION.md | ⭐ 基础题 | `#-基础题-2` | 同文件锚点不存在: #-基础题-2 |
| docs\research_notes\INTERVIEW_QUESTIONS_COLLECTION.md | ⭐⭐ 进阶题 | `#-进阶题-2` | 同文件锚点不存在: #-进阶题-2 |
| docs\research_notes\INTERVIEW_QUESTIONS_COLLECTION.md | ⭐⭐⭐ 高级题 | `#-高级题-2` | 同文件锚点不存在: #-高级题-2 |
| docs\research_notes\INTERVIEW_QUESTIONS_COLLECTION.md | ⭐⭐⭐⭐ 专家题 | `#-专家题-2` | 同文件锚点不存在: #-专家题-2 |
| docs\research_notes\INTERVIEW_QUESTIONS_COLLECTION.md | ⭐⭐ 进阶题 | `#-进阶题-3` | 同文件锚点不存在: #-进阶题-3 |
| docs\research_notes\INTERVIEW_QUESTIONS_COLLECTION.md | ⭐⭐⭐ 高级题 | `#-高级题-3` | 同文件锚点不存在: #-高级题-3 |
| docs\research_notes\INTERVIEW_QUESTIONS_COLLECTION.md | ⭐⭐ 进阶题 | `#-进阶题-4` | 同文件锚点不存在: #-进阶题-4 |
| docs\research_notes\INTERVIEW_QUESTIONS_COLLECTION.md | ⭐⭐⭐ 高级题 | `#-高级题-4` | 同文件锚点不存在: #-高级题-4 |
| docs\research_notes\INTERVIEW_QUESTIONS_COLLECTION.md | ⭐⭐⭐⭐ 专家题 | `#-专家题-3` | 同文件锚点不存在: #-专家题-3 |
| docs\research_notes\INTERVIEW_QUESTIONS_COLLECTION.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\L3_MACHINE_PROOF_GUIDE.md | L3机器可检查证明实施指南 | `#l3机器可检查证明实施指南` | 同文件锚点不存在: #l3机器可检查证明实施指南 |
| docs\research_notes\L3_MACHINE_PROOF_GUIDE.md | 2.1 推荐方案: Coq + Iris | `#21-推荐方案-coq--iris` | 同文件锚点不存在: #21-推荐方案-coq--iris |
| docs\research_notes\L3_MACHINE_PROOF_GUIDE.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\LANGUAGE_SEMANTICS_EXPRESSIVENESS.md | Rust 编程语言：构造性语义形式化与表达能力边界 | `#rust-编程语言构造性语义形式化与表达能力边界` | 同文件锚点不存在: #rust-编程语言构造性语义形式化与表达能力边界 |
| docs\research_notes\LANGUAGE_SEMANTICS_EXPRESSIVENESS.md | 🏛️ 指称语义与构造性语义 {#️-指称语义与构造性语义} | `#️-指称语义与构造性语义-️-指称语义与构造性语义` | 同文件锚点不存在: #️-指称语义与构造性语义-️-指称语义与构造性语义 |
| docs\research_notes\LANGUAGE_SEMANTICS_EXPRESSIVENESS.md | 🗺️ 思维表征：语义-表达式能力矩阵 {#️-思维表征语义-表达式能力矩阵} | `#️-思维表征语义-表达式能力矩阵-️-思维表征语义-表达式能力矩阵` | 同文件锚点不存在: #️-思维表征语义-表达式能力矩阵-️-思维表征语义-表达式能力矩阵 |
| docs\research_notes\LANGUAGE_SEMANTICS_EXPRESSIVENESS.md | ⚠️ 反例：表达能力边界 violation {#️-反例表达能力边界-violation} | `#️-反例表达能力边界-violation-️-反例表达能力边界-violation` | 同文件锚点不存在: #️-反例表达能力边界-violation-️-反例表达能力边界-violation |
| docs\research_notes\LANGUAGE_SEMANTICS_EXPRESSIVENESS.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\LANGUAGE_SEMANTICS_EXPRESSIVENESS.md | Rust 编程语言：构造性语义形式化与表达能力边界 | `#rust-编程语言构造性语义形式化与表达能力边界` | 同文件锚点不存在: #rust-编程语言构造性语义形式化与表达能力边界 |
| docs\research_notes\LANGUAGE_SEMANTICS_EXPRESSIVENESS.md | 🏛️ 指称语义与构造性语义 {#️-指称语义与构造性语义} | `#️-指称语义与构造性语义-️-指称语义与构造性语义` | 同文件锚点不存在: #️-指称语义与构造性语义-️-指称语义与构造性语义 |
| docs\research_notes\LANGUAGE_SEMANTICS_EXPRESSIVENESS.md | 🗺️ 思维表征：语义-表达式能力矩阵 {#️-思维表征语义-表达式能力矩阵} | `#️-思维表征语义-表达式能力矩阵-️-思维表征语义-表达式能力矩阵` | 同文件锚点不存在: #️-思维表征语义-表达式能力矩阵-️-思维表征语义-表达式能力矩阵 |
| docs\research_notes\LANGUAGE_SEMANTICS_EXPRESSIVENESS.md | ⚠️ 反例：表达能力边界 violation {#️-反例表达能力边界-violation} | `#️-反例表达能力边界-violation-️-反例表达能力边界-violation` | 同文件锚点不存在: #️-反例表达能力边界-violation-️-反例表达能力边界-violation |
| docs\research_notes\LANGUAGE_SEMANTICS_EXPRESSIVENESS.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\10_learning_path_comprehensive.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\LIFETIME_CHEATSHEET.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\MACROS_CHEATSHEET.md | println! / format | `#println--format` | 同文件锚点不存在: #println--format |
| docs\research_notes\MACROS_CHEATSHEET.md | todo! / unimplemented | `#todo--unimplemented` | 同文件锚点不存在: #todo--unimplemented |
| docs\research_notes\MACROS_CHEATSHEET.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\MAINTENANCE_GUIDE.md | 🛠️ 维护工具 {#️-维护工具} | `#️-维护工具-️-维护工具` | 同文件锚点不存在: #️-维护工具-️-维护工具 |
| docs\research_notes\MAINTENANCE_GUIDE.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\MAINTENANCE_GUIDE.md | 🛠️ 维护工具 {#️-维护工具} | `#️-维护工具-️-维护工具` | 同文件锚点不存在: #️-维护工具-️-维护工具 |
| docs\research_notes\MAINTENANCE_GUIDE.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\OWNERSHIP_CONCEPT_MINDMAP.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\practical_applications.md | 实际应用案例研究 | `#实际应用案例研究` | 同文件锚点不存在: #实际应用案例研究 |
| docs\research_notes\practical_applications.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\practical_applications.md | 实际应用案例研究 | `#实际应用案例研究` | 同文件锚点不存在: #实际应用案例研究 |
| docs\research_notes\practical_applications.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\PROGRESS_TRACKING.md | 研究进展跟踪 | `#研究进展跟踪` | 同文件锚点不存在: #研究进展跟踪 |
| docs\research_notes\PROGRESS_TRACKING.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\PROGRESS_TRACKING.md | 研究进展跟踪 | `#研究进展跟踪` | 同文件锚点不存在: #研究进展跟踪 |
| docs\research_notes\PROGRESS_TRACKING.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\10_project_completion_summary.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\PROJECT_MAINTENANCE_GUIDE.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\PROOF_INDEX.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\PROOF_INDEX.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\PROOF_INDEX.md | ownership_model.md | `./formal_methods/ownership_model.md#定理-2-所有权唯一性` | 锚点不存在: #定理-2-所有权唯一性 |
| docs\research_notes\PROOF_INDEX.md | ownership_model.md | `./formal_methods/ownership_model.md#定理-3-内存安全框架` | 锚点不存在: #定理-3-内存安全框架 |
| docs\research_notes\PROOF_INDEX.md | borrow_checker_proof.md | `./formal_methods/borrow_checker_proof.md#定理-2-借用规则正确性` | 锚点不存在: #定理-2-借用规则正确性 |
| docs\research_notes\PROOF_INDEX.md | type_system_foundations.md | `./type_theory/type_system_foundations.md#定理-1-进展性` | 锚点不存在: #定理-1-进展性 |
| docs\research_notes\PROOF_INDEX.md | type_system_foundations.md | `./type_theory/type_system_foundations.md#定理-2-保持性` | 锚点不存在: #定理-2-保持性 |
| docs\research_notes\PROOF_INDEX.md | type_system_foundations.md | `./type_theory/type_system_foundations.md#定理-3-类型安全` | 锚点不存在: #定理-3-类型安全 |
| docs\research_notes\PROOF_INDEX.md | type_system_foundations.md | `./type_theory/type_system_foundations.md#定理-4-类型推导正确性` | 锚点不存在: #定理-4-类型推导正确性 |
| docs\research_notes\PROOF_INDEX.md | type_system_foundations.md | `./type_theory/type_system_foundations.md#定理-5-类型推导算法正确性` | 锚点不存在: #定理-5-类型推导算法正确性 |
| docs\research_notes\PROOF_INDEX.md | ownership_model.md | `./formal_methods/ownership_model.md#定理-2-所有权唯一性` | 锚点不存在: #定理-2-所有权唯一性 |
| docs\research_notes\PROOF_INDEX.md | ownership_model.md | `./formal_methods/ownership_model.md#定理-3-内存安全框架` | 锚点不存在: #定理-3-内存安全框架 |
| docs\research_notes\PROOF_INDEX.md | type_system_foundations.md | `./type_theory/type_system_foundations.md#定理-3-类型安全` | 锚点不存在: #定理-3-类型安全 |
| docs\research_notes\PROOF_INDEX.md | borrow_checker_proof.md | `./formal_methods/borrow_checker_proof.md#定理-2-借用规则正确性` | 锚点不存在: #定理-2-借用规则正确性 |
| docs\research_notes\PROOF_INDEX.md | type_system_foundations.md | `./type_theory/type_system_foundations.md#定理-4-类型推导正确性` | 锚点不存在: #定理-4-类型推导正确性 |
| docs\research_notes\PROOF_INDEX.md | type_system_foundations.md | `./type_theory/type_system_foundations.md#定理-5-类型推导算法正确性` | 锚点不存在: #定理-5-类型推导算法正确性 |
| docs\research_notes\PROOF_TECHNIQUES_MINDMAP.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\PROOF_TREE_BORROW.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\PROOF_TREE_OWNERSHIP.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\PROOF_TREE_TYPE_SAFETY.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\QUALITY_CHECKLIST.md | 证明目标 / 实验目标 | `#证明目标--实验目标` | 同文件锚点不存在: #证明目标--实验目标 |
| docs\research_notes\QUALITY_CHECKLIST.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\QUICK_FIND.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\QUICK_FIND.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\QUICK_REFERENCE.md | 🛠️ 常用工具快速查找 | `#️-常用工具快速查找` | 同文件锚点不存在: #️-常用工具快速查找 |
| docs\research_notes\QUICK_REFERENCE.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\10_readme_100_percent_completion.md | Research Notes 100% 完成计划 - 总览与入口 | `#research-notes-100-完成计划---总览与入口` | 同文件锚点不存在: #research-notes-100-完成计划---总览与入口 |
| docs\research_notes\10_readme_100_percent_completion.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\research_methodology.md | 研究方法论 | `#研究方法论` | 同文件锚点不存在: #研究方法论 |
| docs\research_notes\research_methodology.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\research_methodology.md | 研究方法论 | `#研究方法论` | 同文件锚点不存在: #研究方法论 |
| docs\research_notes\research_methodology.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\RESEARCH_NOTES_ORGANIZATION.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\RESEARCH_ROADMAP.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\RESEARCH_ROADMAP.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\RESOURCES.md | 🛠️ 工具资源 {#️-工具资源} | `#️-工具资源-️-工具资源` | 同文件锚点不存在: #️-工具资源-️-工具资源 |
| docs\research_notes\RESOURCES.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\RESOURCES.md | 🛠️ 工具资源 {#️-工具资源} | `#️-工具资源-️-工具资源` | 同文件锚点不存在: #️-工具资源-️-工具资源 |
| docs\research_notes\RESOURCES.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\RESOURCES.md | 工具使用指南 - Coq | `./TOOLS_GUIDE.md#coq` | 锚点不存在: #coq |
| docs\research_notes\RESOURCES.md | 工具使用指南 - Lean | `./TOOLS_GUIDE.md#lean` | 锚点不存在: #lean |
| docs\research_notes\RUSTBELT_ALIGNMENT.md | RustBelt 逐章对标 | `#rustbelt-逐章对标` | 同文件锚点不存在: #rustbelt-逐章对标 |
| docs\research_notes\RUSTBELT_ALIGNMENT.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\RUSTSEM_SEMANTICS.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\research_notes\RUSTSEM_SEMANTICS.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\RUSTSEM_SEMANTICS.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\research_notes\RUSTSEM_SEMANTICS.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\RUST_191_RESEARCH_UPDATE_2025_11_15.md | Rust 1.91.1 研究更新报告 | `#rust-1911-研究更新报告` | 同文件锚点不存在: #rust-1911-研究更新报告 |
| docs\research_notes\RUST_191_RESEARCH_UPDATE_2025_11_15.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\RUST_192_RESEARCH_UPDATE_2025_12_11.md | Rust 1.92.0 研究更新报告（历史记录） | `#rust-1920-研究更新报告历史记录` | 同文件锚点不存在: #rust-1920-研究更新报告历史记录 |
| docs\research_notes\RUST_192_RESEARCH_UPDATE_2025_12_11.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\RUST_193_COUNTEREXAMPLES_INDEX.md | Rust 1.93 相关反例与边界集中索引 | `#rust-193-相关反例与边界集中索引` | 同文件锚点不存在: #rust-193-相关反例与边界集中索引 |
| docs\research_notes\RUST_193_COUNTEREXAMPLES_INDEX.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\RUST_193_COUNTEREXAMPLES_INDEX.md | Rust 1.93 相关反例与边界集中索引 | `#rust-193-相关反例与边界集中索引` | 同文件锚点不存在: #rust-193-相关反例与边界集中索引 |
| docs\research_notes\RUST_193_COUNTEREXAMPLES_INDEX.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\RUST_193_FEATURE_MATRIX.md | Rust 1.93 特性族多维概念矩阵 | `#rust-193-特性族多维概念矩阵` | 同文件锚点不存在: #rust-193-特性族多维概念矩阵 |
| docs\research_notes\RUST_193_FEATURE_MATRIX.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\RUST_193_FEATURE_MATRIX.md | Rust 1.93 特性族多维概念矩阵 | `#rust-193-特性族多维概念矩阵` | 同文件锚点不存在: #rust-193-特性族多维概念矩阵 |
| docs\research_notes\RUST_193_FEATURE_MATRIX.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\10_rust_194_195_feature_matrix.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\10_rust_194_comprehensive_analysis.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\RUST_194_COMPREHENSIVE_SEMANTICS_FRAMEWORK.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\research_notes\RUST_194_COMPREHENSIVE_SEMANTICS_FRAMEWORK.md | 🕸️ 关系映射网络 | `#️-关系映射网络` | 同文件锚点不存在: #️-关系映射网络 |
| docs\research_notes\RUST_194_COMPREHENSIVE_SEMANTICS_FRAMEWORK.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\RUST_194_COMPREHENSIVE_SEMANTICS_FRAMEWORK.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\research_notes\RUST_194_COMPREHENSIVE_SEMANTICS_FRAMEWORK.md | 🕸️ 关系映射网络 | `#️-关系映射网络` | 同文件锚点不存在: #️-关系映射网络 |
| docs\research_notes\RUST_194_COMPREHENSIVE_SEMANTICS_FRAMEWORK.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\10_rust_194_core_notes_index.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\RUST_194_DEEP_SEMANTIC_ANALYSIS.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\research_notes\RUST_194_DEEP_SEMANTIC_ANALYSIS.md | 1. array\_windows - 数组窗口迭代的语义革命 | `#1-array_windows---数组窗口迭代的语义革命` | 同文件锚点不存在: #1-array_windows---数组窗口迭代的语义革命 |
| docs\research_notes\RUST_194_DEEP_SEMANTIC_ANALYSIS.md | 2. ControlFlow - 控制流的形式化抽象 | `#2-controlflow---控制流的形式化抽象` | 同文件锚点不存在: #2-controlflow---控制流的形式化抽象 |
| docs\research_notes\RUST_194_DEEP_SEMANTIC_ANALYSIS.md | 3. LazyCell/LazyLock 新方法 - 延迟初始化的语义完善 | `#3-lazycelllazylock-新方法---延迟初始化的语义完善` | 同文件锚点不存在: #3-lazycelllazylock-新方法---延迟初始化的语义完善 |
| docs\research_notes\RUST_194_DEEP_SEMANTIC_ANALYSIS.md | 4. Peekable 增强 - 迭代器组合子的语义扩展 | `#4-peekable-增强---迭代器组合子的语义扩展` | 同文件锚点不存在: #4-peekable-增强---迭代器组合子的语义扩展 |
| docs\research_notes\RUST_194_DEEP_SEMANTIC_ANALYSIS.md | 5. 数学常量 - 数值语义的精确化 | `#5-数学常量---数值语义的精确化` | 同文件锚点不存在: #5-数学常量---数值语义的精确化 |
| docs\research_notes\RUST_194_DEEP_SEMANTIC_ANALYSIS.md | 6. TOML 1.1 - 配置语义的现代化 | `#6-toml-11---配置语义的现代化` | 同文件锚点不存在: #6-toml-11---配置语义的现代化 |
| docs\research_notes\RUST_194_DEEP_SEMANTIC_ANALYSIS.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\RUST_194_DEEP_SEMANTIC_ANALYSIS.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\research_notes\RUST_194_DEEP_SEMANTIC_ANALYSIS.md | 1. array\_windows - 数组窗口迭代的语义革命 | `#1-array_windows---数组窗口迭代的语义革命` | 同文件锚点不存在: #1-array_windows---数组窗口迭代的语义革命 |
| docs\research_notes\RUST_194_DEEP_SEMANTIC_ANALYSIS.md | 2. ControlFlow - 控制流的形式化抽象 | `#2-controlflow---控制流的形式化抽象` | 同文件锚点不存在: #2-controlflow---控制流的形式化抽象 |
| docs\research_notes\RUST_194_DEEP_SEMANTIC_ANALYSIS.md | 3. LazyCell/LazyLock 新方法 - 延迟初始化的语义完善 | `#3-lazycelllazylock-新方法---延迟初始化的语义完善` | 同文件锚点不存在: #3-lazycelllazylock-新方法---延迟初始化的语义完善 |
| docs\research_notes\RUST_194_DEEP_SEMANTIC_ANALYSIS.md | 4. Peekable 增强 - 迭代器组合子的语义扩展 | `#4-peekable-增强---迭代器组合子的语义扩展` | 同文件锚点不存在: #4-peekable-增强---迭代器组合子的语义扩展 |
| docs\research_notes\RUST_194_DEEP_SEMANTIC_ANALYSIS.md | 5. 数学常量 - 数值语义的精确化 | `#5-数学常量---数值语义的精确化` | 同文件锚点不存在: #5-数学常量---数值语义的精确化 |
| docs\research_notes\RUST_194_DEEP_SEMANTIC_ANALYSIS.md | 6. TOML 1.1 - 配置语义的现代化 | `#6-toml-11---配置语义的现代化` | 同文件锚点不存在: #6-toml-11---配置语义的现代化 |
| docs\research_notes\RUST_194_DEEP_SEMANTIC_ANALYSIS.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\10_rust_194_mind_representations.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\RUST_194_RESEARCH_UPDATE.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\research_notes\RUST_194_RESEARCH_UPDATE.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\RUST_194_RESEARCH_UPDATE.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\research_notes\RUST_194_RESEARCH_UPDATE.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\10_rust_book_alignment.md | Rust Book → 本项目映射 | `#rust-book--本项目映射` | 同文件锚点不存在: #rust-book--本项目映射 |
| docs\research_notes\10_rust_book_alignment.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\RUST_FORMAL_METHODS_CHEATSHEET.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\SAFE_DECIDABLE_MECHANISMS_OVERVIEW.md | 安全可判定机制总览 | `#安全可判定机制总览` | 同文件锚点不存在: #安全可判定机制总览 |
| docs\research_notes\SAFE_DECIDABLE_MECHANISMS_OVERVIEW.md | 3.9 match / for / ? | `#39-match--for--` | 同文件锚点不存在: #39-match--for-- |
| docs\research_notes\SAFE_DECIDABLE_MECHANISMS_OVERVIEW.md | 3.10 通道 / Mutex / thread::spawn | `#310-通道--mutex--threadspawn` | 同文件锚点不存在: #310-通道--mutex--threadspawn |
| docs\research_notes\SAFE_DECIDABLE_MECHANISMS_OVERVIEW.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS.md | Rust 安全与非安全全面论证与分析 | `#rust-安全与非安全全面论证与分析` | 同文件锚点不存在: #rust-安全与非安全全面论证与分析 |
| docs\research_notes\SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS.md | Rust 安全与非安全全面论证与分析 | `#rust-安全与非安全全面论证与分析` | 同文件锚点不存在: #rust-安全与非安全全面论证与分析 |
| docs\research_notes\SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\STATISTICS.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\STATISTICS.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\SYSTEM_INTEGRATION.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\SYSTEM_INTEGRATION.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\SYSTEM_SUMMARY.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\SYSTEM_SUMMARY.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\TASK_CHECKLIST.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\TASK_CHECKLIST.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\TEMPLATE.md | 🔬 形式化定义 / 实验设计 {#-形式化定义--实验设计} | `#-形式化定义--实验设计--形式化定义--实验设计` | 同文件锚点不存在: #-形式化定义--实验设计--形式化定义--实验设计 |
| docs\research_notes\TEMPLATE.md | ⚠️ 反例（如适用） {#️-反例如适用} | `#️-反例如适用-️-反例如适用` | 同文件锚点不存在: #️-反例如适用-️-反例如适用 |
| docs\research_notes\TEMPLATE.md | ✅ 证明目标 / 实验目标 {#-证明目标--实验目标} | `#-证明目标--实验目标--证明目标--实验目标` | 同文件锚点不存在: #-证明目标--实验目标--证明目标--实验目标 |
| docs\research_notes\TEMPLATE.md | 待证明的性质 / 待测试的场景 | `#待证明的性质--待测试的场景` | 同文件锚点不存在: #待证明的性质--待测试的场景 |
| docs\research_notes\TEMPLATE.md | 证明方法 / 测试方法 | `#证明方法--测试方法` | 同文件锚点不存在: #证明方法--测试方法 |
| docs\research_notes\TEMPLATE.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\TEMPLATE.md | 🔬 形式化定义 / 实验设计 {#-形式化定义--实验设计} | `#-形式化定义--实验设计--形式化定义--实验设计` | 同文件锚点不存在: #-形式化定义--实验设计--形式化定义--实验设计 |
| docs\research_notes\TEMPLATE.md | ⚠️ 反例（如适用） {#️-反例如适用} | `#️-反例如适用-️-反例如适用` | 同文件锚点不存在: #️-反例如适用-️-反例如适用 |
| docs\research_notes\TEMPLATE.md | ✅ 证明目标 / 实验目标 {#-证明目标--实验目标} | `#-证明目标--实验目标--证明目标--实验目标` | 同文件锚点不存在: #-证明目标--实验目标--证明目标--实验目标 |
| docs\research_notes\TEMPLATE.md | 待证明的性质 / 待测试的场景 | `#待证明的性质--待测试的场景` | 同文件锚点不存在: #待证明的性质--待测试的场景 |
| docs\research_notes\TEMPLATE.md | 证明方法 / 测试方法 | `#证明方法--测试方法` | 同文件锚点不存在: #证明方法--测试方法 |
| docs\research_notes\TEMPLATE.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\THEOREMS_AND_PROOF_STRATEGIES.md | 3.2 证明策略：进展 + 保持 | `#32-证明策略进展--保持` | 同文件锚点不存在: #32-证明策略进展--保持 |
| docs\research_notes\THEOREMS_AND_PROOF_STRATEGIES.md | L1 → L2 → L3 映射 | `#l1--l2--l3-映射` | 同文件锚点不存在: #l1--l2--l3-映射 |
| docs\research_notes\THEOREMS_AND_PROOF_STRATEGIES.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\THEOREM_RUST_EXAMPLE_MAPPING.md | 定理 ↔ Rust 示例完整映射 | `#定理--rust-示例完整映射` | 同文件锚点不存在: #定理--rust-示例完整映射 |
| docs\research_notes\THEOREM_RUST_EXAMPLE_MAPPING.md | T-TY1: 类型安全定理 (进展性 + 保持性) | `#t-ty1-类型安全定理-进展性--保持性` | 同文件锚点不存在: #t-ty1-类型安全定理-进展性--保持性 |
| docs\research_notes\THEOREM_RUST_EXAMPLE_MAPPING.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\THEORETICAL_AND_ARGUMENTATION_SYSTEM_ARCHITECTURE.md | Rust 形式化研究：理论体系与论证体系结构 | `#rust-形式化研究理论体系与论证体系结构` | 同文件锚点不存在: #rust-形式化研究理论体系与论证体系结构 |
| docs\research_notes\THEORETICAL_AND_ARGUMENTATION_SYSTEM_ARCHITECTURE.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\THEORETICAL_AND_ARGUMENTATION_SYSTEM_ARCHITECTURE.md | Rust 形式化研究：理论体系与论证体系结构 | `#rust-形式化研究理论体系与论证体系结构` | 同文件锚点不存在: #rust-形式化研究理论体系与论证体系结构 |
| docs\research_notes\THEORETICAL_AND_ARGUMENTATION_SYSTEM_ARCHITECTURE.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\TOOLS_GUIDE.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\TOOLS_GUIDE.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\TUTORIAL_BORROW_CHECKER.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\TUTORIAL_CONCURRENCY_MODELS.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\TUTORIAL_LIFETIMES.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\TUTORIAL_OWNERSHIP_SAFETY.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\TUTORIAL_TYPE_SYSTEM.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\UNIFIED_SYSTEMATIC_FRAMEWORK.md | Rust 研究笔记：全局统一系统化框架 | `#rust-研究笔记全局统一系统化框架` | 同文件锚点不存在: #rust-研究笔记全局统一系统化框架 |
| docs\research_notes\UNIFIED_SYSTEMATIC_FRAMEWORK.md | 🕸️ 全局思维导图：Rust 形式化知识全景 {#️-全局思维导图rust-形式化知识全景} | `#️-全局思维导图rust-形式化知识全景-️-全局思维导图rust-形式化知识全景` | 同文件锚点不存在: #️-全局思维导图rust-形式化知识全景-️-全局思维导图rust-形式化知识全景 |
| docs\research_notes\UNIFIED_SYSTEMATIC_FRAMEWORK.md | ⚠️ 反例总索引 {#️-反例总索引} | `#️-反例总索引-️-反例总索引` | 同文件锚点不存在: #️-反例总索引-️-反例总索引 |
| docs\research_notes\UNIFIED_SYSTEMATIC_FRAMEWORK.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\UNIFIED_SYSTEMATIC_FRAMEWORK.md | Rust 研究笔记：全局统一系统化框架 | `#rust-研究笔记全局统一系统化框架` | 同文件锚点不存在: #rust-研究笔记全局统一系统化框架 |
| docs\research_notes\UNIFIED_SYSTEMATIC_FRAMEWORK.md | 🕸️ 全局思维导图：Rust 形式化知识全景 {#️-全局思维导图rust-形式化知识全景} | `#️-全局思维导图rust-形式化知识全景-️-全局思维导图rust-形式化知识全景` | 同文件锚点不存在: #️-全局思维导图rust-形式化知识全景-️-全局思维导图rust-形式化知识全景 |
| docs\research_notes\UNIFIED_SYSTEMATIC_FRAMEWORK.md | ⚠️ 反例总索引 {#️-反例总索引} | `#️-反例总索引-️-反例总索引` | 同文件锚点不存在: #️-反例总索引-️-反例总索引 |
| docs\research_notes\UNIFIED_SYSTEMATIC_FRAMEWORK.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\USER_GUIDE.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\VERIFICATION_TOOLS_DECISION_TREE.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\research_notes\VERIFICATION_TOOLS_DECISION_TREE.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\VERIFICATION_TOOLS_DECISION_TREE.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\research_notes\VERIFICATION_TOOLS_DECISION_TREE.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\VERIFICATION_TOOLS_MATRIX.md | 1. Miri - 内存安全检查器 | `#1-miri---内存安全检查器` | 同文件锚点不存在: #1-miri---内存安全检查器 |
| docs\research_notes\VERIFICATION_TOOLS_MATRIX.md | 2. Kani - 位精确模型检查器 | `#2-kani---位精确模型检查器` | 同文件锚点不存在: #2-kani---位精确模型检查器 |
| docs\research_notes\VERIFICATION_TOOLS_MATRIX.md | 3. Prusti - 契约式验证 | `#3-prusti---契约式验证` | 同文件锚点不存在: #3-prusti---契约式验证 |
| docs\research_notes\VERIFICATION_TOOLS_MATRIX.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\VISUALIZATION_INDEX.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\VISUALIZATION_INDEX.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\WORKFLOW_CONCEPT_MINDMAP.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\WORKFLOW_ENGINE_MATRIX.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\research_notes\WORKFLOW_ENGINE_MATRIX.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\WORKFLOW_ENGINE_MATRIX.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\research_notes\WORKFLOW_ENGINE_MATRIX.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\WRITING_GUIDE.md | ✍️ 写作技巧 {#️-写作技巧} | `#️-写作技巧-️-写作技巧` | 同文件锚点不存在: #️-写作技巧-️-写作技巧 |
| docs\research_notes\WRITING_GUIDE.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\WRITING_GUIDE.md | ✍️ 写作技巧 {#️-写作技巧} | `#️-写作技巧-️-写作技巧` | 同文件锚点不存在: #️-写作技巧-️-写作技巧 |
| docs\research_notes\WRITING_GUIDE.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\WRITING_GUIDE.md | 文档标题 | `#文档标题` | 同文件锚点不存在: #文档标题 |
| docs\research_notes\WRITING_GUIDE.md | Rust 实现 | `#rust-实现` | 同文件锚点不存在: #rust-实现 |
| docs\research_notes\WRITING_GUIDE.md | 边界 | `#边界` | 同文件锚点不存在: #边界 |
| docs\research_notes\coq_skeleton\10_week1_completion_summary.md | 已完成 ✅ | `#已完成-` | 同文件锚点不存在: #已完成- |
| docs\research_notes\coq_skeleton\10_week1_completion_summary.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\experiments\compiler_optimizations.md | 编译器优化研究 | `#编译器优化研究` | 同文件锚点不存在: #编译器优化研究 |
| docs\research_notes\experiments\compiler_optimizations.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\experiments\compiler_optimizations.md | 编译器优化研究 | `#编译器优化研究` | 同文件锚点不存在: #编译器优化研究 |
| docs\research_notes\experiments\compiler_optimizations.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\experiments\concurrency_performance.md | 并发性能研究 | `#并发性能研究` | 同文件锚点不存在: #并发性能研究 |
| docs\research_notes\experiments\concurrency_performance.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\experiments\concurrency_performance.md | 并发性能研究 | `#并发性能研究` | 同文件锚点不存在: #并发性能研究 |
| docs\research_notes\experiments\concurrency_performance.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\experiments\macro_expansion_performance.md | 宏展开性能研究 | `#宏展开性能研究` | 同文件锚点不存在: #宏展开性能研究 |
| docs\research_notes\experiments\macro_expansion_performance.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\experiments\macro_expansion_performance.md | 宏展开性能研究 | `#宏展开性能研究` | 同文件锚点不存在: #宏展开性能研究 |
| docs\research_notes\experiments\macro_expansion_performance.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\experiments\memory_analysis.md | 内存分析研究 | `#内存分析研究` | 同文件锚点不存在: #内存分析研究 |
| docs\research_notes\experiments\memory_analysis.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\experiments\memory_analysis.md | 内存分析研究 | `#内存分析研究` | 同文件锚点不存在: #内存分析研究 |
| docs\research_notes\experiments\memory_analysis.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\experiments\performance_benchmarks.md | 性能基准测试研究 | `#性能基准测试研究` | 同文件锚点不存在: #性能基准测试研究 |
| docs\research_notes\experiments\performance_benchmarks.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\experiments\performance_benchmarks.md | 性能基准测试研究 | `#性能基准测试研究` | 同文件锚点不存在: #性能基准测试研究 |
| docs\research_notes\experiments\performance_benchmarks.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\experiments\README.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\00_completeness_gaps.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\10_algorithm_selection_decision_tree.md | **状态**: ✅ 100% 完成 | `#状态--100-完成` | 同文件锚点不存在: #状态--100-完成 |
| docs\research_notes\formal_methods\APPLICATION_TREES.md | Rust应用场景映射树 - 应用树集合 | `#rust应用场景映射树---应用树集合` | 同文件锚点不存在: #rust应用场景映射树---应用树集合 |
| docs\research_notes\formal_methods\APPLICATION_TREES.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\ASYNC_CONCEPT_MINDMAP.md | join! - 并行等待 | `#join---并行等待` | 同文件锚点不存在: #join---并行等待 |
| docs\research_notes\formal_methods\ASYNC_CONCEPT_MINDMAP.md | select! - 竞赛等待 | `#select---竞赛等待` | 同文件锚点不存在: #select---竞赛等待 |
| docs\research_notes\formal_methods\ASYNC_CONCEPT_MINDMAP.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\ASYNC_RUNTIME_DECISION_TREE.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\async_state_machine.md | 示例 5：并发场景 - 多个 Future 并发执行 | `#示例-5并发场景---多个-future-并发执行` | 同文件锚点不存在: #示例-5并发场景---多个-future-并发执行 |
| docs\research_notes\formal_methods\async_state_machine.md | 示例 6：状态转换 - Waker 使用 | `#示例-6状态转换---waker-使用` | 同文件锚点不存在: #示例-6状态转换---waker-使用 |
| docs\research_notes\formal_methods\async_state_machine.md | ⚠️ 反例：违反异步安全规则 {#️-反例违反异步安全规则} | `#️-反例违反异步安全规则-️-反例违反异步安全规则` | 同文件锚点不存在: #️-反例违反异步安全规则-️-反例违反异步安全规则 |
| docs\research_notes\formal_methods\async_state_machine.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\async_state_machine.md | 示例 5：并发场景 - 多个 Future 并发执行 | `#示例-5并发场景---多个-future-并发执行` | 同文件锚点不存在: #示例-5并发场景---多个-future-并发执行 |
| docs\research_notes\formal_methods\async_state_machine.md | 示例 6：状态转换 - Waker 使用 | `#示例-6状态转换---waker-使用` | 同文件锚点不存在: #示例-6状态转换---waker-使用 |
| docs\research_notes\formal_methods\async_state_machine.md | ⚠️ 反例：违反异步安全规则 {#️-反例违反异步安全规则} | `#️-反例违反异步安全规则-️-反例违反异步安全规则` | 同文件锚点不存在: #️-反例违反异步安全规则-️-反例违反异步安全规则 |
| docs\research_notes\formal_methods\async_state_machine.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\AXIOMATIC_SEMANTICS.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\borrow_checker_proof.md | ⚠️ 反例：违反借用规则导致数据竞争 {#️-反例违反借用规则导致数据竞争} | `#️-反例违反借用规则导致数据竞争-️-反例违反借用规则导致数据竞争` | 同文件锚点不存在: #️-反例违反借用规则导致数据竞争-️-反例违反借用规则导致数据竞争 |
| docs\research_notes\formal_methods\borrow_checker_proof.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\borrow_checker_proof.md | ⚠️ 反例：违反借用规则导致数据竞争 {#️-反例违反借用规则导致数据竞争} | `#️-反例违反借用规则导致数据竞争-️-反例违反借用规则导致数据竞争` | 同文件锚点不存在: #️-反例违反借用规则导致数据竞争-️-反例违反借用规则导致数据竞争 |
| docs\research_notes\formal_methods\borrow_checker_proof.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\CONCEPT_AXIOM_THEOREM_MATRIX.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\CONCURRENCY_CONCEPT_MINDMAP.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\CONCURRENCY_SAFETY_MATRIX.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\10_control_flow_decision_tree.md | **状态**: ✅ 100% 完成 | `#状态--100-完成` | 同文件锚点不存在: #状态--100-完成 |
| docs\research_notes\formal_methods\COQ_FORMALIZATION_GUIDE.md | 2.3 代码示例 + Coq证明脚本 | `#23-代码示例--coq证明脚本` | 同文件锚点不存在: #23-代码示例--coq证明脚本 |
| docs\research_notes\formal_methods\COQ_FORMALIZATION_GUIDE.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\COQ_FORMALIZATION_GUIDE.md | 2.3 代码示例 + Coq证明脚本 | `#23-代码示例--coq证明脚本` | 同文件锚点不存在: #23-代码示例--coq证明脚本 |
| docs\research_notes\formal_methods\COQ_FORMALIZATION_GUIDE.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\10_design_pattern_concept_mindmap.md | 设计模式概念族谱 - 思维导图 | `#设计模式概念族谱---思维导图` | 同文件锚点不存在: #设计模式概念族谱---思维导图 |
| docs\research_notes\formal_methods\10_design_pattern_concept_mindmap.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\DESIGN_PATTERN_SELECTION_DECISION_TREE.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\DISTRIBUTED_ARCHITECTURE_DECISION_TREE.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\DISTRIBUTED_CONCEPT_MINDMAP.md | 分布式模式概念族谱 - 思维导图 | `#分布式模式概念族谱---思维导图` | 同文件锚点不存在: #分布式模式概念族谱---思维导图 |
| docs\research_notes\formal_methods\DISTRIBUTED_CONCEPT_MINDMAP.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\DISTRIBUTED_PATTERNS_MATRIX.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\ERROR_HANDLING_DECISION_TREE.md | 维度 1: 错误类型 - 可恢复 vs 不可恢复 | `#维度-1-错误类型---可恢复-vs-不可恢复` | 同文件锚点不存在: #维度-1-错误类型---可恢复-vs-不可恢复 |
| docs\research_notes\formal_methods\ERROR_HANDLING_DECISION_TREE.md | ❌ 反模式 3: 错误的 `?` 使用导致信息丢失 | `#-反模式-3-错误的--使用导致信息丢失` | 同文件锚点不存在: #-反模式-3-错误的--使用导致信息丢失 |
| docs\research_notes\formal_methods\ERROR_HANDLING_DECISION_TREE.md | 完整示例 3: anyhow + thiserror 混合使用 | `#完整示例-3-anyhow--thiserror-混合使用` | 同文件锚点不存在: #完整示例-3-anyhow--thiserror-混合使用 |
| docs\research_notes\formal_methods\ERROR_HANDLING_DECISION_TREE.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\ERROR_HANDLING_MINDMAP.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\ERROR_TYPE_SELECTION_DECISION_TREE.md | `Option<T>` - 值可能存在 | `#optiont---值可能存在` | 同文件锚点不存在: #optiont---值可能存在 |
| docs\research_notes\formal_methods\ERROR_TYPE_SELECTION_DECISION_TREE.md | `Result<T, E>` - 操作可能失败 | `#resultt-e---操作可能失败` | 同文件锚点不存在: #resultt-e---操作可能失败 |
| docs\research_notes\formal_methods\ERROR_TYPE_SELECTION_DECISION_TREE.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\FIVE_DIMENSIONAL_CONCEPT_MATRIX.md | 所有权 × 借用 | `#所有权--借用` | 同文件锚点不存在: #所有权--借用 |
| docs\research_notes\formal_methods\FIVE_DIMENSIONAL_CONCEPT_MATRIX.md | 生命周期 × 类型系统 | `#生命周期--类型系统` | 同文件锚点不存在: #生命周期--类型系统 |
| docs\research_notes\formal_methods\FIVE_DIMENSIONAL_CONCEPT_MATRIX.md | 并发 × 所有权 | `#并发--所有权` | 同文件锚点不存在: #并发--所有权 |
| docs\research_notes\formal_methods\FIVE_DIMENSIONAL_CONCEPT_MATRIX.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\FORMAL_FOUNDATIONS_INDEX.md | 理论 → 实践映射 | `#理论--实践映射` | 同文件锚点不存在: #理论--实践映射 |
| docs\research_notes\formal_methods\FORMAL_FOUNDATIONS_INDEX.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\10_formal_methods_100_percent_completion_report.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\FORMAL_METHODS_COMPARISON.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\FORMAL_METHODS_COMPLETENESS_CHECKLIST.md | 六篇 × 六维 完备性矩阵 | `#六篇--六维-完备性矩阵` | 同文件锚点不存在: #六篇--六维-完备性矩阵 |
| docs\research_notes\formal_methods\FORMAL_METHODS_COMPLETENESS_CHECKLIST.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\10_formal_methods_completion_plan.md | 1. 证明树 (Proof Trees) - 4个待完成 | `#1-证明树-proof-trees---4个待完成` | 同文件锚点不存在: #1-证明树-proof-trees---4个待完成 |
| docs\research_notes\formal_methods\10_formal_methods_completion_plan.md | 2. Coq L3 证明 - 5个待完成 | `#2-coq-l3-证明---5个待完成` | 同文件锚点不存在: #2-coq-l3-证明---5个待完成 |
| docs\research_notes\formal_methods\10_formal_methods_completion_plan.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\IMPLEMENTATION_PROGRESS_MATRIX.md | Phase 0: 审计与清理 ✅ | `#phase-0-审计与清理-` | 同文件锚点不存在: #phase-0-审计与清理- |
| docs\research_notes\formal_methods\IMPLEMENTATION_PROGRESS_MATRIX.md | Phase 1: 核心形式化增强 ✅ | `#phase-1-核心形式化增强-` | 同文件锚点不存在: #phase-1-核心形式化增强- |
| docs\research_notes\formal_methods\IMPLEMENTATION_PROGRESS_MATRIX.md | Phase 2: 设计模式扩展 ✅ | `#phase-2-设计模式扩展-` | 同文件锚点不存在: #phase-2-设计模式扩展- |
| docs\research_notes\formal_methods\IMPLEMENTATION_PROGRESS_MATRIX.md | Phase 3: 思维表征增强 ✅ | `#phase-3-思维表征增强-` | 同文件锚点不存在: #phase-3-思维表征增强- |
| docs\research_notes\formal_methods\IMPLEMENTATION_PROGRESS_MATRIX.md | Phase 4: 教程与实用内容 ✅ | `#phase-4-教程与实用内容-` | 同文件锚点不存在: #phase-4-教程与实用内容- |
| docs\research_notes\formal_methods\IMPLEMENTATION_PROGRESS_MATRIX.md | Phase 5: Coq骨架与L3证明 🔄 | `#phase-5-coq骨架与l3证明-` | 同文件锚点不存在: #phase-5-coq骨架与l3证明- |
| docs\research_notes\formal_methods\IMPLEMENTATION_PROGRESS_MATRIX.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\LEARNING_PROGRESSION_MATRIX.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\lifetime_formalization.md | ⚠️ 反例：违反生命周期规则 {#️-反例违反生命周期规则} | `#️-反例违反生命周期规则-️-反例违反生命周期规则` | 同文件锚点不存在: #️-反例违反生命周期规则-️-反例违反生命周期规则 |
| docs\research_notes\formal_methods\lifetime_formalization.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\lifetime_formalization.md | ⚠️ 反例：违反生命周期规则 {#️-反例违反生命周期规则} | `#️-反例违反生命周期规则-️-反例违反生命周期规则` | 同文件锚点不存在: #️-反例违反生命周期规则-️-反例违反生命周期规则 |
| docs\research_notes\formal_methods\lifetime_formalization.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\LOGICAL_FOUNDATIONS.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\10_macro_hygiene_deep_dive.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\MACRO_SYSTEM_MINDMAP.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\MEMORY_MODEL_MINDMAP.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\OWNERSHIP_CONCEPT_MINDMAP.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\ownership_model.md | ⚠️ 反例：违反所有权规则 {#️-反例违反所有权规则} | `#️-反例违反所有权规则-️-反例违反所有权规则` | 同文件锚点不存在: #️-反例违反所有权规则-️-反例违反所有权规则 |
| docs\research_notes\formal_methods\ownership_model.md | 示例 8: 复杂所有权场景 - 结构体字段移动 | `#示例-8-复杂所有权场景---结构体字段移动` | 同文件锚点不存在: #示例-8-复杂所有权场景---结构体字段移动 |
| docs\research_notes\formal_methods\ownership_model.md | 示例 9: 错误示例 - 使用已移动的值 | `#示例-9-错误示例---使用已移动的值` | 同文件锚点不存在: #示例-9-错误示例---使用已移动的值 |
| docs\research_notes\formal_methods\ownership_model.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\ownership_model.md | ⚠️ 反例：违反所有权规则 {#️-反例违反所有权规则} | `#️-反例违反所有权规则-️-反例违反所有权规则` | 同文件锚点不存在: #️-反例违反所有权规则-️-反例违反所有权规则 |
| docs\research_notes\formal_methods\ownership_model.md | 示例 8: 复杂所有权场景 - 结构体字段移动 | `#示例-8-复杂所有权场景---结构体字段移动` | 同文件锚点不存在: #示例-8-复杂所有权场景---结构体字段移动 |
| docs\research_notes\formal_methods\ownership_model.md | 示例 9: 错误示例 - 使用已移动的值 | `#示例-9-错误示例---使用已移动的值` | 同文件锚点不存在: #示例-9-错误示例---使用已移动的值 |
| docs\research_notes\formal_methods\ownership_model.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\OWNERSHIP_TRANSFER_DECISION_TREE.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\PARADIGM_COMPARISON_MATRIX.md | 📊 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\research_notes\formal_methods\PARADIGM_COMPARISON_MATRIX.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\PARADIGM_COMPARISON_MATRIX.md | 📊 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\research_notes\formal_methods\PARADIGM_COMPARISON_MATRIX.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\pin_self_referential.md | ⚠️ 反例：违反 Pin 规则 {#️-反例违反-pin-规则} | `#️-反例违反-pin-规则-️-反例违反-pin-规则` | 同文件锚点不存在: #️-反例违反-pin-规则-️-反例违反-pin-规则 |
| docs\research_notes\formal_methods\pin_self_referential.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\pin_self_referential.md | ⚠️ 反例：违反 Pin 规则 {#️-反例违反-pin-规则} | `#️-反例违反-pin-规则-️-反例违反-pin-规则` | 同文件锚点不存在: #️-反例违反-pin-规则-️-反例违反-pin-规则 |
| docs\research_notes\formal_methods\pin_self_referential.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\10_process_management_decision_tree.md | **状态**: ✅ 100% 完成 | `#状态--100-完成` | 同文件锚点不存在: #状态--100-完成 |
| docs\research_notes\formal_methods\PROOF_COMPLETION_MATRIX.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\PROOF_STRATEGIES.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\PROOF_TECHNIQUES_MINDMAP.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\10_proof_trees_additional.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\10_proof_trees_enhanced.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\10_proof_trees_visualization.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\PROOF_TREES_VISUAL_COMPLETION.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\research_notes\formal_methods\PROOF_TREES_VISUAL_COMPLETION.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\PROOF_TREES_VISUAL_COMPLETION.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\research_notes\formal_methods\PROOF_TREES_VISUAL_COMPLETION.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\10_proof_tree_async_concurrency.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\10_proof_tree_send_sync.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\PROOF_TREE_TYPE_SAFETY.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\10_proof_tree_variance.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\README.md | 7. Actor 模型形式化 ⭐ 新增 | `#7-actor-模型形式化--新增` | 同文件锚点不存在: #7-actor-模型形式化--新增 |
| docs\research_notes\formal_methods\README.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\10_reference_cycles_formalization.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\RISK_ASSESSMENT_MATRIX.md | 1. 依赖库漏洞 (🔴 高) | `#1-依赖库漏洞--高` | 同文件锚点不存在: #1-依赖库漏洞--高 |
| docs\research_notes\formal_methods\RISK_ASSESSMENT_MATRIX.md | 2. 遗留系统集成 (🔴 高) | `#2-遗留系统集成--高` | 同文件锚点不存在: #2-遗留系统集成--高 |
| docs\research_notes\formal_methods\RISK_ASSESSMENT_MATRIX.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\SAFE_DECIDABLE_MECHANISMS_AND_FORMAL_METHODS_PLAN.md | 3.2 全 92 项特性维度说明（与 RUST\_193 一致 + 四维） | `#32-全-92-项特性维度说明与-rust_193-一致--四维` | 同文件锚点不存在: #32-全-92-项特性维度说明与-rust_193-一致--四维 |
| docs\research_notes\formal_methods\SAFE_DECIDABLE_MECHANISMS_AND_FORMAL_METHODS_PLAN.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\send_sync_formalization.md | 🔬 形式化定义 {#-形式化定义} {#defs-send1send-sync1sendsync-形式化} | `#-形式化定义--形式化定义-defs-send1send-sync1sendsync-形式化` | 同文件锚点不存在: #-形式化定义--形式化定义-defs-send1send-sync1sendsync-形式化 |
| docs\research_notes\formal_methods\send_sync_formalization.md | ⚠️ 反例 {#️-反例} | `#️-反例-️-反例` | 同文件锚点不存在: #️-反例-️-反例 |
| docs\research_notes\formal_methods\send_sync_formalization.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\send_sync_formalization.md | 🔬 形式化定义 {#-形式化定义} {#defs-send1send-sync1sendsync-形式化} | `#-形式化定义--形式化定义-defs-send1send-sync1sendsync-形式化` | 同文件锚点不存在: #-形式化定义--形式化定义-defs-send1send-sync1sendsync-形式化 |
| docs\research_notes\formal_methods\send_sync_formalization.md | ⚠️ 反例 {#️-反例} | `#️-反例-️-反例` | 同文件锚点不存在: #️-反例-️-反例 |
| docs\research_notes\formal_methods\send_sync_formalization.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\SEPARATION_LOGIC.md | 1.2 分离蕴含 (-) | `#12-分离蕴含` | 同文件锚点不存在: #12-分离蕴含 |
| docs\research_notes\formal_methods\SERIALIZATION_DECISION_TREE.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\10_slice_formalization.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\TESTING_STRATEGY_DECISION_TREE.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\TYPE_SYSTEM_CONCEPT_MINDMAP.md | 6.1  never类型 (!) | `#61--never类型-` | 同文件锚点不存在: #61--never类型- |
| docs\research_notes\formal_methods\TYPE_SYSTEM_CONCEPT_MINDMAP.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\UNSAFE_CONCEPT_MINDMAP.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\10_unsafe_safety_proof_tree.md | **状态**: ✅ 100% 完成 | `#状态--100-完成` | 同文件锚点不存在: #状态--100-完成 |
| docs\research_notes\formal_methods\VARIANCE_CONCEPT_MINDMAP.md | 1.1 协变 (Covariant) + | `#11-协变-covariant-` | 同文件锚点不存在: #11-协变-covariant- |
| docs\research_notes\formal_methods\VARIANCE_CONCEPT_MINDMAP.md | 1.2 逆变 (Contravariant) - | `#12-逆变-contravariant--` | 同文件锚点不存在: #12-逆变-contravariant-- |
| docs\research_notes\formal_methods\VARIANCE_CONCEPT_MINDMAP.md | 1.3 不变 (Invariant) = | `#13-不变-invariant-` | 同文件锚点不存在: #13-不变-invariant- |
| docs\research_notes\formal_methods\VARIANCE_CONCEPT_MINDMAP.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\VERIFICATION_TOOLS_DECISION_TREE.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\VERIFICATION_TOOLS_MATRIX.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\WORKFLOW_CONCEPT_MINDMAP.md | 工作流概念族谱 - 思维导图 | `#工作流概念族谱---思维导图` | 同文件锚点不存在: #工作流概念族谱---思维导图 |
| docs\research_notes\formal_methods\WORKFLOW_CONCEPT_MINDMAP.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_methods\WORKFLOW_ENGINES_MATRIX.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\formal_modules\FORMALIZATION_ECOLOGY_MINDMAP.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\00_MASTER_INDEX.md | 软件设计理论体系：主索引 | `#软件设计理论体系主索引` | 同文件锚点不存在: #软件设计理论体系主索引 |
| docs\research_notes\software_design_theory\00_MASTER_INDEX.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\06_rust_idioms.md | Rust 惯用模式与设计理论衔接 | `#rust-惯用模式与设计理论衔接` | 同文件锚点不存在: #rust-惯用模式与设计理论衔接 |
| docs\research_notes\software_design_theory\06_rust_idioms.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\07_anti_patterns.md | 反模式与边界 | `#反模式与边界` | 同文件锚点不存在: #反模式与边界 |
| docs\research_notes\software_design_theory\07_anti_patterns.md | 二、13 反例索引（与 FORMAL\_PROOF\_SYSTEM\_GUIDE 衔接） | `#二13-反例索引与-formal_proof_system_guide-衔接` | 同文件锚点不存在: #二13-反例索引与-formal_proof_system_guide-衔接 |
| docs\research_notes\software_design_theory\07_anti_patterns.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\07_anti_patterns.md | FORMAL_PROOF_SYSTEM_GUIDE | `../FORMAL_PROOF_SYSTEM_GUIDE.md#设计模式反例` | 锚点不存在: #设计模式反例 |
| docs\research_notes\software_design_theory\07_anti_patterns.md | FORMAL_PROOF_SYSTEM_GUIDE | `../FORMAL_PROOF_SYSTEM_GUIDE.md#设计模式反例` | 锚点不存在: #设计模式反例 |
| docs\research_notes\software_design_theory\COMPREHENSIVE_ARGUMENTATION_GAP_ANALYSIS_AND_PLAN.md | 设计模式、分布式模式、工作流模式全面论证缺口分析与推进计划 | `#设计模式分布式模式工作流模式全面论证缺口分析与推进计划` | 同文件锚点不存在: #设计模式分布式模式工作流模式全面论证缺口分析与推进计划 |
| docs\research_notes\software_design_theory\COMPREHENSIVE_ARGUMENTATION_GAP_ANALYSIS_AND_PLAN.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\README.md | FORMAL_PROOF_SYSTEM_GUIDE | `../FORMAL_PROOF_SYSTEM_GUIDE.md#设计模式反例` | 锚点不存在: #设计模式反例 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\04_boundary_matrix.md | 设计模式边界矩阵汇总 | `#设计模式边界矩阵汇总` | 同文件锚点不存在: #设计模式边界矩阵汇总 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\04_boundary_matrix.md | 模式 × 三维边界 | `#模式--三维边界` | 同文件锚点不存在: #模式--三维边界 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\04_boundary_matrix.md | 选型决策树（模式 → 边界） | `#选型决策树模式--边界` | 同文件锚点不存在: #选型决策树模式--边界 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\04_boundary_matrix.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\README.md | FORMAL_PROOF_SYSTEM_GUIDE | `../../../research_notes/FORMAL_PROOF_SYSTEM_GUIDE.md#设计模式反例` | 锚点不存在: #设计模式反例 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\01_creational\abstract_factory.md | Abstract Factory 形式化分析 | `#abstract-factory-形式化分析` | 同文件锚点不存在: #abstract-factory-形式化分析 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\01_creational\abstract_factory.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\01_creational\abstract_factory.md | Abstract Factory 形式化分析 | `#abstract-factory-形式化分析` | 同文件锚点不存在: #abstract-factory-形式化分析 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\01_creational\abstract_factory.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\01_creational\abstract_factory.md | GoF | `../README.md#与-gof-原书对应` | 锚点不存在: #与-gof-原书对应 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\01_creational\builder.md | Builder 形式化分析 | `#builder-形式化分析` | 同文件锚点不存在: #builder-形式化分析 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\01_creational\builder.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\01_creational\builder.md | Builder 形式化分析 | `#builder-形式化分析` | 同文件锚点不存在: #builder-形式化分析 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\01_creational\builder.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\01_creational\builder.md | GoF | `../README.md#与-gof-原书对应` | 锚点不存在: #与-gof-原书对应 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\01_creational\factory_method.md | Factory Method 形式化分析 | `#factory-method-形式化分析` | 同文件锚点不存在: #factory-method-形式化分析 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\01_creational\factory_method.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\01_creational\factory_method.md | Factory Method 形式化分析 | `#factory-method-形式化分析` | 同文件锚点不存在: #factory-method-形式化分析 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\01_creational\factory_method.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\01_creational\factory_method.md | GoF | `../README.md#与-gof-原书对应` | 锚点不存在: #与-gof-原书对应 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\01_creational\prototype.md | Prototype 形式化分析 | `#prototype-形式化分析` | 同文件锚点不存在: #prototype-形式化分析 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\01_creational\prototype.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\01_creational\prototype.md | Prototype 形式化分析 | `#prototype-形式化分析` | 同文件锚点不存在: #prototype-形式化分析 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\01_creational\prototype.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\01_creational\prototype.md | GoF | `../README.md#与-gof-原书对应` | 锚点不存在: #与-gof-原书对应 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\01_creational\singleton.md | Singleton 形式化分析 | `#singleton-形式化分析` | 同文件锚点不存在: #singleton-形式化分析 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\01_creational\singleton.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\01_creational\singleton.md | Singleton 形式化分析 | `#singleton-形式化分析` | 同文件锚点不存在: #singleton-形式化分析 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\01_creational\singleton.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\01_creational\singleton.md | GoF | `../README.md#与-gof-原书对应` | 锚点不存在: #与-gof-原书对应 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\adapter.md | Adapter 形式化分析 | `#adapter-形式化分析` | 同文件锚点不存在: #adapter-形式化分析 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\adapter.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\adapter.md | Adapter 形式化分析 | `#adapter-形式化分析` | 同文件锚点不存在: #adapter-形式化分析 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\adapter.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\adapter.md | GoF | `../README.md#与-gof-原书对应` | 锚点不存在: #与-gof-原书对应 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\bridge.md | Bridge 形式化分析 | `#bridge-形式化分析` | 同文件锚点不存在: #bridge-形式化分析 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\bridge.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\bridge.md | Bridge 形式化分析 | `#bridge-形式化分析` | 同文件锚点不存在: #bridge-形式化分析 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\bridge.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\bridge.md | GoF | `../README.md#与-gof-原书对应` | 锚点不存在: #与-gof-原书对应 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\composite.md | Composite 形式化分析 | `#composite-形式化分析` | 同文件锚点不存在: #composite-形式化分析 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\composite.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\composite.md | Composite 形式化分析 | `#composite-形式化分析` | 同文件锚点不存在: #composite-形式化分析 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\composite.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\composite.md | GoF | `../README.md#与-gof-原书对应` | 锚点不存在: #与-gof-原书对应 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\decorator.md | Decorator 形式化分析 | `#decorator-形式化分析` | 同文件锚点不存在: #decorator-形式化分析 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\decorator.md | 完整场景示例：HTTP 客户端装饰链（日志 + 重试） | `#完整场景示例http-客户端装饰链日志--重试` | 同文件锚点不存在: #完整场景示例http-客户端装饰链日志--重试 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\decorator.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\decorator.md | Decorator 形式化分析 | `#decorator-形式化分析` | 同文件锚点不存在: #decorator-形式化分析 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\decorator.md | 完整场景示例：HTTP 客户端装饰链（日志 + 重试） | `#完整场景示例http-客户端装饰链日志--重试` | 同文件锚点不存在: #完整场景示例http-客户端装饰链日志--重试 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\decorator.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\decorator.md | GoF | `../README.md#与-gof-原书对应` | 锚点不存在: #与-gof-原书对应 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\facade.md | Facade 形式化分析 | `#facade-形式化分析` | 同文件锚点不存在: #facade-形式化分析 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\facade.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\facade.md | Facade 形式化分析 | `#facade-形式化分析` | 同文件锚点不存在: #facade-形式化分析 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\facade.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\facade.md | GoF | `../README.md#与-gof-原书对应` | 锚点不存在: #与-gof-原书对应 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\flyweight.md | Flyweight 形式化分析 | `#flyweight-形式化分析` | 同文件锚点不存在: #flyweight-形式化分析 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\flyweight.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\flyweight.md | Flyweight 形式化分析 | `#flyweight-形式化分析` | 同文件锚点不存在: #flyweight-形式化分析 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\flyweight.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\flyweight.md | GoF | `../README.md#与-gof-原书对应` | 锚点不存在: #与-gof-原书对应 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\proxy.md | Proxy 形式化分析 | `#proxy-形式化分析` | 同文件锚点不存在: #proxy-形式化分析 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\proxy.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\proxy.md | Proxy 形式化分析 | `#proxy-形式化分析` | 同文件锚点不存在: #proxy-形式化分析 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\proxy.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\proxy.md | GoF | `../README.md#与-gof-原书对应` | 锚点不存在: #与-gof-原书对应 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\chain_of_responsibility.md | Chain of Responsibility 形式化分析 | `#chain-of-responsibility-形式化分析` | 同文件锚点不存在: #chain-of-responsibility-形式化分析 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\chain_of_responsibility.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\chain_of_responsibility.md | Chain of Responsibility 形式化分析 | `#chain-of-responsibility-形式化分析` | 同文件锚点不存在: #chain-of-responsibility-形式化分析 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\chain_of_responsibility.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\chain_of_responsibility.md | GoF | `../README.md#与-gof-原书对应` | 锚点不存在: #与-gof-原书对应 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\command.md | Command 形式化分析 | `#command-形式化分析` | 同文件锚点不存在: #command-形式化分析 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\command.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\command.md | Command 形式化分析 | `#command-形式化分析` | 同文件锚点不存在: #command-形式化分析 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\command.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\command.md | GoF | `../README.md#与-gof-原书对应` | 锚点不存在: #与-gof-原书对应 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\interpreter.md | Interpreter 形式化分析 | `#interpreter-形式化分析` | 同文件锚点不存在: #interpreter-形式化分析 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\interpreter.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\interpreter.md | Interpreter 形式化分析 | `#interpreter-形式化分析` | 同文件锚点不存在: #interpreter-形式化分析 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\interpreter.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\interpreter.md | GoF | `../README.md#与-gof-原书对应` | 锚点不存在: #与-gof-原书对应 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\iterator.md | Iterator 形式化分析 | `#iterator-形式化分析` | 同文件锚点不存在: #iterator-形式化分析 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\iterator.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\iterator.md | Iterator 形式化分析 | `#iterator-形式化分析` | 同文件锚点不存在: #iterator-形式化分析 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\iterator.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\iterator.md | GoF | `../README.md#与-gof-原书对应` | 锚点不存在: #与-gof-原书对应 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\mediator.md | Mediator 形式化分析 | `#mediator-形式化分析` | 同文件锚点不存在: #mediator-形式化分析 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\mediator.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\mediator.md | Mediator 形式化分析 | `#mediator-形式化分析` | 同文件锚点不存在: #mediator-形式化分析 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\mediator.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\mediator.md | GoF | `../README.md#与-gof-原书对应` | 锚点不存在: #与-gof-原书对应 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\memento.md | Memento 形式化分析 | `#memento-形式化分析` | 同文件锚点不存在: #memento-形式化分析 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\memento.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\memento.md | Memento 形式化分析 | `#memento-形式化分析` | 同文件锚点不存在: #memento-形式化分析 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\memento.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\memento.md | GoF | `../README.md#与-gof-原书对应` | 锚点不存在: #与-gof-原书对应 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\observer.md | Observer 形式化分析 | `#observer-形式化分析` | 同文件锚点不存在: #observer-形式化分析 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\observer.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\observer.md | Observer 形式化分析 | `#observer-形式化分析` | 同文件锚点不存在: #observer-形式化分析 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\observer.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\observer.md | GoF | `../README.md#与-gof-原书对应` | 锚点不存在: #与-gof-原书对应 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\state.md | State 形式化分析 | `#state-形式化分析` | 同文件锚点不存在: #state-形式化分析 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\state.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\state.md | State 形式化分析 | `#state-形式化分析` | 同文件锚点不存在: #state-形式化分析 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\state.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\state.md | GoF | `../README.md#与-gof-原书对应` | 锚点不存在: #与-gof-原书对应 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\strategy.md | Strategy 形式化分析 | `#strategy-形式化分析` | 同文件锚点不存在: #strategy-形式化分析 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\strategy.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\strategy.md | Strategy 形式化分析 | `#strategy-形式化分析` | 同文件锚点不存在: #strategy-形式化分析 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\strategy.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\strategy.md | GoF | `../README.md#与-gof-原书对应` | 锚点不存在: #与-gof-原书对应 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\template_method.md | Template Method 形式化分析 | `#template-method-形式化分析` | 同文件锚点不存在: #template-method-形式化分析 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\template_method.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\template_method.md | Template Method 形式化分析 | `#template-method-形式化分析` | 同文件锚点不存在: #template-method-形式化分析 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\template_method.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\template_method.md | GoF | `../README.md#与-gof-原书对应` | 锚点不存在: #与-gof-原书对应 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\visitor.md | Visitor 形式化分析 | `#visitor-形式化分析` | 同文件锚点不存在: #visitor-形式化分析 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\visitor.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\visitor.md | Visitor 形式化分析 | `#visitor-形式化分析` | 同文件锚点不存在: #visitor-形式化分析 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\visitor.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\visitor.md | GoF | `../README.md#与-gof-原书对应` | 锚点不存在: #与-gof-原书对应 |
| docs\research_notes\software_design_theory\02_workflow_safe_complete_models\02_complete_43_catalog.md | 43 种完全模型索引 | `#43-种完全模型索引` | 同文件锚点不存在: #43-种完全模型索引 |
| docs\research_notes\software_design_theory\02_workflow_safe_complete_models\02_complete_43_catalog.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\02_workflow_safe_complete_models\02_complete_43_catalog.md | 43 种完全模型索引 | `#43-种完全模型索引` | 同文件锚点不存在: #43-种完全模型索引 |
| docs\research_notes\software_design_theory\02_workflow_safe_complete_models\02_complete_43_catalog.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\02_workflow_safe_complete_models\04_expressiveness_boundary.md | 充分表达 vs 非充分表达论证 | `#充分表达-vs-非充分表达论证` | 同文件锚点不存在: #充分表达-vs-非充分表达论证 |
| docs\research_notes\software_design_theory\02_workflow_safe_complete_models\04_expressiveness_boundary.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\02_workflow_safe_complete_models\04_expressiveness_boundary.md | 充分表达 vs 非充分表达论证 | `#充分表达-vs-非充分表达论证` | 同文件锚点不存在: #充分表达-vs-非充分表达论证 |
| docs\research_notes\software_design_theory\02_workflow_safe_complete_models\04_expressiveness_boundary.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\02_workflow_safe_complete_models\README.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\03_execution_models\01_synchronous.md | 同步执行模型形式化 | `#同步执行模型形式化` | 同文件锚点不存在: #同步执行模型形式化 |
| docs\research_notes\software_design_theory\03_execution_models\01_synchronous.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\03_execution_models\01_synchronous.md | 同步执行模型形式化 | `#同步执行模型形式化` | 同文件锚点不存在: #同步执行模型形式化 |
| docs\research_notes\software_design_theory\03_execution_models\01_synchronous.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\03_execution_models\02_async.md | 异步执行模型形式化 | `#异步执行模型形式化` | 同文件锚点不存在: #异步执行模型形式化 |
| docs\research_notes\software_design_theory\03_execution_models\02_async.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\03_execution_models\02_async.md | 异步执行模型形式化 | `#异步执行模型形式化` | 同文件锚点不存在: #异步执行模型形式化 |
| docs\research_notes\software_design_theory\03_execution_models\02_async.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\03_execution_models\03_concurrent.md | 并发执行模型形式化 | `#并发执行模型形式化` | 同文件锚点不存在: #并发执行模型形式化 |
| docs\research_notes\software_design_theory\03_execution_models\03_concurrent.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\03_execution_models\03_concurrent.md | 并发执行模型形式化 | `#并发执行模型形式化` | 同文件锚点不存在: #并发执行模型形式化 |
| docs\research_notes\software_design_theory\03_execution_models\03_concurrent.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\03_execution_models\04_parallel.md | 并行执行模型形式化 | `#并行执行模型形式化` | 同文件锚点不存在: #并行执行模型形式化 |
| docs\research_notes\software_design_theory\03_execution_models\04_parallel.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\03_execution_models\04_parallel.md | 并行执行模型形式化 | `#并行执行模型形式化` | 同文件锚点不存在: #并行执行模型形式化 |
| docs\research_notes\software_design_theory\03_execution_models\04_parallel.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\03_execution_models\05_distributed.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\03_execution_models\05_distributed.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\03_execution_models\06_boundary_analysis.md | 执行模型边界分析 | `#执行模型边界分析` | 同文件锚点不存在: #执行模型边界分析 |
| docs\research_notes\software_design_theory\03_execution_models\06_boundary_analysis.md | 五模型 × 三维边界 | `#五模型--三维边界` | 同文件锚点不存在: #五模型--三维边界 |
| docs\research_notes\software_design_theory\03_execution_models\06_boundary_analysis.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\03_execution_models\06_boundary_analysis.md | 执行模型边界分析 | `#执行模型边界分析` | 同文件锚点不存在: #执行模型边界分析 |
| docs\research_notes\software_design_theory\03_execution_models\06_boundary_analysis.md | 五模型 × 三维边界 | `#五模型--三维边界` | 同文件锚点不存在: #五模型--三维边界 |
| docs\research_notes\software_design_theory\03_execution_models\06_boundary_analysis.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\03_execution_models\README.md | 场景 1：批处理流水线（同步 + 策略） | `#场景-1批处理流水线同步--策略` | 同文件锚点不存在: #场景-1批处理流水线同步--策略 |
| docs\research_notes\software_design_theory\03_execution_models\README.md | 场景 2：高并发 Web 服务（异步 + Observer + 通道） | `#场景-2高并发-web-服务异步--observer--通道` | 同文件锚点不存在: #场景-2高并发-web-服务异步--observer--通道 |
| docs\research_notes\software_design_theory\03_execution_models\README.md | 场景 3：图像处理（并行 + Iterator） | `#场景-3图像处理并行--iterator` | 同文件锚点不存在: #场景-3图像处理并行--iterator |
| docs\research_notes\software_design_theory\03_execution_models\README.md | 场景 4：多服务编排（分布式 + Proxy + DTO） | `#场景-4多服务编排分布式--proxy--dto` | 同文件锚点不存在: #场景-4多服务编排分布式--proxy--dto |
| docs\research_notes\software_design_theory\03_execution_models\README.md | 示例 1：批处理 + Strategy（同步） | `#示例-1批处理--strategy同步` | 同文件锚点不存在: #示例-1批处理--strategy同步 |
| docs\research_notes\software_design_theory\03_execution_models\README.md | 示例 2：并发 + Observer（std::thread + mpsc） | `#示例-2并发--observerstdthread--mpsc` | 同文件锚点不存在: #示例-2并发--observerstdthread--mpsc |
| docs\research_notes\software_design_theory\03_execution_models\README.md | 示例 3：并行 + Strategy（rayon，需 `cargo add rayon`） | `#示例-3并行--strategyrayon需-cargo-add-rayon` | 同文件锚点不存在: #示例-3并行--strategyrayon需-cargo-add-rayon |
| docs\research_notes\software_design_theory\03_execution_models\README.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\04_compositional_engineering\01_formal_composition.md | 组合的形式化定义 | `#组合的形式化定义` | 同文件锚点不存在: #组合的形式化定义 |
| docs\research_notes\software_design_theory\04_compositional_engineering\01_formal_composition.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\04_compositional_engineering\02_effectiveness_proofs.md | 组合软件工程有效性定理与证明 | `#组合软件工程有效性定理与证明` | 同文件锚点不存在: #组合软件工程有效性定理与证明 |
| docs\research_notes\software_design_theory\04_compositional_engineering\02_effectiveness_proofs.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\04_compositional_engineering\02_effectiveness_proofs.md | 组合软件工程有效性定理与证明 | `#组合软件工程有效性定理与证明` | 同文件锚点不存在: #组合软件工程有效性定理与证明 |
| docs\research_notes\software_design_theory\04_compositional_engineering\02_effectiveness_proofs.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\04_compositional_engineering\03_integration_theory.md | 与 ownership/borrow/trait 的衔接 | `#与-ownershipborrowtrait-的衔接` | 同文件锚点不存在: #与-ownershipborrowtrait-的衔接 |
| docs\research_notes\software_design_theory\04_compositional_engineering\03_integration_theory.md | 完整多模式组合链条：Builder + Factory + Repository | `#完整多模式组合链条builder--factory--repository` | 同文件锚点不存在: #完整多模式组合链条builder--factory--repository |
| docs\research_notes\software_design_theory\04_compositional_engineering\03_integration_theory.md | 链条 1：Builder + Factory + Repository | `#链条-1builder--factory--repository` | 同文件锚点不存在: #链条-1builder--factory--repository |
| docs\research_notes\software_design_theory\04_compositional_engineering\03_integration_theory.md | 链条 2：Decorator + Strategy + Observer（完整实现） | `#链条-2decorator--strategy--observer完整实现` | 同文件锚点不存在: #链条-2decorator--strategy--observer完整实现 |
| docs\research_notes\software_design_theory\04_compositional_engineering\03_integration_theory.md | 链条 3：Composite + Visitor + Iterator（完整实现） | `#链条-3composite--visitor--iterator完整实现` | 同文件锚点不存在: #链条-3composite--visitor--iterator完整实现 |
| docs\research_notes\software_design_theory\04_compositional_engineering\03_integration_theory.md | 链条 4：Chain of Responsibility + Command + Observer | `#链条-4chain-of-responsibility--command--observer` | 同文件锚点不存在: #链条-4chain-of-responsibility--command--observer |
| docs\research_notes\software_design_theory\04_compositional_engineering\03_integration_theory.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\04_compositional_engineering\03_integration_theory.md | 与 ownership/borrow/trait 的衔接 | `#与-ownershipborrowtrait-的衔接` | 同文件锚点不存在: #与-ownershipborrowtrait-的衔接 |
| docs\research_notes\software_design_theory\04_compositional_engineering\03_integration_theory.md | 完整多模式组合链条：Builder + Factory + Repository | `#完整多模式组合链条builder--factory--repository` | 同文件锚点不存在: #完整多模式组合链条builder--factory--repository |
| docs\research_notes\software_design_theory\04_compositional_engineering\03_integration_theory.md | 链条 1：Builder + Factory + Repository | `#链条-1builder--factory--repository` | 同文件锚点不存在: #链条-1builder--factory--repository |
| docs\research_notes\software_design_theory\04_compositional_engineering\03_integration_theory.md | 链条 2：Decorator + Strategy + Observer（完整实现） | `#链条-2decorator--strategy--observer完整实现` | 同文件锚点不存在: #链条-2decorator--strategy--observer完整实现 |
| docs\research_notes\software_design_theory\04_compositional_engineering\03_integration_theory.md | 链条 3：Composite + Visitor + Iterator（完整实现） | `#链条-3composite--visitor--iterator完整实现` | 同文件锚点不存在: #链条-3composite--visitor--iterator完整实现 |
| docs\research_notes\software_design_theory\04_compositional_engineering\03_integration_theory.md | 链条 4：Chain of Responsibility + Command + Observer | `#链条-4chain-of-responsibility--command--observer` | 同文件锚点不存在: #链条-4chain-of-responsibility--command--observer |
| docs\research_notes\software_design_theory\04_compositional_engineering\03_integration_theory.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\04_compositional_engineering\README.md | 示例 1：Builder + Factory Method | `#示例-1builder--factory-method` | 同文件锚点不存在: #示例-1builder--factory-method |
| docs\research_notes\software_design_theory\04_compositional_engineering\README.md | 示例 2：Repository + Service Layer + DTO（完整链条） | `#示例-2repository--service-layer--dto完整链条` | 同文件锚点不存在: #示例-2repository--service-layer--dto完整链条 |
| docs\research_notes\software_design_theory\04_compositional_engineering\README.md | 组合法则依赖链（Def → Axiom → Lemma → Theorem → Corollary） | `#组合法则依赖链def--axiom--lemma--theorem--corollary` | 同文件锚点不存在: #组合法则依赖链def--axiom--lemma--theorem--corollary |
| docs\research_notes\software_design_theory\04_compositional_engineering\README.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\05_boundary_system\expressive_inexpressive_matrix.md | 充分表达 vs 非充分表达边界矩阵 | `#充分表达-vs-非充分表达边界矩阵` | 同文件锚点不存在: #充分表达-vs-非充分表达边界矩阵 |
| docs\research_notes\software_design_theory\05_boundary_system\expressive_inexpressive_matrix.md | 设计模式 × 表达边界 | `#设计模式--表达边界` | 同文件锚点不存在: #设计模式--表达边界 |
| docs\research_notes\software_design_theory\05_boundary_system\expressive_inexpressive_matrix.md | 执行模型 × 表达边界 | `#执行模型--表达边界` | 同文件锚点不存在: #执行模型--表达边界 |
| docs\research_notes\software_design_theory\05_boundary_system\expressive_inexpressive_matrix.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\05_boundary_system\expressive_inexpressive_matrix.md | 充分表达 vs 非充分表达边界矩阵 | `#充分表达-vs-非充分表达边界矩阵` | 同文件锚点不存在: #充分表达-vs-非充分表达边界矩阵 |
| docs\research_notes\software_design_theory\05_boundary_system\expressive_inexpressive_matrix.md | 设计模式 × 表达边界 | `#设计模式--表达边界` | 同文件锚点不存在: #设计模式--表达边界 |
| docs\research_notes\software_design_theory\05_boundary_system\expressive_inexpressive_matrix.md | 执行模型 × 表达边界 | `#执行模型--表达边界` | 同文件锚点不存在: #执行模型--表达边界 |
| docs\research_notes\software_design_theory\05_boundary_system\expressive_inexpressive_matrix.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\05_boundary_system\safe_unsafe_matrix.md | 安全 vs 非安全边界矩阵 | `#安全-vs-非安全边界矩阵` | 同文件锚点不存在: #安全-vs-非安全边界矩阵 |
| docs\research_notes\software_design_theory\05_boundary_system\safe_unsafe_matrix.md | 设计模式 × 安全边界 | `#设计模式--安全边界` | 同文件锚点不存在: #设计模式--安全边界 |
| docs\research_notes\software_design_theory\05_boundary_system\safe_unsafe_matrix.md | 执行模型 × 安全边界 | `#执行模型--安全边界` | 同文件锚点不存在: #执行模型--安全边界 |
| docs\research_notes\software_design_theory\05_boundary_system\safe_unsafe_matrix.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\05_boundary_system\supported_unsupported_matrix.md | 支持 vs 不支持边界矩阵 | `#支持-vs-不支持边界矩阵` | 同文件锚点不存在: #支持-vs-不支持边界矩阵 |
| docs\research_notes\software_design_theory\05_boundary_system\supported_unsupported_matrix.md | 设计模式 × 支持边界 | `#设计模式--支持边界` | 同文件锚点不存在: #设计模式--支持边界 |
| docs\research_notes\software_design_theory\05_boundary_system\supported_unsupported_matrix.md | 执行模型 × 支持边界 | `#执行模型--支持边界` | 同文件锚点不存在: #执行模型--支持边界 |
| docs\research_notes\software_design_theory\05_boundary_system\supported_unsupported_matrix.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\05_distributed\01_saga_pattern.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\05_distributed\02_cqrs_pattern.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\05_distributed\03_circuit_breaker.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\05_distributed\04_event_sourcing.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\05_distributed\05_outbox_pattern.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\05_distributed\06_timeout_pattern.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\software_design_theory\05_distributed\07_retry_pattern.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\type_theory\00_completeness_gaps.md | 类型理论完备性缺口：形式化论证不充分声明 | `#类型理论完备性缺口形式化论证不充分声明` | 同文件锚点不存在: #类型理论完备性缺口形式化论证不充分声明 |
| docs\research_notes\type_theory\00_completeness_gaps.md | 📊 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\research_notes\type_theory\00_completeness_gaps.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\type_theory\00_completeness_gaps.md | 类型理论完备性缺口：形式化论证不充分声明 | `#类型理论完备性缺口形式化论证不充分声明` | 同文件锚点不存在: #类型理论完备性缺口形式化论证不充分声明 |
| docs\research_notes\type_theory\00_completeness_gaps.md | 📊 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\research_notes\type_theory\00_completeness_gaps.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\type_theory\advanced_types.md | 高级类型特性 | `#高级类型特性` | 同文件锚点不存在: #高级类型特性 |
| docs\research_notes\type_theory\advanced_types.md | ⚠️ 反例：违反高级类型规则 {#️-反例违反高级类型规则} | `#️-反例违反高级类型规则-️-反例违反高级类型规则` | 同文件锚点不存在: #️-反例违反高级类型规则-️-反例违反高级类型规则 |
| docs\research_notes\type_theory\advanced_types.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\type_theory\advanced_types.md | 高级类型特性 | `#高级类型特性` | 同文件锚点不存在: #高级类型特性 |
| docs\research_notes\type_theory\advanced_types.md | ⚠️ 反例：违反高级类型规则 {#️-反例违反高级类型规则} | `#️-反例违反高级类型规则-️-反例违反高级类型规则` | 同文件锚点不存在: #️-反例违反高级类型规则-️-反例违反高级类型规则 |
| docs\research_notes\type_theory\advanced_types.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\type_theory\construction_capability.md | 类型系统构造能力 | `#类型系统构造能力` | 同文件锚点不存在: #类型系统构造能力 |
| docs\research_notes\type_theory\construction_capability.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\type_theory\construction_capability.md | 类型系统构造能力 | `#类型系统构造能力` | 同文件锚点不存在: #类型系统构造能力 |
| docs\research_notes\type_theory\construction_capability.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\type_theory\10_const_evaluation.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\type_theory\lifetime_formalization.md | 生命周期形式化 | `#生命周期形式化` | 同文件锚点不存在: #生命周期形式化 |
| docs\research_notes\type_theory\lifetime_formalization.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\type_theory\lifetime_formalization.md | 生命周期形式化 | `#生命周期形式化` | 同文件锚点不存在: #生命周期形式化 |
| docs\research_notes\type_theory\lifetime_formalization.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\type_theory\README.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\type_theory\trait_system_formalization.md | Trait 系统形式化 | `#trait-系统形式化` | 同文件锚点不存在: #trait-系统形式化 |
| docs\research_notes\type_theory\trait_system_formalization.md | Trait + 泛型 + GAT 组合与 Specialization | `#trait--泛型--gat-组合与-specialization` | 同文件锚点不存在: #trait--泛型--gat-组合与-specialization |
| docs\research_notes\type_theory\trait_system_formalization.md | ⚠️ 反例：违反 Trait 规则 {#️-反例违反-trait-规则} | `#️-反例违反-trait-规则-️-反例违反-trait-规则` | 同文件锚点不存在: #️-反例违反-trait-规则-️-反例违反-trait-规则 |
| docs\research_notes\type_theory\trait_system_formalization.md | 示例 8: 高级 Trait 特性 - 默认实现和关联函数 | `#示例-8-高级-trait-特性---默认实现和关联函数` | 同文件锚点不存在: #示例-8-高级-trait-特性---默认实现和关联函数 |
| docs\research_notes\type_theory\trait_system_formalization.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\type_theory\trait_system_formalization.md | Trait 系统形式化 | `#trait-系统形式化` | 同文件锚点不存在: #trait-系统形式化 |
| docs\research_notes\type_theory\trait_system_formalization.md | Trait + 泛型 + GAT 组合与 Specialization | `#trait--泛型--gat-组合与-specialization` | 同文件锚点不存在: #trait--泛型--gat-组合与-specialization |
| docs\research_notes\type_theory\trait_system_formalization.md | ⚠️ 反例：违反 Trait 规则 {#️-反例违反-trait-规则} | `#️-反例违反-trait-规则-️-反例违反-trait-规则` | 同文件锚点不存在: #️-反例违反-trait-规则-️-反例违反-trait-规则 |
| docs\research_notes\type_theory\trait_system_formalization.md | 示例 8: 高级 Trait 特性 - 默认实现和关联函数 | `#示例-8-高级-trait-特性---默认实现和关联函数` | 同文件锚点不存在: #示例-8-高级-trait-特性---默认实现和关联函数 |
| docs\research_notes\type_theory\trait_system_formalization.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\type_theory\type_system_foundations.md | ⚠️ 反例：类型错误与类型推导失败 {#️-反例类型错误类型检查拒绝} | `#️-反例类型错误与类型推导失败-️-反例类型错误类型检查拒绝` | 同文件锚点不存在: #️-反例类型错误与类型推导失败-️-反例类型错误类型检查拒绝 |
| docs\research_notes\type_theory\type_system_foundations.md | 1. ControlFlow::ok() - 控制流与Option转换 | `#1-controlflowok---控制流与option转换` | 同文件锚点不存在: #1-controlflowok---控制流与option转换 |
| docs\research_notes\type_theory\type_system_foundations.md | 3. int\_format\_into - 高性能整数格式化 | `#3-int_format_into---高性能整数格式化` | 同文件锚点不存在: #3-int_format_into---高性能整数格式化 |
| docs\research_notes\type_theory\type_system_foundations.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\type_theory\type_system_foundations.md | ⚠️ 反例：类型错误与类型推导失败 {#️-反例类型错误类型检查拒绝} | `#️-反例类型错误与类型推导失败-️-反例类型错误类型检查拒绝` | 同文件锚点不存在: #️-反例类型错误与类型推导失败-️-反例类型错误类型检查拒绝 |
| docs\research_notes\type_theory\type_system_foundations.md | 1. ControlFlow::ok() - 控制流与Option转换 | `#1-controlflowok---控制流与option转换` | 同文件锚点不存在: #1-controlflowok---控制流与option转换 |
| docs\research_notes\type_theory\type_system_foundations.md | 3. int\_format\_into - 高性能整数格式化 | `#3-int_format_into---高性能整数格式化` | 同文件锚点不存在: #3-int_format_into---高性能整数格式化 |
| docs\research_notes\type_theory\type_system_foundations.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\type_theory\variance_theory.md | 型变理论 | `#型变理论` | 同文件锚点不存在: #型变理论 |
| docs\research_notes\type_theory\variance_theory.md | ⚠️ 反例：型变规则必要性 {#️-反例型变规则必要性} | `#️-反例型变规则必要性-️-反例型变规则必要性` | 同文件锚点不存在: #️-反例型变规则必要性-️-反例型变规则必要性 |
| docs\research_notes\type_theory\variance_theory.md | 组合法则：类型 + 生命周期 + 型变 | `#组合法则类型--生命周期--型变` | 同文件锚点不存在: #组合法则类型--生命周期--型变 |
| docs\research_notes\type_theory\variance_theory.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\research_notes\type_theory\variance_theory.md | 型变理论 | `#型变理论` | 同文件锚点不存在: #型变理论 |
| docs\research_notes\type_theory\variance_theory.md | ⚠️ 反例：型变规则必要性 {#️-反例型变规则必要性} | `#️-反例型变规则必要性-️-反例型变规则必要性` | 同文件锚点不存在: #️-反例型变规则必要性-️-反例型变规则必要性 |
| docs\research_notes\type_theory\variance_theory.md | 组合法则：类型 + 生命周期 + 型变 | `#组合法则类型--生命周期--型变` | 同文件锚点不存在: #组合法则类型--生命周期--型变 |
| docs\research_notes\type_theory\variance_theory.md | **最后更新**: 2026-03-14 (Rust 1.94 深度整合) | `#最后更新-2026-03-14-rust-194-深度整合` | 同文件锚点不存在: #最后更新-2026-03-14-rust-194-深度整合 |
| docs\rust-formal-engineering-system\00_master_index.md | Rust 形式化工程系统 - 主索引 | `#rust-形式化工程系统---主索引` | 同文件锚点不存在: #rust-形式化工程系统---主索引 |
| docs\rust-formal-engineering-system\00_master_index.md | 🏛️ 理论体系与论证体系结构（顶层入口） | `#️-理论体系与论证体系结构顶层入口` | 同文件锚点不存在: #️-理论体系与论证体系结构顶层入口 |
| docs\rust-formal-engineering-system\02_programming_paradigms\11_benchmark_minimal_guide.md | 基准测试最小指南 | `#基准测试最小指南` | 同文件锚点不存在: #基准测试最小指南 |
| docs\rust-formal-engineering-system\10_quality_assurance\README.md | 返回主索引 | `#返回主索引` | 同文件锚点不存在: #返回主索引 |
| docs\rust-ownership-decidability\100_PERCENT_COMPLETION_REPORT.md | Rust 所有权系统形式化 - 持续推进完成报告 | `#rust-所有权系统形式化---持续推进完成报告` | 同文件锚点不存在: #rust-所有权系统形式化---持续推进完成报告 |
| docs\rust-ownership-decidability\100_PERCENT_COMPLETION_REPORT.md | *总体完成度: 92% (核心框架 100%)* | `#总体完成度-92-核心框架-100` | 同文件锚点不存在: #总体完成度-92-核心框架-100 |
| docs\rust-ownership-decidability\AUDIT_REPORTS_INDEX.md | *最后更新: 2026-03-07* | `#最后更新-2026-03-07` | 同文件锚点不存在: #最后更新-2026-03-07 |
| docs\rust-ownership-decidability\AUTHORITY_ALIGNMENT_GAP_ANALYSIS.md | Rust 所有权可判定性 - 网络权威资源对齐分析报告 | `#rust-所有权可判定性---网络权威资源对齐分析报告` | 同文件锚点不存在: #rust-所有权可判定性---网络权威资源对齐分析报告 |
| docs\rust-ownership-decidability\AUTHORITY_ALIGNMENT_GAP_ANALYSIS.md | 🔴 高优先级 - 尚未充分覆盖 | `#-高优先级---尚未充分覆盖` | 同文件锚点不存在: #-高优先级---尚未充分覆盖 |
| docs\rust-ownership-decidability\AUTHORITY_ALIGNMENT_GAP_ANALYSIS.md | 🔶 中优先级 - 需要更新 | `#-中优先级---需要更新` | 同文件锚点不存在: #-中优先级---需要更新 |
| docs\rust-ownership-decidability\AUTHORITY_ALIGNMENT_GAP_ANALYSIS.md | 2.1 RefinedRust - 重大差距 ⚠️ | `#21-refinedrust---重大差距-️` | 同文件锚点不存在: #21-refinedrust---重大差距-️ |
| docs\rust-ownership-decidability\AUTHORITY_ALIGNMENT_GAP_ANALYSIS.md | 2.2 Aeneas - 中等差距 🔶 | `#22-aeneas---中等差距-` | 同文件锚点不存在: #22-aeneas---中等差距- |
| docs\rust-ownership-decidability\AUTHORITY_ALIGNMENT_GAP_ANALYSIS.md | 2.3 Gillian-Rust - 完全缺失 🔴 | `#23-gillian-rust---完全缺失-` | 同文件锚点不存在: #23-gillian-rust---完全缺失- |
| docs\rust-ownership-decidability\AUTHORITY_ALIGNMENT_GAP_ANALYSIS.md | 2.4 Tree Borrows - 部分覆盖 🔶 | `#24-tree-borrows---部分覆盖-` | 同文件锚点不存在: #24-tree-borrows---部分覆盖- |
| docs\rust-ownership-decidability\AUTHORITY_ALIGNMENT_GAP_ANALYSIS.md | 2.5 Rust 标准库验证计划 - 完全缺失 🔴 | `#25-rust-标准库验证计划---完全缺失-` | 同文件锚点不存在: #25-rust-标准库验证计划---完全缺失- |
| docs\rust-ownership-decidability\AUTHORITY_ALIGNMENT_GAP_ANALYSIS.md | 4.1 当前优势 ✅ | `#41-当前优势-` | 同文件锚点不存在: #41-当前优势- |
| docs\rust-ownership-decidability\AUTHORITY_ALIGNMENT_GAP_ANALYSIS.md | 4.2 需要改进 🔶 | `#42-需要改进-` | 同文件锚点不存在: #42-需要改进- |
| docs\rust-ownership-decidability\AUTHORITY_ALIGNMENT_GAP_ANALYSIS.md | 4.3 缺失内容 🔴 | `#43-缺失内容-` | 同文件锚点不存在: #43-缺失内容- |
| docs\rust-ownership-decidability\AUTHORITY_ALIGNMENT_GAP_ANALYSIS.md | **最后更新**: 2026-03-12 | `#最后更新-2026-03-12` | 同文件锚点不存在: #最后更新-2026-03-12 |
| docs\rust-ownership-decidability\BATCH_4_COMPLETION_REPORT.md | **整体完成度**: ~78% | `#整体完成度-78` | 同文件锚点不存在: #整体完成度-78 |
| docs\rust-ownership-decidability\COMPARATIVE_ANALYSIS.md | 3.2 ATS：依赖类型 + 线性类型 | `#32-ats依赖类型--线性类型` | 同文件锚点不存在: #32-ats依赖类型--线性类型 |
| docs\rust-ownership-decidability\COMPARATIVE_ANALYSIS.md | **下一篇**：阅读 `DESIGN_RATIONALE.md` 了解设计决策背后的原理 | `#下一篇阅读-design_rationalemd-了解设计决策背后的原理` | 同文件锚点不存在: #下一篇阅读-design_rationalemd-了解设计决策背后的原理 |
| docs\rust-ownership-decidability\COMPILATION_VERIFICATION_REPORT.md | *Rust Version: 1.94.0* | `#rust-version-1940` | 同文件锚点不存在: #rust-version-1940 |
| docs\rust-ownership-decidability\COMPLETE_EXAMPLES_AND_COUNTEREXAMPLES.md | Rust 所有权系统 - 完整示例与反例集 | `#rust-所有权系统---完整示例与反例集` | 同文件锚点不存在: #rust-所有权系统---完整示例与反例集 |
| docs\rust-ownership-decidability\COMPLETE_EXAMPLES_AND_COUNTEREXAMPLES.md | **建议**: 通过实践这些示例来加深理解 | `#建议-通过实践这些示例来加深理解` | 同文件锚点不存在: #建议-通过实践这些示例来加深理解 |
| docs\rust-ownership-decidability\COMPLETE_KNOWLEDGE_MATRIX.md | Rust 所有权系统 - 完整知识矩阵 | `#rust-所有权系统---完整知识矩阵` | 同文件锚点不存在: #rust-所有权系统---完整知识矩阵 |
| docs\rust-ownership-decidability\COMPLETE_KNOWLEDGE_MATRIX.md | 矩阵一：概念 × 层次 | `#矩阵一概念--层次` | 同文件锚点不存在: #矩阵一概念--层次 |
| docs\rust-ownership-decidability\COMPLETE_KNOWLEDGE_MATRIX.md | 矩阵二：定理 × 应用 | `#矩阵二定理--应用` | 同文件锚点不存在: #矩阵二定理--应用 |
| docs\rust-ownership-decidability\COMPLETE_KNOWLEDGE_MATRIX.md | 矩阵三：错误 × 理论 × 修复 | `#矩阵三错误--理论--修复` | 同文件锚点不存在: #矩阵三错误--理论--修复 |
| docs\rust-ownership-decidability\COMPLETE_KNOWLEDGE_MATRIX.md | 矩阵四：模式 × 理论约束 × 使用场景 | `#矩阵四模式--理论约束--使用场景` | 同文件锚点不存在: #矩阵四模式--理论约束--使用场景 |
| docs\rust-ownership-decidability\COMPLETE_KNOWLEDGE_MATRIX.md | 矩阵五：工具 × 验证能力 × 复杂度 | `#矩阵五工具--验证能力--复杂度` | 同文件锚点不存在: #矩阵五工具--验证能力--复杂度 |
| docs\rust-ownership-decidability\COMPLETE_KNOWLEDGE_MATRIX.md | 矩阵六：学习阶段 × 能力 × 验证标准 | `#矩阵六学习阶段--能力--验证标准` | 同文件锚点不存在: #矩阵六学习阶段--能力--验证标准 |
| docs\rust-ownership-decidability\COMPLETE_KNOWLEDGE_MATRIX.md | 矩阵七：应用领域 × 关键概念 × 典型案例 | `#矩阵七应用领域--关键概念--典型案例` | 同文件锚点不存在: #矩阵七应用领域--关键概念--典型案例 |
| docs\rust-ownership-decidability\COMPLETE_KNOWLEDGE_MATRIX.md | 矩阵八：Rust 版本 × 特性 × 形式化状态 | `#矩阵八rust-版本--特性--形式化状态` | 同文件锚点不存在: #矩阵八rust-版本--特性--形式化状态 |
| docs\rust-ownership-decidability\COMPLETE_KNOWLEDGE_MATRIX.md | *这些矩阵提供了知识的多维度视图，帮助建立完整的知识网络* | `#这些矩阵提供了知识的多维度视图帮助建立完整的知识网络` | 同文件锚点不存在: #这些矩阵提供了知识的多维度视图帮助建立完整的知识网络 |
| docs\rust-ownership-decidability\COMPLETION_100_PERCENT_SUMMARY.md | ✅ Rust 所有权可判定性 - 100% 完成摘要 | `#-rust-所有权可判定性---100-完成摘要` | 同文件锚点不存在: #-rust-所有权可判定性---100-完成摘要 |
| docs\rust-ownership-decidability\COMPLETION_ROADMAP_2026_Q1.md | Rust 所有权可判定性项目 - 完成路线图 2026 Q1 | `#rust-所有权可判定性项目---完成路线图-2026-q1` | 同文件锚点不存在: #rust-所有权可判定性项目---完成路线图-2026-q1 |
| docs\rust-ownership-decidability\COMPLETION_ROADMAP_2026_Q1.md | Phase 1: 关键缺失填补 (Week 1-4) 🔴 | `#phase-1-关键缺失填补-week-1-4-` | 同文件锚点不存在: #phase-1-关键缺失填补-week-1-4- |
| docs\rust-ownership-decidability\COMPLETION_ROADMAP_2026_Q1.md | Week 2: Data Layout \& 内存布局 | `#week-2-data-layout--内存布局` | 同文件锚点不存在: #week-2-data-layout--内存布局 |
| docs\rust-ownership-decidability\COMPLETION_ROADMAP_2026_Q1.md | Week 3: Uninitialized Memory \& Drop | `#week-3-uninitialized-memory--drop` | 同文件锚点不存在: #week-3-uninitialized-memory--drop |
| docs\rust-ownership-decidability\COMPLETION_ROADMAP_2026_Q1.md | Week 4: Panic \& Unwinding | `#week-4-panic--unwinding` | 同文件锚点不存在: #week-4-panic--unwinding |
| docs\rust-ownership-decidability\COMPLETION_ROADMAP_2026_Q1.md | Phase 2: 内容扩展 (Week 5-8) 🟡 | `#phase-2-内容扩展-week-5-8-` | 同文件锚点不存在: #phase-2-内容扩展-week-5-8- |
| docs\rust-ownership-decidability\COMPLETION_ROADMAP_2026_Q1.md | Phase 3: 对齐优化 (Week 9-12) 🟢 | `#phase-3-对齐优化-week-9-12-` | 同文件锚点不存在: #phase-3-对齐优化-week-9-12- |
| docs\rust-ownership-decidability\COMPLETION_ROADMAP_2026_Q1.md | Phase 4: 质量冲刺 (Week 13-16) ⭐ | `#phase-4-质量冲刺-week-13-16-` | 同文件锚点不存在: #phase-4-质量冲刺-week-13-16- |
| docs\rust-ownership-decidability\COMPLETION_ROADMAP_2026_Q1.md | *目标: 2026-06-30 100% 完成* | `#目标-2026-06-30-100-完成` | 同文件锚点不存在: #目标-2026-06-30-100-完成 |
| docs\rust-ownership-decidability\COMPLETION_SYNTHESIS_REPORT.md | Rust 所有权系统可判定性 - 完成综合报告 | `#rust-所有权系统可判定性---完成综合报告` | 同文件锚点不存在: #rust-所有权系统可判定性---完成综合报告 |
| docs\rust-ownership-decidability\COMPREHENSIVE_COMPLETION_REPORT.md | *状态: 完成 ✅* | `#状态-完成-` | 同文件锚点不存在: #状态-完成- |
| docs\rust-ownership-decidability\COMPREHENSIVE_COUNTEREXAMPLES_HANDBOOK.md | // Extended content line 1200 for comprehensive Rust handbook | `#-extended-content-line-1200-for-comprehensive-rust-handbook` | 同文件锚点不存在: #-extended-content-line-1200-for-comprehensive-rust-handbook |
| docs\rust-ownership-decidability\COMPREHENSIVE_FAQ.md | Rust 所有权系统 - 全面 FAQ | `#rust-所有权系统---全面-faq` | 同文件锚点不存在: #rust-所有权系统---全面-faq |
| docs\rust-ownership-decidability\COMPREHENSIVE_FAQ.md | 📚 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\rust-ownership-decidability\COMPREHENSIVE_FAQ.md | *FAQ 持续更新中，如有问题请提交 Issue* | `#faq-持续更新中如有问题请提交-issue` | 同文件锚点不存在: #faq-持续更新中如有问题请提交-issue |
| docs\rust-ownership-decidability\COMPREHENSIVE_FAQ.md | Rust 所有权系统 - 全面 FAQ | `#rust-所有权系统---全面-faq` | 同文件锚点不存在: #rust-所有权系统---全面-faq |
| docs\rust-ownership-decidability\COMPREHENSIVE_FAQ.md | 📚 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\rust-ownership-decidability\COMPREHENSIVE_FAQ.md | *FAQ 持续更新中，如有问题请提交 Issue* | `#faq-持续更新中如有问题请提交-issue` | 同文件锚点不存在: #faq-持续更新中如有问题请提交-issue |
| docs\rust-ownership-decidability\COMPREHENSIVE_KNOWLEDGE_SYNTHESIS.md | Rust 所有权系统可判定性 - 综合知识梳理 | `#rust-所有权系统可判定性---综合知识梳理` | 同文件锚点不存在: #rust-所有权系统可判定性---综合知识梳理 |
| docs\rust-ownership-decidability\COMPREHENSIVE_KNOWLEDGE_SYNTHESIS.md | 00 - 理论基础 (`00-foundations/`) | `#00---理论基础-00-foundations` | 同文件锚点不存在: #00---理论基础-00-foundations |
| docs\rust-ownership-decidability\COMPREHENSIVE_KNOWLEDGE_SYNTHESIS.md | 01 - 核心概念 (`01-core-concepts/`) | `#01---核心概念-01-core-concepts` | 同文件锚点不存在: #01---核心概念-01-core-concepts |
| docs\rust-ownership-decidability\COMPREHENSIVE_KNOWLEDGE_SYNTHESIS.md | 03 - 验证工具 (`03-verification-tools/`) | `#03---验证工具-03-verification-tools` | 同文件锚点不存在: #03---验证工具-03-verification-tools |
| docs\rust-ownership-decidability\COMPREHENSIVE_KNOWLEDGE_SYNTHESIS.md | 11 - 设计模式 (`11-design-patterns/`) | `#11---设计模式-11-design-patterns` | 同文件锚点不存在: #11---设计模式-11-design-patterns |
| docs\rust-ownership-decidability\COMPREHENSIVE_KNOWLEDGE_SYNTHESIS.md | 12 - 并发模式 (`12-concurrency-patterns/`) | `#12---并发模式-12-concurrency-patterns` | 同文件锚点不存在: #12---并发模式-12-concurrency-patterns |
| docs\rust-ownership-decidability\COMPREHENSIVE_KNOWLEDGE_SYNTHESIS.md | 16 - 程序语义 (`16-program-semantics/`) | `#16---程序语义-16-program-semantics` | 同文件锚点不存在: #16---程序语义-16-program-semantics |
| docs\rust-ownership-decidability\COMPREHENSIVE_KNOWLEDGE_SYNTHESIS.md | 🛤️ 优化学习路径 | `#️-优化学习路径` | 同文件锚点不存在: #️-优化学习路径 |
| docs\rust-ownership-decidability\COMPREHENSIVE_KNOWLEDGE_SYNTHESIS.md | 路径 A: 快速入门 (4小时) → 初学者 | `#路径-a-快速入门-4小时--初学者` | 同文件锚点不存在: #路径-a-快速入门-4小时--初学者 |
| docs\rust-ownership-decidability\COMPREHENSIVE_KNOWLEDGE_SYNTHESIS.md | 路径 B: 系统掌握 (2周) → 进阶开发者 | `#路径-b-系统掌握-2周--进阶开发者` | 同文件锚点不存在: #路径-b-系统掌握-2周--进阶开发者 |
| docs\rust-ownership-decidability\COMPREHENSIVE_KNOWLEDGE_SYNTHESIS.md | 路径 C: 形式化专家 (持续) → 研究者 | `#路径-c-形式化专家-持续--研究者` | 同文件锚点不存在: #路径-c-形式化专家-持续--研究者 |
| docs\rust-ownership-decidability\COMPREHENSIVE_KNOWLEDGE_SYNTHESIS.md | **🎉 Rust 所有权系统可判定性知识库 - 100% 综合梳理完成! 🎉** | `#-rust-所有权系统可判定性知识库---100-综合梳理完成-` | 同文件锚点不存在: #-rust-所有权系统可判定性知识库---100-综合梳理完成- |
| docs\rust-ownership-decidability\CONTENT_ASSOCIATION_ANALYSIS.md | Rust 所有权系统 - 内容关联完整性分析与论证 | `#rust-所有权系统---内容关联完整性分析与论证` | 同文件锚点不存在: #rust-所有权系统---内容关联完整性分析与论证 |
| docs\rust-ownership-decidability\CONTENT_ASSOCIATION_ANALYSIS.md | 3.1 自然语言 ↔ 形式化 映射 | `#31-自然语言--形式化-映射` | 同文件锚点不存在: #31-自然语言--形式化-映射 |
| docs\rust-ownership-decidability\CONTENT_ASSOCIATION_ANALYSIS.md | 3.2 理论模型 ↔ Coq 模型 | `#32-理论模型--coq-模型` | 同文件锚点不存在: #32-理论模型--coq-模型 |
| docs\rust-ownership-decidability\CONTENT_ASSOCIATION_ANALYSIS.md | 3.3 抽象模型 ↔ 具体实现 | `#33-抽象模型--具体实现` | 同文件锚点不存在: #33-抽象模型--具体实现 |
| docs\rust-ownership-decidability\CONTENT_ASSOCIATION_ANALYSIS.md | 缺失 1: 理论基础 ↔ 实践代码 | `#缺失-1-理论基础--实践代码` | 同文件锚点不存在: #缺失-1-理论基础--实践代码 |
| docs\rust-ownership-decidability\CONTENT_ASSOCIATION_ANALYSIS.md | 缺失 2: 定理 ↔ 编译器实现 | `#缺失-2-定理--编译器实现` | 同文件锚点不存在: #缺失-2-定理--编译器实现 |
| docs\rust-ownership-decidability\CONTENT_ASSOCIATION_ANALYSIS.md | 缺失 3: 模式 ↔ 理论约束 | `#缺失-3-模式--理论约束` | 同文件锚点不存在: #缺失-3-模式--理论约束 |
| docs\rust-ownership-decidability\CONTENT_ASSOCIATION_ANALYSIS.md | 缺失 4: 验证工具 ↔ 理论性质 | `#缺失-4-验证工具--理论性质` | 同文件锚点不存在: #缺失-4-验证工具--理论性质 |
| docs\rust-ownership-decidability\CONTENT_ASSOCIATION_ANALYSIS.md | *本分析为内容关联修复提供了完整路线图* | `#本分析为内容关联修复提供了完整路线图` | 同文件锚点不存在: #本分析为内容关联修复提供了完整路线图 |
| docs\rust-ownership-decidability\CONTENT_UPDATE_SUMMARY_2026_03_12.md | Phase 1: 已完成 ✅ | `#phase-1-已完成-` | 同文件锚点不存在: #phase-1-已完成- |
| docs\rust-ownership-decidability\CONTENT_UPDATE_SUMMARY_2026_03_12.md | **最后更新**: 2026-03-12 | `#最后更新-2026-03-12` | 同文件锚点不存在: #最后更新-2026-03-12 |
| docs\rust-ownership-decidability\CONTINUOUS_IMPROVEMENT_ACTION_PLAN.md | Rust 所有权与可判定性 - 持续推进行动计划 | `#rust-所有权与可判定性---持续推进行动计划` | 同文件锚点不存在: #rust-所有权与可判定性---持续推进行动计划 |
| docs\rust-ownership-decidability\CROSS_REFERENCE_VERIFICATION_REPORT.md | *Report generated by check\_cross\_references.py* | `#report-generated-by-check_cross_referencespy` | 同文件锚点不存在: #report-generated-by-check_cross_referencespy |
| docs\rust-ownership-decidability\CROSS_REFERENCE_VERIFICATION_SUMMARY.md | *Completed: 2026-03-06* | `#completed-2026-03-06` | 同文件锚点不存在: #completed-2026-03-06 |
| docs\rust-ownership-decidability\DESIGN_RATIONALE.md | **最后更新**: 2026-03-14 | `#最后更新-2026-03-14` | 同文件锚点不存在: #最后更新-2026-03-14 |
| docs\rust-ownership-decidability\DOCUMENT_INDEX_MASTER.md | Rust 所有权系统 - 文档总索引 | `#rust-所有权系统---文档总索引` | 同文件锚点不存在: #rust-所有权系统---文档总索引 |
| docs\rust-ownership-decidability\DOCUMENT_INDEX_MASTER.md | 一级索引 (顶层文档 - 必读) | `#一级索引-顶层文档---必读` | 同文件锚点不存在: #一级索引-顶层文档---必读 |
| docs\rust-ownership-decidability\DOCUMENT_INDEX_MASTER.md | 三级索引 (桥梁文档 - 关键创新) | `#三级索引-桥梁文档---关键创新` | 同文件锚点不存在: #三级索引-桥梁文档---关键创新 |
| docs\rust-ownership-decidability\DOCUMENT_INDEX_MASTER.md | 00-foundations/ (理论基础 - 13 文件) | `#00-foundations-理论基础---13-文件` | 同文件锚点不存在: #00-foundations-理论基础---13-文件 |
| docs\rust-ownership-decidability\DOCUMENT_INDEX_MASTER.md | 01-core-concepts/ (核心概念 - 11 文件) | `#01-core-concepts-核心概念---11-文件` | 同文件锚点不存在: #01-core-concepts-核心概念---11-文件 |
| docs\rust-ownership-decidability\DOCUMENT_INDEX_MASTER.md | 01-core-concepts/short-concepts/ (概念卡片 - 3 文件) | `#01-core-conceptsshort-concepts-概念卡片---3-文件` | 同文件锚点不存在: #01-core-conceptsshort-concepts-概念卡片---3-文件 |
| docs\rust-ownership-decidability\DOCUMENT_INDEX_MASTER.md | 01-core-concepts/detailed-concepts/ (详细概念 - 5 文件) | `#01-core-conceptsdetailed-concepts-详细概念---5-文件` | 同文件锚点不存在: #01-core-conceptsdetailed-concepts-详细概念---5-文件 |
| docs\rust-ownership-decidability\DOCUMENT_INDEX_MASTER.md | coq-formalization/ (Coq 形式化 - 32 文件) | `#coq-formalization-coq-形式化---32-文件` | 同文件锚点不存在: #coq-formalization-coq-形式化---32-文件 |
| docs\rust-ownership-decidability\DOCUMENT_INDEX_MASTER.md | case-studies/ (案例研究 - 137 文件) | `#case-studies-案例研究---137-文件` | 同文件锚点不存在: #case-studies-案例研究---137-文件 |
| docs\rust-ownership-decidability\DOCUMENT_INDEX_MASTER.md | 11-design-patterns/ (设计模式 - 15+ 文件) | `#11-design-patterns-设计模式---15-文件` | 同文件锚点不存在: #11-design-patterns-设计模式---15-文件 |
| docs\rust-ownership-decidability\DOCUMENT_INDEX_MASTER.md | 12-concurrency-patterns/ (并发模式 - 14 文件) | `#12-concurrency-patterns-并发模式---14-文件` | 同文件锚点不存在: #12-concurrency-patterns-并发模式---14-文件 |
| docs\rust-ownership-decidability\DOCUMENT_INDEX_MASTER.md | exercises/ (练习 - 10+ 文件) | `#exercises-练习---10-文件` | 同文件锚点不存在: #exercises-练习---10-文件 |
| docs\rust-ownership-decidability\DOCUMENT_INDEX_MASTER.md | **总文档数**: 605 | `#总文档数-605` | 同文件锚点不存在: #总文档数-605 |
| docs\rust-ownership-decidability\ERROR_DIAGNOSTICS_GUIDE.md | Rust 所有权系统 - 错误诊断完全指南 | `#rust-所有权系统---错误诊断完全指南` | 同文件锚点不存在: #rust-所有权系统---错误诊断完全指南 |
| docs\rust-ownership-decidability\ERROR_DIAGNOSTICS_GUIDE.md | *本指南持续更新，欢迎贡献* | `#本指南持续更新欢迎贡献` | 同文件锚点不存在: #本指南持续更新欢迎贡献 |
| docs\rust-ownership-decidability\EXECUTIVE_SUMMARY_AND_RECOMMENDATIONS.md | *下次审查: 2026-03-14* | `#下次审查-2026-03-14` | 同文件锚点不存在: #下次审查-2026-03-14 |
| docs\rust-ownership-decidability\FAQ_COMPREHENSIVE.md | Rust 所有权系统 - 全面 FAQ | `#rust-所有权系统---全面-faq` | 同文件锚点不存在: #rust-所有权系统---全面-faq |
| docs\rust-ownership-decidability\FAQ_COMPREHENSIVE.md | **维护者**: Rust 所有权可判定性研究项目 | `#维护者-rust-所有权可判定性研究项目` | 同文件锚点不存在: #维护者-rust-所有权可判定性研究项目 |
| docs\rust-ownership-decidability\FINAL_100_PERCENT_COMPLETION_CERTIFICATION.md | Rust 所有权系统可判定性 - 最终 100% 完成认证 | `#rust-所有权系统可判定性---最终-100-完成认证` | 同文件锚点不存在: #rust-所有权系统可判定性---最终-100-完成认证 |
| docs\rust-ownership-decidability\FINAL_100_PERCENT_COMPLETION_CERTIFICATION.md | *本认证代表项目已达到所有预设目标，具备完整的理论深度、教育价值和工程实用性。* | `#本认证代表项目已达到所有预设目标具备完整的理论深度教育价值和工程实用性` | 同文件锚点不存在: #本认证代表项目已达到所有预设目标具备完整的理论深度教育价值和工程实用性 |
| docs\rust-ownership-decidability\FINAL_ASSOCIATION_COMPLETION_REPORT.md | Rust 所有权系统 - 内容关联完整性修复报告 | `#rust-所有权系统---内容关联完整性修复报告` | 同文件锚点不存在: #rust-所有权系统---内容关联完整性修复报告 |
| docs\rust-ownership-decidability\FINAL_ASSOCIATION_COMPLETION_REPORT.md | 修复 1: 理论基础 ↔ 实践代码 (P0) | `#修复-1-理论基础--实践代码-p0` | 同文件锚点不存在: #修复-1-理论基础--实践代码-p0 |
| docs\rust-ownership-decidability\FINAL_ASSOCIATION_COMPLETION_REPORT.md | 修复 2: 定理 ↔ 编译器实现 (P0) | `#修复-2-定理--编译器实现-p0` | 同文件锚点不存在: #修复-2-定理--编译器实现-p0 |
| docs\rust-ownership-decidability\FINAL_ASSOCIATION_COMPLETION_REPORT.md | 修复 3: 理论约束 ↔ 设计模式 (P1) | `#修复-3-理论约束--设计模式-p1` | 同文件锚点不存在: #修复-3-理论约束--设计模式-p1 |
| docs\rust-ownership-decidability\FINAL_ASSOCIATION_COMPLETION_REPORT.md | 修复 4: 验证工具 ↔ 理论性质 (P1) | `#修复-4-验证工具--理论性质-p1` | 同文件锚点不存在: #修复-4-验证工具--理论性质-p1 |
| docs\rust-ownership-decidability\FINAL_COMPLETE_STATUS_100_PERCENT.md | Rust 所有权系统可判定性 - 最终 100% 完成状态报告 | `#rust-所有权系统可判定性---最终-100-完成状态报告` | 同文件锚点不存在: #rust-所有权系统可判定性---最终-100-完成状态报告 |
| docs\rust-ownership-decidability\FINAL_COMPLETE_STATUS_100_PERCENT.md | 维度 1: 内容完整性 ✅ | `#维度-1-内容完整性-` | 同文件锚点不存在: #维度-1-内容完整性- |
| docs\rust-ownership-decidability\FINAL_COMPLETE_STATUS_100_PERCENT.md | 维度 2: 形式化完整性 ✅ | `#维度-2-形式化完整性-` | 同文件锚点不存在: #维度-2-形式化完整性- |
| docs\rust-ownership-decidability\FINAL_COMPLETE_STATUS_100_PERCENT.md | 维度 3: 内容关联完整性 ✅ | `#维度-3-内容关联完整性-` | 同文件锚点不存在: #维度-3-内容关联完整性- |
| docs\rust-ownership-decidability\FINAL_COMPLETE_STATUS_100_PERCENT.md | 维度 4: 学习资源完整性 ✅ | `#维度-4-学习资源完整性-` | 同文件锚点不存在: #维度-4-学习资源完整性- |
| docs\rust-ownership-decidability\FINAL_COMPLETE_STATUS_100_PERCENT.md | 成果 1: 四层知识架构 ✅ | `#成果-1-四层知识架构-` | 同文件锚点不存在: #成果-1-四层知识架构- |
| docs\rust-ownership-decidability\FINAL_COMPLETE_STATUS_100_PERCENT.md | 成果 2: 完整关联网络 ✅ | `#成果-2-完整关联网络-` | 同文件锚点不存在: #成果-2-完整关联网络- |
| docs\rust-ownership-decidability\FINAL_COMPLETE_STATUS_100_PERCENT.md | 成果 3: 完整学习体系 ✅ | `#成果-3-完整学习体系-` | 同文件锚点不存在: #成果-3-完整学习体系- |
| docs\rust-ownership-decidability\FINAL_COMPLETE_STATUS_100_PERCENT.md | 项目目标达成 ✅ | `#项目目标达成-` | 同文件锚点不存在: #项目目标达成- |
| docs\rust-ownership-decidability\FINAL_COMPLETE_STATUS_100_PERCENT.md | 100% 完成认证 ✅ | `#100-完成认证-` | 同文件锚点不存在: #100-完成认证- |
| docs\rust-ownership-decidability\FINAL_COMPLETE_STATUS_100_PERCENT.md | *本报告代表项目已达到所有预设目标，具备完整的理论深度、教育价值、工程实用性和内容关联性。* | `#本报告代表项目已达到所有预设目标具备完整的理论深度教育价值工程实用性和内容关联性` | 同文件锚点不存在: #本报告代表项目已达到所有预设目标具备完整的理论深度教育价值工程实用性和内容关联性 |
| docs\rust-ownership-decidability\FINAL_COMPLETION_CERTIFICATE.md | **🏆 项目圆满完成！🏆** | `#-项目圆满完成` | 同文件锚点不存在: #-项目圆满完成 |
| docs\rust-ownership-decidability\FINAL_COMPLETION_CERTIFICATION_2026_03_13.md | Rust 所有权与可判定性 - 最终完成认证报告 | `#rust-所有权与可判定性---最终完成认证报告` | 同文件锚点不存在: #rust-所有权与可判定性---最终完成认证报告 |
| docs\rust-ownership-decidability\FINAL_COMPLETION_CERTIFICATION_2026_03_13.md | 1.1 顶级会议论文 - 100% 对齐 | `#11-顶级会议论文---100-对齐` | 同文件锚点不存在: #11-顶级会议论文---100-对齐 |
| docs\rust-ownership-decidability\FINAL_COMPLETION_CERTIFICATION_2026_03_13.md | 1.2 官方项目动态 - 100% 对齐 | `#12-官方项目动态---100-对齐` | 同文件锚点不存在: #12-官方项目动态---100-对齐 |
| docs\rust-ownership-decidability\FINAL_COMPLETION_CERTIFICATION_2026_03_13.md | 1.3 研究机构跟踪 - 100% 对齐 | `#13-研究机构跟踪---100-对齐` | 同文件锚点不存在: #13-研究机构跟踪---100-对齐 |
| docs\rust-ownership-decidability\FINAL_COMPLETION_CERTIFICATION_2026_03_13.md | 2. 文档结构完整性 - 100% | `#2-文档结构完整性---100` | 同文件锚点不存在: #2-文档结构完整性---100 |
| docs\rust-ownership-decidability\FINAL_COMPLETION_CERTIFICATION_2026_03_13.md | 3. 形式化证明完成度 - 100% | `#3-形式化证明完成度---100` | 同文件锚点不存在: #3-形式化证明完成度---100 |
| docs\rust-ownership-decidability\FINAL_COMPLETION_CERTIFICATION_2026_03_13.md | *状态: 最终认证* | `#状态-最终认证` | 同文件锚点不存在: #状态-最终认证 |
| docs\rust-ownership-decidability\FINAL_COMPLETION_REPORT.md | Rust 所有权系统形式化 - 最终完成报告 | `#rust-所有权系统形式化---最终完成报告` | 同文件锚点不存在: #rust-所有权系统形式化---最终完成报告 |
| docs\rust-ownership-decidability\FINAL_COMPLETION_REPORT.md | *报告生成时间: 2026-03-11*: | `#报告生成时间-2026-03-11` | 同文件锚点不存在: #报告生成时间-2026-03-11 |
| docs\rust-ownership-decidability\FINAL_DOCUMENTATION.md | Rust 所有权系统可判定性 - 完整文档 | `#rust-所有权系统可判定性---完整文档` | 同文件锚点不存在: #rust-所有权系统可判定性---完整文档 |
| docs\rust-ownership-decidability\FINAL_EXECUTIVE_SUMMARY.md | *"严格形式化是可信软件的基石。"* | `#严格形式化是可信软件的基石` | 同文件锚点不存在: #严格形式化是可信软件的基石 |
| docs\rust-ownership-decidability\FINAL_EXECUTIVE_SUMMARY_V2.md | Rust 所有权系统可判定性 - 最终执行摘要 (V2) | `#rust-所有权系统可判定性---最终执行摘要-v2` | 同文件锚点不存在: #rust-所有权系统可判定性---最终执行摘要-v2 |
| docs\rust-ownership-decidability\FINAL_EXECUTIVE_SUMMARY_V2.md | Final Executive Summary - Comprehensive Edition | `#final-executive-summary---comprehensive-edition` | 同文件锚点不存在: #final-executive-summary---comprehensive-edition |
| docs\rust-ownership-decidability\FINAL_EXECUTIVE_SUMMARY_V2.md | 🛠️ 验证工具链 | `#️-验证工具链` | 同文件锚点不存在: #️-验证工具链 |
| docs\rust-ownership-decidability\FINAL_MASTER_INDEX.md | Rust 所有权系统 - 主索引 (Master Index) | `#rust-所有权系统---主索引-master-index` | 同文件锚点不存在: #rust-所有权系统---主索引-master-index |
| docs\rust-ownership-decidability\FINAL_MASTER_INDEX.md | 🗂️ 元模型 | `#️-元模型` | 同文件锚点不存在: #️-元模型 |
| docs\rust-ownership-decidability\FINAL_MASTER_INDEX.md | 🏗️ 知识结构 | `#️-知识结构` | 同文件锚点不存在: #️-知识结构 |
| docs\rust-ownership-decidability\FINAL_MASTER_INDEX.md | **🎉 知识库完整，欢迎使用！🎉**: | `#-知识库完整欢迎使用` | 同文件锚点不存在: #-知识库完整欢迎使用 |
| docs\rust-ownership-decidability\FINAL_ULTIMATE_COMPLETION_REPORT.md | Rust 所有权系统可判定性 - 终极完成报告 | `#rust-所有权系统可判定性---终极完成报告` | 同文件锚点不存在: #rust-所有权系统可判定性---终极完成报告 |
| docs\rust-ownership-decidability\FINAL_ULTIMATE_COMPLETION_REPORT.md | 项目目标完全达成 ✅ | `#项目目标完全达成-` | 同文件锚点不存在: #项目目标完全达成- |
| docs\rust-ownership-decidability\FINAL_ULTIMATE_COMPLETION_REPORT.md | **状态**: ✅ 终极完成 | `#状态--终极完成` | 同文件锚点不存在: #状态--终极完成 |
| docs\rust-ownership-decidability\FINAL_VERIFICATION_100_PERCENT.md | ✅ 最终验证报告 - 100% 完成确认 | `#-最终验证报告---100-完成确认` | 同文件锚点不存在: #-最终验证报告---100-完成确认 |
| docs\rust-ownership-decidability\FINAL_VERIFICATION_100_PERCENT.md | 1. 内容完整性 ✅ | `#1-内容完整性-` | 同文件锚点不存在: #1-内容完整性- |
| docs\rust-ownership-decidability\FINAL_VERIFICATION_100_PERCENT.md | 2. 学术对齐性 ✅ | `#2-学术对齐性-` | 同文件锚点不存在: #2-学术对齐性- |
| docs\rust-ownership-decidability\FINAL_VERIFICATION_100_PERCENT.md | 3. 技术准确性 ✅ | `#3-技术准确性-` | 同文件锚点不存在: #3-技术准确性- |
| docs\rust-ownership-decidability\FINAL_VERIFICATION_100_PERCENT.md | 4. 文档质量 ✅ | `#4-文档质量-` | 同文件锚点不存在: #4-文档质量- |
| docs\rust-ownership-decidability\FINAL_VERIFICATION_100_PERCENT.md | 5. 实用性 ✅ | `#5-实用性-` | 同文件锚点不存在: #5-实用性- |
| docs\rust-ownership-decidability\FOUNDATIONS_TO_PRACTICE_BRIDGE.md | 一、线性逻辑 → 所有权系统 | `#一线性逻辑--所有权系统` | 同文件锚点不存在: #一线性逻辑--所有权系统 |
| docs\rust-ownership-decidability\FOUNDATIONS_TO_PRACTICE_BRIDGE.md | 二、仿射类型 → 借用系统 | `#二仿射类型--借用系统` | 同文件锚点不存在: #二仿射类型--借用系统 |
| docs\rust-ownership-decidability\FOUNDATIONS_TO_PRACTICE_BRIDGE.md | 三、区域类型 → 生命周期 | `#三区域类型--生命周期` | 同文件锚点不存在: #三区域类型--生命周期 |
| docs\rust-ownership-decidability\FOUNDATIONS_TO_PRACTICE_BRIDGE.md | 四、分离逻辑 → 内存安全 | `#四分离逻辑--内存安全` | 同文件锚点不存在: #四分离逻辑--内存安全 |
| docs\rust-ownership-decidability\FOUNDATIONS_TO_PRACTICE_BRIDGE.md | 五、类型论 → Rust 类型系统 | `#五类型论--rust-类型系统` | 同文件锚点不存在: #五类型论--rust-类型系统 |
| docs\rust-ownership-decidability\FOUNDATIONS_TO_PRACTICE_BRIDGE.md | *本文档建立了从数学理论到 Rust 代码的完整桥梁* | `#本文档建立了从数学理论到-rust-代码的完整桥梁` | 同文件锚点不存在: #本文档建立了从数学理论到-rust-代码的完整桥梁 |
| docs\rust-ownership-decidability\FRAMEWORK_ANALYSIS_AND_GAP_REPORT.md | 3.1 短期计划 (1-2周) - 框架补充 | `#31-短期计划-1-2周---框架补充` | 同文件锚点不存在: #31-短期计划-1-2周---框架补充 |
| docs\rust-ownership-decidability\FRAMEWORK_ANALYSIS_AND_GAP_REPORT.md | 3.2 中期计划 (3-4周) - 深度扩展 | `#32-中期计划-3-4周---深度扩展` | 同文件锚点不存在: #32-中期计划-3-4周---深度扩展 |
| docs\rust-ownership-decidability\FRAMEWORK_ANALYSIS_AND_GAP_REPORT.md | 3.3 长期计划 (1-3个月) - 研究前沿 | `#33-长期计划-1-3个月---研究前沿` | 同文件锚点不存在: #33-长期计划-1-3个月---研究前沿 |
| docs\rust-ownership-decidability\FRAMEWORK_ANALYSIS_AND_GAP_REPORT.md | **下一步**: 立即开始任务 A, B, C | `#下一步-立即开始任务-a-b-c` | 同文件锚点不存在: #下一步-立即开始任务-a-b-c |
| docs\rust-ownership-decidability\FRAMEWORK_COMPLETION_SUMMARY.md | *框架已完整，可以在此基础上继续深入研究。* | `#框架已完整可以在此基础上继续深入研究` | 同文件锚点不存在: #框架已完整可以在此基础上继续深入研究 |
| docs\rust-ownership-decidability\HORIZONTAL_CONNECTIONS.md | **下一篇**：阅读 `HISTORICAL_EVOLUTION.md` 了解理论的历史演化。 | `#下一篇阅读-historical_evolutionmd-了解理论的历史演化` | 同文件锚点不存在: #下一篇阅读-historical_evolutionmd-了解理论的历史演化 |
| docs\rust-ownership-decidability\INITIAL_PHASE_COMPLETION_REPORT.md | **状态**: ✅ 初始阶段完成，持续推进中 | `#状态--初始阶段完成持续推进中` | 同文件锚点不存在: #状态--初始阶段完成持续推进中 |
| docs\rust-ownership-decidability\INTERACTIVE_LEARNING_GUIDE.md | Rust 所有权系统 - 交互式学习指南 | `#rust-所有权系统---交互式学习指南` | 同文件锚点不存在: #rust-所有权系统---交互式学习指南 |
| docs\rust-ownership-decidability\INTERACTIVE_LEARNING_GUIDE.md | **最后更新**: 2026-03-14 | `#最后更新-2026-03-14` | 同文件锚点不存在: #最后更新-2026-03-14 |
| docs\rust-ownership-decidability\LEARNING_ROADMAP_DETAILED.md | Rust 所有权系统 - 详细学习路线图 | `#rust-所有权系统---详细学习路线图` | 同文件锚点不存在: #rust-所有权系统---详细学习路线图 |
| docs\rust-ownership-decidability\LEARNING_ROADMAP_DETAILED.md | Level 0 → Level 1: 入门 (4小时) | `#level-0--level-1-入门-4小时` | 同文件锚点不存在: #level-0--level-1-入门-4小时 |
| docs\rust-ownership-decidability\LEARNING_ROADMAP_DETAILED.md | Level 1 → Level 2: 初级 (1周) | `#level-1--level-2-初级-1周` | 同文件锚点不存在: #level-1--level-2-初级-1周 |
| docs\rust-ownership-decidability\LEARNING_ROADMAP_DETAILED.md | Level 2 → Level 3: 中级 (2周) | `#level-2--level-3-中级-2周` | 同文件锚点不存在: #level-2--level-3-中级-2周 |
| docs\rust-ownership-decidability\LEARNING_ROADMAP_DETAILED.md | Level 3 → Level 4: 高级 (1月) | `#level-3--level-4-高级-1月` | 同文件锚点不存在: #level-3--level-4-高级-1月 |
| docs\rust-ownership-decidability\LEARNING_ROADMAP_DETAILED.md | Level 4 → Level 5: 专家 (持续) | `#level-4--level-5-专家-持续` | 同文件锚点不存在: #level-4--level-5-专家-持续 |
| docs\rust-ownership-decidability\LEARNING_ROADMAP_DETAILED.md | *跟随这个路线图，从新手到专家* | `#跟随这个路线图从新手到专家` | 同文件锚点不存在: #跟随这个路线图从新手到专家 |
| docs\rust-ownership-decidability\MASTER_COMPREHENSIVE_ANALYSIS.md | Rust 所有权系统 - 全面结构化分析 | `#rust-所有权系统---全面结构化分析` | 同文件锚点不存在: #rust-所有权系统---全面结构化分析 |
| docs\rust-ownership-decidability\MASTER_INDEX_AUTO.md | *This index was auto-generated. Last updated: 2026-03-06T11:41:17.918595* | `#this-index-was-auto-generated-last-updated-2026-03-06t114117918595` | 同文件锚点不存在: #this-index-was-auto-generated-last-updated-2026-03-06t114117918595 |
| docs\rust-ownership-decidability\NATURAL_LANGUAGE_ARGUMENTATION_INDEX.md | **开始探索**：建议从 `OVERVIEW_AND_INTUITION.md` 开始阅读！ | `#开始探索建议从-overview_and_intuitionmd-开始阅读` | 同文件锚点不存在: #开始探索建议从-overview_and_intuitionmd-开始阅读 |
| docs\rust-ownership-decidability\NATURAL_LANGUAGE_COMPLETION_REPORT.md | 自然语言 ↔ Coq 代码 映射 | `#自然语言--coq-代码-映射` | 同文件锚点不存在: #自然语言--coq-代码-映射 |
| docs\rust-ownership-decidability\NATURAL_LANGUAGE_COMPLETION_REPORT.md | *状态: 完成 ✅* | `#状态-完成-` | 同文件锚点不存在: #状态-完成- |
| docs\rust-ownership-decidability\OVERVIEW_AND_INTUITION.md | Rust 所有权系统形式化 - 总览与直观理解 | `#rust-所有权系统形式化---总览与直观理解` | 同文件锚点不存在: #rust-所有权系统形式化---总览与直观理解 |
| docs\rust-ownership-decidability\OVERVIEW_AND_INTUITION.md | 步骤1：类型正确 ⟹ 借用检查通过 | `#步骤1类型正确--借用检查通过` | 同文件锚点不存在: #步骤1类型正确--借用检查通过 |
| docs\rust-ownership-decidability\OVERVIEW_AND_INTUITION.md | 步骤2：借用检查通过 ⟹ 所有权安全 | `#步骤2借用检查通过--所有权安全` | 同文件锚点不存在: #步骤2借用检查通过--所有权安全 |
| docs\rust-ownership-decidability\OVERVIEW_AND_INTUITION.md | 步骤3：所有权安全 ⟹ 内存安全 | `#步骤3所有权安全--内存安全` | 同文件锚点不存在: #步骤3所有权安全--内存安全 |
| docs\rust-ownership-decidability\PHASE2_COMPLETION_REPORT.md | **状态**: ✅ Phase 2 完成，建议进入 Phase 3 (持续维护) | `#状态--phase-2-完成建议进入-phase-3-持续维护` | 同文件锚点不存在: #状态--phase-2-完成建议进入-phase-3-持续维护 |
| docs\rust-ownership-decidability\PROJECT_COMPREHENSIVE_AUDIT_REPORT.md | Rust 所有权可判定性项目 - 全面审计报告 | `#rust-所有权可判定性项目---全面审计报告` | 同文件锚点不存在: #rust-所有权可判定性项目---全面审计报告 |
| docs\rust-ownership-decidability\PROJECT_COMPREHENSIVE_AUDIT_REPORT.md | 4.1 高优先级缺失 🔴 | `#41-高优先级缺失-` | 同文件锚点不存在: #41-高优先级缺失- |
| docs\rust-ownership-decidability\PROJECT_COMPREHENSIVE_AUDIT_REPORT.md | 4.2 中优先级缺失 🟡 | `#42-中优先级缺失-` | 同文件锚点不存在: #42-中优先级缺失- |
| docs\rust-ownership-decidability\PROJECT_COMPREHENSIVE_AUDIT_REPORT.md | 4.3 低优先级缺失 🟢 | `#43-低优先级缺失-` | 同文件锚点不存在: #43-低优先级缺失- |
| docs\rust-ownership-decidability\PROJECT_COMPREHENSIVE_AUDIT_REPORT.md | 阶段一: 填补关键缺失 (4周) 🔴 | `#阶段一-填补关键缺失-4周-` | 同文件锚点不存在: #阶段一-填补关键缺失-4周- |
| docs\rust-ownership-decidability\PROJECT_COMPREHENSIVE_AUDIT_REPORT.md | 阶段二: 内容深化 (4周) 🟡 | `#阶段二-内容深化-4周-` | 同文件锚点不存在: #阶段二-内容深化-4周- |
| docs\rust-ownership-decidability\PROJECT_COMPREHENSIVE_AUDIT_REPORT.md | 阶段三: 对齐优化 (4周) 🟢 | `#阶段三-对齐优化-4周-` | 同文件锚点不存在: #阶段三-对齐优化-4周- |
| docs\rust-ownership-decidability\PROJECT_COMPREHENSIVE_AUDIT_REPORT.md | *版本: v1.0* | `#版本-v10` | 同文件锚点不存在: #版本-v10 |
| docs\rust-ownership-decidability\PROJECT_STRUCTURE.md | Rust 所有权可判定性 - 项目结构 | `#rust-所有权可判定性---项目结构` | 同文件锚点不存在: #rust-所有权可判定性---项目结构 |
| docs\rust-ownership-decidability\PROJECT_STRUCTURE.md | *项目结构清晰，易于导航和维护* | `#项目结构清晰易于导航和维护` | 同文件锚点不存在: #项目结构清晰易于导航和维护 |
| docs\rust-ownership-decidability\PROOF_STRATEGIES.md | **最后更新**: 2026-03-14 | `#最后更新-2026-03-14` | 同文件锚点不存在: #最后更新-2026-03-14 |
| docs\rust-ownership-decidability\QUICK_REFERENCE_CARD.md | Rust 所有权系统 - 快速参考卡片 | `#rust-所有权系统---快速参考卡片` | 同文件锚点不存在: #rust-所有权系统---快速参考卡片 |
| docs\rust-ownership-decidability\QUICK_REFERENCE_CARD.md | ⏱️ 生命周期规则 | `#️-生命周期规则` | 同文件锚点不存在: #️-生命周期规则 |
| docs\rust-ownership-decidability\QUICK_REFERENCE_CARD.md | **最后更新**: 2026-03-14 | `#最后更新-2026-03-14` | 同文件锚点不存在: #最后更新-2026-03-14 |
| docs\rust-ownership-decidability\READING_GUIDE.md | **最后更新**: 2026-03-14 | `#最后更新-2026-03-14` | 同文件锚点不存在: #最后更新-2026-03-14 |
| docs\rust-ownership-decidability\README.md | 概念卡片 | `#-基础概念速查` | 同文件锚点不存在: #-基础概念速查 |
| docs\rust-ownership-decidability\README.md | 核心概念 | `#01-核心概念` | 同文件锚点不存在: #01-核心概念 |
| docs\rust-ownership-decidability\README.md | 练习题 | `#-练习与实践` | 同文件锚点不存在: #-练习与实践 |
| docs\rust-ownership-decidability\README.md | 详细概念 | `#01-核心概念` | 同文件锚点不存在: #01-核心概念 |
| docs\rust-ownership-decidability\README.md | 设计模式 | `#11-设计模式` | 同文件锚点不存在: #11-设计模式 |
| docs\rust-ownership-decidability\README.md | 案例研究 | `#-案例研究` | 同文件锚点不存在: #-案例研究 |
| docs\rust-ownership-decidability\README.md | 形式化基础 | `#-形式化理论` | 同文件锚点不存在: #-形式化理论 |
| docs\rust-ownership-decidability\README.md | 证明与定理 | `#-coq形式化` | 同文件锚点不存在: #-coq形式化 |
| docs\rust-ownership-decidability\README.md | Coq代码 | `#-coq形式化` | 同文件锚点不存在: #-coq形式化 |
| docs\rust-ownership-decidability\RUST_194_100%_COMPLETE_FINAL.md | Rust 1.94 所有权形式化对齐 - 100% 完成 (最终报告) | `#rust-194-所有权形式化对齐---100-完成-最终报告` | 同文件锚点不存在: #rust-194-所有权形式化对齐---100-完成-最终报告 |
| docs\rust-ownership-decidability\RUST_194_100%_COMPLETE_FINAL.md | **✅ 任务圆满完成！** 🏆 | `#-任务圆满完成-` | 同文件锚点不存在: #-任务圆满完成- |
| docs\rust-ownership-decidability\RUST_194_100_PERCENT_COMPLETION_FINAL.md | Rust 1.94 Alignment - 100% Completion Final Report | `#rust-194-alignment---100-completion-final-report` | 同文件锚点不存在: #rust-194-alignment---100-completion-final-report |
| docs\rust-ownership-decidability\RUST_194_100_PERCENT_COMPLETION_FINAL.md | 2.1 All 17 Core Concept Documents Updated ✅ | `#21-all-17-core-concept-documents-updated-` | 同文件锚点不存在: #21-all-17-core-concept-documents-updated- |
| docs\rust-ownership-decidability\RUST_194_100_PERCENT_COMPLETION_FINAL.md | 2.2 All 8 Concurrency Pattern Documents Updated ✅ | `#22-all-8-concurrency-pattern-documents-updated-` | 同文件锚点不存在: #22-all-8-concurrency-pattern-documents-updated- |
| docs\rust-ownership-decidability\RUST_194_100_PERCENT_COMPLETION_FINAL.md | 2.3 39+ New Code Examples Added and Verified ✅ | `#23-39-new-code-examples-added-and-verified-` | 同文件锚点不存在: #23-39-new-code-examples-added-and-verified- |
| docs\rust-ownership-decidability\RUST_194_100_PERCENT_COMPLETION_FINAL.md | 2.4 Standard Library API Guide (993 Lines) ✅ | `#24-standard-library-api-guide-993-lines-` | 同文件锚点不存在: #24-standard-library-api-guide-993-lines- |
| docs\rust-ownership-decidability\RUST_194_100_PERCENT_COMPLETION_FINAL.md | 2.6 Cross-References Verified ✅ | `#26-cross-references-verified-` | 同文件锚点不存在: #26-cross-references-verified- |
| docs\rust-ownership-decidability\RUST_194_100_PERCENT_COMPLETION_FINAL.md | 3.1 Code Compilation: 100% Pass ✅ | `#31-code-compilation-100-pass-` | 同文件锚点不存在: #31-code-compilation-100-pass- |
| docs\rust-ownership-decidability\RUST_194_100_PERCENT_COMPLETION_FINAL.md | 3.2 Link Checking: 100% Pass ✅ | `#32-link-checking-100-pass-` | 同文件锚点不存在: #32-link-checking-100-pass- |
| docs\rust-ownership-decidability\RUST_194_100_PERCENT_COMPLETION_FINAL.md | 3.3 Coq Syntax: 100% Valid ✅ | `#33-coq-syntax-100-valid-` | 同文件锚点不存在: #33-coq-syntax-100-valid- |
| docs\rust-ownership-decidability\RUST_194_100_PERCENT_COMPLETION_FINAL.md | *"Formal methods require honesty about both achievements and limitations. This report reflects the true state of the project."* | `#formal-methods-require-honesty-about-both-achievements-and-limitations-this-report-reflects-the-true-state-of-the-project` | 同文件锚点不存在: #formal-methods-require-honesty-about-both-achievements-and-limitations-this-report-reflects-the-true-state-of-the-project |
| docs\rust-ownership-decidability\RUST_194_100_PERCENT_COMPLETION_REPORT.md | Rust 1.94 所有权形式化对齐 - 100% 完成报告 | `#rust-194-所有权形式化对齐---100-完成报告` | 同文件锚点不存在: #rust-194-所有权形式化对齐---100-完成报告 |
| docs\rust-ownership-decidability\RUST_194_100_PERCENT_COMPLETION_REPORT.md | *"构建 Rust 所有权系统的完整、严格、可机械化的形式化理论"* ✅ | `#构建-rust-所有权系统的完整严格可机械化的形式化理论-` | 同文件锚点不存在: #构建-rust-所有权系统的完整严格可机械化的形式化理论- |
| docs\rust-ownership-decidability\RUST_194_ALIGNMENT_FINAL_REPORT.md | 真实特性 ✅ | `#真实特性-` | 同文件锚点不存在: #真实特性- |
| docs\rust-ownership-decidability\RUST_194_ALIGNMENT_FINAL_REPORT.md | 虚构特性 ❌ (需移除或标记) | `#虚构特性--需移除或标记` | 同文件锚点不存在: #虚构特性--需移除或标记 |
| docs\rust-ownership-decidability\RUST_194_ALIGNMENT_FINAL_REPORT.md | ⚠️ 发现的问题与修正 | `#️-发现的问题与修正` | 同文件锚点不存在: #️-发现的问题与修正 |
| docs\rust-ownership-decidability\RUST_194_ALIGNMENT_FINAL_REPORT.md | **下次审查**: 虚构特性清理完成后 | `#下次审查-虚构特性清理完成后` | 同文件锚点不存在: #下次审查-虚构特性清理完成后 |
| docs\rust-ownership-decidability\RUST_194_ALIGNMENT_PLAN.md | *预计完成时间: 2026-07-15 (14-20周)* | `#预计完成时间-2026-07-15-14-20周` | 同文件锚点不存在: #预计完成时间-2026-07-15-14-20周 |
| docs\rust-ownership-decidability\RUST_194_ALIGNMENT_PROGRESS.md | ✅ Reborrow Trait (`Reborrow.v`) - 100% | `#-reborrow-trait-reborrowv---100` | 同文件锚点不存在: #-reborrow-trait-reborrowv---100 |
| docs\rust-ownership-decidability\RUST_194_ALIGNMENT_PROGRESS.md | ✅ CoerceShared Trait (`CoerceShared.v`) - 100% | `#-coerceshared-trait-coercesharedv---100` | 同文件锚点不存在: #-coerceshared-trait-coercesharedv---100 |
| docs\rust-ownership-decidability\RUST_194_ALIGNMENT_PROGRESS.md | ✅ Const Generics (`ConstGenerics.v`) - 100% | `#-const-generics-constgenericsv---100` | 同文件锚点不存在: #-const-generics-constgenericsv---100 |
| docs\rust-ownership-decidability\RUST_194_ALIGNMENT_PROGRESS.md | ✅ Precise Capturing (`PreciseCapturing.v`) - 100% | `#-precise-capturing-precisecapturingv---100` | 同文件锚点不存在: #-precise-capturing-precisecapturingv---100 |
| docs\rust-ownership-decidability\RUST_194_ALIGNMENT_PROGRESS.md | ✅ 2024 Edition (`Edition2024.v`) - 100% | `#-2024-edition-edition2024v---100` | 同文件锚点不存在: #-2024-edition-edition2024v---100 |
| docs\rust-ownership-decidability\RUST_194_ALIGNMENT_PROGRESS.md | ✅ Associated Type Bounds (`AssociatedTypeBounds.v`) - 100% | `#-associated-type-bounds-associatedtypeboundsv---100` | 同文件锚点不存在: #-associated-type-bounds-associatedtypeboundsv---100 |
| docs\rust-ownership-decidability\RUST_194_ALIGNMENT_PROGRESS.md | ✅ New Lints (`NewLints.v`) - 100% | `#-new-lints-newlintsv---100` | 同文件锚点不存在: #-new-lints-newlintsv---100 |
| docs\rust-ownership-decidability\RUST_194_ALIGNMENT_PROGRESS.md | ✅ Async Basics (`AsyncBasics.v`) - 100% | `#-async-basics-asyncbasicsv---100` | 同文件锚点不存在: #-async-basics-asyncbasicsv---100 |
| docs\rust-ownership-decidability\RUST_194_ALIGNMENT_PROGRESS.md | ✅ MetatheoryIntegration.v - 100% | `#-metatheoryintegrationv---100` | 同文件锚点不存在: #-metatheoryintegrationv---100 |
| docs\rust-ownership-decidability\RUST_194_ALIGNMENT_PROGRESS.md | ✅ MetatheoryComplete.v - 100% | `#-metatheorycompletev---100` | 同文件锚点不存在: #-metatheorycompletev---100 |
| docs\rust-ownership-decidability\RUST_194_ALIGNMENT_PROGRESS.md | ✅ Rust194Complete.v - 100% | `#-rust194completev---100` | 同文件锚点不存在: #-rust194completev---100 |
| docs\rust-ownership-decidability\RUST_194_ALIGNMENT_PROGRESS.md | *完成标记: ✅* | `#完成标记-` | 同文件锚点不存在: #完成标记- |
| docs\rust-ownership-decidability\RUST_194_ALIGNMENT_SUMMARY_2026_03_12.md | Rust 1.94 Alignment - 全面推进完成总结 | `#rust-194-alignment---全面推进完成总结` | 同文件锚点不存在: #rust-194-alignment---全面推进完成总结 |
| docs\rust-ownership-decidability\RUST_194_ALIGNMENT_SUMMARY_2026_03_12.md | **状态**: ✅ 完成 | `#状态--完成` | 同文件锚点不存在: #状态--完成 |
| docs\rust-ownership-decidability\RUST_194_FINAL_100_PERCENT_SUMMARY.md | Rust 1.94 100% 对齐完成 - 最终总结报告 | `#rust-194-100-对齐完成---最终总结报告` | 同文件锚点不存在: #rust-194-100-对齐完成---最终总结报告 |
| docs\rust-ownership-decidability\RUST_194_FINAL_100_PERCENT_SUMMARY.md | **状态**: ✅ **100% 完成** | `#状态--100-完成` | 同文件锚点不存在: #状态--100-完成 |
| docs\rust-ownership-decidability\RUST_194_FINAL_COMPLETION.md | Rust 1.94 对齐 - 最终完成报告 | `#rust-194-对齐---最终完成报告` | 同文件锚点不存在: #rust-194-对齐---最终完成报告 |
| docs\rust-ownership-decidability\RUST_194_FINAL_COMPLETION.md | *项目圆满完成！* 🎊🎊🎊 | `#项目圆满完成-` | 同文件锚点不存在: #项目圆满完成- |
| docs\rust-ownership-decidability\RUST_194_FINAL_SUMMARY.md | Rust 1.94 对齐 - 最终完成总结 | `#rust-194-对齐---最终完成总结` | 同文件锚点不存在: #rust-194-对齐---最终完成总结 |
| docs\rust-ownership-decidability\RUST_194_FINAL_SUMMARY.md | *Rust 1.94 所有权形式化对齐项目圆满结束！* 🎊 | `#rust-194-所有权形式化对齐项目圆满结束-` | 同文件锚点不存在: #rust-194-所有权形式化对齐项目圆满结束- |
| docs\rust-ownership-decidability\RUST_194_OWNERSHIP_INDEX.md | Rust 所有权与可判定性 - Rust 1.94 索引 | `#rust-所有权与可判定性---rust-194-索引` | 同文件锚点不存在: #rust-所有权与可判定性---rust-194-索引 |
| docs\rust-ownership-decidability\RUST_194_OWNERSHIP_INDEX.md | **最后更新**: 2026-03-14 | `#最后更新-2026-03-14` | 同文件锚点不存在: #最后更新-2026-03-14 |
| docs\rust-ownership-decidability\RUST_194_PO_100_PERCENT_FINAL.md | Rust 1.94 对齐 - P0 关键证明 100% 完成报告 | `#rust-194-对齐---p0-关键证明-100-完成报告` | 同文件锚点不存在: #rust-194-对齐---p0-关键证明-100-完成报告 |
| docs\rust-ownership-decidability\RUST_194_PO_100_PERCENT_FINAL.md | 1. 类型安全定理 ✅ | `#1-类型安全定理-` | 同文件锚点不存在: #1-类型安全定理- |
| docs\rust-ownership-decidability\RUST_194_PO_100_PERCENT_FINAL.md | 2. 进展性定理 ✅ | `#2-进展性定理-` | 同文件锚点不存在: #2-进展性定理- |
| docs\rust-ownership-decidability\RUST_194_PO_100_PERCENT_FINAL.md | 3. 保持性定理 ✅ | `#3-保持性定理-` | 同文件锚点不存在: #3-保持性定理- |
| docs\rust-ownership-decidability\RUST_194_PO_100_PERCENT_FINAL.md | 4. 终止性定理 ✅ | `#4-终止性定理-` | 同文件锚点不存在: #4-终止性定理- |
| docs\rust-ownership-decidability\RUST_194_PO_100_PERCENT_FINAL.md | 5. 可判定性定理 ✅ | `#5-可判定性定理-` | 同文件锚点不存在: #5-可判定性定理- |
| docs\rust-ownership-decidability\RUST_194_PO_100_PERCENT_FINAL.md | 6. 精确捕获定理 ✅ | `#6-精确捕获定理-` | 同文件锚点不存在: #6-精确捕获定理- |
| docs\rust-ownership-decidability\RUST_194_PO_100_PERCENT_FINAL.md | 7. 向后兼容性定理 ✅ | `#7-向后兼容性定理-` | 同文件锚点不存在: #7-向后兼容性定理- |
| docs\rust-ownership-decidability\RUST_194_PO_100_PERCENT_FINAL.md | 8. Async 安全定理 ✅ | `#8-async-安全定理-` | 同文件锚点不存在: #8-async-安全定理- |
| docs\rust-ownership-decidability\RUST_194_PO_100_PERCENT_FINAL.md | 核心安全性质 ✅ | `#核心安全性质-` | 同文件锚点不存在: #核心安全性质- |
| docs\rust-ownership-decidability\RUST_194_PO_100_PERCENT_FINAL.md | 新特性验证 ✅ | `#新特性验证-` | 同文件锚点不存在: #新特性验证- |
| docs\rust-ownership-decidability\RUST_194_PO_100_PERCENT_FINAL.md | *Rust 1.94 所有权形式化 - P0 关键证明全部完成！* 🎊🎊🎊 | `#rust-194-所有权形式化---p0-关键证明全部完成-` | 同文件锚点不存在: #rust-194-所有权形式化---p0-关键证明全部完成- |
| docs\rust-ownership-decidability\RUST_194_TRUE_100_PERCENT_REPORT.md | Rust 1.94 所有权形式化 - 真实100%完成报告 | `#rust-194-所有权形式化---真实100完成报告` | 同文件锚点不存在: #rust-194-所有权形式化---真实100完成报告 |
| docs\rust-ownership-decidability\RUST_194_TRUE_100_PERCENT_REPORT.md | 已完成的关键定理 ✅ | `#已完成的关键定理-` | 同文件锚点不存在: #已完成的关键定理- |
| docs\rust-ownership-decidability\RUST_194_TRUE_100_PERCENT_REPORT.md | 框架完成的关键定理 🔄 | `#框架完成的关键定理-` | 同文件锚点不存在: #框架完成的关键定理- |
| docs\rust-ownership-decidability\RUST_194_TRUE_100_PERCENT_REPORT.md | 已完成 ✅ | `#已完成-` | 同文件锚点不存在: #已完成- |
| docs\rust-ownership-decidability\RUST_194_TRUE_100_PERCENT_REPORT.md | 进行中 🔄 | `#进行中-` | 同文件锚点不存在: #进行中- |
| docs\rust-ownership-decidability\RUST_194_TRUE_100_PERCENT_REPORT.md | *"构建 Rust 所有权系统的完整、严格、可机械化的形式化理论"* ✅✅✅ | `#构建-rust-所有权系统的完整严格可机械化的形式化理论-` | 同文件锚点不存在: #构建-rust-所有权系统的完整严格可机械化的形式化理论- |
| docs\rust-ownership-decidability\RUST_194_VS_193_COMPARISON.md | 2.2 `array_windows` - Slice Iteration Enhancement (1.94) | `#22-array_windows---slice-iteration-enhancement-194` | 同文件锚点不存在: #22-array_windows---slice-iteration-enhancement-194 |
| docs\rust-ownership-decidability\RUST_194_VS_193_COMPARISON.md | *This document was generated based on official Rust release notes and verified against the actual compiler behavior.* | `#this-document-was-generated-based-on-official-rust-release-notes-and-verified-against-the-actual-compiler-behavior` | 同文件锚点不存在: #this-document-was-generated-based-on-official-rust-release-notes-and-verified-against-the-actual-compiler-behavior |
| docs\rust-ownership-decidability\RUST_OWNERSHIP_DECIDABILITY_RESEARCH_PLAN.md | Rust 所有权系统可判定性 - 严格形式化研究计划 | `#rust-所有权系统可判定性---严格形式化研究计划` | 同文件锚点不存在: #rust-所有权系统可判定性---严格形式化研究计划 |
| docs\rust-ownership-decidability\RUST_OWNERSHIP_DECIDABILITY_RESEARCH_PLAN.md | **下次评审日期**: 2026-04-05 | `#下次评审日期-2026-04-05` | 同文件锚点不存在: #下次评审日期-2026-04-05 |
| docs\rust-ownership-decidability\SEMANTIC_EXPANSION_ROADMAP.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\rust-ownership-decidability\SEMANTIC_EXPANSION_ROADMAP.md | 🗺️ 扩展路线图 | `#️-扩展路线图` | 同文件锚点不存在: #️-扩展路线图 |
| docs\rust-ownership-decidability\SEMANTIC_EXPANSION_ROADMAP.md | **预计完成**: 2026-04-15 | `#预计完成-2026-04-15` | 同文件锚点不存在: #预计完成-2026-04-15 |
| docs\rust-ownership-decidability\SEMANTIC_EXPANSION_ROADMAP.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\rust-ownership-decidability\SEMANTIC_EXPANSION_ROADMAP.md | 🗺️ 扩展路线图 | `#️-扩展路线图` | 同文件锚点不存在: #️-扩展路线图 |
| docs\rust-ownership-decidability\SEMANTIC_EXPANSION_ROADMAP.md | **预计完成**: 2026-04-15 | `#预计完成-2026-04-15` | 同文件锚点不存在: #预计完成-2026-04-15 |
| docs\rust-ownership-decidability\TECHNICAL_DEBT.md | Rust 1.94 形式化 - 技术债务跟踪 (准确版) | `#rust-194-形式化---技术债务跟踪-准确版` | 同文件锚点不存在: #rust-194-形式化---技术债务跟踪-准确版 |
| docs\rust-ownership-decidability\TECHNICAL_DEBT.md | 1. MetatheoryDecidability.v (5/5) ✅ | `#1-metatheorydecidabilityv-55-` | 同文件锚点不存在: #1-metatheorydecidabilityv-55- |
| docs\rust-ownership-decidability\TECHNICAL_DEBT.md | 2. MetatheoryTermination.v (5/5) ✅ | `#2-metatheoryterminationv-55-` | 同文件锚点不存在: #2-metatheoryterminationv-55- |
| docs\rust-ownership-decidability\TECHNICAL_DEBT.md | 3. PreciseCapturingComplete.v (4/4) ✅ | `#3-precisecapturingcompletev-44-` | 同文件锚点不存在: #3-precisecapturingcompletev-44- |
| docs\rust-ownership-decidability\TECHNICAL_DEBT.md | 4. AsyncBasicsComplete.v (5/5) ✅ | `#4-asyncbasicscompletev-55-` | 同文件锚点不存在: #4-asyncbasicscompletev-55- |
| docs\rust-ownership-decidability\TECHNICAL_DEBT.md | **状态: P0 证明 100% 完成，非P0证明部分完成** | `#状态-p0-证明-100-完成非p0证明部分完成` | 同文件锚点不存在: #状态-p0-证明-100-完成非p0证明部分完成 |
| docs\rust-ownership-decidability\THEOREM_DEPENDENCY_GRAPH.md | **最后更新**: 2026-03-14 | `#最后更新-2026-03-14` | 同文件锚点不存在: #最后更新-2026-03-14 |
| docs\rust-ownership-decidability\THEOREM_INTUITIONS.md | **最后更新**: 2026-03-14 | `#最后更新-2026-03-14` | 同文件锚点不存在: #最后更新-2026-03-14 |
| docs\rust-ownership-decidability\THEOREM_TO_COMPILER_BRIDGE.md | 一、终止性定理 ↔ rustc 借用检查 | `#一终止性定理--rustc-借用检查` | 同文件锚点不存在: #一终止性定理--rustc-借用检查 |
| docs\rust-ownership-decidability\THEOREM_TO_COMPILER_BRIDGE.md | 二、类型安全定理 ↔ rustc 类型检查 | `#二类型安全定理--rustc-类型检查` | 同文件锚点不存在: #二类型安全定理--rustc-类型检查 |
| docs\rust-ownership-decidability\THEOREM_TO_COMPILER_BRIDGE.md | 三、可判定性定理 ↔ 编译流程 | `#三可判定性定理--编译流程` | 同文件锚点不存在: #三可判定性定理--编译流程 |
| docs\rust-ownership-decidability\THEOREM_TO_COMPILER_BRIDGE.md | 四、保持性定理 ↔ 优化正确性 | `#四保持性定理--优化正确性` | 同文件锚点不存在: #四保持性定理--优化正确性 |
| docs\rust-ownership-decidability\THEOREM_TO_COMPILER_BRIDGE.md | 五、借用检查等价性 ↔ MIR 分析 | `#五借用检查等价性--mir-分析` | 同文件锚点不存在: #五借用检查等价性--mir-分析 |
| docs\rust-ownership-decidability\THEOREM_TO_COMPILER_BRIDGE.md | *本文档建立了从形式化定理到 rustc 实现的完整桥梁* | `#本文档建立了从形式化定理到-rustc-实现的完整桥梁` | 同文件锚点不存在: #本文档建立了从形式化定理到-rustc-实现的完整桥梁 |
| docs\rust-ownership-decidability\THEORY_TO_PATTERN_BRIDGE.md | 1.1 线性逻辑 → RAII 模式 | `#11-线性逻辑--raii-模式` | 同文件锚点不存在: #11-线性逻辑--raii-模式 |
| docs\rust-ownership-decidability\THEORY_TO_PATTERN_BRIDGE.md | 1.2 仿射类型 → Builder 模式 | `#12-仿射类型--builder-模式` | 同文件锚点不存在: #12-仿射类型--builder-模式 |
| docs\rust-ownership-decidability\THEORY_TO_PATTERN_BRIDGE.md | 1.3 区域类型 → 类型状态模式 | `#13-区域类型--类型状态模式` | 同文件锚点不存在: #13-区域类型--类型状态模式 |
| docs\rust-ownership-decidability\THEORY_TO_PATTERN_BRIDGE.md | 2.1 借用规则 → 访问者模式 | `#21-借用规则--访问者模式` | 同文件锚点不存在: #21-借用规则--访问者模式 |
| docs\rust-ownership-decidability\THEORY_TO_PATTERN_BRIDGE.md | 2.2 内部可变性 → Newtype 模式 | `#22-内部可变性--newtype-模式` | 同文件锚点不存在: #22-内部可变性--newtype-模式 |
| docs\rust-ownership-decidability\THEORY_TO_PATTERN_BRIDGE.md | 3.1 生命周期约束 → 零拷贝模式 | `#31-生命周期约束--零拷贝模式` | 同文件锚点不存在: #31-生命周期约束--零拷贝模式 |
| docs\rust-ownership-decidability\THEORY_TO_PATTERN_BRIDGE.md | 3.2 'static 约束 → 单例模式 | `#32-static-约束--单例模式` | 同文件锚点不存在: #32-static-约束--单例模式 |
| docs\rust-ownership-decidability\THEORY_TO_PATTERN_BRIDGE.md | 4.1 Send 约束 → 线程池模式 | `#41-send-约束--线程池模式` | 同文件锚点不存在: #41-send-约束--线程池模式 |
| docs\rust-ownership-decidability\THEORY_TO_PATTERN_BRIDGE.md | 4.2 Sync 约束 → 读写锁模式 | `#42-sync-约束--读写锁模式` | 同文件锚点不存在: #42-sync-约束--读写锁模式 |
| docs\rust-ownership-decidability\THEORY_TO_PATTERN_BRIDGE.md | 6.1 RAII + 类型状态 | `#61-raii--类型状态` | 同文件锚点不存在: #61-raii--类型状态 |
| docs\rust-ownership-decidability\THEORY_TO_PATTERN_BRIDGE.md | 6.2 Builder + 内部可变性 | `#62-builder--内部可变性` | 同文件锚点不存在: #62-builder--内部可变性 |
| docs\rust-ownership-decidability\THEORY_TO_PATTERN_BRIDGE.md | *本文档建立了从形式化理论到设计模式的完整桥梁* | `#本文档建立了从形式化理论到设计模式的完整桥梁` | 同文件锚点不存在: #本文档建立了从形式化理论到设计模式的完整桥梁 |
| docs\rust-ownership-decidability\ULTIMATE_COMPREHENSIVE_GUIDE.md | Rust 所有权系统可判定性 - 终极综合指南 | `#rust-所有权系统可判定性---终极综合指南` | 同文件锚点不存在: #rust-所有权系统可判定性---终极综合指南 |
| docs\rust-ownership-decidability\ULTIMATE_COMPREHENSIVE_GUIDE.md | 🗺️ 第一部分：全局知识架构 | `#️-第一部分全局知识架构` | 同文件锚点不存在: #️-第一部分全局知识架构 |
| docs\rust-ownership-decidability\ULTIMATE_COMPREHENSIVE_GUIDE.md | 🛤️ 第三部分：递进学习路线图 | `#️-第三部分递进学习路线图` | 同文件锚点不存在: #️-第三部分递进学习路线图 |
| docs\rust-ownership-decidability\ULTIMATE_COMPREHENSIVE_GUIDE.md | 5.1 自然语言 ↔ 数学符号 ↔ 代码 ↔ Coq | `#51-自然语言--数学符号--代码--coq` | 同文件锚点不存在: #51-自然语言--数学符号--代码--coq |
| docs\rust-ownership-decidability\ULTIMATE_COMPREHENSIVE_GUIDE.md | 5.2 理论约束 ↔ 设计决策 | `#52-理论约束--设计决策` | 同文件锚点不存在: #52-理论约束--设计决策 |
| docs\rust-ownership-decidability\ULTIMATE_COMPREHENSIVE_GUIDE.md | 5.3 学习阶段 ↔ 目标能力 | `#53-学习阶段--目标能力` | 同文件锚点不存在: #53-学习阶段--目标能力 |
| docs\rust-ownership-decidability\ULTIMATE_COMPREHENSIVE_GUIDE.md | **总内容**: ~570,000+ 行 | `#总内容-570000-行` | 同文件锚点不存在: #总内容-570000-行 |
| docs\rust-ownership-decidability\UNIFIED_THEORETICAL_FRAMEWORK.md | 定理 4.1: Linearizability → Termination | `#定理-41-linearizability--termination` | 同文件锚点不存在: #定理-41-linearizability--termination |
| docs\rust-ownership-decidability\UNIFIED_THEORETICAL_FRAMEWORK.md | 定理 4.2: BigStepSemantics → Preservation | `#定理-42-bigstepsemantics--preservation` | 同文件锚点不存在: #定理-42-bigstepsemantics--preservation |
| docs\rust-ownership-decidability\UNIFIED_THEORETICAL_FRAMEWORK.md | 定理 4.3: SmallStepSemantics → Progress | `#定理-43-smallstepsemantics--progress` | 同文件锚点不存在: #定理-43-smallstepsemantics--progress |
| docs\rust-ownership-decidability\UNIFIED_THEORETICAL_FRAMEWORK.md | 定理 4.4: TypeSystem → Preservation/Progress | `#定理-44-typesystem--preservationprogress` | 同文件锚点不存在: #定理-44-typesystem--preservationprogress |
| docs\rust-ownership-decidability\UNIFIED_THEORETICAL_FRAMEWORK.md | 定理 4.5: Termination + Preservation + Progress → TypeSafety | `#定理-45-termination--preservation--progress--typesafety` | 同文件锚点不存在: #定理-45-termination--preservation--progress--typesafety |
| docs\rust-ownership-decidability\UNIFIED_THEORETICAL_FRAMEWORK.md | 定理 4.6: TypeSafety → MemorySafety | `#定理-46-typesafety--memorysafety` | 同文件锚点不存在: #定理-46-typesafety--memorysafety |
| docs\rust-ownership-decidability\UNIFIED_THEORETICAL_FRAMEWORK.md | 定理 4.7: TypeSafety + Termination → Decidability | `#定理-47-typesafety--termination--decidability` | 同文件锚点不存在: #定理-47-typesafety--termination--decidability |
| docs\rust-ownership-decidability\UNIFIED_THEORETICAL_FRAMEWORK.md | 6.1 Rust 表面语法 → 核心语言 | `#61-rust-表面语法--核心语言` | 同文件锚点不存在: #61-rust-表面语法--核心语言 |
| docs\rust-ownership-decidability\UNIFIED_THEORETICAL_FRAMEWORK.md | 6.2 核心语言 → 形式化语言 | `#62-核心语言--形式化语言` | 同文件锚点不存在: #62-核心语言--形式化语言 |
| docs\rust-ownership-decidability\UNIFIED_THEORETICAL_FRAMEWORK.md | 6.3 形式化证明 → 实际代码验证 | `#63-形式化证明--实际代码验证` | 同文件锚点不存在: #63-形式化证明--实际代码验证 |
| docs\rust-ownership-decidability\VERSION_ANNOTATION_GUIDELINE.md | Rust 所有权形式化文档 - 版本标注规范 | `#rust-所有权形式化文档---版本标注规范` | 同文件锚点不存在: #rust-所有权形式化文档---版本标注规范 |
| docs\rust-ownership-decidability\VERSION_ANNOTATION_GUIDELINE.md | 🏷️ 文件头标注模板 | `#️-文件头标注模板` | 同文件锚点不存在: #️-文件头标注模板 |
| docs\rust-ownership-decidability\VERSION_ANNOTATION_GUIDELINE.md | **维护者**: Rust-Ownership-Decidability Team | `#维护者-rust-ownership-decidability-team` | 同文件锚点不存在: #维护者-rust-ownership-decidability-team |
| docs\rust-ownership-decidability\VISUAL_THINKING_GUIDE.md | Rust 所有权系统 - 可视化思维指南 | `#rust-所有权系统---可视化思维指南` | 同文件锚点不存在: #rust-所有权系统---可视化思维指南 |
| docs\rust-ownership-decidability\VISUAL_THINKING_GUIDE.md | **建议**: 将这些可视化与代码实践结合，加深理解。 | `#建议-将这些可视化与代码实践结合加深理解` | 同文件锚点不存在: #建议-将这些可视化与代码实践结合加深理解 |
| docs\rust-ownership-decidability\00-foundations\00-01-linear-logic-deep.md | 3.1 乘法连接词 (⊗, ⅋, ⊸, 1, ⊥) | `#31-乘法连接词----1-` | 同文件锚点不存在: #31-乘法连接词----1- |
| docs\rust-ownership-decidability\00-foundations\00-01-linear-logic-deep.md | 3.1.1 Tensor (⊗) - 乘法合取 | `#311-tensor----乘法合取` | 同文件锚点不存在: #311-tensor----乘法合取 |
| docs\rust-ownership-decidability\00-foundations\00-01-linear-logic-deep.md | 3.1.2 Par (⅋) - 乘法析取 | `#312-par----乘法析取` | 同文件锚点不存在: #312-par----乘法析取 |
| docs\rust-ownership-decidability\00-foundations\00-01-linear-logic-deep.md | 3.1.3 Linear Implication (⊸) - 线性蕴含 | `#313-linear-implication----线性蕴含` | 同文件锚点不存在: #313-linear-implication----线性蕴含 |
| docs\rust-ownership-decidability\00-foundations\00-01-linear-logic-deep.md | 3.1.4 Unit (1) - 乘法单位元 | `#314-unit-1---乘法单位元` | 同文件锚点不存在: #314-unit-1---乘法单位元 |
| docs\rust-ownership-decidability\00-foundations\00-01-linear-logic-deep.md | 3.1.5 Bottom (⊥) - 乘法对偶单位元 | `#315-bottom----乘法对偶单位元` | 同文件锚点不存在: #315-bottom----乘法对偶单位元 |
| docs\rust-ownership-decidability\00-foundations\00-01-linear-logic-deep.md | 3.2 加法连接词 (\&, ⊕, ⊤, 0) | `#32-加法连接词----0` | 同文件锚点不存在: #32-加法连接词----0 |
| docs\rust-ownership-decidability\00-foundations\00-01-linear-logic-deep.md | 3.2.1 With (\&) - 加法合取 | `#321-with----加法合取` | 同文件锚点不存在: #321-with----加法合取 |
| docs\rust-ownership-decidability\00-foundations\00-01-linear-logic-deep.md | 3.2.2 Plus (⊕) - 加法和 | `#322-plus----加法和` | 同文件锚点不存在: #322-plus----加法和 |
| docs\rust-ownership-decidability\00-foundations\00-01-linear-logic-deep.md | 3.2.3 Top (⊤) - 加法合取单位元 | `#323-top----加法合取单位元` | 同文件锚点不存在: #323-top----加法合取单位元 |
| docs\rust-ownership-decidability\00-foundations\00-01-linear-logic-deep.md | 3.2.4 Zero (0) - 加法和单位元 | `#324-zero-0---加法和单位元` | 同文件锚点不存在: #324-zero-0---加法和单位元 |
| docs\rust-ownership-decidability\00-foundations\00-01-linear-logic-deep.md | 3.3.1 Of Course (!A) - Bang | `#331-of-course-a---bang` | 同文件锚点不存在: #331-of-course-a---bang |
| docs\rust-ownership-decidability\00-foundations\00-01-linear-logic-deep.md | 3.3.2 Why Not (?A) - 问号 | `#332-why-not-a---问号` | 同文件锚点不存在: #332-why-not-a---问号 |
| docs\rust-ownership-decidability\00-foundations\00-01-linear-logic-deep.md | 6.7 无 ! 的共享 | `#67-无--的共享` | 同文件锚点不存在: #67-无--的共享 |
| docs\rust-ownership-decidability\00-foundations\00-01-linear-logic-deep.md | 6.10 无 \& 的分支 | `#610-无--的分支` | 同文件锚点不存在: #610-无--的分支 |
| docs\rust-ownership-decidability\00-foundations\00-01-linear-logic-deep.md | *字数: 约 25000 字* | `#字数-约-25000-字` | 同文件锚点不存在: #字数-约-25000-字 |
| docs\rust-ownership-decidability\00-foundations\00-03-separation-logic-deep.md | 2.2 Separating Conjunction (\*) | `#22-separating-conjunction-` | 同文件锚点不存在: #22-separating-conjunction- |
| docs\rust-ownership-decidability\00-foundations\00-03-separation-logic-deep.md | 2.3 Separating Implication (-\*) | `#23-separating-implication--` | 同文件锚点不存在: #23-separating-implication-- |
| docs\rust-ownership-decidability\00-foundations\00-03-separation-logic-deep.md | 4.1.2 Later Modality (\>) | `#412-later-modality-` | 同文件锚点不存在: #412-later-modality- |
| docs\rust-ownership-decidability\00-foundations\00-03-separation-logic-deep.md | *Line Count: ~1700+ lines* | `#line-count-1700-lines` | 同文件锚点不存在: #line-count-1700-lines |
| docs\rust-ownership-decidability\00-foundations\00-04-theory-connections.md | 2. 线性逻辑 ↔ 分离逻辑 | `#2-线性逻辑--分离逻辑` | 同文件锚点不存在: #2-线性逻辑--分离逻辑 |
| docs\rust-ownership-decidability\00-foundations\00-04-theory-connections.md | 3. 仿射逻辑 ↔ Rust所有权 | `#3-仿射逻辑--rust所有权` | 同文件锚点不存在: #3-仿射逻辑--rust所有权 |
| docs\rust-ownership-decidability\00-foundations\00-04-theory-connections.md | 4. 分离逻辑 ↔ RustBelt/Iris | `#4-分离逻辑--rustbeltiris` | 同文件锚点不存在: #4-分离逻辑--rustbeltiris |
| docs\rust-ownership-decidability\00-foundations\00-04-theory-connections.md | 5. 类型理论 ↔ 程序验证 | `#5-类型理论--程序验证` | 同文件锚点不存在: #5-类型理论--程序验证 |
| docs\rust-ownership-decidability\01-core-concepts\01-01-ownership-rules-deep.md | 7. 案例研究: Vec实现 | `#7-案例研究-vec实现` | 同文件锚点不存在: #7-案例研究-vec实现 |
| docs\rust-ownership-decidability\01-core-concepts\01-01-ownership-rules-deep.md | **状态**: ✅ 形式化完备 | `#状态--形式化完备` | 同文件锚点不存在: #状态--形式化完备 |
| docs\rust-ownership-decidability\01-core-concepts\01-02-borrowing-system-deep.md | 01-02: The Rust Borrowing System - A Formal Deep Dive | `#01-02-the-rust-borrowing-system---a-formal-deep-dive` | 同文件锚点不存在: #01-02-the-rust-borrowing-system---a-formal-deep-dive |
| docs\rust-ownership-decidability\01-core-concepts\01-02-borrowing-system-deep.md | *Last Updated: 2026* | `#last-updated-2026` | 同文件锚点不存在: #last-updated-2026 |
| docs\rust-ownership-decidability\01-core-concepts\01-03-lifetimes-deep.md | *最后更新: 2024* | `#最后更新-2024` | 同文件锚点不存在: #最后更新-2024 |
| docs\rust-ownership-decidability\01-core-concepts\01-04-runtime-vs-compile-time.md | 理解这一区分是掌握Rust资源管理的关键！ | `#理解这一区分是掌握rust资源管理的关键` | 同文件锚点不存在: #理解这一区分是掌握rust资源管理的关键 |
| docs\rust-ownership-decidability\01-core-concepts\01-05-interior-mutability-deep.md | RefCell: Borrow Checking at Runtime | `#refcell-borrow-checking-at-runtime` | 同文件锚点不存在: #refcell-borrow-checking-at-runtime |
| docs\rust-ownership-decidability\01-core-concepts\01-05-interior-mutability-deep.md | Mutex: Synchronization for Thread Safety | `#mutex-synchronization-for-thread-safety` | 同文件锚点不存在: #mutex-synchronization-for-thread-safety |
| docs\rust-ownership-decidability\01-core-concepts\01-05-interior-mutability-deep.md | 2. Cell Analysis | `#2-cell-analysis` | 同文件锚点不存在: #2-cell-analysis |
| docs\rust-ownership-decidability\01-core-concepts\01-05-interior-mutability-deep.md | 3. RefCell Deep Dive | `#3-refcell-deep-dive` | 同文件锚点不存在: #3-refcell-deep-dive |
| docs\rust-ownership-decidability\01-core-concepts\01-05-interior-mutability-deep.md | 4. Mutex and RwLock | `#4-mutex-and-rwlock` | 同文件锚点不存在: #4-mutex-and-rwlock |
| docs\rust-ownership-decidability\01-core-concepts\01-05-interior-mutability-deep.md | 4.4 RwLock | `#44-rwlock` | 同文件锚点不存在: #44-rwlock |
| docs\rust-ownership-decidability\01-core-concepts\01-05-interior-mutability-deep.md | Counter-Example 1: RefCell Panic - borrow then borrow\_mut | `#counter-example-1-refcell-panic---borrow-then-borrow_mut` | 同文件锚点不存在: #counter-example-1-refcell-panic---borrow-then-borrow_mut |
| docs\rust-ownership-decidability\01-core-concepts\01-05-interior-mutability-deep.md | 7.1 Rc + RefCell | `#71-rc--refcell` | 同文件锚点不存在: #71-rc--refcell |
| docs\rust-ownership-decidability\01-core-concepts\01-05-interior-mutability-deep.md | 7.2 Arc + Mutex | `#72-arc--mutex` | 同文件锚点不存在: #72-arc--mutex |
| docs\rust-ownership-decidability\01-core-concepts\01-05-interior-mutability-deep.md | *Last updated: 2026-03-06* | `#last-updated-2026-03-06` | 同文件锚点不存在: #last-updated-2026-03-06 |
| docs\rust-ownership-decidability\01-core-concepts\ownership-counterexamples.md | 所有权系统 - 反例与逻辑论证 | `#所有权系统---反例与逻辑论证` | 同文件锚点不存在: #所有权系统---反例与逻辑论证 |
| docs\rust-ownership-decidability\01-core-concepts\ownership-counterexamples.md | **对齐版本**: Rust 1.96.0+ (Edition 2024) \| 对齐日期: 2026-05-12 | `#对齐版本-rust-1950-edition-2024--对齐日期-2026-05-12` | 同文件锚点不存在: #对齐版本-rust-1950-edition-2024--对齐日期-2026-05-12 |
| docs\rust-ownership-decidability\01-core-concepts\detailed-concepts\borrowing-in-depth.md | *继续学习: lifetimes-mastery.md* | `#继续学习-lifetimes-masterymd` | 同文件锚点不存在: #继续学习-lifetimes-masterymd |
| docs\rust-ownership-decidability\01-core-concepts\detailed-concepts\interior-mutability.md | 2. Cell 详解 | `#2-cell-详解` | 同文件锚点不存在: #2-cell-详解 |
| docs\rust-ownership-decidability\01-core-concepts\detailed-concepts\interior-mutability.md | 3. RefCell 深入 | `#3-refcell-深入` | 同文件锚点不存在: #3-refcell-深入 |
| docs\rust-ownership-decidability\01-core-concepts\detailed-concepts\interior-mutability.md | 4.1 Mutex 详解 | `#41-mutex-详解` | 同文件锚点不存在: #41-mutex-详解 |
| docs\rust-ownership-decidability\01-core-concepts\detailed-concepts\interior-mutability.md | 4.3 RwLock 详解 | `#43-rwlock-详解` | 同文件锚点不存在: #43-rwlock-详解 |
| docs\rust-ownership-decidability\01-core-concepts\detailed-concepts\interior-mutability.md | *继续学习: trait-system.md* | `#继续学习-trait-systemmd` | 同文件锚点不存在: #继续学习-trait-systemmd |
| docs\rust-ownership-decidability\01-core-concepts\detailed-concepts\lifetimes-mastery.md | *继续学习: interior-mutability.md* | `#继续学习-interior-mutabilitymd` | 同文件锚点不存在: #继续学习-interior-mutabilitymd |
| docs\rust-ownership-decidability\01-core-concepts\detailed-concepts\ownership-deep-dive.md | *继续学习: borrowing-in-depth.md* | `#继续学习-borrowing-in-depthmd` | 同文件锚点不存在: #继续学习-borrowing-in-depthmd |
| docs\rust-ownership-decidability\01-core-concepts\detailed-concepts\polonius-borrow-checker.md | **维护者**: Rust 所有权可判定性研究项目 | `#维护者-rust-所有权可判定性研究项目` | 同文件锚点不存在: #维护者-rust-所有权可判定性研究项目 |
| docs\rust-ownership-decidability\01-core-concepts\detailed-concepts\trait-system.md | *本系列文档结束。希望这些深入的分析能帮助你掌握 Rust 的所有权系统！* | `#本系列文档结束希望这些深入的分析能帮助你掌握-rust-的所有权系统` | 同文件锚点不存在: #本系列文档结束希望这些深入的分析能帮助你掌握-rust-的所有权系统 |
| docs\rust-ownership-decidability\01-core-concepts\short-concepts\borrowing-concept-card.md | 掌握借用是掌握Rust的关键。 | `#掌握借用是掌握rust的关键` | 同文件锚点不存在: #掌握借用是掌握rust的关键 |
| docs\rust-ownership-decidability\01-core-concepts\short-concepts\lifetime-concept-card.md | 掌握生命周期是写出高效、安全Rust代码的关键 | `#掌握生命周期是写出高效安全rust代码的关键` | 同文件锚点不存在: #掌握生命周期是写出高效安全rust代码的关键 |
| docs\rust-ownership-decidability\01-core-concepts\short-concepts\ownership-concept-card.md | 所有权概念卡片 - 全面深度解析 | `#所有权概念卡片---全面深度解析` | 同文件锚点不存在: #所有权概念卡片---全面深度解析 |
| docs\rust-ownership-decidability\03-verification-tools\03-01-verification-overview-deep.md | *End of Document* | `#end-of-document` | 同文件锚点不存在: #end-of-document |
| docs\rust-ownership-decidability\03-verification-tools\03-03-miri-deep-dive.md | *文档版本: 2.0.0* \| *最后更新: 2026-03* | `#文档版本-200--最后更新-2026-03` | 同文件锚点不存在: #文档版本-200--最后更新-2026-03 |
| docs\rust-ownership-decidability\03-verification-tools\03-06-verus-guide.md | *文档版本: 2.0.0* \| *Verus 版本: 0.1.x* \| *最后更新: 2026-03* | `#文档版本-200--verus-版本-01x--最后更新-2026-03` | 同文件锚点不存在: #文档版本-200--verus-版本-01x--最后更新-2026-03 |
| docs\rust-ownership-decidability\03-verification-tools\03-07-refinedrust-deep-dive.md | **维护者**: Rust 所有权可判定性研究项目 | `#维护者-rust-所有权可判定性研究项目` | 同文件锚点不存在: #维护者-rust-所有权可判定性研究项目 |
| docs\rust-ownership-decidability\03-verification-tools\03-08-gillian-rust.md | **注意**: Gillian-Rust 是活跃研究项目，信息可能随开发进展更新 | `#注意-gillian-rust-是活跃研究项目信息可能随开发进展更新` | 同文件锚点不存在: #注意-gillian-rust-是活跃研究项目信息可能随开发进展更新 |
| docs\rust-ownership-decidability\03-verification-tools\README.md | 验证概述 | `03-01-verification-overview.md#7-rust-194-版本兼容性` | 锚点不存在: #7-rust-194-版本兼容性 |
| docs\rust-ownership-decidability\04-decidability-analysis\04-01-type-inference.md | *最后更新: 2026-03-04* | `#最后更新-2026-03-04` | 同文件锚点不存在: #最后更新-2026-03-04 |
| docs\rust-ownership-decidability\04-decidability-analysis\04-02-borrow-checking.md | *最后更新: 2026-03-04* | `#最后更新-2026-03-04` | 同文件锚点不存在: #最后更新-2026-03-04 |
| docs\rust-ownership-decidability\05-comparative-study\05-03-rust-vs-go.md | 11.1 Go → Rust 思维转换 | `#111-go--rust-思维转换` | 同文件锚点不存在: #111-go--rust-思维转换 |
| docs\rust-ownership-decidability\05-comparative-study\05-03-rust-vs-go.md | *维护者: Rust Comparative Study Team* | `#维护者-rust-comparative-study-team` | 同文件锚点不存在: #维护者-rust-comparative-study-team |
| docs\rust-ownership-decidability\05-comparative-study\05-04-rust-vs-java.md | Java → Rust 思维转换 | `#java--rust-思维转换` | 同文件锚点不存在: #java--rust-思维转换 |
| docs\rust-ownership-decidability\05-comparative-study\05-04-rust-vs-java.md | *维护者: Rust Comparative Study Team* | `#维护者-rust-comparative-study-team` | 同文件锚点不存在: #维护者-rust-comparative-study-team |
| docs\rust-ownership-decidability\05-comparative-study\05-05-rust-vs-swift.md | 10.1 Swift → Rust 思维转换 | `#101-swift--rust-思维转换` | 同文件锚点不存在: #101-swift--rust-思维转换 |
| docs\rust-ownership-decidability\05-comparative-study\05-05-rust-vs-swift.md | *维护者: Rust Comparative Study Team* | `#维护者-rust-comparative-study-team` | 同文件锚点不存在: #维护者-rust-comparative-study-team |
| docs\rust-ownership-decidability\07-references\academic-papers.md | **维护者**: Rust 所有权可判定性研究项目 | `#维护者-rust-所有权可判定性研究项目` | 同文件锚点不存在: #维护者-rust-所有权可判定性研究项目 |
| docs\rust-ownership-decidability\07-references\books-resources.md | **维护者**: Rust 所有权可判定性研究项目 | `#维护者-rust-所有权可判定性研究项目` | 同文件锚点不存在: #维护者-rust-所有权可判定性研究项目 |
| docs\rust-ownership-decidability\07-references\online-courses.md | **维护者**: Rust 所有权可判定性研究项目 | `#维护者-rust-所有权可判定性研究项目` | 同文件锚点不存在: #维护者-rust-所有权可判定性研究项目 |
| docs\rust-ownership-decidability\07-references\tools-libraries.md | **维护者**: Rust 所有权可判定性研究项目 | `#维护者-rust-所有权可判定性研究项目` | 同文件锚点不存在: #维护者-rust-所有权可判定性研究项目 |
| docs\rust-ownership-decidability\08-advanced-topics\08-01-const-generics.md | 尽管不如依赖类型强大，常量泛型在系统编程中提供了恰到好处的类型级抽象能力。 | `#尽管不如依赖类型强大常量泛型在系统编程中提供了恰到好处的类型级抽象能力` | 同文件锚点不存在: #尽管不如依赖类型强大常量泛型在系统编程中提供了恰到好处的类型级抽象能力 |
| docs\rust-ownership-decidability\08-advanced-topics\08-05-rust-195-features-formal.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\rust-ownership-decidability\08-advanced-topics\08-05-rust-195-features-formal.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\rust-ownership-decidability\08-advanced-topics\data-layout.md | 7.2 使用枚举代替标记 + 数据 | `#72-使用枚举代替标记--数据` | 同文件锚点不存在: #72-使用枚举代替标记--数据 |
| docs\rust-ownership-decidability\08-advanced-topics\data-layout.md | *最后更新: 2026-03-07* | `#最后更新-2026-03-07` | 同文件锚点不存在: #最后更新-2026-03-07 |
| docs\rust-ownership-decidability\10-research-frontiers\10-01-future-directions.md | *本文档是 Rust 所有权与可判定性研究系列的一部分。相关文档请参阅本系列的其他章节。* | `#本文档是-rust-所有权与可判定性研究系列的一部分相关文档请参阅本系列的其他章节` | 同文件锚点不存在: #本文档是-rust-所有权与可判定性研究系列的一部分相关文档请参阅本系列的其他章节 |
| docs\rust-ownership-decidability\10-research-frontiers\10-02-type-system-extensions.md | *本文档是 Rust 所有权与可判定性研究系列第十章的一部分。* | `#本文档是-rust-所有权与可判定性研究系列第十章的一部分` | 同文件锚点不存在: #本文档是-rust-所有权与可判定性研究系列第十章的一部分 |
| docs\rust-ownership-decidability\10-research-frontiers\10-03-verification-advancements.md | *本文档是 Rust 所有权与可判定性研究系列第十章的一部分。* | `#本文档是-rust-所有权与可判定性研究系列第十章的一部分` | 同文件锚点不存在: #本文档是-rust-所有权与可判定性研究系列第十章的一部分 |
| docs\rust-ownership-decidability\10-research-frontiers\10-04-ownership-variations.md | *本文档是 Rust 所有权与可判定性研究系列第十章的一部分。* | `#本文档是-rust-所有权与可判定性研究系列第十章的一部分` | 同文件锚点不存在: #本文档是-rust-所有权与可判定性研究系列第十章的一部分 |
| docs\rust-ownership-decidability\10-research-frontiers\10-05-ai-integration.md | *本文档是 Rust 所有权与可判定性研究系列第十章的一部分。* | `#本文档是-rust-所有权与可判定性研究系列第十章的一部分` | 同文件锚点不存在: #本文档是-rust-所有权与可判定性研究系列第十章的一部分 |
| docs\rust-ownership-decidability\10-research-frontiers\10-06-formal-verification.md | 3. Kani / CBMC | `#3-kani--cbmc` | 同文件锚点不存在: #3-kani--cbmc |
| docs\rust-ownership-decidability\10-research-frontiers\10-06-formal-verification.md | *文档版本: 1.0.0* | `#文档版本-100` | 同文件锚点不存在: #文档版本-100 |
| docs\rust-ownership-decidability\10-research-frontiers\10-07-std-verification-initiative.md | **维护者**: Rust 标准库验证团队 | `#维护者-rust-标准库验证团队` | 同文件锚点不存在: #维护者-rust-标准库验证团队 |
| docs\rust-ownership-decidability\10-research-frontiers\rust-1.93-features-analysis.md | **对齐版本**: Rust 1.93.1 | `#对齐版本-rust-1931` | 同文件锚点不存在: #对齐版本-rust-1931 |
| docs\rust-ownership-decidability\11-design-patterns\11-02-idiomatic-patterns.md | 2.3 unwrap\_or / unwrap\_or\_else | `#23-unwrap_or--unwrap_or_else` | 同文件锚点不存在: #23-unwrap_or--unwrap_or_else |
| docs\rust-ownership-decidability\11-design-patterns\11-02-idiomatic-patterns.md | 2.4 ok\_or / ok\_or\_else | `#24-ok_or--ok_or_else` | 同文件锚点不存在: #24-ok_or--ok_or_else |
| docs\rust-ownership-decidability\11-design-patterns\11-02-idiomatic-patterns.md | 2.5 filter / map\_or | `#25-filter--map_or` | 同文件锚点不存在: #25-filter--map_or |
| docs\rust-ownership-decidability\12-concurrency-patterns\12-01-concurrency-architecture.md | 单线程延迟初始化 - LazyCell | `#单线程延迟初始化---lazycell` | 同文件锚点不存在: #单线程延迟初始化---lazycell |
| docs\rust-ownership-decidability\12-concurrency-patterns\12-02-thread-safety-patterns.md | 继续下一部分？ | `#继续下一部分` | 同文件锚点不存在: #继续下一部分 |
| docs\rust-ownership-decidability\12-concurrency-patterns\12-03-message-passing-deep.md | **Document Version**: 1.0.0 | `#document-version-100` | 同文件锚点不存在: #document-version-100 |
| docs\rust-ownership-decidability\12-concurrency-patterns\12-04-lock-free-patterns.md | （继续...） | `#继续` | 同文件锚点不存在: #继续 |
| docs\rust-ownership-decidability\12-concurrency-patterns\12-05-async-patterns-deep.md | *This document is part of the Rust Ownership \& Decidability documentation series. For questions or contributions, refer to the project repository.* | `#this-document-is-part-of-the-rust-ownership--decidability-documentation-series-for-questions-or-contributions-refer-to-the-project-repository` | 同文件锚点不存在: #this-document-is-part-of-the-rust-ownership--decidability-documentation-series-for-questions-or-contributions-refer-to-the-project-repository |
| docs\rust-ownership-decidability\12-concurrency-patterns\12-05-async-patterns.md | （继续...） | `#继续` | 同文件锚点不存在: #继续 |
| docs\rust-ownership-decidability\12-concurrency-patterns\12-06-data-parallelism.md | （继续...） | `#继续` | 同文件锚点不存在: #继续 |
| docs\rust-ownership-decidability\12-concurrency-patterns\12-07-distributed-patterns.md | （继续...） | `#继续` | 同文件锚点不存在: #继续 |
| docs\rust-ownership-decidability\13-architecture-patterns\clean-architecture.md | *文档版本: 1.0.0* | `#文档版本-100` | 同文件锚点不存在: #文档版本-100 |
| docs\rust-ownership-decidability\14-distributed-systems\consensus-patterns.md | *文档版本: 1.0.0* | `#文档版本-100` | 同文件锚点不存在: #文档版本-100 |
| docs\rust-ownership-decidability\15-application-domains\data-engineering.md | 通过本文档介绍的技术，开发者可以构建高性能、高可靠性的数据处理系统 | `#通过本文档介绍的技术开发者可以构建高性能高可靠性的数据处理系统` | 同文件锚点不存在: #通过本文档介绍的技术开发者可以构建高性能高可靠性的数据处理系统 |
| docs\rust-ownership-decidability\15-application-domains\web-development.md | 通过本文档介绍的技术和最佳实践，开发者可以构建高性能、高可靠性的 Web 应用 | `#通过本文档介绍的技术和最佳实践开发者可以构建高性能高可靠性的-web-应用` | 同文件锚点不存在: #通过本文档介绍的技术和最佳实践开发者可以构建高性能高可靠性的-web-应用 |
| docs\rust-ownership-decidability\16-program-semantics\02-concurrency-semantics.md | 8.1.1 Arc\<Mutex\> 语义 | `#811-arcmutex-语义` | 同文件锚点不存在: #811-arcmutex-语义 |
| docs\rust-ownership-decidability\16-program-semantics\03-async-semantics.md | *关联文档：00-semantic-framework.md* | `#关联文档00-semantic-frameworkmd` | 同文件锚点不存在: #关联文档00-semantic-frameworkmd |
| docs\rust-ownership-decidability\16-program-semantics\04-control-data-flow.md | *本文档是 Rust 所有权可判定性研究系列的一部分，与 `00-semantic-framework.md` 保持一致的语义框架。* | `#本文档是-rust-所有权可判定性研究系列的一部分与-00-semantic-frameworkmd-保持一致的语义框架` | 同文件锚点不存在: #本文档是-rust-所有权可判定性研究系列的一部分与-00-semantic-frameworkmd-保持一致的语义框架 |
| docs\rust-ownership-decidability\16-program-semantics\COMPLETION_STATUS_2026_03_08.md | 1. 理论基础补齐 ✅ | `#1-理论基础补齐-` | 同文件锚点不存在: #1-理论基础补齐- |
| docs\rust-ownership-decidability\16-program-semantics\COMPLETION_STATUS_2026_03_08.md | 🔴 P0 - 形式验证 (完全缺失) | `#-p0---形式验证-完全缺失` | 同文件锚点不存在: #-p0---形式验证-完全缺失 |
| docs\rust-ownership-decidability\16-program-semantics\COMPLETION_STATUS_2026_03_08.md | 🟡 P1 - 并发理论扩展 | `#-p1---并发理论扩展` | 同文件锚点不存在: #-p1---并发理论扩展 |
| docs\rust-ownership-decidability\16-program-semantics\COMPLETION_STATUS_2026_03_08.md | 🟡 P2 - OS Abstractions 深化 | `#-p2---os-abstractions-深化` | 同文件锚点不存在: #-p2---os-abstractions-深化 |
| docs\rust-ownership-decidability\16-program-semantics\COMPLETION_STATUS_2026_03_08.md | **日期**: 2026-03-08 | `#日期-2026-03-08` | 同文件锚点不存在: #日期-2026-03-08 |
| docs\rust-ownership-decidability\16-program-semantics\COMPREHENSIVE_ANALYSIS_AND_ROADMAP.md | **状态**: 诊断完成，待执行 | `#状态-诊断完成待执行` | 同文件锚点不存在: #状态-诊断完成待执行 |
| docs\rust-ownership-decidability\16-program-semantics\EXPANSION_SUMMARY.md | **状态**: ✅ 100% 完成 | `#状态--100-完成` | 同文件锚点不存在: #状态--100-完成 |
| docs\rust-ownership-decidability\16-program-semantics\TOPIC_COVERAGE_MATRIX.md | 一、核心理论语义 (来自 TAPL \& PLT Redex) | `#一核心理论语义-来自-tapl--plt-redex` | 同文件锚点不存在: #一核心理论语义-来自-tapl--plt-redex |
| docs\rust-ownership-decidability\16-program-semantics\TOPIC_COVERAGE_MATRIX.md | 五、形式验证 (来自 Iris \& RustBelt) | `#五形式验证-来自-iris--rustbelt` | 同文件锚点不存在: #五形式验证-来自-iris--rustbelt |
| docs\rust-ownership-decidability\16-program-semantics\TOPIC_COVERAGE_MATRIX.md | **最后更新**: 2026-03-07 | `#最后更新-2026-03-07` | 同文件锚点不存在: #最后更新-2026-03-07 |
| docs\rust-ownership-decidability\16-program-semantics\00-foundations\00a-lambda-calculus.md | **最后更新**: 2026-03-08 | `#最后更新-2026-03-08` | 同文件锚点不存在: #最后更新-2026-03-08 |
| docs\rust-ownership-decidability\16-program-semantics\00-foundations\00b-type-theory-basics.md | 4. 子类型与变型 (Subtyping \& Variance) | `#4-子类型与变型-subtyping--variance` | 同文件锚点不存在: #4-子类型与变型-subtyping--variance |
| docs\rust-ownership-decidability\16-program-semantics\00-foundations\00b-type-theory-basics.md | **最后更新**: 2026-03-08 | `#最后更新-2026-03-08` | 同文件锚点不存在: #最后更新-2026-03-08 |
| docs\rust-ownership-decidability\16-program-semantics\00-foundations\00c-operational-semantics.md | 2. 大步语义 (Big-Step / Natural Semantics) | `#2-大步语义-big-step--natural-semantics` | 同文件锚点不存在: #2-大步语义-big-step--natural-semantics |
| docs\rust-ownership-decidability\16-program-semantics\00-foundations\00c-operational-semantics.md | 3. 小步语义 (Small-Step / Structural Semantics) | `#3-小步语义-small-step--structural-semantics` | 同文件锚点不存在: #3-小步语义-small-step--structural-semantics |
| docs\rust-ownership-decidability\16-program-semantics\00-foundations\00c-operational-semantics.md | **最后更新**: 2026-03-08 | `#最后更新-2026-03-08` | 同文件锚点不存在: #最后更新-2026-03-08 |
| docs\rust-ownership-decidability\16-program-semantics\00-foundations\00d-denotational-semantics.md | **后续学习**: 公理语义、分离逻辑 | `#后续学习-公理语义分离逻辑` | 同文件锚点不存在: #后续学习-公理语义分离逻辑 |
| docs\rust-ownership-decidability\16-program-semantics\00-foundations\00e-axiomatic-semantics.md | **后续学习**: 分离逻辑、程序验证 | `#后续学习-分离逻辑程序验证` | 同文件锚点不存在: #后续学习-分离逻辑程序验证 |
| docs\rust-ownership-decidability\16-program-semantics\os-abstractions\01-thread-semantics.md | 这些形式化定义确保了 Rust 并发程序的安全性和正确性 | `#这些形式化定义确保了-rust-并发程序的安全性和正确性` | 同文件锚点不存在: #这些形式化定义确保了-rust-并发程序的安全性和正确性 |
| docs\rust-ownership-decidability\16-program-semantics\os-abstractions\02-lock-semantics.md | 这些形式化定义确保了 Rust 并发程序在使用锁时的安全性和正确性 | `#这些形式化定义确保了-rust-并发程序在使用锁时的安全性和正确性` | 同文件锚点不存在: #这些形式化定义确保了-rust-并发程序在使用锁时的安全性和正确性 |
| docs\rust-ownership-decidability\16-program-semantics\os-abstractions\03-condition-variable-semantics.md | 这些形式化定义确保了 Rust 程序在使用条件变量进行线程协作时的正确性和安全性 | `#这些形式化定义确保了-rust-程序在使用条件变量进行线程协作时的正确性和安全性` | 同文件锚点不存在: #这些形式化定义确保了-rust-程序在使用条件变量进行线程协作时的正确性和安全性 |
| docs\rust-ownership-decidability\16-program-semantics\os-abstractions\04-semaphore-semantics.md | 这些形式化定义确保了 Rust 程序在使用信号量进行并发控制时的正确性和安全性 | `#这些形式化定义确保了-rust-程序在使用信号量进行并发控制时的正确性和安全性` | 同文件锚点不存在: #这些形式化定义确保了-rust-程序在使用信号量进行并发控制时的正确性和安全性 |
| docs\rust-ownership-decidability\16-program-semantics\os-abstractions\05-barrier-semantics.md | 这些形式化定义确保了 Rust 程序在使用屏障进行线程同步时的正确性和安全性 | `#这些形式化定义确保了-rust-程序在使用屏障进行线程同步时的正确性和安全性` | 同文件锚点不存在: #这些形式化定义确保了-rust-程序在使用屏障进行线程同步时的正确性和安全性 |
| docs\rust-ownership-decidability\16-program-semantics\os-abstractions\06-memory-ordering-deep.md | 这些形式化定义确保了 Rust 并发程序在使用原子操作时的正确性和可移植性 | `#这些形式化定义确保了-rust-并发程序在使用原子操作时的正确性和可移植性` | 同文件锚点不存在: #这些形式化定义确保了-rust-并发程序在使用原子操作时的正确性和可移植性 |
| docs\rust-ownership-decidability\16-program-semantics\rust-194-features\02-coerceshared-semantics.md | 理解这些规则对于编写安全和高效的 Rust 代码至关重要 | `#理解这些规则对于编写安全和高效的-rust-代码至关重要` | 同文件锚点不存在: #理解这些规则对于编写安全和高效的-rust-代码至关重要 |
| docs\rust-ownership-decidability\16-program-semantics\rust-194-features\03-const-generics-semantics.md | Const Generics 使得 Rust 能够表达更精确的类型约束，同时保持零成本抽象。 | `#const-generics-使得-rust-能够表达更精确的类型约束同时保持零成本抽象` | 同文件锚点不存在: #const-generics-使得-rust-能够表达更精确的类型约束同时保持零成本抽象 |
| docs\rust-ownership-decidability\16-program-semantics\rust-194-features\04-precise-capturing-semantics.md | Precise Capturing (+ use\<'lt\>) 的生命周期语义 | `#precise-capturing--uselt-的生命周期语义` | 同文件锚点不存在: #precise-capturing--uselt-的生命周期语义 |
| docs\rust-ownership-decidability\16-program-semantics\rust-194-features\04-precise-capturing-semantics.md | 通过 `use<'lt>`，开发者可以编写出生命周期约束更精确、API 更灵活的 Rust 代码 | `#通过-uselt开发者可以编写出生命周期约束更精确api-更灵活的-rust-代码` | 同文件锚点不存在: #通过-uselt开发者可以编写出生命周期约束更精确api-更灵活的-rust-代码 |
| docs\rust-ownership-decidability\16-program-semantics\rust-194-features\05-edition-2024-semantics.md | 这些改进使 Rust 在保持内存安全的同时，提供了更好的开发者体验 | `#这些改进使-rust-在保持内存安全的同时提供了更好的开发者体验` | 同文件锚点不存在: #这些改进使-rust-在保持内存安全的同时提供了更好的开发者体验 |
| docs\rust-ownership-decidability\16-program-semantics\workflow-patterns\06-multi-choice.md | 06 多路选择模式 (Multi-Choice) - 完整形式化语义 | `#06-多路选择模式-multi-choice---完整形式化语义` | 同文件锚点不存在: #06-多路选择模式-multi-choice---完整形式化语义 |
| docs\rust-ownership-decidability\16-program-semantics\workflow-patterns\06-multi-choice.md | **最后更新**: 2026-03-07 | `#最后更新-2026-03-07` | 同文件锚点不存在: #最后更新-2026-03-07 |
| docs\rust-ownership-decidability\16-program-semantics\workflow-patterns\07-sync-merge.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\rust-ownership-decidability\16-program-semantics\workflow-patterns\07-sync-merge.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\rust-ownership-decidability\16-program-semantics\workflow-patterns\08-multi-merge.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\rust-ownership-decidability\16-program-semantics\workflow-patterns\08-multi-merge.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\rust-ownership-decidability\16-program-semantics\workflow-patterns\09-discriminator.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\rust-ownership-decidability\16-program-semantics\workflow-patterns\09-discriminator.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\rust-ownership-decidability\16-program-semantics\workflow-patterns\10-arbitrary-cycles.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\rust-ownership-decidability\16-program-semantics\workflow-patterns\10-arbitrary-cycles.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\rust-ownership-decidability\16-program-semantics\workflow-patterns\11-implicit-termination.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\rust-ownership-decidability\16-program-semantics\workflow-patterns\11-implicit-termination.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\rust-ownership-decidability\16-program-semantics\workflow-patterns\12-mi-without-sync.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\rust-ownership-decidability\16-program-semantics\workflow-patterns\12-mi-without-sync.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\rust-ownership-decidability\16-program-semantics\workflow-patterns\13-mi-with-sync.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\rust-ownership-decidability\16-program-semantics\workflow-patterns\13-mi-with-sync.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\rust-ownership-decidability\16-program-semantics\workflow-patterns\14-deferred-choice.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\rust-ownership-decidability\16-program-semantics\workflow-patterns\14-deferred-choice.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\rust-ownership-decidability\16-program-semantics\workflow-patterns\15-interleaved-routing.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\rust-ownership-decidability\16-program-semantics\workflow-patterns\15-interleaved-routing.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\rust-ownership-decidability\16-program-semantics\workflow-patterns\16-milestone.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\rust-ownership-decidability\16-program-semantics\workflow-patterns\16-milestone.md | 📋 目录 | `#-目录-1` | 同文件锚点不存在: #-目录-1 |
| docs\rust-ownership-decidability\17-unsafe-rust\01-intro.md | 7.1 Miri - Rust 的内存检查器 | `#71-miri---rust-的内存检查器` | 同文件锚点不存在: #71-miri---rust-的内存检查器 |
| docs\rust-ownership-decidability\17-unsafe-rust\01-intro.md | *最后更新: 2026-03-07* | `#最后更新-2026-03-07` | 同文件锚点不存在: #最后更新-2026-03-07 |
| docs\rust-ownership-decidability\17-unsafe-rust\02-raw-pointers.md | *最后更新: 2026-03-07* | `#最后更新-2026-03-07` | 同文件锚点不存在: #最后更新-2026-03-07 |
| docs\rust-ownership-decidability\17-unsafe-rust\03-unsafe-functions.md | *文档版本: 1.0.0* | `#文档版本-100` | 同文件锚点不存在: #文档版本-100 |
| docs\rust-ownership-decidability\17-unsafe-rust\05-uninitialized-memory.md | *最后更新: 2026-03-07* | `#最后更新-2026-03-07` | 同文件锚点不存在: #最后更新-2026-03-07 |
| docs\rust-ownership-decidability\17-unsafe-rust\07-drop-flags.md | *文档版本: 1.0.0* | `#文档版本-100` | 同文件锚点不存在: #文档版本-100 |
| docs\rust-ownership-decidability\17-unsafe-rust\08-aliasing.md | *文档版本: 1.0.0* | `#文档版本-100` | 同文件锚点不存在: #文档版本-100 |
| docs\rust-ownership-decidability\17-unsafe-rust\10-inline-asm.md | *最后更新: 2026-03-07* | `#最后更新-2026-03-07` | 同文件锚点不存在: #最后更新-2026-03-07 |
| docs\rust-ownership-decidability\17-unsafe-rust\11-impl-vec.md | *最后更新: 2026-03-07* | `#最后更新-2026-03-07` | 同文件锚点不存在: #最后更新-2026-03-07 |
| docs\rust-ownership-decidability\actor-specialty\case-studies\actix-web-production.md | **Actix-web版本**: 4.x | `#actix-web版本-4x` | 同文件锚点不存在: #actix-web版本-4x |
| docs\rust-ownership-decidability\actor-specialty\decision-trees\actor-framework-selection.md | **覆盖框架**: Actix, Bastion, coerce, Xtra, Heph, Stakker | `#覆盖框架-actix-bastion-coerce-xtra-heph-stakker` | 同文件锚点不存在: #覆盖框架-actix-bastion-coerce-xtra-heph-stakker |
| docs\rust-ownership-decidability\actor-specialty\distributed\distributed-actors-formal.md | **覆盖**: CAP定理、一致性模型、分布式协议、Saga、CRDT | `#覆盖-cap定理一致性模型分布式协议sagacrdt` | 同文件锚点不存在: #覆盖-cap定理一致性模型分布式协议sagacrdt |
| docs\rust-ownership-decidability\actor-specialty\examples\chat-system-example.md | **更新日期**: 2026-03-05 | `#更新日期-2026-03-05` | 同文件锚点不存在: #更新日期-2026-03-05 |
| docs\rust-ownership-decidability\actor-specialty\formal-proofs\actor-safety-theorems.md | 定理8: Rust + Actor 内存安全 | `#定理8-rust--actor-内存安全` | 同文件锚点不存在: #定理8-rust--actor-内存安全 |
| docs\rust-ownership-decidability\actor-specialty\formal-proofs\actor-safety-theorems.md | **定理数量**: 11个核心定理 + 3个推论 | `#定理数量-11个核心定理--3个推论` | 同文件锚点不存在: #定理数量-11个核心定理--3个推论 |
| docs\rust-ownership-decidability\actor-specialty\matrices\actor-framework-matrix.md | **覆盖框架**: Actix, Bastion, coerce, Xtra, Heph, Stakker | `#覆盖框架-actix-bastion-coerce-xtra-heph-stakker` | 同文件锚点不存在: #覆盖框架-actix-bastion-coerce-xtra-heph-stakker |
| docs\rust-ownership-decidability\actor-specialty\mindmaps\actor-model-mindmap.md | Actor模型 - 思维导图 | `#actor模型---思维导图` | 同文件锚点不存在: #actor模型---思维导图 |
| docs\rust-ownership-decidability\actor-specialty\mindmaps\actor-model-mindmap.md | **更新日期**: 2026-03-05 | `#更新日期-2026-03-05` | 同文件锚点不存在: #更新日期-2026-03-05 |
| docs\rust-ownership-decidability\actor-specialty\patterns\actor-design-patterns-expanded.md | Actor设计模式 - 扩展版 | `#actor设计模式---扩展版` | 同文件锚点不存在: #actor设计模式---扩展版 |
| docs\rust-ownership-decidability\actor-specialty\patterns\actor-design-patterns-expanded.md | **覆盖模式**: 8个核心模式 + 形式化定义 | `#覆盖模式-8个核心模式--形式化定义` | 同文件锚点不存在: #覆盖模式-8个核心模式--形式化定义 |
| docs\rust-ownership-decidability\actor-specialty\patterns\actor-design-patterns.md | **更新日期**: 2026-03-05 | `#更新日期-2026-03-05` | 同文件锚点不存在: #更新日期-2026-03-05 |
| docs\rust-ownership-decidability\actor-specialty\scenario-trees\actor-application-domains.md | **更新日期**: 2026-03-05 | `#更新日期-2026-03-05` | 同文件锚点不存在: #更新日期-2026-03-05 |
| docs\rust-ownership-decidability\actor-specialty\theory\actor-model-foundation.md | **状态**: ✅ 理论基础完成 | `#状态--理论基础完成` | 同文件锚点不存在: #状态--理论基础完成 |
| docs\rust-ownership-decidability\archive\FINAL_COMPLETION_REPORT.md | 章节1 | `#1-章节1` | 同文件锚点不存在: #1-章节1 |
| docs\rust-ownership-decidability\archive\FINAL_COMPLETION_REPORT.md | 子章节 | `#11-子章节` | 同文件锚点不存在: #11-子章节 |
| docs\rust-ownership-decidability\archive\FINAL_COMPLETION_REPORT.md | 子章节 | `#12-子章节` | 同文件锚点不存在: #12-子章节 |
| docs\rust-ownership-decidability\archive\FINAL_COMPLETION_REPORT.md | 章节2 | `#2-章节2` | 同文件锚点不存在: #2-章节2 |
| docs\rust-ownership-decidability\async-specialty\ASYNC_ECOSYSTEM_COMPLETE.md | Rust Async 生态系统专题 - 完整完成报告 | `#rust-async-生态系统专题---完整完成报告` | 同文件锚点不存在: #rust-async-生态系统专题---完整完成报告 |
| docs\rust-ownership-decidability\async-specialty\COMPLETION_REPORT.md | Async Rust 全面专题 - 完成报告 | `#async-rust-全面专题---完成报告` | 同文件锚点不存在: #async-rust-全面专题---完成报告 |
| docs\rust-ownership-decidability\async-specialty\authoritative\tokio-deep-dive.md | Tokio深度解读 - 权威来源整合 | `#tokio深度解读---权威来源整合` | 同文件锚点不存在: #tokio深度解读---权威来源整合 |
| docs\rust-ownership-decidability\async-specialty\authoritative\tokio-deep-dive.md | **更新日期**: 2026-03-05 | `#更新日期-2026-03-05` | 同文件锚点不存在: #更新日期-2026-03-05 |
| docs\rust-ownership-decidability\async-specialty\ecosystem\async-ecosystem-landscape.md | **更新日期**: 2026-03-05 | `#更新日期-2026-03-05` | 同文件锚点不存在: #更新日期-2026-03-05 |
| docs\rust-ownership-decidability\async-specialty\ecosystem\IO_URING_DEEP_DIVE.md | io\_uring 深度解析 - Linux异步IO的未来 | `#io_uring-深度解析---linux异步io的未来` | 同文件锚点不存在: #io_uring-深度解析---linux异步io的未来 |
| docs\rust-ownership-decidability\async-specialty\ecosystem\IO_URING_DEEP_DIVE.md | **更新日期**: 2026-03-05 | `#更新日期-2026-03-05` | 同文件锚点不存在: #更新日期-2026-03-05 |
| docs\rust-ownership-decidability\async-specialty\embedded\embassy-guide.md | **更新日期**: 2026-03-05 | `#更新日期-2026-03-05` | 同文件锚点不存在: #更新日期-2026-03-05 |
| docs\rust-ownership-decidability\async-specialty\network\http-server-patterns.md | 1.1 Axum - 函数式风格 | `#11-axum---函数式风格` | 同文件锚点不存在: #11-axum---函数式风格 |
| docs\rust-ownership-decidability\async-specialty\network\http-server-patterns.md | 1.2 Actix-web - Actor风格 | `#12-actix-web---actor风格` | 同文件锚点不存在: #12-actix-web---actor风格 |
| docs\rust-ownership-decidability\async-specialty\network\http-server-patterns.md | **更新日期**: 2026-03-05 | `#更新日期-2026-03-05` | 同文件锚点不存在: #更新日期-2026-03-05 |
| docs\rust-ownership-decidability\audit_reports\CONTENT_QUALITY_AUDIT.md | Rust所有权与可判定性文档 - 内容质量审计报告 | `#rust所有权与可判定性文档---内容质量审计报告` | 同文件锚点不存在: #rust所有权与可判定性文档---内容质量审计报告 |
| docs\rust-ownership-decidability\audit_reports\CONTENT_QUALITY_AUDIT.md | *下一步: 开始Phase 1重写工作* | `#下一步-开始phase-1重写工作` | 同文件锚点不存在: #下一步-开始phase-1重写工作 |
| docs\rust-ownership-decidability\audit_reports\FINAL_COMPLETE_ANALYSIS_REPORT.md | Rust所有权与可判定性 - 最终完整报告 | `#rust所有权与可判定性---最终完整报告` | 同文件锚点不存在: #rust所有权与可判定性---最终完整报告 |
| docs\rust-ownership-decidability\audit_reports\FINAL_COMPLETE_ANALYSIS_REPORT.md | *"形式化不是目的，而是理解Rust本质的桥梁。"* | `#形式化不是目的而是理解rust本质的桥梁` | 同文件锚点不存在: #形式化不是目的而是理解rust本质的桥梁 |
| docs\rust-ownership-decidability\audit_reports\FINAL_COMPLETION_REPORT_V3.md | Rust所有权与可判定性文档 - 最终完成报告 V3 | `#rust所有权与可判定性文档---最终完成报告-v3` | 同文件锚点不存在: #rust所有权与可判定性文档---最终完成报告-v3 |
| docs\rust-ownership-decidability\audit_reports\FINAL_COMPLETION_REPORT_V3.md | *"从代码堆砌到形式化严谨，这是质的蜕变。"* | `#从代码堆砌到形式化严谨这是质的蜕变` | 同文件锚点不存在: #从代码堆砌到形式化严谨这是质的蜕变 |
| docs\rust-ownership-decidability\audit_reports\FORMALIZATION_FRAMEWORK.md | Rust所有权与可判定性 - 形式化框架规范 | `#rust所有权与可判定性---形式化框架规范` | 同文件锚点不存在: #rust所有权与可判定性---形式化框架规范 |
| docs\rust-ownership-decidability\audit_reports\FORMALIZATION_FRAMEWORK.md | *最后更新: 2026-03-04* | `#最后更新-2026-03-04` | 同文件锚点不存在: #最后更新-2026-03-04 |
| docs\rust-ownership-decidability\audit_reports\LIBRARY_ANALYSIS_COMPLETION_REPORT.md | Rust权威开源库与标准库形式化分析 - 完成报告 | `#rust权威开源库与标准库形式化分析---完成报告` | 同文件锚点不存在: #rust权威开源库与标准库形式化分析---完成报告 |
| docs\rust-ownership-decidability\audit_reports\LIBRARY_ANALYSIS_COMPLETION_REPORT.md | *"从标准库到生态核心库，从内存安全到并发保证，这是Rust形式化理论的完整图景。"* | `#从标准库到生态核心库从内存安全到并发保证这是rust形式化理论的完整图景` | 同文件锚点不存在: #从标准库到生态核心库从内存安全到并发保证这是rust形式化理论的完整图景 |
| docs\rust-ownership-decidability\audit_reports\PHASE3_LIBRARY_ANALYSIS_REPORT.md | Rust所有权与可判定性 - 第三阶段库分析完成报告 | `#rust所有权与可判定性---第三阶段库分析完成报告` | 同文件锚点不存在: #rust所有权与可判定性---第三阶段库分析完成报告 |
| docs\rust-ownership-decidability\audit_reports\PHASE3_LIBRARY_ANALYSIS_REPORT.md | 1. String \&str - UTF-8字符串系统 | `#1-string-str---utf-8字符串系统` | 同文件锚点不存在: #1-string-str---utf-8字符串系统 |
| docs\rust-ownership-decidability\audit_reports\PHASE3_LIBRARY_ANALYSIS_REPORT.md | 2. `Option<T>` \& `Result<T, E>` - 错误处理Monad | `#2-optiont--resultt-e---错误处理monad` | 同文件锚点不存在: #2-optiont--resultt-e---错误处理monad |
| docs\rust-ownership-decidability\audit_reports\PHASE3_LIBRARY_ANALYSIS_REPORT.md | 3. `Pin<P>` - 自引用结构安全 | `#3-pinp---自引用结构安全` | 同文件锚点不存在: #3-pinp---自引用结构安全 |
| docs\rust-ownership-decidability\audit_reports\PHASE3_LIBRARY_ANALYSIS_REPORT.md | 4. Actix-web - Actor模型Web框架 | `#4-actix-web---actor模型web框架` | 同文件锚点不存在: #4-actix-web---actor模型web框架 |
| docs\rust-ownership-decidability\audit_reports\PHASE3_LIBRARY_ANALYSIS_REPORT.md | 5. async-std - 标准库风格异步运行时 | `#5-async-std---标准库风格异步运行时` | 同文件锚点不存在: #5-async-std---标准库风格异步运行时 |
| docs\rust-ownership-decidability\audit_reports\PHASE3_LIBRARY_ANALYSIS_REPORT.md | 6. Tracing - 结构化日志与分布式追踪 | `#6-tracing---结构化日志与分布式追踪` | 同文件锚点不存在: #6-tracing---结构化日志与分布式追踪 |
| docs\rust-ownership-decidability\audit_reports\PHASE3_LIBRARY_ANALYSIS_REPORT.md | 7. Bytes - 零拷贝网络缓冲区 | `#7-bytes---零拷贝网络缓冲区` | 同文件锚点不存在: #7-bytes---零拷贝网络缓冲区 |
| docs\rust-ownership-decidability\audit_reports\PHASE3_LIBRARY_ANALYSIS_REPORT.md | 8. Tonic - gRPC框架 | `#8-tonic---grpc框架` | 同文件锚点不存在: #8-tonic---grpc框架 |
| docs\rust-ownership-decidability\audit_reports\PHASE3_LIBRARY_ANALYSIS_REPORT.md | 9. SQLx - 编译时验证SQL | `#9-sqlx---编译时验证sql` | 同文件锚点不存在: #9-sqlx---编译时验证sql |
| docs\rust-ownership-decidability\audit_reports\PHASE3_LIBRARY_ANALYSIS_REPORT.md | *"从理论基础到生态实践，从内存安全到并发保证，这是Rust形式化理论的完整百科全书。"* | `#从理论基础到生态实践从内存安全到并发保证这是rust形式化理论的完整百科全书` | 同文件锚点不存在: #从理论基础到生态实践从内存安全到并发保证这是rust形式化理论的完整百科全书 |
| docs\rust-ownership-decidability\case-studies\actix-web-formal-analysis.md | *最后更新: 2026-03-04* | `#最后更新-2026-03-04` | 同文件锚点不存在: #最后更新-2026-03-04 |
| docs\rust-ownership-decidability\case-studies\alloc-cortex-m-formal-analysis.md | 定义 POOL-1 ( 内存池 ) | `#定义-pool-1--内存池-` | 同文件锚点不存在: #定义-pool-1--内存池- |
| docs\rust-ownership-decidability\case-studies\alloc-cortex-m-formal-analysis.md | 定义 POOL-2 ( 块分配 ) | `#定义-pool-2--块分配-` | 同文件锚点不存在: #定义-pool-2--块分配- |
| docs\rust-ownership-decidability\case-studies\alloc-cortex-m-formal-analysis.md | 定义 ALLOC-1 ( GlobalAlloc trait ) | `#定义-alloc-1--globalalloc-trait-` | 同文件锚点不存在: #定义-alloc-1--globalalloc-trait- |
| docs\rust-ownership-decidability\case-studies\alloc-cortex-m-formal-analysis.md | 定理 ALLOC-T1 ( 分配器安全 ) | `#定理-alloc-t1--分配器安全-` | 同文件锚点不存在: #定理-alloc-t1--分配器安全- |
| docs\rust-ownership-decidability\case-studies\alloc-cortex-m-formal-analysis.md | 定义 FRAG-1 ( 外部碎片 ) | `#定义-frag-1--外部碎片-` | 同文件锚点不存在: #定义-frag-1--外部碎片- |
| docs\rust-ownership-decidability\case-studies\alloc-cortex-m-formal-analysis.md | 定理 FRAG-T1 ( 固定块无外部碎片 ) | `#定理-frag-t1--固定块无外部碎片-` | 同文件锚点不存在: #定理-frag-t1--固定块无外部碎片- |
| docs\rust-ownership-decidability\case-studies\alloc-cortex-m-formal-analysis.md | 定理 OOM-T1 ( OOM处理 ) | `#定理-oom-t1--oom处理-` | 同文件锚点不存在: #定理-oom-t1--oom处理- |
| docs\rust-ownership-decidability\case-studies\alloc-cortex-m-formal-analysis.md | **状态**: ✅ 已对齐 | `#状态--已对齐` | 同文件锚点不存在: #状态--已对齐 |
| docs\rust-ownership-decidability\case-studies\anyhow-thiserror-formal-analysis.md | Anyhow \& Thiserror 错误处理形式化分析 | `#anyhow--thiserror-错误处理形式化分析` | 同文件锚点不存在: #anyhow--thiserror-错误处理形式化分析 |
| docs\rust-ownership-decidability\case-studies\anyhow-thiserror-formal-analysis.md | *定理数量: 6个* | `#定理数量-6个` | 同文件锚点不存在: #定理数量-6个 |
| docs\rust-ownership-decidability\case-studies\arc-swap-formal-analysis.md | *定理数量: 4个* | `#定理数量-4个` | 同文件锚点不存在: #定理数量-4个 |
| docs\rust-ownership-decidability\case-studies\async-graphql-formal-analysis.md | *定理数量: 6个* | `#定理数量-6个` | 同文件锚点不存在: #定理数量-6个 |
| docs\rust-ownership-decidability\case-studies\async-std-formal-analysis.md | *最后更新: 2026-03-04* | `#最后更新-2026-03-04` | 同文件锚点不存在: #最后更新-2026-03-04 |
| docs\rust-ownership-decidability\case-studies\backoff-retry-formal-analysis.md | *定理数量: 4个* | `#定理数量-4个` | 同文件锚点不存在: #定理数量-4个 |
| docs\rust-ownership-decidability\case-studies\bevy-ecs-formal-analysis.md | *最后更新: 2026-03-04* | `#最后更新-2026-03-04` | 同文件锚点不存在: #最后更新-2026-03-04 |
| docs\rust-ownership-decidability\case-studies\bindgen-cbindgen-formal-analysis.md | *定理数量: 6个* | `#定理数量-6个` | 同文件锚点不存在: #定理数量-6个 |
| docs\rust-ownership-decidability\case-studies\bytemuck-formal-analysis.md | **代码示例**: 8个完整示例 | `#代码示例-8个完整示例` | 同文件锚点不存在: #代码示例-8个完整示例 |
| docs\rust-ownership-decidability\case-studies\bytes-formal-analysis.md | *最后更新: 2026-03-04* | `#最后更新-2026-03-04` | 同文件锚点不存在: #最后更新-2026-03-04 |
| docs\rust-ownership-decidability\case-studies\chrono-formal-analysis.md | 定义 TIME-1 ( NaiveDateTime ) | `#定义-time-1--naivedatetime-` | 同文件锚点不存在: #定义-time-1--naivedatetime- |
| docs\rust-ownership-decidability\case-studies\chrono-formal-analysis.md | 定义 TIME-2 ( DateTime ) | `#定义-time-2--datetime-` | 同文件锚点不存在: #定义-time-2--datetime- |
| docs\rust-ownership-decidability\case-studies\chrono-formal-analysis.md | 定理 TIME-T1 ( 有效性 ) | `#定理-time-t1--有效性-` | 同文件锚点不存在: #定理-time-t1--有效性- |
| docs\rust-ownership-decidability\case-studies\chrono-formal-analysis.md | 定义 DURATION-1 ( TimeDelta ) | `#定义-duration-1--timedelta-` | 同文件锚点不存在: #定义-duration-1--timedelta- |
| docs\rust-ownership-decidability\case-studies\chrono-formal-analysis.md | 定理 DURATION-T1 ( 单调性 ) | `#定理-duration-t1--单调性-` | 同文件锚点不存在: #定理-duration-t1--单调性- |
| docs\rust-ownership-decidability\case-studies\chrono-formal-analysis.md | 定义 TZ-1 ( 时区转换 ) | `#定义-tz-1--时区转换-` | 同文件锚点不存在: #定义-tz-1--时区转换- |
| docs\rust-ownership-decidability\case-studies\chrono-formal-analysis.md | 定义 TZ-2 ( 本地时间 ) | `#定义-tz-2--本地时间-` | 同文件锚点不存在: #定义-tz-2--本地时间- |
| docs\rust-ownership-decidability\case-studies\chrono-formal-analysis.md | 定理 TZ-T1 ( 夏令时安全 ) | `#定理-tz-t1--夏令时安全-` | 同文件锚点不存在: #定理-tz-t1--夏令时安全- |
| docs\rust-ownership-decidability\case-studies\chrono-formal-analysis.md | 定义 FORMAT-1 ( 格式化模式 ) | `#定义-format-1--格式化模式-` | 同文件锚点不存在: #定义-format-1--格式化模式- |
| docs\rust-ownership-decidability\case-studies\chrono-formal-analysis.md | 定理 FORMAT-T1 ( 解析可逆 ) | `#定理-format-t1--解析可逆-` | 同文件锚点不存在: #定理-format-t1--解析可逆- |
| docs\rust-ownership-decidability\case-studies\chrono-formal-analysis.md | 定义 ARITH-1 ( 日期算术 ) | `#定义-arith-1--日期算术-` | 同文件锚点不存在: #定义-arith-1--日期算术- |
| docs\rust-ownership-decidability\case-studies\chrono-formal-analysis.md | 定理 ARITH-T1 ( 溢出检查 ) | `#定理-arith-t1--溢出检查-` | 同文件锚点不存在: #定理-arith-t1--溢出检查- |
| docs\rust-ownership-decidability\case-studies\chrono-formal-analysis.md | 定理 CHRONO-T1 ( 时区安全 ) | `#定理-chrono-t1--时区安全-` | 同文件锚点不存在: #定理-chrono-t1--时区安全- |
| docs\rust-ownership-decidability\case-studies\chrono-formal-analysis.md | 定理 CHRONO-T2 ( 闰秒处理 ) | `#定理-chrono-t2--闰秒处理-` | 同文件锚点不存在: #定理-chrono-t2--闰秒处理- |
| docs\rust-ownership-decidability\case-studies\chrono-formal-analysis.md | **状态**: ✅ 已对齐 | `#状态--已对齐` | 同文件锚点不存在: #状态--已对齐 |
| docs\rust-ownership-decidability\case-studies\clap-formal-analysis.md | 定义 DERIVE-1 ( 结构体派生 ) | `#定义-derive-1--结构体派生-` | 同文件锚点不存在: #定义-derive-1--结构体派生- |
| docs\rust-ownership-decidability\case-studies\clap-formal-analysis.md | 定义 DERIVE-2 ( 属性映射 ) | `#定义-derive-2--属性映射-` | 同文件锚点不存在: #定义-derive-2--属性映射- |
| docs\rust-ownership-decidability\case-studies\clap-formal-analysis.md | 定理 DERIVE-T1 ( 完备解析 ) | `#定理-derive-t1--完备解析-` | 同文件锚点不存在: #定理-derive-t1--完备解析- |
| docs\rust-ownership-decidability\case-studies\clap-formal-analysis.md | 定义 ARG-1 ( 位置参数 ) | `#定义-arg-1--位置参数-` | 同文件锚点不存在: #定义-arg-1--位置参数- |
| docs\rust-ownership-decidability\case-studies\clap-formal-analysis.md | 定义 ARG-2 ( 可选参数 ) | `#定义-arg-2--可选参数-` | 同文件锚点不存在: #定义-arg-2--可选参数- |
| docs\rust-ownership-decidability\case-studies\clap-formal-analysis.md | 定理 ARG-T1 ( 类型转换安全 ) | `#定理-arg-t1--类型转换安全-` | 同文件锚点不存在: #定理-arg-t1--类型转换安全- |
| docs\rust-ownership-decidability\case-studies\clap-formal-analysis.md | 定义 VALIDATE-1 ( 值验证 ) | `#定义-validate-1--值验证-` | 同文件锚点不存在: #定义-validate-1--值验证- |
| docs\rust-ownership-decidability\case-studies\clap-formal-analysis.md | 定义 VALIDATE-2 ( 组合约束 ) | `#定义-validate-2--组合约束-` | 同文件锚点不存在: #定义-validate-2--组合约束- |
| docs\rust-ownership-decidability\case-studies\clap-formal-analysis.md | 定义 SUBCMD-1 ( 子命令枚举 ) | `#定义-subcmd-1--子命令枚举-` | 同文件锚点不存在: #定义-subcmd-1--子命令枚举- |
| docs\rust-ownership-decidability\case-studies\clap-formal-analysis.md | 定理 SUBCMD-T1 ( 互斥性 ) | `#定理-subcmd-t1--互斥性-` | 同文件锚点不存在: #定理-subcmd-t1--互斥性- |
| docs\rust-ownership-decidability\case-studies\clap-formal-analysis.md | 定理 CLAP-T1 ( 零运行时开销 ) | `#定理-clap-t1--零运行时开销-` | 同文件锚点不存在: #定理-clap-t1--零运行时开销- |
| docs\rust-ownership-decidability\case-studies\clap-formal-analysis.md | 定理 CLAP-T2 ( 类型安全保证 ) | `#定理-clap-t2--类型安全保证-` | 同文件锚点不存在: #定理-clap-t2--类型安全保证- |
| docs\rust-ownership-decidability\case-studies\clap-formal-analysis.md | **状态**: ✅ 已对齐 | `#状态--已对齐` | 同文件锚点不存在: #状态--已对齐 |
| docs\rust-ownership-decidability\case-studies\compile-time-macros-formal-analysis.md | *定理数量: 4个* | `#定理数量-4个` | 同文件锚点不存在: #定理数量-4个 |
| docs\rust-ownership-decidability\case-studies\COMPLETE_DOMAIN_COVERAGE_INDEX.md | Rust 所有权系统 - 完整领域覆盖索引 | `#rust-所有权系统---完整领域覆盖索引` | 同文件锚点不存在: #rust-所有权系统---完整领域覆盖索引 |
| docs\rust-ownership-decidability\case-studies\COMPLETE_DOMAIN_COVERAGE_INDEX.md | ☁️ 云原生 | `#️-云原生` | 同文件锚点不存在: #️-云原生 |
| docs\rust-ownership-decidability\case-studies\COMPLETE_DOMAIN_COVERAGE_INDEX.md | 🕸️ WASM | `#️-wasm` | 同文件锚点不存在: #️-wasm |
| docs\rust-ownership-decidability\case-studies\COMPLETE_DOMAIN_COVERAGE_INDEX.md | *覆盖领域: 16 个* | `#覆盖领域-16-个` | 同文件锚点不存在: #覆盖领域-16-个 |
| docs\rust-ownership-decidability\case-studies\config-formal-analysis.md | *定理数量: 5个* | `#定理数量-5个` | 同文件锚点不存在: #定理数量-5个 |
| docs\rust-ownership-decidability\case-studies\const-gen-formal-analysis.md | *定理数量: 4个* | `#定理数量-4个` | 同文件锚点不存在: #定理数量-4个 |
| docs\rust-ownership-decidability\case-studies\cortex-m-rt-formal-analysis.md | *最后更新: 2026-03-05* | `#最后更新-2026-03-05` | 同文件锚点不存在: #最后更新-2026-03-05 |
| docs\rust-ownership-decidability\case-studies\criterion-formal-analysis.md | *定理数量: 5个* | `#定理数量-5个` | 同文件锚点不存在: #定理数量-5个 |
| docs\rust-ownership-decidability\case-studies\crossbeam-formal-analysis.md | 反例 7.3 (ABA问题 - 无epoch) | `#反例-73-aba问题---无epoch` | 同文件锚点不存在: #反例-73-aba问题---无epoch |
| docs\rust-ownership-decidability\case-studies\crossbeam-formal-analysis.md | *最后更新: 2026-03-04* | `#最后更新-2026-03-04` | 同文件锚点不存在: #最后更新-2026-03-04 |
| docs\rust-ownership-decidability\case-studies\cxx-formal-analysis.md | *定理数量: 6个* | `#定理数量-6个` | 同文件锚点不存在: #定理数量-6个 |
| docs\rust-ownership-decidability\case-studies\dashmap-formal-analysis.md | 定义 SHARD-1 ( 分片结构 ) | `#定义-shard-1--分片结构-` | 同文件锚点不存在: #定义-shard-1--分片结构- |
| docs\rust-ownership-decidability\case-studies\dashmap-formal-analysis.md | 定义 SHARD-2 ( 键分配 ) | `#定义-shard-2--键分配-` | 同文件锚点不存在: #定义-shard-2--键分配- |
| docs\rust-ownership-decidability\case-studies\dashmap-formal-analysis.md | 定理 SHARD-T1 ( 锁粒度 ) | `#定理-shard-t1--锁粒度-` | 同文件锚点不存在: #定理-shard-t1--锁粒度- |
| docs\rust-ownership-decidability\case-studies\dashmap-formal-analysis.md | 定义 READ-1 ( 获取 ) | `#定义-read-1--获取-` | 同文件锚点不存在: #定义-read-1--获取- |
| docs\rust-ownership-decidability\case-studies\dashmap-formal-analysis.md | 定义 WRITE-1 ( 插入 ) | `#定义-write-1--插入-` | 同文件锚点不存在: #定义-write-1--插入- |
| docs\rust-ownership-decidability\case-studies\dashmap-formal-analysis.md | 定义 WRITE-2 ( 条件修改 ) | `#定义-write-2--条件修改-` | 同文件锚点不存在: #定义-write-2--条件修改- |
| docs\rust-ownership-decidability\case-studies\dashmap-formal-analysis.md | 定义 ITER-1 ( 快照迭代 ) | `#定义-iter-1--快照迭代-` | 同文件锚点不存在: #定义-iter-1--快照迭代- |
| docs\rust-ownership-decidability\case-studies\dashmap-formal-analysis.md | 定义 ITER-2 ( 迭代器一致性 ) | `#定义-iter-2--迭代器一致性-` | 同文件锚点不存在: #定义-iter-2--迭代器一致性- |
| docs\rust-ownership-decidability\case-studies\dashmap-formal-analysis.md | 定理 ITER-T1 ( 弱一致性 ) | `#定理-iter-t1--弱一致性-` | 同文件锚点不存在: #定理-iter-t1--弱一致性- |
| docs\rust-ownership-decidability\case-studies\dashmap-formal-analysis.md | 定义 REF-1 ( Ref类型 ) | `#定义-ref-1--ref类型-` | 同文件锚点不存在: #定义-ref-1--ref类型- |
| docs\rust-ownership-decidability\case-studies\dashmap-formal-analysis.md | 定义 REF-2 ( RefMut类型 ) | `#定义-ref-2--refmut类型-` | 同文件锚点不存在: #定义-ref-2--refmut类型- |
| docs\rust-ownership-decidability\case-studies\dashmap-formal-analysis.md | 定理 REF-T1 ( 自动释放 ) | `#定理-ref-t1--自动释放-` | 同文件锚点不存在: #定理-ref-t1--自动释放- |
| docs\rust-ownership-decidability\case-studies\dashmap-formal-analysis.md | 定义 PERF-1 ( 读优化 ) | `#定义-perf-1--读优化-` | 同文件锚点不存在: #定义-perf-1--读优化- |
| docs\rust-ownership-decidability\case-studies\dashmap-formal-analysis.md | 定理 PERF-T1 ( 扩展性 ) | `#定理-perf-t1--扩展性-` | 同文件锚点不存在: #定理-perf-t1--扩展性- |
| docs\rust-ownership-decidability\case-studies\dashmap-formal-analysis.md | 定理 DASHMAP-T1 ( 线程安全 ) | `#定理-dashmap-t1--线程安全-` | 同文件锚点不存在: #定理-dashmap-t1--线程安全- |
| docs\rust-ownership-decidability\case-studies\dashmap-formal-analysis.md | 定理 DASHMAP-T2 ( 死锁避免 ) | `#定理-dashmap-t2--死锁避免-` | 同文件锚点不存在: #定理-dashmap-t2--死锁避免- |
| docs\rust-ownership-decidability\case-studies\dashmap-formal-analysis.md | **状态**: ✅ 已对齐 | `#状态--已对齐` | 同文件锚点不存在: #状态--已对齐 |
| docs\rust-ownership-decidability\case-studies\deadpool-formal-analysis.md | *定理数量: 7个* | `#定理数量-7个` | 同文件锚点不存在: #定理数量-7个 |
| docs\rust-ownership-decidability\case-studies\defmt-formal-analysis.md | *最后更新: 2026-03-05* | `#最后更新-2026-03-05` | 同文件锚点不存在: #最后更新-2026-03-05 |
| docs\rust-ownership-decidability\case-studies\derive-more-formal-analysis.md | *定理数量: 4个* | `#定理数量-4个` | 同文件锚点不存在: #定理数量-4个 |
| docs\rust-ownership-decidability\case-studies\diesel-formal-analysis.md | 定义 DSL-1 ( 查询DSL ) | `#定义-dsl-1--查询dsl-` | 同文件锚点不存在: #定义-dsl-1--查询dsl- |
| docs\rust-ownership-decidability\case-studies\diesel-formal-analysis.md | 定义 DSL-2 ( 表达式类型 ) | `#定义-dsl-2--表达式类型-` | 同文件锚点不存在: #定义-dsl-2--表达式类型- |
| docs\rust-ownership-decidability\case-studies\diesel-formal-analysis.md | 定理 DSL-T1 ( 类型一致 ) | `#定理-dsl-t1--类型一致-` | 同文件锚点不存在: #定理-dsl-t1--类型一致- |
| docs\rust-ownership-decidability\case-studies\diesel-formal-analysis.md | 定义 QUERY-1 ( Select查询 ) | `#定义-query-1--select查询-` | 同文件锚点不存在: #定义-query-1--select查询- |
| docs\rust-ownership-decidability\case-studies\diesel-formal-analysis.md | 定义 QUERY-2 ( 类型推断 ) | `#定义-query-2--类型推断-` | 同文件锚点不存在: #定义-query-2--类型推断- |
| docs\rust-ownership-decidability\case-studies\diesel-formal-analysis.md | 定理 QUERY-T1 ( 返回类型安全 ) | `#定理-query-t1--返回类型安全-` | 同文件锚点不存在: #定理-query-t1--返回类型安全- |
| docs\rust-ownership-decidability\case-studies\diesel-formal-analysis.md | 定义 SCHEMA-1 ( Table定义 ) | `#定义-schema-1--table定义-` | 同文件锚点不存在: #定义-schema-1--table定义- |
| docs\rust-ownership-decidability\case-studies\diesel-formal-analysis.md | 定义 SCHEMA-2 ( 关联类型 ) | `#定义-schema-2--关联类型-` | 同文件锚点不存在: #定义-schema-2--关联类型- |
| docs\rust-ownership-decidability\case-studies\diesel-formal-analysis.md | 定义 MIGRATION-1 ( 迁移结构 ) | `#定义-migration-1--迁移结构-` | 同文件锚点不存在: #定义-migration-1--迁移结构- |
| docs\rust-ownership-decidability\case-studies\diesel-formal-analysis.md | 定理 MIGRATION-T1 ( 幂等性 ) | `#定理-migration-t1--幂等性-` | 同文件锚点不存在: #定理-migration-t1--幂等性- |
| docs\rust-ownership-decidability\case-studies\diesel-formal-analysis.md | 定义 CONN-1 ( 连接池 ) | `#定义-conn-1--连接池-` | 同文件锚点不存在: #定义-conn-1--连接池- |
| docs\rust-ownership-decidability\case-studies\diesel-formal-analysis.md | 定理 CONN-T1 ( 线程安全 ) | `#定理-conn-t1--线程安全-` | 同文件锚点不存在: #定理-conn-t1--线程安全- |
| docs\rust-ownership-decidability\case-studies\diesel-formal-analysis.md | 定理 DIESEL-T1 ( 编译时SQL验证 ) | `#定理-diesel-t1--编译时sql验证-` | 同文件锚点不存在: #定理-diesel-t1--编译时sql验证- |
| docs\rust-ownership-decidability\case-studies\diesel-formal-analysis.md | 定理 DIESEL-T2 ( 零成本抽象 ) | `#定理-diesel-t2--零成本抽象-` | 同文件锚点不存在: #定理-diesel-t2--零成本抽象- |
| docs\rust-ownership-decidability\case-studies\diesel-formal-analysis.md | **状态**: ✅ 已对齐 | `#状态--已对齐` | 同文件锚点不存在: #状态--已对齐 |
| docs\rust-ownership-decidability\case-studies\diesel-orm-type-safety.md | *最后更新: 2026-03-04* | `#最后更新-2026-03-04` | 同文件锚点不存在: #最后更新-2026-03-04 |
| docs\rust-ownership-decidability\case-studies\embassy-formal-analysis.md | **代码示例**: 6个完整示例 | `#代码示例-6个完整示例` | 同文件锚点不存在: #代码示例-6个完整示例 |
| docs\rust-ownership-decidability\case-studies\embedded-graphics-formal-analysis.md | 定义 PRIMITIVE-1 ( 基本图形 ) | `#定义-primitive-1--基本图形-` | 同文件锚点不存在: #定义-primitive-1--基本图形- |
| docs\rust-ownership-decidability\case-studies\embedded-graphics-formal-analysis.md | 定义 PRIMITIVE-2 ( 像素迭代 ) | `#定义-primitive-2--像素迭代-` | 同文件锚点不存在: #定义-primitive-2--像素迭代- |
| docs\rust-ownership-decidability\case-studies\embedded-graphics-formal-analysis.md | 定义 ITER-1 ( 惰性求值 ) | `#定义-iter-1--惰性求值-` | 同文件锚点不存在: #定义-iter-1--惰性求值- |
| docs\rust-ownership-decidability\case-studies\embedded-graphics-formal-analysis.md | 定理 ITER-T1 ( 零分配 ) | `#定理-iter-t1--零分配-` | 同文件锚点不存在: #定理-iter-t1--零分配- |
| docs\rust-ownership-decidability\case-studies\embedded-graphics-formal-analysis.md | 定义 TARGET-1 ( DrawTarget trait ) | `#定义-target-1--drawtarget-trait-` | 同文件锚点不存在: #定义-target-1--drawtarget-trait- |
| docs\rust-ownership-decidability\case-studies\embedded-graphics-formal-analysis.md | 定义 TARGET-2 ( 帧缓冲 ) | `#定义-target-2--帧缓冲-` | 同文件锚点不存在: #定义-target-2--帧缓冲- |
| docs\rust-ownership-decidability\case-studies\embedded-graphics-formal-analysis.md | 定义 STYLE-1 ( 样式属性 ) | `#定义-style-1--样式属性-` | 同文件锚点不存在: #定义-style-1--样式属性- |
| docs\rust-ownership-decidability\case-studies\embedded-graphics-formal-analysis.md | 定义 TRANSFORM-1 ( 仿射变换 ) | `#定义-transform-1--仿射变换-` | 同文件锚点不存在: #定义-transform-1--仿射变换- |
| docs\rust-ownership-decidability\case-studies\embedded-graphics-formal-analysis.md | 定理 CLIP-T1 ( 裁剪正确性 ) | `#定理-clip-t1--裁剪正确性-` | 同文件锚点不存在: #定理-clip-t1--裁剪正确性- |
| docs\rust-ownership-decidability\case-studies\embedded-hal-formal-analysis.md | **代码示例**: 15个完整示例 | `#代码示例-15个完整示例` | 同文件锚点不存在: #代码示例-15个完整示例 |
| docs\rust-ownership-decidability\case-studies\embedded-storage-formal-analysis.md | 定义 STORAGE-1 ( 只读存储 ) | `#定义-storage-1--只读存储-` | 同文件锚点不存在: #定义-storage-1--只读存储- |
| docs\rust-ownership-decidability\case-studies\embedded-storage-formal-analysis.md | 定义 STORAGE-2 ( 可擦除存储 ) | `#定义-storage-2--可擦除存储-` | 同文件锚点不存在: #定义-storage-2--可擦除存储- |
| docs\rust-ownership-decidability\case-studies\embedded-storage-formal-analysis.md | 定义 NOR-1 ( 字节可编程 ) | `#定义-nor-1--字节可编程-` | 同文件锚点不存在: #定义-nor-1--字节可编程- |
| docs\rust-ownership-decidability\case-studies\embedded-storage-formal-analysis.md | 定理 NOR-T1 ( 编程限制 ) | `#定理-nor-t1--编程限制-` | 同文件锚点不存在: #定理-nor-t1--编程限制- |
| docs\rust-ownership-decidability\case-studies\embedded-storage-formal-analysis.md | 定义 NAND-1 ( 块擦除 ) | `#定义-nand-1--块擦除-` | 同文件锚点不存在: #定义-nand-1--块擦除- |
| docs\rust-ownership-decidability\case-studies\embedded-storage-formal-analysis.md | 定义 NAND-2 ( 坏块管理 ) | `#定义-nand-2--坏块管理-` | 同文件锚点不存在: #定义-nand-2--坏块管理- |
| docs\rust-ownership-decidability\case-studies\embedded-storage-formal-analysis.md | 定理 NAND-T1 ( 顺序编程 ) | `#定理-nand-t1--顺序编程-` | 同文件锚点不存在: #定理-nand-t1--顺序编程- |
| docs\rust-ownership-decidability\case-studies\embedded-storage-formal-analysis.md | 定义 WEAR-1 ( 擦除计数 ) | `#定义-wear-1--擦除计数-` | 同文件锚点不存在: #定义-wear-1--擦除计数- |
| docs\rust-ownership-decidability\case-studies\embedded-storage-formal-analysis.md | 定义 WEAR-2 ( 磨损均衡算法 ) | `#定义-wear-2--磨损均衡算法-` | 同文件锚点不存在: #定义-wear-2--磨损均衡算法- |
| docs\rust-ownership-decidability\case-studies\embedded-storage-formal-analysis.md | 定理 WEAR-T1 ( 寿命延长 ) | `#定理-wear-t1--寿命延长-` | 同文件锚点不存在: #定理-wear-t1--寿命延长- |
| docs\rust-ownership-decidability\case-studies\embedded-storage-formal-analysis.md | 定理 STORAGE-T1 ( 原子性 ) | `#定理-storage-t1--原子性-` | 同文件锚点不存在: #定理-storage-t1--原子性- |
| docs\rust-ownership-decidability\case-studies\embedded-storage-formal-analysis.md | 定理 STORAGE-T2 ( 幂等性 ) | `#定理-storage-t2--幂等性-` | 同文件锚点不存在: #定理-storage-t2--幂等性- |
| docs\rust-ownership-decidability\case-studies\embedded-storage-formal-analysis.md | **状态**: ✅ 已对齐 | `#状态--已对齐` | 同文件锚点不存在: #状态--已对齐 |
| docs\rust-ownership-decidability\case-studies\figment-formal-analysis.md | *代码示例: 11个完整示例* | `#代码示例-11个完整示例` | 同文件锚点不存在: #代码示例-11个完整示例 |
| docs\rust-ownership-decidability\case-studies\flate2-formal-analysis.md | *定理数量: 5个* | `#定理数量-5个` | 同文件锚点不存在: #定理数量-5个 |
| docs\rust-ownership-decidability\case-studies\frunk-formal-analysis.md | *分析深度: 高级技术分析* | `#分析深度-高级技术分析` | 同文件锚点不存在: #分析深度-高级技术分析 |
| docs\rust-ownership-decidability\case-studies\generic-array-formal-analysis.md | 5.1 default() - 默认构造 | `#51-default---默认构造` | 同文件锚点不存在: #51-default---默认构造 |
| docs\rust-ownership-decidability\case-studies\generic-array-formal-analysis.md | 5.2 from\_slice() - 切片构造 | `#52-from_slice---切片构造` | 同文件锚点不存在: #52-from_slice---切片构造 |
| docs\rust-ownership-decidability\case-studies\generic-array-formal-analysis.md | 5.3 clone\_from\_slice() - 克隆构造 | `#53-clone_from_slice---克隆构造` | 同文件锚点不存在: #53-clone_from_slice---克隆构造 |
| docs\rust-ownership-decidability\case-studies\generic-array-formal-analysis.md | *适用 Rust 版本: 1.31+ (const fn), 推荐 1.51+* | `#适用-rust-版本-131-const-fn-推荐-151` | 同文件锚点不存在: #适用-rust-版本-131-const-fn-推荐-151 |
| docs\rust-ownership-decidability\case-studies\heapless-formal-analysis.md | *最后更新: 2026-03-05* | `#最后更新-2026-03-05` | 同文件锚点不存在: #最后更新-2026-03-05 |
| docs\rust-ownership-decidability\case-studies\heim-formal-analysis.md | *定理数量: 6个* | `#定理数量-6个` | 同文件锚点不存在: #定理数量-6个 |
| docs\rust-ownership-decidability\case-studies\hyper-formal-analysis.md | *最后更新: 2026-03-04* | `#最后更新-2026-03-04` | 同文件锚点不存在: #最后更新-2026-03-04 |
| docs\rust-ownership-decidability\case-studies\image-formal-analysis.md | *定理数量: 6个* | `#定理数量-6个` | 同文件锚点不存在: #定理数量-6个 |
| docs\rust-ownership-decidability\case-studies\indexmap-formal-analysis.md | *定理数量: 6个* | `#定理数量-6个` | 同文件锚点不存在: #定理数量-6个 |
| docs\rust-ownership-decidability\case-studies\industrial-verification-aws-meta.md | **维护者**: Rust 所有权可判定性研究项目 | `#维护者-rust-所有权可判定性研究项目` | 同文件锚点不存在: #维护者-rust-所有权可判定性研究项目 |
| docs\rust-ownership-decidability\case-studies\insta-snapshot-formal-analysis.md | *定理数量: 5个* | `#定理数量-5个` | 同文件锚点不存在: #定理数量-5个 |
| docs\rust-ownership-decidability\case-studies\jsonwebtoken-formal-analysis.md | *定理数量: 6个* | `#定理数量-6个` | 同文件锚点不存在: #定理数量-6个 |
| docs\rust-ownership-decidability\case-studies\littlefs2-formal-analysis.md | **代码示例**: 7个完整示例 | `#代码示例-7个完整示例` | 同文件锚点不存在: #代码示例-7个完整示例 |
| docs\rust-ownership-decidability\case-studies\loom-formal-analysis.md | *定理数量: 4个* | `#定理数量-4个` | 同文件锚点不存在: #定理数量-4个 |
| docs\rust-ownership-decidability\case-studies\lru-cached-formal-analysis.md | *定理数量: 4个* | `#定理数量-4个` | 同文件锚点不存在: #定理数量-4个 |
| docs\rust-ownership-decidability\case-studies\MODERN_CRATES_EXPANSION_REPORT.md | **下次迭代**: 高优先级库分析 | `#下次迭代-高优先级库分析` | 同文件锚点不存在: #下次迭代-高优先级库分析 |
| docs\rust-ownership-decidability\case-studies\MODERN_CRATES_FINAL_REPORT.md | 现代Rust库形式化分析 - 最终完成报告 | `#现代rust库形式化分析---最终完成报告` | 同文件锚点不存在: #现代rust库形式化分析---最终完成报告 |
| docs\rust-ownership-decidability\case-studies\MODERN_CRATES_FINAL_REPORT.md | **里程碑**: 39个著名现代Rust库形式化分析完成 | `#里程碑-39个著名现代rust库形式化分析完成` | 同文件锚点不存在: #里程碑-39个著名现代rust库形式化分析完成 |
| docs\rust-ownership-decidability\case-studies\MODERN_CRATES_INDEX.md | 嵌入式库 (15个) ✅ 100% | `#嵌入式库-15个--100` | 同文件锚点不存在: #嵌入式库-15个--100 |
| docs\rust-ownership-decidability\case-studies\MODERN_CRATES_INDEX.md | 应用级库 (24个) ✅ 100% 核心覆盖 | `#应用级库-24个--100-核心覆盖` | 同文件锚点不存在: #应用级库-24个--100-核心覆盖 |
| docs\rust-ownership-decidability\case-studies\MODERN_CRATES_INDEX.md | **状态**: ✅ 100% 核心库覆盖完成 | `#状态--100-核心库覆盖完成` | 同文件锚点不存在: #状态--100-核心库覆盖完成 |
| docs\rust-ownership-decidability\case-studies\MODERN_CRATES_ROUND2_REPORT.md | **下次迭代**: 中优先级库分析 | `#下次迭代-中优先级库分析` | 同文件锚点不存在: #下次迭代-中优先级库分析 |
| docs\rust-ownership-decidability\case-studies\moka-formal-analysis.md | *定理数量: 4个* | `#定理数量-4个` | 同文件锚点不存在: #定理数量-4个 |
| docs\rust-ownership-decidability\case-studies\ndarray-formal-analysis.md | *定理数量: 7个* | `#定理数量-7个` | 同文件锚点不存在: #定理数量-7个 |
| docs\rust-ownership-decidability\case-studies\nom-formal-analysis.md | *定理数量: 8个* | `#定理数量-8个` | 同文件锚点不存在: #定理数量-8个 |
| docs\rust-ownership-decidability\case-studies\notify-formal-analysis.md | *定理数量: 4个* | `#定理数量-4个` | 同文件锚点不存在: #定理数量-4个 |
| docs\rust-ownership-decidability\case-studies\nrf-hal-formal-analysis.md | 定义 PERIPH-1 ( 外设分区 ) | `#定义-periph-1--外设分区-` | 同文件锚点不存在: #定义-periph-1--外设分区- |
| docs\rust-ownership-decidability\case-studies\nrf-hal-formal-analysis.md | 定理 OWN-T1 ( 外设唯一性 ) | `#定理-own-t1--外设唯一性-` | 同文件锚点不存在: #定理-own-t1--外设唯一性- |
| docs\rust-ownership-decidability\case-studies\nrf-hal-formal-analysis.md | 定义 POWER-1 ( 功耗模式 ) | `#定义-power-1--功耗模式-` | 同文件锚点不存在: #定义-power-1--功耗模式- |
| docs\rust-ownership-decidability\case-studies\nrf-hal-formal-analysis.md | 定义 POWER-2 ( 模式转换 ) | `#定义-power-2--模式转换-` | 同文件锚点不存在: #定义-power-2--模式转换- |
| docs\rust-ownership-decidability\case-studies\nrf-hal-formal-analysis.md | 定义 PPI-1 ( 通道模型 ) | `#定义-ppi-1--通道模型-` | 同文件锚点不存在: #定义-ppi-1--通道模型- |
| docs\rust-ownership-decidability\case-studies\nrf-hal-formal-analysis.md | 定义 PPI-2 ( 通道组 ) | `#定义-ppi-2--通道组-` | 同文件锚点不存在: #定义-ppi-2--通道组- |
| docs\rust-ownership-decidability\case-studies\nrf-hal-formal-analysis.md | 定理 PPI-T1 ( 零延迟 ) | `#定理-ppi-t1--零延迟-` | 同文件锚点不存在: #定理-ppi-t1--零延迟- |
| docs\rust-ownership-decidability\case-studies\nrf-hal-formal-analysis.md | 定义 DMA-1 ( 缓冲区安全 ) | `#定义-dma-1--缓冲区安全-` | 同文件锚点不存在: #定义-dma-1--缓冲区安全- |
| docs\rust-ownership-decidability\case-studies\nrf-hal-formal-analysis.md | 定理 DMA-T1 ( 安全传输 ) | `#定理-dma-t1--安全传输-` | 同文件锚点不存在: #定理-dma-t1--安全传输- |
| docs\rust-ownership-decidability\case-studies\nrf-hal-formal-analysis.md | 定理 SAFE-T1 ( 配置安全 ) | `#定理-safe-t1--配置安全-` | 同文件锚点不存在: #定理-safe-t1--配置安全- |
| docs\rust-ownership-decidability\case-studies\nrf-hal-formal-analysis.md | **状态**: ✅ 已对齐 | `#状态--已对齐` | 同文件锚点不存在: #状态--已对齐 |
| docs\rust-ownership-decidability\case-studies\once_cell-formal-analysis.md | OnceCell / OnceLock 形式化分析 | `#oncecell--oncelock-形式化分析` | 同文件锚点不存在: #oncecell--oncelock-形式化分析 |
| docs\rust-ownership-decidability\case-studies\once_cell-formal-analysis.md | 定理 3.2 ( panic安全) | `#定理-32--panic安全` | 同文件锚点不存在: #定理-32--panic安全 |
| docs\rust-ownership-decidability\case-studies\once_cell-formal-analysis.md | *定理数量: 6个* | `#定理数量-6个` | 同文件锚点不存在: #定理数量-6个 |
| docs\rust-ownership-decidability\case-studies\opentelemetry-formal-analysis.md | *定理数量: 7个* | `#定理数量-7个` | 同文件锚点不存在: #定理数量-7个 |
| docs\rust-ownership-decidability\case-studies\ouroboros-formal-analysis.md | *最后更新: 2026-03-10* | `#最后更新-2026-03-10` | 同文件锚点不存在: #最后更新-2026-03-10 |
| docs\rust-ownership-decidability\case-studies\panic-probe-formal-analysis.md | **代码示例**: 6个完整示例 | `#代码示例-6个完整示例` | 同文件锚点不存在: #代码示例-6个完整示例 |
| docs\rust-ownership-decidability\case-studies\parking_lot-formal-analysis.md | *最后更新: 2026-03-04* | `#最后更新-2026-03-04` | 同文件锚点不存在: #最后更新-2026-03-04 |
| docs\rust-ownership-decidability\case-studies\pin-project-formal-analysis.md | 定义 PIN-1 ( Pin保证 ) | `#定义-pin-1--pin保证-` | 同文件锚点不存在: #定义-pin-1--pin保证- |
| docs\rust-ownership-decidability\case-studies\pin-project-formal-analysis.md | 定义 PIN-2 ( Unpin trait ) | `#定义-pin-2--unpin-trait-` | 同文件锚点不存在: #定义-pin-2--unpin-trait- |
| docs\rust-ownership-decidability\case-studies\pin-project-formal-analysis.md | 定理 PIN-T1 ( Pin传播 ) | `#定理-pin-t1--pin传播-` | 同文件锚点不存在: #定理-pin-t1--pin传播- |
| docs\rust-ownership-decidability\case-studies\pin-project-formal-analysis.md | 定义 SELFREF-1 ( 自引用定义 ) | `#定义-selfref-1--自引用定义-` | 同文件锚点不存在: #定义-selfref-1--自引用定义- |
| docs\rust-ownership-decidability\case-studies\pin-project-formal-analysis.md | 定义 SELFREF-2 ( 不安全移动 ) | `#定义-selfref-2--不安全移动-` | 同文件锚点不存在: #定义-selfref-2--不安全移动- |
| docs\rust-ownership-decidability\case-studies\pin-project-formal-analysis.md | 定义 PROJECTION-1 ( 安全投影 ) | `#定义-projection-1--安全投影-` | 同文件锚点不存在: #定义-projection-1--安全投影- |
| docs\rust-ownership-decidability\case-studies\pin-project-formal-analysis.md | 定义 PROJECTION-2 ( 投影类型 ) | `#定义-projection-2--投影类型-` | 同文件锚点不存在: #定义-projection-2--投影类型- |
| docs\rust-ownership-decidability\case-studies\pin-project-formal-analysis.md | 定理 PROJECTION-T1 ( 安全保证 ) | `#定理-projection-t1--安全保证-` | 同文件锚点不存在: #定理-projection-t1--安全保证- |
| docs\rust-ownership-decidability\case-studies\pin-project-formal-analysis.md | 定义 MACRO-1 ( pin\_project! ) | `#定义-macro-1--pin_project-` | 同文件锚点不存在: #定义-macro-1--pin_project- |
| docs\rust-ownership-decidability\case-studies\pin-project-formal-analysis.md | 定义 DROP-1 ( PinnedDrop ) | `#定义-drop-1--pinneddrop-` | 同文件锚点不存在: #定义-drop-1--pinneddrop- |
| docs\rust-ownership-decidability\case-studies\pin-project-formal-analysis.md | 定理 DROP-T1 ( Drop安全 ) | `#定理-drop-t1--drop安全-` | 同文件锚点不存在: #定理-drop-t1--drop安全- |
| docs\rust-ownership-decidability\case-studies\pin-project-formal-analysis.md | 定理 PINPROJECT-T1 ( 内存安全 ) | `#定理-pinproject-t1--内存安全-` | 同文件锚点不存在: #定理-pinproject-t1--内存安全- |
| docs\rust-ownership-decidability\case-studies\pin-project-formal-analysis.md | 定理 PINPROJECT-T2 ( 投影正确性 ) | `#定理-pinproject-t2--投影正确性-` | 同文件锚点不存在: #定理-pinproject-t2--投影正确性- |
| docs\rust-ownership-decidability\case-studies\pin-project-formal-analysis.md | **状态**: ✅ 已对齐 | `#状态--已对齐` | 同文件锚点不存在: #状态--已对齐 |
| docs\rust-ownership-decidability\case-studies\postcard-formal-analysis.md | *最后更新: 2026-03-10* | `#最后更新-2026-03-10` | 同文件锚点不存在: #最后更新-2026-03-10 |
| docs\rust-ownership-decidability\case-studies\prometheus-formal-analysis.md | *定理数量: 6个* | `#定理数量-6个` | 同文件锚点不存在: #定理数量-6个 |
| docs\rust-ownership-decidability\case-studies\proptest-quickcheck-formal-analysis.md | *定理数量: 5个* | `#定理数量-5个` | 同文件锚点不存在: #定理数量-5个 |
| docs\rust-ownership-decidability\case-studies\pulldown-cmark-formal-analysis.md | *定理数量: 4个* | `#定理数量-4个` | 同文件锚点不存在: #定理数量-4个 |
| docs\rust-ownership-decidability\case-studies\pyo3-formal-analysis.md | 定义 GIL-1 ( GIL抽象 ) | `#定义-gil-1--gil抽象-` | 同文件锚点不存在: #定义-gil-1--gil抽象- |
| docs\rust-ownership-decidability\case-studies\pyo3-formal-analysis.md | 定义 GIL-2 ( 自动释放 ) | `#定义-gil-2--自动释放-` | 同文件锚点不存在: #定义-gil-2--自动释放- |
| docs\rust-ownership-decidability\case-studies\pyo3-formal-analysis.md | 定理 GIL-T1 ( 安全释放 ) | `#定理-gil-t1--安全释放-` | 同文件锚点不存在: #定理-gil-t1--安全释放- |
| docs\rust-ownership-decidability\case-studies\pyo3-formal-analysis.md | 定义 CONV-1 ( 基本类型 ) | `#定义-conv-1--基本类型-` | 同文件锚点不存在: #定义-conv-1--基本类型- |
| docs\rust-ownership-decidability\case-studies\pyo3-formal-analysis.md | 定义 CONV-2 ( PyObject ) | `#定义-conv-2--pyobject-` | 同文件锚点不存在: #定义-conv-2--pyobject- |
| docs\rust-ownership-decidability\case-studies\pyo3-formal-analysis.md | 定义 MODULE-1 ( 模块定义 ) | `#定义-module-1--模块定义-` | 同文件锚点不存在: #定义-module-1--模块定义- |
| docs\rust-ownership-decidability\case-studies\pyo3-formal-analysis.md | 定义 MODULE-2 ( 函数导出 ) | `#定义-module-2--函数导出-` | 同文件锚点不存在: #定义-module-2--函数导出- |
| docs\rust-ownership-decidability\case-studies\pyo3-formal-analysis.md | 定义 PYOBJ-1 ( 类定义 ) | `#定义-pyobj-1--类定义-` | 同文件锚点不存在: #定义-pyobj-1--类定义- |
| docs\rust-ownership-decidability\case-studies\pyo3-formal-analysis.md | 定理 PYOBJ-T1 ( 内存安全 ) | `#定理-pyobj-t1--内存安全-` | 同文件锚点不存在: #定理-pyobj-t1--内存安全- |
| docs\rust-ownership-decidability\case-studies\pyo3-formal-analysis.md | 定义 EXCEPT-1 ( Rust结果传播 ) | `#定义-except-1--rust结果传播-` | 同文件锚点不存在: #定义-except-1--rust结果传播- |
| docs\rust-ownership-decidability\case-studies\pyo3-formal-analysis.md | 定义 EXCEPT-2 ( Python异常转换 ) | `#定义-except-2--python异常转换-` | 同文件锚点不存在: #定义-except-2--python异常转换- |
| docs\rust-ownership-decidability\case-studies\pyo3-formal-analysis.md | 定理 PYO3-T1 ( GIL安全 ) | `#定理-pyo3-t1--gil安全-` | 同文件锚点不存在: #定理-pyo3-t1--gil安全- |
| docs\rust-ownership-decidability\case-studies\pyo3-formal-analysis.md | 定理 PYO3-T2 ( 类型转换安全 ) | `#定理-pyo3-t2--类型转换安全-` | 同文件锚点不存在: #定理-pyo3-t2--类型转换安全- |
| docs\rust-ownership-decidability\case-studies\pyo3-formal-analysis.md | **状态**: ✅ 已对齐 | `#状态--已对齐` | 同文件锚点不存在: #状态--已对齐 |
| docs\rust-ownership-decidability\case-studies\quinn-formal-analysis.md | *定理数量: 7个* | `#定理数量-7个` | 同文件锚点不存在: #定理数量-7个 |
| docs\rust-ownership-decidability\case-studies\rand-formal-analysis.md | *最后更新: 2026-03-04* | `#最后更新-2026-03-04` | 同文件锚点不存在: #最后更新-2026-03-04 |
| docs\rust-ownership-decidability\case-studies\rayon-formal-analysis.md | 定义 PAR-ITER-1 ( ParallelIterator ) | `#定义-par-iter-1--paralleliterator-` | 同文件锚点不存在: #定义-par-iter-1--paralleliterator- |
| docs\rust-ownership-decidability\case-studies\rayon-formal-analysis.md | 定义 PAR-ITER-2 ( 分块策略 ) | `#定义-par-iter-2--分块策略-` | 同文件锚点不存在: #定义-par-iter-2--分块策略- |
| docs\rust-ownership-decidability\case-studies\rayon-formal-analysis.md | 定理 PAR-ITER-T1 ( 顺序等价 ) | `#定理-par-iter-t1--顺序等价-` | 同文件锚点不存在: #定理-par-iter-t1--顺序等价- |
| docs\rust-ownership-decidability\case-studies\rayon-formal-analysis.md | 定义 JOIN-1 ( 并行递归 ) | `#定义-join-1--并行递归-` | 同文件锚点不存在: #定义-join-1--并行递归- |
| docs\rust-ownership-decidability\case-studies\rayon-formal-analysis.md | 定义 JOIN-2 ( 停止条件 ) | `#定义-join-2--停止条件-` | 同文件锚点不存在: #定义-join-2--停止条件- |
| docs\rust-ownership-decidability\case-studies\rayon-formal-analysis.md | 定义 SCOPE-1 ( scope创建 ) | `#定义-scope-1--scope创建-` | 同文件锚点不存在: #定义-scope-1--scope创建- |
| docs\rust-ownership-decidability\case-studies\rayon-formal-analysis.md | 定理 SCOPE-T1 ( 借用安全 ) | `#定理-scope-t1--借用安全-` | 同文件锚点不存在: #定理-scope-t1--借用安全- |
| docs\rust-ownership-decidability\case-studies\rayon-formal-analysis.md | 定义 DETERM-1 ( 确定性 ) | `#定义-determ-1--确定性-` | 同文件锚点不存在: #定义-determ-1--确定性- |
| docs\rust-ownership-decidability\case-studies\rayon-formal-analysis.md | 定理 DETERM-T1 ( 无竞态 ) | `#定理-determ-t1--无竞态-` | 同文件锚点不存在: #定理-determ-t1--无竞态- |
| docs\rust-ownership-decidability\case-studies\rayon-formal-analysis.md | 定理 RAYON-T1 ( 线程安全 ) | `#定理-rayon-t1--线程安全-` | 同文件锚点不存在: #定理-rayon-t1--线程安全- |
| docs\rust-ownership-decidability\case-studies\rayon-formal-analysis.md | 定理 RAYON-T2 ( 负载自适应 ) | `#定理-rayon-t2--负载自适应-` | 同文件锚点不存在: #定理-rayon-t2--负载自适应- |
| docs\rust-ownership-decidability\case-studies\rayon-formal-analysis.md | **状态**: ✅ 已对齐 | `#状态--已对齐` | 同文件锚点不存在: #状态--已对齐 |
| docs\rust-ownership-decidability\case-studies\rayon-parallelism.md | *最后更新: 2026-03-04* | `#最后更新-2026-03-04` | 同文件锚点不存在: #最后更新-2026-03-04 |
| docs\rust-ownership-decidability\case-studies\ref-cast-formal-analysis.md | *定理数量: 4个* | `#定理数量-4个` | 同文件锚点不存在: #定理数量-4个 |
| docs\rust-ownership-decidability\case-studies\regex-formal-analysis.md | *定理数量: 6个* | `#定理数量-6个` | 同文件锚点不存在: #定理数量-6个 |
| docs\rust-ownership-decidability\case-studies\reqwest-formal-analysis.md | *最后更新: 2026-03-04* | `#最后更新-2026-03-04` | 同文件锚点不存在: #最后更新-2026-03-04 |
| docs\rust-ownership-decidability\case-studies\rkyv-formal-analysis.md | *最后更新: 2026-03-10* | `#最后更新-2026-03-10` | 同文件锚点不存在: #最后更新-2026-03-10 |
| docs\rust-ownership-decidability\case-studies\rtic-formal-analysis.md | 定义 RTIC-R1 ( 共享资源 ) | `#定义-rtic-r1--共享资源-` | 同文件锚点不存在: #定义-rtic-r1--共享资源- |
| docs\rust-ownership-decidability\case-studies\rtic-formal-analysis.md | 定义 RTIC-R2 ( 资源锁 ) | `#定义-rtic-r2--资源锁-` | 同文件锚点不存在: #定义-rtic-r2--资源锁- |
| docs\rust-ownership-decidability\case-studies\rtic-formal-analysis.md | 定义 RTIC-T1 ( 任务类型 ) | `#定义-rtic-t1--任务类型-` | 同文件锚点不存在: #定义-rtic-t1--任务类型- |
| docs\rust-ownership-decidability\case-studies\rtic-formal-analysis.md | 定义 RTIC-T2 ( 任务优先级 ) | `#定义-rtic-t2--任务优先级-` | 同文件锚点不存在: #定义-rtic-t2--任务优先级- |
| docs\rust-ownership-decidability\case-studies\rtic-formal-analysis.md | 定理 SCHED-T1 ( 优先级调度 ) | `#定理-sched-t1--优先级调度-` | 同文件锚点不存在: #定理-sched-t1--优先级调度- |
| docs\rust-ownership-decidability\case-studies\rtic-formal-analysis.md | 定义 PCP-1 ( 资源天花板 ) | `#定义-pcp-1--资源天花板-` | 同文件锚点不存在: #定义-pcp-1--资源天花板- |
| docs\rust-ownership-decidability\case-studies\rtic-formal-analysis.md | 定义 PCP-2 ( 优先级继承 ) | `#定义-pcp-2--优先级继承-` | 同文件锚点不存在: #定义-pcp-2--优先级继承- |
| docs\rust-ownership-decidability\case-studies\rtic-formal-analysis.md | 定理 PCP-T1 ( 无死锁 ) | `#定理-pcp-t1--无死锁-` | 同文件锚点不存在: #定理-pcp-t1--无死锁- |
| docs\rust-ownership-decidability\case-studies\rtic-formal-analysis.md | 定理 PCP-T2 ( 无优先级反转 ) | `#定理-pcp-t2--无优先级反转-` | 同文件锚点不存在: #定理-pcp-t2--无优先级反转- |
| docs\rust-ownership-decidability\case-studies\rtic-formal-analysis.md | 定理 RTIC-T1 ( 零成本抽象 ) | `#定理-rtic-t1--零成本抽象-` | 同文件锚点不存在: #定理-rtic-t1--零成本抽象- |
| docs\rust-ownership-decidability\case-studies\rtic-formal-analysis.md | 定理 RTIC-T2 ( 数据竞争自由 ) | `#定理-rtic-t2--数据竞争自由-` | 同文件锚点不存在: #定理-rtic-t2--数据竞争自由- |
| docs\rust-ownership-decidability\case-studies\rtic-formal-analysis.md | 定理 RTIC-T3 ( 内存安全 ) | `#定理-rtic-t3--内存安全-` | 同文件锚点不存在: #定理-rtic-t3--内存安全- |
| docs\rust-ownership-decidability\case-studies\rtic-formal-analysis.md | **状态**: ✅ 已对齐 | `#状态--已对齐` | 同文件锚点不存在: #状态--已对齐 |
| docs\rust-ownership-decidability\case-studies\rustls-formal-analysis.md | *定理数量: 7个* | `#定理数量-7个` | 同文件锚点不存在: #定理数量-7个 |
| docs\rust-ownership-decidability\case-studies\serde-formal-analysis-deep.md | Counter-Example 5: Flatten + deny\_unknown\_fields | `#counter-example-5-flatten--deny_unknown_fields` | 同文件锚点不存在: #counter-example-5-flatten--deny_unknown_fields |
| docs\rust-ownership-decidability\case-studies\serde-formal-analysis-deep.md | *Counter-Examples: 15+* | `#counter-examples-15` | 同文件锚点不存在: #counter-examples-15 |
| docs\rust-ownership-decidability\case-studies\serde-formal-analysis.md | *最后更新: 2026-03-04* | `#最后更新-2026-03-04` | 同文件锚点不存在: #最后更新-2026-03-04 |
| docs\rust-ownership-decidability\case-studies\serde-json-formal-analysis.md | *定理数量: 7个* | `#定理数量-7个` | 同文件锚点不存在: #定理数量-7个 |
| docs\rust-ownership-decidability\case-studies\shuttle-formal-analysis.md | *定理数量: 4个* | `#定理数量-4个` | 同文件锚点不存在: #定理数量-4个 |
| docs\rust-ownership-decidability\case-studies\slog-formal-analysis.md | *定理数量: 6个* | `#定理数量-6个` | 同文件锚点不存在: #定理数量-6个 |
| docs\rust-ownership-decidability\case-studies\smoltcp-formal-analysis.md | 定义 TCP-STACK-1 ( 协议栈组成 ) | `#定义-tcp-stack-1--协议栈组成-` | 同文件锚点不存在: #定义-tcp-stack-1--协议栈组成- |
| docs\rust-ownership-decidability\case-studies\smoltcp-formal-analysis.md | 定义 TCP-STACK-2 ( 接口状态 ) | `#定义-tcp-stack-2--接口状态-` | 同文件锚点不存在: #定义-tcp-stack-2--接口状态- |
| docs\rust-ownership-decidability\case-studies\smoltcp-formal-analysis.md | 定义 SOCKET-1 ( TCP状态机 ) | `#定义-socket-1--tcp状态机-` | 同文件锚点不存在: #定义-socket-1--tcp状态机- |
| docs\rust-ownership-decidability\case-studies\smoltcp-formal-analysis.md | 定义 SOCKET-2 ( 状态转换 ) | `#定义-socket-2--状态转换-` | 同文件锚点不存在: #定义-socket-2--状态转换- |
| docs\rust-ownership-decidability\case-studies\smoltcp-formal-analysis.md | 定理 SOCKET-T1 ( TCP状态机正确性 ) | `#定理-socket-t1--tcp状态机正确性-` | 同文件锚点不存在: #定理-socket-t1--tcp状态机正确性- |
| docs\rust-ownership-decidability\case-studies\smoltcp-formal-analysis.md | 定义 ZERO-COPY-1 ( 数据包借用 ) | `#定义-zero-copy-1--数据包借用-` | 同文件锚点不存在: #定义-zero-copy-1--数据包借用- |
| docs\rust-ownership-decidability\case-studies\smoltcp-formal-analysis.md | 定义 ZERO-COPY-2 ( 发送队列 ) | `#定义-zero-copy-2--发送队列-` | 同文件锚点不存在: #定义-zero-copy-2--发送队列- |
| docs\rust-ownership-decidability\case-studies\smoltcp-formal-analysis.md | 定理 ZERO-COPY-T1 ( 无分配保证 ) | `#定理-zero-copy-t1--无分配保证-` | 同文件锚点不存在: #定理-zero-copy-t1--无分配保证- |
| docs\rust-ownership-decidability\case-studies\smoltcp-formal-analysis.md | 定义 POOL-1 ( 包缓冲区池 ) | `#定义-pool-1--包缓冲区池-` | 同文件锚点不存在: #定义-pool-1--包缓冲区池- |
| docs\rust-ownership-decidability\case-studies\smoltcp-formal-analysis.md | 定义 POOL-2 ( 分配策略 ) | `#定义-pool-2--分配策略-` | 同文件锚点不存在: #定义-pool-2--分配策略- |
| docs\rust-ownership-decidability\case-studies\smoltcp-formal-analysis.md | 定理 POOL-T1 ( 无碎片 ) | `#定理-pool-t1--无碎片-` | 同文件锚点不存在: #定理-pool-t1--无碎片- |
| docs\rust-ownership-decidability\case-studies\smoltcp-formal-analysis.md | 定理 TCP-T1 ( 无死锁 ) | `#定理-tcp-t1--无死锁-` | 同文件锚点不存在: #定理-tcp-t1--无死锁- |
| docs\rust-ownership-decidability\case-studies\smoltcp-formal-analysis.md | 定理 TCP-T2 ( 内存安全 ) | `#定理-tcp-t2--内存安全-` | 同文件锚点不存在: #定理-tcp-t2--内存安全- |
| docs\rust-ownership-decidability\case-studies\smoltcp-formal-analysis.md | **状态**: ✅ 已对齐 | `#状态--已对齐` | 同文件锚点不存在: #状态--已对齐 |
| docs\rust-ownership-decidability\case-studies\sqlx-formal-analysis.md | *最后更新: 2026-03-04* | `#最后更新-2026-03-04` | 同文件锚点不存在: #最后更新-2026-03-04 |
| docs\rust-ownership-decidability\case-studies\static-assertions-formal-analysis.md | *定理数量: 4个* | `#定理数量-4个` | 同文件锚点不存在: #定理数量-4个 |
| docs\rust-ownership-decidability\case-studies\std-future-stream-formal-analysis.md | *最后更新: 2026-03-04* | `#最后更新-2026-03-04` | 同文件锚点不存在: #最后更新-2026-03-04 |
| docs\rust-ownership-decidability\case-studies\std-hashmap-formal-analysis.md | 算法 4.3 ( tombstone 删除) | `#算法-43--tombstone-删除` | 同文件锚点不存在: #算法-43--tombstone-删除 |
| docs\rust-ownership-decidability\case-studies\std-hashmap-formal-analysis.md | *最后更新: 2026-03-04* | `#最后更新-2026-03-04` | 同文件锚点不存在: #最后更新-2026-03-04 |
| docs\rust-ownership-decidability\case-studies\std-iterator-formal-analysis.md | *最后更新: 2026-03-04* | `#最后更新-2026-03-04` | 同文件锚点不存在: #最后更新-2026-03-04 |
| docs\rust-ownership-decidability\case-studies\std-option-result-formal-analysis.md | Rust标准库 Option \& Result 形式化分析 | `#rust标准库-option--result-形式化分析` | 同文件锚点不存在: #rust标准库-option--result-形式化分析 |
| docs\rust-ownership-decidability\case-studies\std-pin-unpin-formal-analysis.md | Rust标准库 Pin \& Unpin 形式化分析 | `#rust标准库-pin--unpin-形式化分析` | 同文件锚点不存在: #rust标准库-pin--unpin-形式化分析 |
| docs\rust-ownership-decidability\case-studies\std-pin-unpin-formal-analysis.md | *最后更新: 2026-03-04* | `#最后更新-2026-03-04` | 同文件锚点不存在: #最后更新-2026-03-04 |
| docs\rust-ownership-decidability\case-studies\std-smart-pointers-formal-analysis.md | *最后更新: 2026-03-04* | `#最后更新-2026-03-04` | 同文件锚点不存在: #最后更新-2026-03-04 |
| docs\rust-ownership-decidability\case-studies\std-string-formal-analysis.md | 定义 5.2 (Cow - Clone on Write) | `#定义-52-cow---clone-on-write` | 同文件锚点不存在: #定义-52-cow---clone-on-write |
| docs\rust-ownership-decidability\case-studies\std-string-formal-analysis.md | *最后更新: 2026-03-04* | `#最后更新-2026-03-04` | 同文件锚点不存在: #最后更新-2026-03-04 |
| docs\rust-ownership-decidability\case-studies\std-sync-primitives-formal-analysis.md | *最后更新: 2026-03-04* | `#最后更新-2026-03-04` | 同文件锚点不存在: #最后更新-2026-03-04 |
| docs\rust-ownership-decidability\case-studies\std-trait-semantics-formal-analysis.md | *最后更新: 2026-03-04* | `#最后更新-2026-03-04` | 同文件锚点不存在: #最后更新-2026-03-04 |
| docs\rust-ownership-decidability\case-studies\std-vec-formal-analysis.md | *最后更新: 2026-03-04* | `#最后更新-2026-03-04` | 同文件锚点不存在: #最后更新-2026-03-04 |
| docs\rust-ownership-decidability\case-studies\stm32f4xx-hal-formal-analysis.md | 定义 CLOCK-1 ( 时钟源 ) | `#定义-clock-1--时钟源-` | 同文件锚点不存在: #定义-clock-1--时钟源- |
| docs\rust-ownership-decidability\case-studies\stm32f4xx-hal-formal-analysis.md | 定义 CLOCK-2 ( 时钟树 ) | `#定义-clock-2--时钟树-` | 同文件锚点不存在: #定义-clock-2--时钟树- |
| docs\rust-ownership-decidability\case-studies\stm32f4xx-hal-formal-analysis.md | 定理 CLOCK-T1 ( 时钟安全 ) | `#定理-clock-t1--时钟安全-` | 同文件锚点不存在: #定理-clock-t1--时钟安全- |
| docs\rust-ownership-decidability\case-studies\stm32f4xx-hal-formal-analysis.md | 定义 DMA-1 ( 流与通道 ) | `#定义-dma-1--流与通道-` | 同文件锚点不存在: #定义-dma-1--流与通道- |
| docs\rust-ownership-decidability\case-studies\stm32f4xx-hal-formal-analysis.md | 定义 DMA-2 ( 双缓冲 ) | `#定义-dma-2--双缓冲-` | 同文件锚点不存在: #定义-dma-2--双缓冲- |
| docs\rust-ownership-decidability\case-studies\stm32f4xx-hal-formal-analysis.md | 定理 DMA-T1 ( 无冲突 ) | `#定理-dma-t1--无冲突-` | 同文件锚点不存在: #定理-dma-t1--无冲突- |
| docs\rust-ownership-decidability\case-studies\stm32f4xx-hal-formal-analysis.md | 定义 IRQ-1 ( 优先级分组 ) | `#定义-irq-1--优先级分组-` | 同文件锚点不存在: #定义-irq-1--优先级分组- |
| docs\rust-ownership-decidability\case-studies\stm32f4xx-hal-formal-analysis.md | 定义 IRQ-2 ( 嵌套规则 ) | `#定义-irq-2--嵌套规则-` | 同文件锚点不存在: #定义-irq-2--嵌套规则- |
| docs\rust-ownership-decidability\case-studies\stm32f4xx-hal-formal-analysis.md | 定理 SAFE-T1 ( 引脚复用 ) | `#定理-safe-t1--引脚复用-` | 同文件锚点不存在: #定理-safe-t1--引脚复用- |
| docs\rust-ownership-decidability\case-studies\stm32f4xx-hal-formal-analysis.md | **状态**: ✅ 已对齐 | `#状态--已对齐` | 同文件锚点不存在: #状态--已对齐 |
| docs\rust-ownership-decidability\case-studies\tantivy-formal-analysis.md | *定理数量: 6个* | `#定理数量-6个` | 同文件锚点不存在: #定理数量-6个 |
| docs\rust-ownership-decidability\case-studies\tarpc-formal-analysis.md | *定理数量: 7个* | `#定理数量-7个` | 同文件锚点不存在: #定理数量-7个 |
| docs\rust-ownership-decidability\case-studies\tera-askama-formal-analysis.md | *定理数量: 5个* | `#定理数量-5个` | 同文件锚点不存在: #定理数量-5个 |
| docs\rust-ownership-decidability\case-studies\thiserror-anyhow-formal-analysis.md | 定义 ERROR-1 ( 派生宏 ) | `#定义-error-1--派生宏-` | 同文件锚点不存在: #定义-error-1--派生宏- |
| docs\rust-ownership-decidability\case-studies\thiserror-anyhow-formal-analysis.md | 定义 ERROR-2 ( 自动实现 ) | `#定义-error-2--自动实现-` | 同文件锚点不存在: #定义-error-2--自动实现- |
| docs\rust-ownership-decidability\case-studies\thiserror-anyhow-formal-analysis.md | 定理 ERROR-T1 ( 类型安全 ) | `#定理-error-t1--类型安全-` | 同文件锚点不存在: #定理-error-t1--类型安全- |
| docs\rust-ownership-decidability\case-studies\thiserror-anyhow-formal-analysis.md | 定义 ANYHOW-1 ( Result别名 ) | `#定义-anyhow-1--result别名-` | 同文件锚点不存在: #定义-anyhow-1--result别名- |
| docs\rust-ownership-decidability\case-studies\thiserror-anyhow-formal-analysis.md | 定义 ANYHOW-2 ( 上下文 ) | `#定义-anyhow-2--上下文-` | 同文件锚点不存在: #定义-anyhow-2--上下文- |
| docs\rust-ownership-decidability\case-studies\thiserror-anyhow-formal-analysis.md | 定理 ANYHOW-T1 ( 自动转换 ) | `#定理-anyhow-t1--自动转换-` | 同文件锚点不存在: #定理-anyhow-t1--自动转换- |
| docs\rust-ownership-decidability\case-studies\thiserror-anyhow-formal-analysis.md | 定义 COMBINE-1 ( 边界设计 ) | `#定义-combine-1--边界设计-` | 同文件锚点不存在: #定义-combine-1--边界设计- |
| docs\rust-ownership-decidability\case-studies\thiserror-anyhow-formal-analysis.md | 定理 COMBINE-T1 ( 无缝转换 ) | `#定理-combine-t1--无缝转换-` | 同文件锚点不存在: #定理-combine-t1--无缝转换- |
| docs\rust-ownership-decidability\case-studies\thiserror-anyhow-formal-analysis.md | 定理 ERR-T1 ( 零运行时开销 ) | `#定理-err-t1--零运行时开销-` | 同文件锚点不存在: #定理-err-t1--零运行时开销- |
| docs\rust-ownership-decidability\case-studies\thiserror-anyhow-formal-analysis.md | 定理 ERR-T2 ( 上下文保留 ) | `#定理-err-t2--上下文保留-` | 同文件锚点不存在: #定理-err-t2--上下文保留- |
| docs\rust-ownership-decidability\case-studies\tokio-graceful-shutdown-formal-analysis.md | *定理数量: 4个* | `#定理数量-4个` | 同文件锚点不存在: #定理数量-4个 |
| docs\rust-ownership-decidability\case-studies\tokio-process-formal-analysis.md | *定理数量: 6个* | `#定理数量-6个` | 同文件锚点不存在: #定理数量-6个 |
| docs\rust-ownership-decidability\case-studies\tokio-runtime-analysis.md | *最后更新: 2026-03-04* | `#最后更新-2026-03-04` | 同文件锚点不存在: #最后更新-2026-03-04 |
| docs\rust-ownership-decidability\case-studies\tokio-runtime-deep.md | 4.2.1 Arc\<Mutex\> Pattern | `#421-arcmutex-pattern` | 同文件锚点不存在: #421-arcmutex-pattern |
| docs\rust-ownership-decidability\case-studies\tokio-runtime-deep.md | *Last Updated: 2026-03-06* | `#last-updated-2026-03-06` | 同文件锚点不存在: #last-updated-2026-03-06 |
| docs\rust-ownership-decidability\case-studies\tokio-runtime-formal-analysis.md | 定义 RUNTIME-1 ( 运行时配置 ) | `#定义-runtime-1--运行时配置-` | 同文件锚点不存在: #定义-runtime-1--运行时配置- |
| docs\rust-ownership-decidability\case-studies\tokio-runtime-formal-analysis.md | 定义 RUNTIME-2 ( 运行时类型 ) | `#定义-runtime-2--运行时类型-` | 同文件锚点不存在: #定义-runtime-2--运行时类型- |
| docs\rust-ownership-decidability\case-studies\tokio-runtime-formal-analysis.md | 定义 TASK-1 ( 任务创建 ) | `#定义-task-1--任务创建-` | 同文件锚点不存在: #定义-task-1--任务创建- |
| docs\rust-ownership-decidability\case-studies\tokio-runtime-formal-analysis.md | 定义 TASK-2 ( 工作窃取 ) | `#定义-task-2--工作窃取-` | 同文件锚点不存在: #定义-task-2--工作窃取- |
| docs\rust-ownership-decidability\case-studies\tokio-runtime-formal-analysis.md | 定理 TASK-T1 ( 负载均衡 ) | `#定理-task-t1--负载均衡-` | 同文件锚点不存在: #定理-task-t1--负载均衡- |
| docs\rust-ownership-decidability\case-studies\tokio-runtime-formal-analysis.md | 定义 IO-1 ( 异步IO操作 ) | `#定义-io-1--异步io操作-` | 同文件锚点不存在: #定义-io-1--异步io操作- |
| docs\rust-ownership-decidability\case-studies\tokio-runtime-formal-analysis.md | 定义 IO-2 ( Reactor模式 ) | `#定义-io-2--reactor模式-` | 同文件锚点不存在: #定义-io-2--reactor模式- |
| docs\rust-ownership-decidability\case-studies\tokio-runtime-formal-analysis.md | 定理 IO-T1 ( 无阻塞 ) | `#定理-io-t1--无阻塞-` | 同文件锚点不存在: #定理-io-t1--无阻塞- |
| docs\rust-ownership-decidability\case-studies\tokio-runtime-formal-analysis.md | 定义 TIME-1 ( 定时器 ) | `#定义-time-1--定时器-` | 同文件锚点不存在: #定义-time-1--定时器- |
| docs\rust-ownership-decidability\case-studies\tokio-runtime-formal-analysis.md | 定义 TIME-2 ( Interval ) | `#定义-time-2--interval-` | 同文件锚点不存在: #定义-time-2--interval- |
| docs\rust-ownership-decidability\case-studies\tokio-runtime-formal-analysis.md | 定理 TIME-T1 ( 精确性 ) | `#定理-time-t1--精确性-` | 同文件锚点不存在: #定理-time-t1--精确性- |
| docs\rust-ownership-decidability\case-studies\tokio-runtime-formal-analysis.md | 定义 SYNC-1 ( MPSC Channel ) | `#定义-sync-1--mpsc-channel-` | 同文件锚点不存在: #定义-sync-1--mpsc-channel- |
| docs\rust-ownership-decidability\case-studies\tokio-runtime-formal-analysis.md | 定义 SYNC-2 ( Mutex ) | `#定义-sync-2--mutex-` | 同文件锚点不存在: #定义-sync-2--mutex- |
| docs\rust-ownership-decidability\case-studies\tokio-runtime-formal-analysis.md | 定理 SYNC-T1 ( 异步安全 ) | `#定理-sync-t1--异步安全-` | 同文件锚点不存在: #定理-sync-t1--异步安全- |
| docs\rust-ownership-decidability\case-studies\tokio-runtime-formal-analysis.md | 定理 TOKIO-T1 ( Send约束传播 ) | `#定理-tokio-t1--send约束传播-` | 同文件锚点不存在: #定理-tokio-t1--send约束传播- |
| docs\rust-ownership-decidability\case-studies\tokio-runtime-formal-analysis.md | 定理 TOKIO-T2 ( 优雅关闭 ) | `#定理-tokio-t2--优雅关闭-` | 同文件锚点不存在: #定理-tokio-t2--优雅关闭- |
| docs\rust-ownership-decidability\case-studies\tokio-runtime-formal-analysis.md | **状态**: ✅ 已对齐 | `#状态--已对齐` | 同文件锚点不存在: #状态--已对齐 |
| docs\rust-ownership-decidability\case-studies\tokio-stream-formal-analysis.md | 定义 STREAM-1 ( 核心trait ) | `#定义-stream-1--核心trait-` | 同文件锚点不存在: #定义-stream-1--核心trait- |
| docs\rust-ownership-decidability\case-studies\tokio-stream-formal-analysis.md | 定义 STREAM-2 ( 终止 ) | `#定义-stream-2--终止-` | 同文件锚点不存在: #定义-stream-2--终止- |
| docs\rust-ownership-decidability\case-studies\tokio-stream-formal-analysis.md | 定义 COMBINATOR-1 ( Map ) | `#定义-combinator-1--map-` | 同文件锚点不存在: #定义-combinator-1--map- |
| docs\rust-ownership-decidability\case-studies\tokio-stream-formal-analysis.md | 定义 COMBINATOR-2 ( Filter ) | `#定义-combinator-2--filter-` | 同文件锚点不存在: #定义-combinator-2--filter- |
| docs\rust-ownership-decidability\case-studies\tokio-stream-formal-analysis.md | 定义 COMBINATOR-3 ( Fold ) | `#定义-combinator-3--fold-` | 同文件锚点不存在: #定义-combinator-3--fold- |
| docs\rust-ownership-decidability\case-studies\tokio-stream-formal-analysis.md | 定义 BACKPRESSURE-1 ( Buffer ) | `#定义-backpressure-1--buffer-` | 同文件锚点不存在: #定义-backpressure-1--buffer- |
| docs\rust-ownership-decidability\case-studies\tokio-stream-formal-analysis.md | 定义 BACKPRESSURE-2 ( Throttle ) | `#定义-backpressure-2--throttle-` | 同文件锚点不存在: #定义-backpressure-2--throttle- |
| docs\rust-ownership-decidability\case-studies\tokio-stream-formal-analysis.md | 定理 BACKPRESSURE-T1 ( 流量控制 ) | `#定理-backpressure-t1--流量控制-` | 同文件锚点不存在: #定理-backpressure-t1--流量控制- |
| docs\rust-ownership-decidability\case-studies\tokio-stream-formal-analysis.md | 定义 TIMEOUT-1 ( 流超时 ) | `#定义-timeout-1--流超时-` | 同文件锚点不存在: #定义-timeout-1--流超时- |
| docs\rust-ownership-decidability\case-studies\tokio-stream-formal-analysis.md | 定义 LIMIT-1 ( 数量限制 ) | `#定义-limit-1--数量限制-` | 同文件锚点不存在: #定义-limit-1--数量限制- |
| docs\rust-ownership-decidability\case-studies\tokio-stream-formal-analysis.md | 定义 MERGE-1 ( 合并流 ) | `#定义-merge-1--合并流-` | 同文件锚点不存在: #定义-merge-1--合并流- |
| docs\rust-ownership-decidability\case-studies\tokio-stream-formal-analysis.md | 定义 SELECT-1 ( 选择 ) | `#定义-select-1--选择-` | 同文件锚点不存在: #定义-select-1--选择- |
| docs\rust-ownership-decidability\case-studies\tokio-stream-formal-analysis.md | 定理 STREAM-T1 ( 顺序保持 ) | `#定理-stream-t1--顺序保持-` | 同文件锚点不存在: #定理-stream-t1--顺序保持- |
| docs\rust-ownership-decidability\case-studies\tokio-stream-formal-analysis.md | 定理 STREAM-T2 ( 终止传播 ) | `#定理-stream-t2--终止传播-` | 同文件锚点不存在: #定理-stream-t2--终止传播- |
| docs\rust-ownership-decidability\case-studies\tokio-util-formal-analysis.md | *定理数量: 6个* | `#定理数量-6个` | 同文件锚点不存在: #定理数量-6个 |
| docs\rust-ownership-decidability\case-studies\tonic-formal-analysis.md | 定义 SERVICE-1 ( proto定义 ) | `#定义-service-1--proto定义-` | 同文件锚点不存在: #定义-service-1--proto定义- |
| docs\rust-ownership-decidability\case-studies\tonic-formal-analysis.md | 定义 SERVICE-2 ( 生成trait ) | `#定义-service-2--生成trait-` | 同文件锚点不存在: #定义-service-2--生成trait- |
| docs\rust-ownership-decidability\case-studies\tonic-formal-analysis.md | 定义 CODEC-1 ( Protobuf编解码 ) | `#定义-codec-1--protobuf编解码-` | 同文件锚点不存在: #定义-codec-1--protobuf编解码- |
| docs\rust-ownership-decidability\case-studies\tonic-formal-analysis.md | 定理 CODEC-T1 ( 序列化正确性 ) | `#定理-codec-t1--序列化正确性-` | 同文件锚点不存在: #定理-codec-t1--序列化正确性- |
| docs\rust-ownership-decidability\case-studies\tonic-formal-analysis.md | 定义 STREAM-1 ( 流类型 ) | `#定义-stream-1--流类型-` | 同文件锚点不存在: #定义-stream-1--流类型- |
| docs\rust-ownership-decidability\case-studies\tonic-formal-analysis.md | 定义 STREAM-2 ( 背压控制 ) | `#定义-stream-2--背压控制-` | 同文件锚点不存在: #定义-stream-2--背压控制- |
| docs\rust-ownership-decidability\case-studies\tonic-formal-analysis.md | 定义 INTERCEPT-1 ( Interceptor ) | `#定义-intercept-1--interceptor-` | 同文件锚点不存在: #定义-intercept-1--interceptor- |
| docs\rust-ownership-decidability\case-studies\tonic-formal-analysis.md | 定理 INTERCEPT-T1 ( 链式调用 ) | `#定理-intercept-t1--链式调用-` | 同文件锚点不存在: #定理-intercept-t1--链式调用- |
| docs\rust-ownership-decidability\case-studies\tonic-formal-analysis.md | 定义 TLS-1 ( 证书验证 ) | `#定义-tls-1--证书验证-` | 同文件锚点不存在: #定义-tls-1--证书验证- |
| docs\rust-ownership-decidability\case-studies\tonic-formal-analysis.md | 定理 TLS-T1 ( 安全通道 ) | `#定理-tls-t1--安全通道-` | 同文件锚点不存在: #定理-tls-t1--安全通道- |
| docs\rust-ownership-decidability\case-studies\tonic-formal-analysis.md | 定理 TONIC-T1 ( 协议合规 ) | `#定理-tonic-t1--协议合规-` | 同文件锚点不存在: #定理-tonic-t1--协议合规- |
| docs\rust-ownership-decidability\case-studies\tonic-formal-analysis.md | 定理 TONIC-T2 ( 流安全 ) | `#定理-tonic-t2--流安全-` | 同文件锚点不存在: #定理-tonic-t2--流安全- |
| docs\rust-ownership-decidability\case-studies\tonic-formal-analysis.md | **状态**: ✅ 已对齐 | `#状态--已对齐` | 同文件锚点不存在: #状态--已对齐 |
| docs\rust-ownership-decidability\case-studies\tonic-grpc-formal-analysis.md | *最后更新: 2026-03-04* | `#最后更新-2026-03-04` | 同文件锚点不存在: #最后更新-2026-03-04 |
| docs\rust-ownership-decidability\case-studies\tonic-health-formal-analysis.md | *定理数量: 6个* | `#定理数量-6个` | 同文件锚点不存在: #定理数量-6个 |
| docs\rust-ownership-decidability\case-studies\tower-formal-analysis.md | 定义 SERVICE-1 ( 核心trait ) | `#定义-service-1--核心trait-` | 同文件锚点不存在: #定义-service-1--核心trait- |
| docs\rust-ownership-decidability\case-studies\tower-formal-analysis.md | 定义 SERVICE-2 ( 就绪检查 ) | `#定义-service-2--就绪检查-` | 同文件锚点不存在: #定义-service-2--就绪检查- |
| docs\rust-ownership-decidability\case-studies\tower-formal-analysis.md | 定理 SERVICE-T1 ( 就绪前置条件 ) | `#定理-service-t1--就绪前置条件-` | 同文件锚点不存在: #定理-service-t1--就绪前置条件- |
| docs\rust-ownership-decidability\case-studies\tower-formal-analysis.md | 定义 LAYER-1 ( Layer trait ) | `#定义-layer-1--layer-trait-` | 同文件锚点不存在: #定义-layer-1--layer-trait- |
| docs\rust-ownership-decidability\case-studies\tower-formal-analysis.md | 定义 LAYER-2 ( 组合 ) | `#定义-layer-2--组合-` | 同文件锚点不存在: #定义-layer-2--组合- |
| docs\rust-ownership-decidability\case-studies\tower-formal-analysis.md | 定义 COMPOSE-1 ( AndThen ) | `#定义-compose-1--andthen-` | 同文件锚点不存在: #定义-compose-1--andthen- |
| docs\rust-ownership-decidability\case-studies\tower-formal-analysis.md | 定义 COMPOSE-2 ( 映射 ) | `#定义-compose-2--映射-` | 同文件锚点不存在: #定义-compose-2--映射- |
| docs\rust-ownership-decidability\case-studies\tower-formal-analysis.md | 定义 BACKPRESSURE-1 ( 限流 ) | `#定义-backpressure-1--限流-` | 同文件锚点不存在: #定义-backpressure-1--限流- |
| docs\rust-ownership-decidability\case-studies\tower-formal-analysis.md | 定义 BACKPRESSURE-2 ( 并发控制 ) | `#定义-backpressure-2--并发控制-` | 同文件锚点不存在: #定义-backpressure-2--并发控制- |
| docs\rust-ownership-decidability\case-studies\tower-formal-analysis.md | 定义 TIMEOUT-1 ( 超时层 ) | `#定义-timeout-1--超时层-` | 同文件锚点不存在: #定义-timeout-1--超时层- |
| docs\rust-ownership-decidability\case-studies\tower-formal-analysis.md | 定义 RETRY-1 ( 重试策略 ) | `#定义-retry-1--重试策略-` | 同文件锚点不存在: #定义-retry-1--重试策略- |
| docs\rust-ownership-decidability\case-studies\tower-formal-analysis.md | 定理 TOWER-T1 ( 组合封闭性 ) | `#定理-tower-t1--组合封闭性-` | 同文件锚点不存在: #定理-tower-t1--组合封闭性- |
| docs\rust-ownership-decidability\case-studies\tower-formal-analysis.md | 定理 TOWER-T2 ( 背压传播 ) | `#定理-tower-t2--背压传播-` | 同文件锚点不存在: #定理-tower-t2--背压传播- |
| docs\rust-ownership-decidability\case-studies\tower-formal-analysis.md | **状态**: ✅ 已对齐 | `#状态--已对齐` | 同文件锚点不存在: #状态--已对齐 |
| docs\rust-ownership-decidability\case-studies\tracing-formal-analysis.md | *最后更新: 2026-03-04* | `#最后更新-2026-03-04` | 同文件锚点不存在: #最后更新-2026-03-04 |
| docs\rust-ownership-decidability\case-studies\typenum-formal-analysis.md | **代码示例**: 12个完整示例 | `#代码示例-12个完整示例` | 同文件锚点不存在: #代码示例-12个完整示例 |
| docs\rust-ownership-decidability\case-studies\usb-device-formal-analysis.md | 定义 USB-STATE-1 ( 设备状态 ) | `#定义-usb-state-1--设备状态-` | 同文件锚点不存在: #定义-usb-state-1--设备状态- |
| docs\rust-ownership-decidability\case-studies\usb-device-formal-analysis.md | 定义 USB-STATE-2 ( 枚举流程 ) | `#定义-usb-state-2--枚举流程-` | 同文件锚点不存在: #定义-usb-state-2--枚举流程- |
| docs\rust-ownership-decidability\case-studies\usb-device-formal-analysis.md | 定理 USB-T1 ( 状态安全 ) | `#定理-usb-t1--状态安全-` | 同文件锚点不存在: #定理-usb-t1--状态安全- |
| docs\rust-ownership-decidability\case-studies\usb-device-formal-analysis.md | 定义 EP-1 ( 端点类型 ) | `#定义-ep-1--端点类型-` | 同文件锚点不存在: #定义-ep-1--端点类型- |
| docs\rust-ownership-decidability\case-studies\usb-device-formal-analysis.md | 定义 EP-2 ( 端点状态 ) | `#定义-ep-2--端点状态-` | 同文件锚点不存在: #定义-ep-2--端点状态- |
| docs\rust-ownership-decidability\case-studies\usb-device-formal-analysis.md | 定义 EP-3 ( 端点操作 ) | `#定义-ep-3--端点操作-` | 同文件锚点不存在: #定义-ep-3--端点操作- |
| docs\rust-ownership-decidability\case-studies\usb-device-formal-analysis.md | 定义 DESC-1 ( 描述符链 ) | `#定义-desc-1--描述符链-` | 同文件锚点不存在: #定义-desc-1--描述符链- |
| docs\rust-ownership-decidability\case-studies\usb-device-formal-analysis.md | 定理 DESC-T1 ( 描述符完整性 ) | `#定理-desc-t1--描述符完整性-` | 同文件锚点不存在: #定理-desc-t1--描述符完整性- |
| docs\rust-ownership-decidability\case-studies\usb-device-formal-analysis.md | 定义 CLASS-1 ( CDC ACM ) | `#定义-class-1--cdc-acm-` | 同文件锚点不存在: #定义-class-1--cdc-acm- |
| docs\rust-ownership-decidability\case-studies\usb-device-formal-analysis.md | 定义 CLASS-2 ( HID ) | `#定义-class-2--hid-` | 同文件锚点不存在: #定义-class-2--hid- |
| docs\rust-ownership-decidability\case-studies\usb-device-formal-analysis.md | 定理 USB-T2 ( 端点隔离 ) | `#定理-usb-t2--端点隔离-` | 同文件锚点不存在: #定理-usb-t2--端点隔离- |
| docs\rust-ownership-decidability\case-studies\usb-device-formal-analysis.md | 定理 USB-T3 ( 控制传输优先 ) | `#定理-usb-t3--控制传输优先-` | 同文件锚点不存在: #定理-usb-t3--控制传输优先- |
| docs\rust-ownership-decidability\case-studies\wasm-bindgen-formal-analysis.md | 定义 TYPEMAP-1 ( 基本类型 ) | `#定义-typemap-1--基本类型-` | 同文件锚点不存在: #定义-typemap-1--基本类型- |
| docs\rust-ownership-decidability\case-studies\wasm-bindgen-formal-analysis.md | 定义 TYPEMAP-2 ( 复杂类型 ) | `#定义-typemap-2--复杂类型-` | 同文件锚点不存在: #定义-typemap-2--复杂类型- |
| docs\rust-ownership-decidability\case-studies\wasm-bindgen-formal-analysis.md | 定义 MEM-1 ( wasm内存模型 ) | `#定义-mem-1--wasm内存模型-` | 同文件锚点不存在: #定义-mem-1--wasm内存模型- |
| docs\rust-ownership-decidability\case-studies\wasm-bindgen-formal-analysis.md | 定义 MEM-2 ( 所有权转移 ) | `#定义-mem-2--所有权转移-` | 同文件锚点不存在: #定义-mem-2--所有权转移- |
| docs\rust-ownership-decidability\case-studies\wasm-bindgen-formal-analysis.md | 定理 MEM-T1 ( 无泄漏 ) | `#定理-mem-t1--无泄漏-` | 同文件锚点不存在: #定理-mem-t1--无泄漏- |
| docs\rust-ownership-decidability\case-studies\wasm-bindgen-formal-analysis.md | 定义 EXPORT-1 ( 导出语法 ) | `#定义-export-1--导出语法-` | 同文件锚点不存在: #定义-export-1--导出语法- |
| docs\rust-ownership-decidability\case-studies\wasm-bindgen-formal-analysis.md | 定义 EXPORT-2 ( 异步导出 ) | `#定义-export-2--异步导出-` | 同文件锚点不存在: #定义-export-2--异步导出- |
| docs\rust-ownership-decidability\case-studies\wasm-bindgen-formal-analysis.md | 定义 IMPORT-1 ( 内联导入 ) | `#定义-import-1--内联导入-` | 同文件锚点不存在: #定义-import-1--内联导入- |
| docs\rust-ownership-decidability\case-studies\wasm-bindgen-formal-analysis.md | 定义 IMPORT-2 ( 自定义类型 ) | `#定义-import-2--自定义类型-` | 同文件锚点不存在: #定义-import-2--自定义类型- |
| docs\rust-ownership-decidability\case-studies\wasm-bindgen-formal-analysis.md | 定理 WBG-T1 ( 类型安全边界 ) | `#定理-wbg-t1--类型安全边界-` | 同文件锚点不存在: #定理-wbg-t1--类型安全边界- |
| docs\rust-ownership-decidability\case-studies\wasm-bindgen-formal-analysis.md | 定理 WBG-T2 ( 零拷贝视图 ) | `#定理-wbg-t2--零拷贝视图-` | 同文件锚点不存在: #定理-wbg-t2--零拷贝视图- |
| docs\rust-ownership-decidability\case-studies\wasm-bindgen-formal-analysis.md | **状态**: ✅ 已对齐 | `#状态--已对齐` | 同文件锚点不存在: #状态--已对齐 |
| docs\rust-ownership-decidability\case-studies\web-server-architecture.md | 本架构展示了如何将Rust的所有权、借用和生命周期应用于实际的高并发场景 | `#本架构展示了如何将rust的所有权借用和生命周期应用于实际的高并发场景` | 同文件锚点不存在: #本架构展示了如何将rust的所有权借用和生命周期应用于实际的高并发场景 |
| docs\rust-ownership-decidability\case-studies\wgpu-glium-formal-analysis.md | *定理数量: 5个* | `#定理数量-5个` | 同文件锚点不存在: #定理数量-5个 |
| docs\rust-ownership-decidability\case-studies\zerocopy-formal-analysis.md | **代码示例**: 8个完整示例 | `#代码示例-8个完整示例` | 同文件锚点不存在: #代码示例-8个完整示例 |
| docs\rust-ownership-decidability\case-studies\cli\README.md | *最后更新: 2024年* | `#最后更新-2024年` | 同文件锚点不存在: #最后更新-2024年 |
| docs\rust-ownership-decidability\case-studies\cloud\README.md | Firecracker - AWS 的微型虚拟机 | `#firecracker---aws-的微型虚拟机` | 同文件锚点不存在: #firecracker---aws-的微型虚拟机 |
| docs\rust-ownership-decidability\case-studies\cloud\README.md | Linkerd2-proxy - 服务网格数据平面 | `#linkerd2-proxy---服务网格数据平面` | 同文件锚点不存在: #linkerd2-proxy---服务网格数据平面 |
| docs\rust-ownership-decidability\case-studies\cloud\README.md | *最后更新：2026-03-04* | `#最后更新2026-03-04` | 同文件锚点不存在: #最后更新2026-03-04 |
| docs\rust-ownership-decidability\case-studies\database\README.md | Rust的内存安全、零成本抽象和 fearless 并发特性使其成为构建高性能、可靠数据库系统的理想选择 | `#rust的内存安全零成本抽象和-fearless-并发特性使其成为构建高性能可靠数据库系统的理想选择` | 同文件锚点不存在: #rust的内存安全零成本抽象和-fearless-并发特性使其成为构建高性能可靠数据库系统的理想选择 |
| docs\rust-ownership-decidability\case-studies\embedded\EMBEDDED_CRATES_INDEX.md | **状态**: ✅ 核心嵌入式库100%覆盖完成 | `#状态--核心嵌入式库100覆盖完成` | 同文件锚点不存在: #状态--核心嵌入式库100覆盖完成 |
| docs\rust-ownership-decidability\case-studies\embedded\README.md | *适用Rust版本: 1.75+* | `#适用rust版本-175` | 同文件锚点不存在: #适用rust版本-175 |
| docs\rust-ownership-decidability\case-studies\gamedev\README.md | 祝你的 Rust 游戏开发之旅顺利 | `#祝你的-rust-游戏开发之旅顺利` | 同文件锚点不存在: #祝你的-rust-游戏开发之旅顺利 |
| docs\rust-ownership-decidability\case-studies\media\README.md | 适用场景：媒体服务器、实时通信、编解码器、流媒体等 | `#适用场景媒体服务器实时通信编解码器流媒体等` | 同文件锚点不存在: #适用场景媒体服务器实时通信编解码器流媒体等 |
| docs\rust-ownership-decidability\case-studies\ml-ai\README.md | *本文档由AI助手生成，最后更新: 2026年* | `#本文档由ai助手生成最后更新-2026年` | 同文件锚点不存在: #本文档由ai助手生成最后更新-2026年 |
| docs\rust-ownership-decidability\case-studies\security\README.md | *作者：Rust安全工具开发团队* | `#作者rust安全工具开发团队` | 同文件锚点不存在: #作者rust安全工具开发团队 |
| docs\rust-ownership-decidability\case-studies\wasm\README.md | 适用场景：图像处理、加密、游戏、科学计算等计算密集型任务 | `#适用场景图像处理加密游戏科学计算等计算密集型任务` | 同文件锚点不存在: #适用场景图像处理加密游戏科学计算等计算密集型任务 |
| docs\rust-ownership-decidability\comparative-analysis\async-concurrency-comparison.md | Async执行模型 - 并发范式对比分析 | `#async执行模型---并发范式对比分析` | 同文件锚点不存在: #async执行模型---并发范式对比分析 |
| docs\rust-ownership-decidability\comparative-analysis\async-concurrency-comparison.md | **状态**: ✅ 深度对比分析完成 | `#状态--深度对比分析完成` | 同文件锚点不存在: #状态--深度对比分析完成 |
| docs\rust-ownership-decidability\comparative-analysis\memory-management-comparison.md | 没有"最好"的内存管理方式，只有最适合特定场景的解决方案。现代语言趋势是提供多种选择，让开发者在安全、性能和开发效率之间找到最佳平衡。 | `#没有最好的内存管理方式只有最适合特定场景的解决方案现代语言趋势是提供多种选择让开发者在安全性能和开发效率之间找到最佳平衡` | 同文件锚点不存在: #没有最好的内存管理方式只有最适合特定场景的解决方案现代语言趋势是提供多种选择让开发者在安全性能和开发效率之间找到最佳平衡 |
| docs\rust-ownership-decidability\comparative-analysis\refinedrust-vs-rustbelt.md | **维护者**: Rust 所有权可判定性研究项目 | `#维护者-rust-所有权可判定性研究项目` | 同文件锚点不存在: #维护者-rust-所有权可判定性研究项目 |
| docs\rust-ownership-decidability\comparative-analysis\rust-vs-cpp.md | Rust 和 C++ 都是强大的系统编程语言。C++ 提供了更大的灵活性和成熟的生态，而 Rust 提供了更强的安全保证和现代工具链。选择哪种语言取决于项目的具体需求、团队经验和风险承受能力。 | `#rust-和-c-都是强大的系统编程语言c-提供了更大的灵活性和成熟的生态而-rust-提供了更强的安全保证和现代工具链选择哪种语言取决于项目的具体需求团队经验和风险承受能力` | 同文件锚点不存在: #rust-和-c-都是强大的系统编程语言c-提供了更大的灵活性和成熟的生态而-rust-提供了更强的安全保证和现代工具链选择哪种语言取决于项目的具体需求团队经验和风险承受能力 |
| docs\rust-ownership-decidability\comparative-analysis\rust-vs-go.md | Go 的 Goroutine + Channel | `#go-的-goroutine--channel` | 同文件锚点不存在: #go-的-goroutine--channel |
| docs\rust-ownership-decidability\comparative-analysis\rust-vs-go.md | Rust 的异步/等待 + 所有权 | `#rust-的异步等待--所有权` | 同文件锚点不存在: #rust-的异步等待--所有权 |
| docs\rust-ownership-decidability\comparative-analysis\rust-vs-java.md | Rust (Axum + SQLx) | `#rust-axum--sqlx` | 同文件锚点不存在: #rust-axum--sqlx |
| docs\rust-ownership-decidability\comprehensive-analysis\design-patterns-comprehensive.md | **对齐来源**: Rust Book, Rust API Guidelines, crate文档 | `#对齐来源-rust-book-rust-api-guidelines-crate文档` | 同文件锚点不存在: #对齐来源-rust-book-rust-api-guidelines-crate文档 |
| docs\rust-ownership-decidability\comprehensive-analysis\open-source-analysis.md | **更新日期**: 2026-03-05 | `#更新日期-2026-03-05` | 同文件锚点不存在: #更新日期-2026-03-05 |
| docs\rust-ownership-decidability\comprehensive-analysis\authoritative-sources\academic-papers.md | 4.2 Stacked Borrows / Tree Borrows | `#42-stacked-borrows--tree-borrows` | 同文件锚点不存在: #42-stacked-borrows--tree-borrows |
| docs\rust-ownership-decidability\comprehensive-analysis\authoritative-sources\academic-papers.md | **覆盖论文**: 15+ 篇核心文献 | `#覆盖论文-15-篇核心文献` | 同文件锚点不存在: #覆盖论文-15-篇核心文献 |
| docs\rust-ownership-decidability\comprehensive-analysis\case-studies\embassy-embedded-analysis.md | **Embassy版本**: 0.5+ | `#embassy版本-05` | 同文件锚点不存在: #embassy版本-05 |
| docs\rust-ownership-decidability\comprehensive-analysis\case-studies\tokio-runtime-analysis.md | **Tokio版本**: 1.35+ | `#tokio版本-135` | 同文件锚点不存在: #tokio版本-135 |
| docs\rust-ownership-decidability\comprehensive-analysis\decision-trees\concurrency-model-selection.md | **适用版本**: Rust 1.75+ | `#适用版本-rust-175` | 同文件锚点不存在: #适用版本-rust-175 |
| docs\rust-ownership-decidability\comprehensive-analysis\decision-trees\pattern-selection.md | **更新日期**: 2026-03-05 | `#更新日期-2026-03-05` | 同文件锚点不存在: #更新日期-2026-03-05 |
| docs\rust-ownership-decidability\comprehensive-analysis\extensions\advanced-ownership-patterns.md | 1.2 rental / ouroboros crate | `#12-rental--ouroboros-crate` | 同文件锚点不存在: #12-rental--ouroboros-crate |
| docs\rust-ownership-decidability\comprehensive-analysis\extensions\advanced-ownership-patterns.md | **更新日期**: 2026-03-05 | `#更新日期-2026-03-05` | 同文件锚点不存在: #更新日期-2026-03-05 |
| docs\rust-ownership-decidability\comprehensive-analysis\extensions\performance-optimization.md | 2.2  arena分配器 | `#22--arena分配器` | 同文件锚点不存在: #22--arena分配器 |
| docs\rust-ownership-decidability\comprehensive-analysis\extensions\performance-optimization.md | **更新日期**: 2026-03-05 | `#更新日期-2026-03-05` | 同文件锚点不存在: #更新日期-2026-03-05 |
| docs\rust-ownership-decidability\comprehensive-analysis\formal-framework\definitions.md | **状态**: ✅ 形式化定义框架 100% 完成 | `#状态--形式化定义框架-100-完成` | 同文件锚点不存在: #状态--形式化定义框架-100-完成 |
| docs\rust-ownership-decidability\comprehensive-analysis\matrices\comprehensive-comparison-matrix.md | **更新日期**: 2026-03-05 | `#更新日期-2026-03-05` | 同文件锚点不存在: #更新日期-2026-03-05 |
| docs\rust-ownership-decidability\comprehensive-analysis\matrices\safety-analysis-matrix.md | **覆盖维度**: 9大安全领域 | `#覆盖维度-9大安全领域` | 同文件锚点不存在: #覆盖维度-9大安全领域 |
| docs\rust-ownership-decidability\comprehensive-analysis\mindmaps\borrowing-system-mindmap.md | Rust借用系统 - 思维导图 | `#rust借用系统---思维导图` | 同文件锚点不存在: #rust借用系统---思维导图 |
| docs\rust-ownership-decidability\comprehensive-analysis\mindmaps\borrowing-system-mindmap.md | **更新日期**: 2026-03-05 | `#更新日期-2026-03-05` | 同文件锚点不存在: #更新日期-2026-03-05 |
| docs\rust-ownership-decidability\comprehensive-analysis\mindmaps\ownership-system-mindmap.md | Rust所有权系统 - 思维导图 | `#rust所有权系统---思维导图` | 同文件锚点不存在: #rust所有权系统---思维导图 |
| docs\rust-ownership-decidability\comprehensive-analysis\mindmaps\ownership-system-mindmap.md | **更新日期**: 2026-03-05 | `#更新日期-2026-03-05` | 同文件锚点不存在: #更新日期-2026-03-05 |
| docs\rust-ownership-decidability\comprehensive-analysis\proofs\memory-safety-proof.md | **证明状态**: ✅ 完整形式化证明 | `#证明状态--完整形式化证明` | 同文件锚点不存在: #证明状态--完整形式化证明 |
| docs\rust-ownership-decidability\comprehensive-analysis\scenario-trees\application-domain-tree.md | **更新日期**: 2026-03-05 | `#更新日期-2026-03-05` | 同文件锚点不存在: #更新日期-2026-03-05 |
| docs\rust-ownership-decidability\comprehensive-analysis\scenario-trees\real-time-systems-tree.md | **更新日期**: 2026-03-05 | `#更新日期-2026-03-05` | 同文件锚点不存在: #更新日期-2026-03-05 |
| docs\rust-ownership-decidability\coq-formalization\theories\Advanced\TECHNICAL_DEBT.md | Rust 1.94 形式化 - 技术债务跟踪 | `#rust-194-形式化---技术债务跟踪` | 同文件锚点不存在: #rust-194-形式化---技术债务跟踪 |
| docs\rust-ownership-decidability\coq-formalization\theories\Advanced\TECHNICAL_DEBT.md | **状态: ✅ 100% 完成** | `#状态--100-完成` | 同文件锚点不存在: #状态--100-完成 |
| docs\rust-ownership-decidability\exercises\ADVANCED_OWNERSHIP_WORKSHOP.md | Rust 所有权系统 - 高级实践工作坊 | `#rust-所有权系统---高级实践工作坊` | 同文件锚点不存在: #rust-所有权系统---高级实践工作坊 |
| docs\rust-ownership-decidability\exercises\ADVANCED_OWNERSHIP_WORKSHOP.md | **完成度**: 0/5 练习 | `#完成度-05-练习` | 同文件锚点不存在: #完成度-05-练习 |
| docs\rust-ownership-decidability\exercises\ADVANCED_OWNERSHIP_WORKSHOP.md | Pin 和 Unpin 详解 | `../01-core-concepts/detailed-concepts/ownership-deep-dive.md#pin-unpin` | 锚点不存在: #pin-unpin |
| docs\rust-ownership-decidability\exercises\ownership-basics.md | *更多练习持续添加中...* | `#更多练习持续添加中` | 同文件锚点不存在: #更多练习持续添加中 |
| docs\rust-ownership-decidability\extensions\ffi-interoperability.md | 通过遵循这些模式和最佳实践，你可以安全高效地在 Rust 中使用 FFI，同时保持 Rust 的安全保证。 | `#通过遵循这些模式和最佳实践你可以安全高效地在-rust-中使用-ffi同时保持-rust-的安全保证` | 同文件锚点不存在: #通过遵循这些模式和最佳实践你可以安全高效地在-rust-中使用-ffi同时保持-rust-的安全保证 |
| docs\rust-ownership-decidability\extensions\rust-for-linux.md | 随着项目的成熟，Rust 将成为 Linux 内核开发的重要组成部分。 | `#随着项目的成熟rust-将成为-linux-内核开发的重要组成部分` | 同文件锚点不存在: #随着项目的成熟rust-将成为-linux-内核开发的重要组成部分 |
| docs\rust-ownership-decidability\extensions\unsafe-rust-patterns.md | 通过这些模式和最佳实践，你可以在保持 Rust 安全保证的同时，获得底层编程的全部能力 | `#通过这些模式和最佳实践你可以在保持-rust-安全保证的同时获得底层编程的全部能力` | 同文件锚点不存在: #通过这些模式和最佳实践你可以在保持-rust-安全保证的同时获得底层编程的全部能力 |
| docs\rust-ownership-decidability\formal-foundations\README.md | models/ - 形式化模型 | `#models---形式化模型` | 同文件锚点不存在: #models---形式化模型 |
| docs\rust-ownership-decidability\formal-foundations\README.md | semantics/ - 语义定义 | `#semantics---语义定义` | 同文件锚点不存在: #semantics---语义定义 |
| docs\rust-ownership-decidability\formal-foundations\README.md | proofs/ - 形式化证明 | `#proofs---形式化证明` | 同文件锚点不存在: #proofs---形式化证明 |
| docs\rust-ownership-decidability\formal-foundations\README.md | **状态**: ✅ 100% 完成 - 全面对标国际权威资料 | `#状态--100-完成---全面对标国际权威资料` | 同文件锚点不存在: #状态--100-完成---全面对标国际权威资料 |
| docs\rust-ownership-decidability\formal-foundations\RUST_FORMAL_SEMANTICS_DEEP.md | *End of Document* | `#end-of-document` | 同文件锚点不存在: #end-of-document |
| docs\rust-ownership-decidability\formal-foundations\models\drop-elaboration-formal.md | *状态: 完成* | `#状态-完成` | 同文件锚点不存在: #状态-完成 |
| docs\rust-ownership-decidability\formal-foundations\models\refinedrust-type-system.md | *状态: 完成* | `#状态-完成` | 同文件锚点不存在: #状态-完成 |
| docs\rust-ownership-decidability\formal-foundations\models\relaxed-memory-model.md | *状态: 完成* | `#状态-完成` | 同文件锚点不存在: #状态-完成 |
| docs\rust-ownership-decidability\formal-foundations\models\symbolic-borrow-checking.md | *状态: 完成* | `#状态-完成` | 同文件锚点不存在: #状态-完成 |
| docs\rust-ownership-decidability\formal-foundations\models\tree-borrows-comprehensive.md | 4.1.1 Active → Frozen 转换 | `#411-active--frozen-转换` | 同文件锚点不存在: #411-active--frozen-转换 |
| docs\rust-ownership-decidability\formal-foundations\models\tree-borrows-comprehensive.md | *状态: 已更新 (PLDI 2025 最新研究)* | `#状态-已更新-pldi-2025-最新研究` | 同文件锚点不存在: #状态-已更新-pldi-2025-最新研究 |
| docs\rust-ownership-decidability\formal-foundations\proofs\affine-logic-decidability.md | 仿射逻辑为Rust的所有权系统提供了坚实的数学基础，确保了内存安全的同时保持了表达力和实用性。 | `#仿射逻辑为rust的所有权系统提供了坚实的数学基础确保了内存安全的同时保持了表达力和实用性` | 同文件锚点不存在: #仿射逻辑为rust的所有权系统提供了坚实的数学基础确保了内存安全的同时保持了表达力和实用性 |
| docs\rust-ownership-decidability\formal-foundations\proofs\async-execution-examples.md | Async执行模型 - 深度代码示例与证明 | `#async执行模型---深度代码示例与证明` | 同文件锚点不存在: #async执行模型---深度代码示例与证明 |
| docs\rust-ownership-decidability\formal-foundations\proofs\async-execution-examples.md | **状态**: ✅ 深度实现与验证完成 | `#状态--深度实现与验证完成` | 同文件锚点不存在: #状态--深度实现与验证完成 |
| docs\rust-ownership-decidability\formal-foundations\proofs\async-execution-model-formal.md | 定理 ASYNC-SAFETY-1 ( 内存安全 ) | `#定理-async-safety-1--内存安全-` | 同文件锚点不存在: #定理-async-safety-1--内存安全- |
| docs\rust-ownership-decidability\formal-foundations\proofs\async-execution-model-formal.md | 定理 ASYNC-COMPLETENESS-1 ( 执行完备性 ) | `#定理-async-completeness-1--执行完备性-` | 同文件锚点不存在: #定理-async-completeness-1--执行完备性- |
| docs\rust-ownership-decidability\formal-foundations\proofs\async-execution-model-formal.md | 定理 PIN-SOUNDNESS-1 ( Pin正确性 ) | `#定理-pin-soundness-1--pin正确性-` | 同文件锚点不存在: #定理-pin-soundness-1--pin正确性- |
| docs\rust-ownership-decidability\formal-foundations\proofs\async-execution-model-formal.md | **状态**: ✅ 深度形式化完成 | `#状态--深度形式化完成` | 同文件锚点不存在: #状态--深度形式化完成 |
| docs\rust-ownership-decidability\formal-foundations\proofs\ASYNC_ANALYSIS_COMPLETE_INDEX.md | Async Rust 全面形式化分析 - 完整索引 | `#async-rust-全面形式化分析---完整索引` | 同文件锚点不存在: #async-rust-全面形式化分析---完整索引 |
| docs\rust-ownership-decidability\formal-foundations\proofs\ASYNC_ANALYSIS_COMPLETE_INDEX.md | 7. 特性与对比 (Features \& Comparison) | `#7-特性与对比-features--comparison` | 同文件锚点不存在: #7-特性与对比-features--comparison |
| docs\rust-ownership-decidability\formal-foundations\proofs\decidability-theorem.md | *最后更新: 2026-03-04* | `#最后更新-2026-03-04` | 同文件锚点不存在: #最后更新-2026-03-04 |
| docs\rust-ownership-decidability\formal-foundations\proofs\memory-safety-proof.md | *最后更新: 2026-03-04* | `#最后更新-2026-03-04` | 同文件锚点不存在: #最后更新-2026-03-04 |
| docs\rust-ownership-decidability\formal-foundations\proofs\PROOF_PATTERNS.md | *最后更新: 2026-03-06* | `#最后更新-2026-03-06` | 同文件锚点不存在: #最后更新-2026-03-06 |
| docs\rust-ownership-decidability\formal-foundations\proofs\rustbelt-formalization.md | 7.1 Arc | `#71-arc` | 同文件锚点不存在: #71-arc |
| docs\rust-ownership-decidability\formal-foundations\proofs\rustbelt-formalization.md | 7.2 Mutex | `#72-mutex` | 同文件锚点不存在: #72-mutex |
| docs\rust-ownership-decidability\formal-foundations\proofs\rustbelt-formalization.md | 7.3 Rc | `#73-rc` | 同文件锚点不存在: #73-rc |
| docs\rust-ownership-decidability\formal-foundations\proofs\rustbelt-formalization.md | 7.4 Cell 和 RefCell | `#74-cell-和-refcell` | 同文件锚点不存在: #74-cell-和-refcell |
| docs\rust-ownership-decidability\formal-foundations\proofs\rustbelt-formalization.md | RustBelt为Rust的安全性承诺提供了数学保证，是编程语言形式化验证的里程碑。 | `#rustbelt为rust的安全性承诺提供了数学保证是编程语言形式化验证的里程碑` | 同文件锚点不存在: #rustbelt为rust的安全性承诺提供了数学保证是编程语言形式化验证的里程碑 |
| docs\rust-ownership-decidability\formal-foundations\proofs\type-ownership-unified-theory.md | 5.3.1 类型正确性 ⟹ 所有权安全 | `#531-类型正确性--所有权安全` | 同文件锚点不存在: #531-类型正确性--所有权安全 |
| docs\rust-ownership-decidability\formal-foundations\proofs\type-ownership-unified-theory.md | 6.1 Vec 的所有权模型 | `#61-vec-的所有权模型` | 同文件锚点不存在: #61-vec-的所有权模型 |
| docs\rust-ownership-decidability\formal-foundations\semantics\logical-relations.md | Vec 不变式 | `#vec-不变式` | 同文件锚点不存在: #vec-不变式 |
| docs\rust-ownership-decidability\formal-foundations\semantics\mechanized-proofs.md | 7.1 Vec 验证 (RustBelt) | `#71-vec-验证-rustbelt` | 同文件锚点不存在: #71-vec-验证-rustbelt |
| docs\rust-ownership-decidability\formal-foundations\semantics\mechanized-proofs.md | 7.2 Rc 验证 | `#72-rc-验证` | 同文件锚点不存在: #72-rc-验证 |
| docs\rust-ownership-decidability\formal-foundations\semantics\mechanized-proofs.md | Coq + Iris | `#coq--iris` | 同文件锚点不存在: #coq--iris |
| docs\rust-ownership-decidability\formal-foundations\semantics\mechanized-proofs.md | *作者：Rust 形式化理论研究组* | `#作者rust-形式化理论研究组` | 同文件锚点不存在: #作者rust-形式化理论研究组 |
| docs\rust-ownership-decidability\formal-foundations\semantics\memory-model-semantics.md | 4.1.2 Box 语义 | `#412-box-语义` | 同文件锚点不存在: #412-box-语义 |
| docs\rust-ownership-decidability\formal-foundations\semantics\memory-model-semantics.md | 6.4.1 Cell 语义 | `#641-cell-语义` | 同文件锚点不存在: #641-cell-语义 |
| docs\rust-ownership-decidability\formal-foundations\semantics\memory-model-semantics.md | 6.4.2 RefCell 语义 | `#642-refcell-语义` | 同文件锚点不存在: #642-refcell-语义 |
| docs\rust-ownership-decidability\formal-foundations\semantics\semantics-equivalence-proof.md | 4.1 大步 ⇒ 小步 (→方向) | `#41-大步--小步-方向` | 同文件锚点不存在: #41-大步--小步-方向 |
| docs\rust-ownership-decidability\formal-foundations\semantics\semantics-equivalence-proof.md | 4.2 小步 ⇒ 大步 (←方向) | `#42-小步--大步-方向` | 同文件锚点不存在: #42-小步--大步-方向 |
| docs\rust-ownership-decidability\meta-model\01_abstract_syntax.md | Rust 所有权系统元模型 - 抽象语法 | `#rust-所有权系统元模型---抽象语法` | 同文件锚点不存在: #rust-所有权系统元模型---抽象语法 |
| docs\rust-ownership-decidability\meta-model\01_abstract_syntax.md | **最后更新**: 2026-03-05 | `#最后更新-2026-03-05` | 同文件锚点不存在: #最后更新-2026-03-05 |
| docs\rust-ownership-decidability\meta-model\02_semantic_domains.md | Rust 所有权系统元模型 - 语义域 | `#rust-所有权系统元模型---语义域` | 同文件锚点不存在: #rust-所有权系统元模型---语义域 |
| docs\rust-ownership-decidability\meta-model\02_semantic_domains.md | 5.2 值环境 (Value Environment / Stack) | `#52-值环境-value-environment--stack` | 同文件锚点不存在: #52-值环境-value-environment--stack |
| docs\rust-ownership-decidability\meta-model\02_semantic_domains.md | **最后更新**: 2026-03-05 | `#最后更新-2026-03-05` | 同文件锚点不存在: #最后更新-2026-03-05 |
| docs\rust-ownership-decidability\meta-model\03_judgments.md | Rust 所有权系统元模型 - 判断形式 | `#rust-所有权系统元模型---判断形式` | 同文件锚点不存在: #rust-所有权系统元模型---判断形式 |
| docs\rust-ownership-decidability\meta-model\03_judgments.md | **最后更新**: 2026-03-05 | `#最后更新-2026-03-05` | 同文件锚点不存在: #最后更新-2026-03-05 |
| docs\rust-ownership-decidability\meta-model\README.md | **状态**: ✅ 完成 | `#状态--完成` | 同文件锚点不存在: #状态--完成 |
| docs\rust-ownership-decidability\meta-model\rust-194-alignment.md | 4. Precise Capturing (`+ use<'lt>`) | `#4-precise-capturing--uselt` | 同文件锚点不存在: #4-precise-capturing--uselt |
| docs\rust-ownership-decidability\meta-model\RUST_194_COMPREHENSIVE_GUIDE.md | Rust 1.94 所有权形式化 - 完整指南 | `#rust-194-所有权形式化---完整指南` | 同文件锚点不存在: #rust-194-所有权形式化---完整指南 |
| docs\rust-ownership-decidability\meta-model\RUST_194_COMPREHENSIVE_GUIDE.md | 4. Precise Capturing (`+ use<'lt>`) | `#4-precise-capturing--uselt` | 同文件锚点不存在: #4-precise-capturing--uselt |
| docs\rust-ownership-decidability\practical-examples\comprehensive-code-collection.md | Rust 所有权系统 - 全面代码示例集 | `#rust-所有权系统---全面代码示例集` | 同文件锚点不存在: #rust-所有权系统---全面代码示例集 |
| docs\rust-ownership-decidability\practical-examples\comprehensive-code-collection.md | Rc | `#rc` | 同文件锚点不存在: #rc |
| docs\rust-ownership-decidability\practical-examples\comprehensive-code-collection.md | Arc\<Mutex\> | `#arcmutex` | 同文件锚点不存在: #arcmutex |
| docs\rust-ownership-decidability\practical-examples\comprehensive-code-collection.md | **所有代码经过 rustc 1.70+ 测试** ✅ | `#所有代码经过-rustc-170-测试-` | 同文件锚点不存在: #所有代码经过-rustc-170-测试- |
| docs\rust-ownership-decidability\progress\2026-03-05_initial_setup.md | 1. 文献调研与总结 ✅ | `#1-文献调研与总结-` | 同文件锚点不存在: #1-文献调研与总结- |
| docs\rust-ownership-decidability\progress\2026-03-05_initial_setup.md | 2. 研究计划制定 ✅ | `#2-研究计划制定-` | 同文件锚点不存在: #2-研究计划制定- |
| docs\rust-ownership-decidability\progress\2026-03-05_initial_setup.md | 3. 元模型初步定义 ✅ | `#3-元模型初步定义-` | 同文件锚点不存在: #3-元模型初步定义- |
| docs\rust-ownership-decidability\progress\2026-03-05_initial_setup.md | 4. 核心定理草拟 ✅ | `#4-核心定理草拟-` | 同文件锚点不存在: #4-核心定理草拟- |
| docs\rust-ownership-decidability\progress\2026-03-05_initial_setup.md | 5. 项目结构搭建 ✅ | `#5-项目结构搭建-` | 同文件锚点不存在: #5-项目结构搭建- |
| docs\rust-ownership-decidability\progress\2026-03-05_initial_setup.md | **下次报告**: 2026-03-12 | `#下次报告-2026-03-12` | 同文件锚点不存在: #下次报告-2026-03-12 |
| docs\rust-ownership-decidability\progress\2026-03-06_100_PERCENT_COMPLETION_FINAL_REPORT.md | Rust 所有权系统形式化分析 - 100% 完成报告 | `#rust-所有权系统形式化分析---100-完成报告` | 同文件锚点不存在: #rust-所有权系统形式化分析---100-完成报告 |
| docs\rust-ownership-decidability\progress\2026-03-06_100_PERCENT_COMPLETION_FINAL_REPORT.md | 1. 统一理论框架 ✅ | `#1-统一理论框架-` | 同文件锚点不存在: #1-统一理论框架- |
| docs\rust-ownership-decidability\progress\2026-03-06_100_PERCENT_COMPLETION_FINAL_REPORT.md | 2. 语义等价性证明 ✅ | `#2-语义等价性证明-` | 同文件锚点不存在: #2-语义等价性证明- |
| docs\rust-ownership-decidability\progress\2026-03-06_100_PERCENT_COMPLETION_FINAL_REPORT.md | 3. 类型-所有权统一理论 ✅ | `#3-类型-所有权统一理论-` | 同文件锚点不存在: #3-类型-所有权统一理论- |
| docs\rust-ownership-decidability\progress\2026-03-06_100_PERCENT_COMPLETION_FINAL_REPORT.md | 4. 元理论核心证明 ✅ | `#4-元理论核心证明-` | 同文件锚点不存在: #4-元理论核心证明- |
| docs\rust-ownership-decidability\progress\2026-03-06_100_PERCENT_COMPLETION_FINAL_REPORT.md | 5. Rust 1.94 特性形式化 ✅ | `#5-rust-194-特性形式化-` | 同文件锚点不存在: #5-rust-194-特性形式化- |
| docs\rust-ownership-decidability\progress\2026-03-06_100_PERCENT_COMPLETION_FINAL_REPORT.md | 框架完整性 ✅ | `#框架完整性-` | 同文件锚点不存在: #框架完整性- |
| docs\rust-ownership-decidability\progress\2026-03-06_100_PERCENT_COMPLETION_FINAL_REPORT.md | 形式化完整性 ✅ | `#形式化完整性-` | 同文件锚点不存在: #形式化完整性- |
| docs\rust-ownership-decidability\progress\2026-03-06_100_PERCENT_COMPLETION_FINAL_REPORT.md | 文档完整性 ✅ | `#文档完整性-` | 同文件锚点不存在: #文档完整性- |
| docs\rust-ownership-decidability\progress\2026-03-06_100_PERCENT_COMPLETION_FINAL_REPORT.md | *"构建 Rust 所有权系统的完整、严格、可机械化的形式化理论"* - 目标达成 | `#构建-rust-所有权系统的完整严格可机械化的形式化理论---目标达成` | 同文件锚点不存在: #构建-rust-所有权系统的完整严格可机械化的形式化理论---目标达成 |
| docs\rust-ownership-decidability\progress\2026-03-06_FORMAL_ANALYSIS_PROGRESS.md | 文档完整性检查 ✅ | `#文档完整性检查-` | 同文件锚点不存在: #文档完整性检查- |
| docs\rust-ownership-decidability\progress\2026-03-06_FORMAL_ANALYSIS_PROGRESS.md | 形式化完整性检查 ⚠️ | `#形式化完整性检查-️` | 同文件锚点不存在: #形式化完整性检查-️ |
| docs\rust-ownership-decidability\progress\2026-03-06_FORMAL_ANALYSIS_PROGRESS.md | *推进负责人: Rust-Ownership-Decidability Team* | `#推进负责人-rust-ownership-decidability-team` | 同文件锚点不存在: #推进负责人-rust-ownership-decidability-team |
| docs\rust-ownership-decidability\progress\2026-03-06_TRUE_100_PERCENT_COMPLETION_CERTIFICATION.md | Rust 所有权系统形式化分析 - 真正 100% 完成认证 | `#rust-所有权系统形式化分析---真正-100-完成认证` | 同文件锚点不存在: #rust-所有权系统形式化分析---真正-100-完成认证 |
| docs\rust-ownership-decidability\progress\2026-03-06_TRUE_100_PERCENT_COMPLETION_CERTIFICATION.md | 1. 统一理论框架 ✅ | `#1-统一理论框架-` | 同文件锚点不存在: #1-统一理论框架- |
| docs\rust-ownership-decidability\progress\2026-03-06_TRUE_100_PERCENT_COMPLETION_CERTIFICATION.md | 2. 语义等价性证明 ✅ | `#2-语义等价性证明-` | 同文件锚点不存在: #2-语义等价性证明- |
| docs\rust-ownership-decidability\progress\2026-03-06_TRUE_100_PERCENT_COMPLETION_CERTIFICATION.md | 3. 类型-所有权统一理论 ✅ | `#3-类型-所有权统一理论-` | 同文件锚点不存在: #3-类型-所有权统一理论- |
| docs\rust-ownership-decidability\progress\2026-03-06_TRUE_100_PERCENT_COMPLETION_CERTIFICATION.md | 4. 证明策略库 ✅ | `#4-证明策略库-` | 同文件锚点不存在: #4-证明策略库- |
| docs\rust-ownership-decidability\progress\2026-03-06_TRUE_100_PERCENT_COMPLETION_CERTIFICATION.md | 5. 元理论核心证明 (全部 Qed) ✅ | `#5-元理论核心证明-全部-qed-` | 同文件锚点不存在: #5-元理论核心证明-全部-qed- |
| docs\rust-ownership-decidability\progress\2026-03-06_TRUE_100_PERCENT_COMPLETION_CERTIFICATION.md | 6. Rust 1.94 特性形式化 (全部 Qed) ✅ | `#6-rust-194-特性形式化-全部-qed-` | 同文件锚点不存在: #6-rust-194-特性形式化-全部-qed- |
| docs\rust-ownership-decidability\progress\2026-03-06_TRUE_100_PERCENT_COMPLETION_CERTIFICATION.md | 形式化完整性 ✅ | `#形式化完整性-` | 同文件锚点不存在: #形式化完整性- |
| docs\rust-ownership-decidability\progress\2026-03-06_TRUE_100_PERCENT_COMPLETION_CERTIFICATION.md | 代码质量 ✅ | `#代码质量-` | 同文件锚点不存在: #代码质量- |
| docs\rust-ownership-decidability\progress\2026-03-06_TRUE_100_PERCENT_COMPLETION_CERTIFICATION.md | 文档完整性 ✅ | `#文档完整性-` | 同文件锚点不存在: #文档完整性- |
| docs\rust-ownership-decidability\progress\2026-03-06_TRUE_100_PERCENT_COMPLETION_CERTIFICATION.md | Coq 代码验证 ✅ | `#coq-代码验证-` | 同文件锚点不存在: #coq-代码验证- |
| docs\rust-ownership-decidability\progress\2026-03-06_TRUE_100_PERCENT_COMPLETION_CERTIFICATION.md | 文档验证 ✅ | `#文档验证-` | 同文件锚点不存在: #文档验证- |
| docs\rust-ownership-decidability\progress\2026-03-06_TRUE_100_PERCENT_COMPLETION_CERTIFICATION.md | *"构建 Rust 所有权系统的完整、严格、可机械化的形式化理论"* - **目标达成 ✅** | `#构建-rust-所有权系统的完整严格可机械化的形式化理论---目标达成-` | 同文件锚点不存在: #构建-rust-所有权系统的完整严格可机械化的形式化理论---目标达成- |
| docs\rust-ownership-decidability\progress\2026-03-06_week1_progress.md | **当前阶段**: Phase 1 (基础构建) - Week 1 of 12 | `#当前阶段-phase-1-基础构建---week-1-of-12` | 同文件锚点不存在: #当前阶段-phase-1-基础构建---week-1-of-12 |
| docs\rust-ownership-decidability\progress\2026-03-07_CONTENT_CREATION_BATCH_1.md | 内容创建批次 1 - 完成报告 | `#内容创建批次-1---完成报告` | 同文件锚点不存在: #内容创建批次-1---完成报告 |
| docs\rust-ownership-decidability\progress\2026-03-07_CONTENT_CREATION_BATCH_1.md | *新增内容: ~74 KB* | `#新增内容-74-kb` | 同文件锚点不存在: #新增内容-74-kb |
| docs\rust-ownership-decidability\progress\2026-03-07_CONTENT_CREATION_BATCH_2.md | 内容创建批次 2 - 完成报告 | `#内容创建批次-2---完成报告` | 同文件锚点不存在: #内容创建批次-2---完成报告 |
| docs\rust-ownership-decidability\progress\2026-03-07_CONTENT_CREATION_BATCH_2.md | 累积统计 (批次 1 + 批次 2) | `#累积统计-批次-1--批次-2` | 同文件锚点不存在: #累积统计-批次-1--批次-2 |
| docs\rust-ownership-decidability\progress\2026-03-07_CONTENT_CREATION_BATCH_2.md | *累积新增: 17 文件, ~112 KB* | `#累积新增-17-文件-112-kb` | 同文件锚点不存在: #累积新增-17-文件-112-kb |
| docs\rust-ownership-decidability\progress\2026-03-07_CONTENT_CREATION_BATCH_3.md | 内容创建批次 3 - 完成报告 | `#内容创建批次-3---完成报告` | 同文件锚点不存在: #内容创建批次-3---完成报告 |
| docs\rust-ownership-decidability\progress\2026-03-07_CONTENT_CREATION_BATCH_3.md | *累积新增: 20 文件, ~123 KB* | `#累积新增-20-文件-123-kb` | 同文件锚点不存在: #累积新增-20-文件-123-kb |
| docs\rust-ownership-decidability\progress\2026-03-07_daily_update.md | **代码总行数**: 2,341 行 Coq + 2,250 行文档 | `#代码总行数-2341-行-coq--2250-行文档` | 同文件锚点不存在: #代码总行数-2341-行-coq--2250-行文档 |
| docs\rust-ownership-decidability\progress\2026-03-07_FINAL_COMPLETION_REPORT.md | Rust 所有权可判定性项目 - 最终推进报告 | `#rust-所有权可判定性项目---最终推进报告` | 同文件锚点不存在: #rust-所有权可判定性项目---最终推进报告 |
| docs\rust-ownership-decidability\progress\2026-03-07_FINAL_COMPLETION_REPORT.md | *当前完成度: 77%* | `#当前完成度-77` | 同文件锚点不存在: #当前完成度-77 |
| docs\rust-ownership-decidability\progress\2026-03-08_weekend_sprint.md | 庆祝里程碑 🎉 | `#庆祝里程碑-` | 同文件锚点不存在: #庆祝里程碑- |
| docs\rust-ownership-decidability\progress\2026-03-08_weekend_sprint.md | **状态**: ahead of schedule ✅ | `#状态-ahead-of-schedule-` | 同文件锚点不存在: #状态-ahead-of-schedule- |
| docs\rust-ownership-decidability\progress\2026-03-09_50_PERCENT_MILESTONE.md | **下次目标**: 60% | `#下次目标-60` | 同文件锚点不存在: #下次目标-60 |
| docs\rust-ownership-decidability\progress\2026-03-09_CONTINUOUS_IMPROVEMENT_REPORT.md | 持续推进报告 - 2026-03-09 | `#持续推进报告---2026-03-09` | 同文件锚点不存在: #持续推进报告---2026-03-09 |
| docs\rust-ownership-decidability\progress\2026-03-09_CONTINUOUS_IMPROVEMENT_REPORT.md | 🛤️ 学习路径优化 | `#️-学习路径优化` | 同文件锚点不存在: #️-学习路径优化 |
| docs\rust-ownership-decidability\progress\2026-03-09_CONTINUOUS_IMPROVEMENT_REPORT.md | 快速入门路径 (4小时) → 更新 | `#快速入门路径-4小时--更新` | 同文件锚点不存在: #快速入门路径-4小时--更新 |
| docs\rust-ownership-decidability\progress\2026-03-09_CONTINUOUS_IMPROVEMENT_REPORT.md | 系统掌握路径 (2周) → 更新 | `#系统掌握路径-2周--更新` | 同文件锚点不存在: #系统掌握路径-2周--更新 |
| docs\rust-ownership-decidability\progress\2026-03-09_phase1_completion.md | **准备进入**: Phase 2 (可判定性证明深化) | `#准备进入-phase-2-可判定性证明深化` | 同文件锚点不存在: #准备进入-phase-2-可判定性证明深化 |
| docs\rust-ownership-decidability\progress\2026-03-10_MILESTONE_75_PERCENT.md | **下次目标**: 90% | `#下次目标-90` | 同文件锚点不存在: #下次目标-90 |
| docs\rust-ownership-decidability\progress\2026-03-11_MILESTONE_90_PERCENT.md | 1. Termination.v - 100% 完成 | `#1-terminationv---100-完成` | 同文件锚点不存在: #1-terminationv---100-完成 |
| docs\rust-ownership-decidability\progress\2026-03-11_MILESTONE_90_PERCENT.md | 2. Preservation.v - 95% 完成 | `#2-preservationv---95-完成` | 同文件锚点不存在: #2-preservationv---95-完成 |
| docs\rust-ownership-decidability\progress\2026-03-11_MILESTONE_90_PERCENT.md | 3. Progress.v - 95% 完成 | `#3-progressv---95-完成` | 同文件锚点不存在: #3-progressv---95-完成 |
| docs\rust-ownership-decidability\progress\2026-03-11_MILESTONE_90_PERCENT.md | 4. DecidabilityTheorems.v - 90% 完成 | `#4-decidabilitytheoremsv---90-完成` | 同文件锚点不存在: #4-decidabilitytheoremsv---90-完成 |
| docs\rust-ownership-decidability\progress\2026-03-11_MILESTONE_90_PERCENT.md | 定理 1: Borrow Checking 终止性 ✅ | `#定理-1-borrow-checking-终止性-` | 同文件锚点不存在: #定理-1-borrow-checking-终止性- |
| docs\rust-ownership-decidability\progress\2026-03-11_MILESTONE_90_PERCENT.md | 定理 2: 类型保持 ✅ | `#定理-2-类型保持-` | 同文件锚点不存在: #定理-2-类型保持- |
| docs\rust-ownership-decidability\progress\2026-03-11_MILESTONE_90_PERCENT.md | 定理 3: 进展 ✅ | `#定理-3-进展-` | 同文件锚点不存在: #定理-3-进展- |
| docs\rust-ownership-decidability\progress\2026-03-11_MILESTONE_90_PERCENT.md | 定理 4: 类型安全 ✅ | `#定理-4-类型安全-` | 同文件锚点不存在: #定理-4-类型安全- |
| docs\rust-ownership-decidability\progress\2026-03-11_MILESTONE_90_PERCENT.md | 定理 5: 可判定性 ✅ | `#定理-5-可判定性-` | 同文件锚点不存在: #定理-5-可判定性- |
| docs\rust-ownership-decidability\progress\2026-03-11_MILESTONE_90_PERCENT.md | **目标**: 100% (明天) | `#目标-100-明天` | 同文件锚点不存在: #目标-100-明天 |
| docs\rust-ownership-decidability\progress\COMPREHENSIVE_STATUS_REPORT.md | Rust 所有权系统可判定性 - 综合状态报告 | `#rust-所有权系统可判定性---综合状态报告` | 同文件锚点不存在: #rust-所有权系统可判定性---综合状态报告 |
| docs\rust-ownership-decidability\progress\COMPREHENSIVE_STATUS_REPORT.md | Day 3 (周一) - Termination 完成 | `#day-3-周一---termination-完成` | 同文件锚点不存在: #day-3-周一---termination-完成 |
| docs\rust-ownership-decidability\progress\COMPREHENSIVE_STATUS_REPORT.md | Day 4 (周二) - Preservation | `#day-4-周二---preservation` | 同文件锚点不存在: #day-4-周二---preservation |
| docs\rust-ownership-decidability\progress\COMPREHENSIVE_STATUS_REPORT.md | Day 5 (周三) - Progress | `#day-5-周三---progress` | 同文件锚点不存在: #day-5-周三---progress |
| docs\rust-ownership-decidability\progress\COMPREHENSIVE_STATUS_REPORT.md | Day 6 (周四) - 扩展 | `#day-6-周四---扩展` | 同文件锚点不存在: #day-6-周四---扩展 |
| docs\rust-ownership-decidability\progress\COMPREHENSIVE_STATUS_REPORT.md | Day 7 (周五) - 整理 | `#day-7-周五---整理` | 同文件锚点不存在: #day-7-周五---整理 |
| docs\rust-ownership-decidability\progress\COMPREHENSIVE_STATUS_REPORT.md | **下次报告**: 2026-03-13 (Week 2 结束) | `#下次报告-2026-03-13-week-2-结束` | 同文件锚点不存在: #下次报告-2026-03-13-week-2-结束 |
| docs\rust-ownership-decidability\progress\FINAL_100_PERCENT_COMPLETION_REPORT.md | � 100% 完成报告 🎉 | `#-100-完成报告-` | 同文件锚点不存在: #-100-完成报告- |
| docs\rust-ownership-decidability\progress\FINAL_100_PERCENT_COMPLETION_REPORT.md | **🎉 项目圆满完成！🎉**: | `#-项目圆满完成` | 同文件锚点不存在: #-项目圆满完成 |
| docs\rust-ownership-decidability\progress\FINAL_COMPLETION_REPORT_40_PERCENT.md | **状态**: 🚀 持续推进中 | `#状态--持续推进中` | 同文件锚点不存在: #状态--持续推进中 |
| docs\rust-ownership-decidability\progress\PROGRESS_TRACKING.md | 进度跟踪 - 最终版 | `#进度跟踪---最终版` | 同文件锚点不存在: #进度跟踪---最终版 |
| docs\rust-ownership-decidability\progress\PROGRESS_TRACKING.md | 代码质量: ✅ | `#代码质量-` | 同文件锚点不存在: #代码质量- |
| docs\rust-ownership-decidability\progress\PROGRESS_TRACKING.md | 理论严谨性: ✅ | `#理论严谨性-` | 同文件锚点不存在: #理论严谨性- |
| docs\rust-ownership-decidability\progress\PROGRESS_TRACKING.md | 可用性: ✅ | `#可用性-` | 同文件锚点不存在: #可用性- |
| docs\rust-ownership-decidability\progress\PROGRESS_TRACKING.md | *项目圆满完成！* | `#项目圆满完成` | 同文件锚点不存在: #项目圆满完成 |
| docs\rust-ownership-decidability\theorems\decidability_theorems.md | Rust 所有权系统可判定性 - 核心定理 | `#rust-所有权系统可判定性---核心定理` | 同文件锚点不存在: #rust-所有权系统可判定性---核心定理 |
| docs\rust-ownership-decidability\theorems\decidability_theorems.md | **最后更新**: 2026-03-05 | `#最后更新-2026-03-05` | 同文件锚点不存在: #最后更新-2026-03-05 |
| docs\rust-ownership-decidability\theorems\README.md | **状态**: ✅ 完成 | `#状态--完成` | 同文件锚点不存在: #状态--完成 |
| docs\rust-ownership-decidability\visualizations\concept-matrix.md | 通过合理选择类型和模式，可以在安全性和性能之间取得最佳平衡。 | `#通过合理选择类型和模式可以在安全性和性能之间取得最佳平衡` | 同文件锚点不存在: #通过合理选择类型和模式可以在安全性和性能之间取得最佳平衡 |
| docs\rust-ownership-decidability\visualizations\KNOWLEDGE_GRAPH_MINDMAP.md | Rust 所有权系统 - 知识图谱思维导图 | `#rust-所有权系统---知识图谱思维导图` | 同文件锚点不存在: #rust-所有权系统---知识图谱思维导图 |
| docs\rust-ownership-decidability\visualizations\KNOWLEDGE_GRAPH_MINDMAP.md | *这些图表使用 Mermaid 语法，可在支持 Mermaid 的 Markdown 查看器中渲染* | `#这些图表使用-mermaid-语法可在支持-mermaid-的-markdown-查看器中渲染` | 同文件锚点不存在: #这些图表使用-mermaid-语法可在支持-mermaid-的-markdown-查看器中渲染 |
| docs\rust-ownership-decidability\visualizations\ownership-comprehensive-mindmap.md | Rust所有权系统 - 综合思维导图 | `#rust所有权系统---综合思维导图` | 同文件锚点不存在: #rust所有权系统---综合思维导图 |
| docs\rust-ownership-decidability\visualizations\ownership-comprehensive-mindmap.md | **对齐版本**: Rust 1.93.1 | `#对齐版本-rust-1931` | 同文件锚点不存在: #对齐版本-rust-1931 |
| docs\rust-ownership-decidability\visualizations\decision-trees\type-selection-decision-tree.md | **对齐版本**: Rust 1.93.1 | `#对齐版本-rust-1931` | 同文件锚点不存在: #对齐版本-rust-1931 |
| docs\rust-ownership-decidability\visualizations\matrices\rust-safety-mechanisms-matrix.md | **更新日期**: 2026-03-05 | `#更新日期-2026-03-05` | 同文件锚点不存在: #更新日期-2026-03-05 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\00_COMPLETION_REPORT_100_PERCENT.md | Rust安全关键生态系统文档集 - 完成报告 ✅ | `#rust安全关键生态系统文档集---完成报告-` | 同文件锚点不存在: #rust安全关键生态系统文档集---完成报告- |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\00_COMPLETION_REPORT_100_PERCENT.md | 最终指标 ✅ | `#最终指标-` | 同文件锚点不存在: #最终指标- |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\00_COMPLETION_REPORT_100_PERCENT.md | 内容验证 ✅ | `#内容验证-` | 同文件锚点不存在: #内容验证- |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\00_COMPLETION_REPORT_100_PERCENT.md | 完整性检查 ✅ | `#完整性检查-` | 同文件锚点不存在: #完整性检查- |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\00_COMPLETION_REPORT_100_PERCENT.md | **质量保证**: 所有文档均经过技术审查，包含可运行的代码示例，可直接用于生产项目参考 | `#质量保证-所有文档均经过技术审查包含可运行的代码示例可直接用于生产项目参考` | 同文件锚点不存在: #质量保证-所有文档均经过技术审查包含可运行的代码示例可直接用于生产项目参考 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\00_RUST_SAFETY_CRITICAL_ECOSYSTEM_MASTER_INDEX.md | Rust安全关键生态系统文档集 - 主索引 | `#rust安全关键生态系统文档集---主索引` | 同文件锚点不存在: #rust安全关键生态系统文档集---主索引 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\00_RUST_SAFETY_CRITICAL_ECOSYSTEM_MASTER_INDEX.md | 01. 思维导图 (Mind Maps) - 全局视角 | `#01-思维导图-mind-maps---全局视角` | 同文件锚点不存在: #01-思维导图-mind-maps---全局视角 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\00_RUST_SAFETY_CRITICAL_ECOSYSTEM_MASTER_INDEX.md | 02. 多维矩阵 (Matrices) - 对比分析 | `#02-多维矩阵-matrices---对比分析` | 同文件锚点不存在: #02-多维矩阵-matrices---对比分析 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\00_RUST_SAFETY_CRITICAL_ECOSYSTEM_MASTER_INDEX.md | 03. 决策树 (Decision Trees) - 选择指南 | `#03-决策树-decision-trees---选择指南` | 同文件锚点不存在: #03-决策树-decision-trees---选择指南 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\00_RUST_SAFETY_CRITICAL_ECOSYSTEM_MASTER_INDEX.md | 04. 公理化推理 (Axiomatic Reasoning) - 形式化基础 | `#04-公理化推理-axiomatic-reasoning---形式化基础` | 同文件锚点不存在: #04-公理化推理-axiomatic-reasoning---形式化基础 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\00_RUST_SAFETY_CRITICAL_ECOSYSTEM_MASTER_INDEX.md | 05. 战略指导 (Strategic Guidance) - 高层规划 | `#05-战略指导-strategic-guidance---高层规划` | 同文件锚点不存在: #05-战略指导-strategic-guidance---高层规划 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\00_RUST_SAFETY_CRITICAL_ECOSYSTEM_MASTER_INDEX.md | 06. 路线图 (Roadmaps) - 前瞻规划 | `#06-路线图-roadmaps---前瞻规划` | 同文件锚点不存在: #06-路线图-roadmaps---前瞻规划 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\00_RUST_SAFETY_CRITICAL_ECOSYSTEM_MASTER_INDEX.md | 07. 案例研究 (Case Studies) - 实际应用 | `#07-案例研究-case-studies---实际应用` | 同文件锚点不存在: #07-案例研究-case-studies---实际应用 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\00_RUST_SAFETY_CRITICAL_ECOSYSTEM_MASTER_INDEX.md | 08. 培训材料 (Training) - 能力建设 | `#08-培训材料-training---能力建设` | 同文件锚点不存在: #08-培训材料-training---能力建设 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\00_RUST_SAFETY_CRITICAL_ECOSYSTEM_MASTER_INDEX.md | 09. 参考资料 (Reference) - 实用工具 | `#09-参考资料-reference---实用工具` | 同文件锚点不存在: #09-参考资料-reference---实用工具 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\00_RUST_SAFETY_CRITICAL_ECOSYSTEM_MASTER_INDEX.md | 10. 标准指南 (Standards) - 合规实施 | `#10-标准指南-standards---合规实施` | 同文件锚点不存在: #10-标准指南-standards---合规实施 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\00_RUST_SAFETY_CRITICAL_ECOSYSTEM_MASTER_INDEX.md | *本文档集已达到100%完成目标，是Rust安全关键系统开发的完整参考资料。* | `#本文档集已达到100完成目标是rust安全关键系统开发的完整参考资料` | 同文件锚点不存在: #本文档集已达到100完成目标是rust安全关键系统开发的完整参考资料 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\README_RUST_SAFETY_CRITICAL_ECOSYSTEM.md | Rust安全关键系统生态系统 - 完整文档集 | `#rust安全关键系统生态系统---完整文档集` | 同文件锚点不存在: #rust安全关键系统生态系统---完整文档集 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\README_RUST_SAFETY_CRITICAL_ECOSYSTEM.md | 学术领域 ✅ | `#学术领域-` | 同文件锚点不存在: #学术领域- |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\README_RUST_SAFETY_CRITICAL_ECOSYSTEM.md | 国际大学 ✅ | `#国际大学-` | 同文件锚点不存在: #国际大学- |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\README_RUST_SAFETY_CRITICAL_ECOSYSTEM.md | 工业标准 ✅ | `#工业标准-` | 同文件锚点不存在: #工业标准- |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\README_RUST_SAFETY_CRITICAL_ECOSYSTEM.md | 国防航天 ✅ | `#国防航天-` | 同文件锚点不存在: #国防航天- |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\README_RUST_SAFETY_CRITICAL_ECOSYSTEM.md | 认证工具链 ✅ | `#认证工具链-` | 同文件锚点不存在: #认证工具链- |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\README_RUST_SAFETY_CRITICAL_ECOSYSTEM.md | **🎉 100% 完成，欢迎使用！** | `#-100-完成欢迎使用` | 同文件锚点不存在: #-100-完成欢迎使用 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\01_mind_maps\10_academic_research_landscape.md | *学术研究是推动Rust在 safety-critical 领域应用的核心动力。* | `#学术研究是推动rust在-safety-critical-领域应用的核心动力` | 同文件锚点不存在: #学术研究是推动rust在-safety-critical-领域应用的核心动力 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\01_mind_maps\RUST_194_195_FEATURES_DEEP_DIVE.md | 1.1 array\_windows - 恒定长度窗口迭代 | `#11-array_windows---恒定长度窗口迭代` | 同文件锚点不存在: #11-array_windows---恒定长度窗口迭代 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\01_mind_maps\RUST_194_195_FEATURES_DEEP_DIVE.md | **基于**: Rust 1.94.0 (2026-03-05) | `#基于-rust-1940-2026-03-05` | 同文件锚点不存在: #基于-rust-1940-2026-03-05 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\02_matrices\COMPREHENSIVE_LANGUAGE_COMPARISON_MATRIX.md | *评分基于当前技术状态，技术快速发展中，建议定期重新评估。* | `#评分基于当前技术状态技术快速发展中建议定期重新评估` | 同文件锚点不存在: #评分基于当前技术状态技术快速发展中建议定期重新评估 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\02_matrices\10_rust_ownership_memory_model_matrix.md | **基于**: Rust 1.94.0 | `#基于-rust-1940` | 同文件锚点不存在: #基于-rust-1940 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\02_matrices\10_toolchain_evaluation_matrix.md | *工具链选择是项目成功的基础，建议充分评估后再做决定。* | `#工具链选择是项目成功的基础建议充分评估后再做决定` | 同文件锚点不存在: #工具链选择是项目成功的基础建议充分评估后再做决定 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\03_decision_trees\SAFETY_INTEGRITY_LEVEL_SELECTION_GUIDE.md | *安全完整性等级的正确选择是功能安全的基础，必须基于充分的风险分析。* | `#安全完整性等级的正确选择是功能安全的基础必须基于充分的风险分析` | 同文件锚点不存在: #安全完整性等级的正确选择是功能安全的基础必须基于充分的风险分析 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\04_axiomatic_reasoning\FORMAL_VERIFICATION_PRACTICAL_GUIDE.md | **基于**: Kani 0.40, Miri latest, Verus 0.1 | `#基于-kani-040-miri-latest-verus-01` | 同文件锚点不存在: #基于-kani-040-miri-latest-verus-01 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\05_strategic_guidance\ADOPTION_STRATEGY_AND_ROI_ANALYSIS.md | *本分析基于当前市场状况，实际结果可能因组织情况而异。* | `#本分析基于当前市场状况实际结果可能因组织情况而异` | 同文件锚点不存在: #本分析基于当前市场状况实际结果可能因组织情况而异 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\05_strategic_guidance\COMPREHENSIVE_RECOMMENDATIONS_AND_OPINIONS.md | Rust安全关键系统应用 - 综合意见与建议 | `#rust安全关键系统应用---综合意见与建议` | 同文件锚点不存在: #rust安全关键系统应用---综合意见与建议 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\06_roadmaps\EDUCATION_AND_TRAINING_ROADMAP.md | *持续学习是保持技术领先的关键。* | `#持续学习是保持技术领先的关键` | 同文件锚点不存在: #持续学习是保持技术领先的关键 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\06_roadmaps\RUST_2026_2030_ROADMAP_FORECAST.md | Rust + AI/ML | `#rust--aiml` | 同文件锚点不存在: #rust--aiml |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\06_roadmaps\RUST_2026_2030_ROADMAP_FORECAST.md | *免责声明：本路线图基于当前公开信息和趋势分析，实际发展可能因技术突破、市场变化或不可预见因素而有所不同。* | `#免责声明本路线图基于当前公开信息和趋势分析实际发展可能因技术突破市场变化或不可预见因素而有所不同` | 同文件锚点不存在: #免责声明本路线图基于当前公开信息和趋势分析实际发展可能因技术突破市场变化或不可预见因素而有所不同 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\06_roadmaps\SUSTAINABLE_ROADMAP_AND_PLANS.md | Rust安全关键系统 - 可持续推进路线图与计划 | `#rust安全关键系统---可持续推进路线图与计划` | 同文件锚点不存在: #rust安全关键系统---可持续推进路线图与计划 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\06_roadmaps\SUSTAINABLE_ROADMAP_AND_PLANS.md | **维护团队**: Rust安全关键系统工作组 | `#维护团队-rust安全关键系统工作组` | 同文件锚点不存在: #维护团队-rust安全关键系统工作组 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\06_roadmaps\10_technology_watch_and_emerging_trends.md | *保持对新技术的关注，但谨慎评估生产采用。* | `#保持对新技术的关注但谨慎评估生产采用` | 同文件锚点不存在: #保持对新技术的关注但谨慎评估生产采用 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\07_case_studies\CASE_STUDY_01_FERROCENE_CERTIFICATION.md | **状态**: 已完成 | `#状态-已完成` | 同文件锚点不存在: #状态-已完成 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\07_case_studies\CASE_STUDY_02_NASA_CFS_RUST.md | **技术就绪水平**: TRL 4-5 (实验室验证) | `#技术就绪水平-trl-4-5-实验室验证` | 同文件锚点不存在: #技术就绪水平-trl-4-5-实验室验证 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\07_case_studies\CASE_STUDY_03_AUTOMOTIVE_ECUS.md | **状态**: 概念验证/预研阶段 | `#状态-概念验证预研阶段` | 同文件锚点不存在: #状态-概念验证预研阶段 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\07_case_studies\10_case_study_04_medical_devices.md | **联系**: <medical-rust@example.com> | `#联系-medical-rustexamplecom` | 同文件锚点不存在: #联系-medical-rustexamplecom |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\07_case_studies\10_case_study_05_railway_signaling.md | **适用标准**: EN 50128:2011, EN 50129:2018, EN 50657:2019 | `#适用标准-en-501282011-en-501292018-en-506572019` | 同文件锚点不存在: #适用标准-en-501282011-en-501292018-en-506572019 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\07_case_studies\10_case_study_06_autonomous_driving.md | *本案例展示了Rust在高性能、高安全要求系统中的实际应用。* | `#本案例展示了rust在高性能高安全要求系统中的实际应用` | 同文件锚点不存在: #本案例展示了rust在高性能高安全要求系统中的实际应用 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\08_training\10_assessment_and_certification.md | *认证是能力的证明，持续学习是职业发展的基础。* | `#认证是能力的证明持续学习是职业发展的基础` | 同文件锚点不存在: #认证是能力的证明持续学习是职业发展的基础 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\08_training\CERTIFICATION_PREP_GUIDE.md | 表格A.1 - 技术措施 (Rust映射) | `#表格a1---技术措施-rust映射` | 同文件锚点不存在: #表格a1---技术措施-rust映射 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\08_training\CERTIFICATION_PREP_GUIDE.md | *祝考试顺利！* | `#祝考试顺利` | 同文件锚点不存在: #祝考试顺利 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\08_training\10_hands_on_lab_exercises.md | *实践是掌握Rust安全关键开发的最佳途径。* | `#实践是掌握rust安全关键开发的最佳途径` | 同文件锚点不存在: #实践是掌握rust安全关键开发的最佳途径 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\08_training\10_interactive_learning_resources.md | *学习是一个持续的过程，利用这些资源加速你的Rust安全关键开发之旅。* | `#学习是一个持续的过程利用这些资源加速你的rust安全关键开发之旅` | 同文件锚点不存在: #学习是一个持续的过程利用这些资源加速你的rust安全关键开发之旅 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\08_training\10_rust_safety_critical_training_program.md | **维护者**: Rust安全关键系统培训团队 | `#维护者-rust安全关键系统培训团队` | 同文件锚点不存在: #维护者-rust安全关键系统培训团队 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\09_reference\10_api_design_guidelines.md | *好的API设计是安全关键系统成功的基础。* | `#好的api设计是安全关键系统成功的基础` | 同文件锚点不存在: #好的api设计是安全关键系统成功的基础 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\09_reference\CHECKLISTS_AND_TEMPLATES.md | Rust安全关键系统 - 检查清单与模板 | `#rust安全关键系统---检查清单与模板` | 同文件锚点不存在: #rust安全关键系统---检查清单与模板 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\09_reference\CHECKLISTS_AND_TEMPLATES.md | **维护者**: Rust安全关键系统工作组 | `#维护者-rust安全关键系统工作组` | 同文件锚点不存在: #维护者-rust安全关键系统工作组 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\09_reference\10_community_and_contributing.md | *社区的力量在于每个人的参与和贡献。* | `#社区的力量在于每个人的参与和贡献` | 同文件锚点不存在: #社区的力量在于每个人的参与和贡献 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\09_reference\COMPREHENSIVE_INTERNATIONAL_ALIGNMENT_COMPLETION_REPORT.md | Rust生态系统全面国际化对齐 - 完成报告 | `#rust生态系统全面国际化对齐---完成报告` | 同文件锚点不存在: #rust生态系统全面国际化对齐---完成报告 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\09_reference\COMPREHENSIVE_INTERNATIONAL_ALIGNMENT_COMPLETION_REPORT.md | **联系邮箱**: <rust-safety-critical@example.com> | `#联系邮箱-rust-safety-criticalexamplecom` | 同文件锚点不存在: #联系邮箱-rust-safety-criticalexamplecom |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\09_reference\10_deployment_and_maintenance_guide.md | *良好的部署和维护实践是系统长期可靠运行的保障。* | `#良好的部署和维护实践是系统长期可靠运行的保障` | 同文件锚点不存在: #良好的部署和维护实践是系统长期可靠运行的保障 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\09_reference\FAQ_AND_TROUBLESHOOTING.md | Rust安全关键系统 - 常见问题与故障排除 | `#rust安全关键系统---常见问题与故障排除` | 同文件锚点不存在: #rust安全关键系统---常见问题与故障排除 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\09_reference\FAQ_AND_TROUBLESHOOTING.md | *找不到答案？提交新问题到项目issue跟踪器。* | `#找不到答案提交新问题到项目issue跟踪器` | 同文件锚点不存在: #找不到答案提交新问题到项目issue跟踪器 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\09_reference\FFI_INTEGRATION_GUIDE.md | FFI集成指南 - 安全关键系统 | `#ffi集成指南---安全关键系统` | 同文件锚点不存在: #ffi集成指南---安全关键系统 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\09_reference\FFI_INTEGRATION_GUIDE.md | *FFI是安全关键系统中的高风险区域，必须经过严格审查。* | `#ffi是安全关键系统中的高风险区域必须经过严格审查` | 同文件锚点不存在: #ffi是安全关键系统中的高风险区域必须经过严格审查 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\09_reference\GLOSSARY_AND_DEFINITIONS.md | Rust安全关键系统 - 术语表与定义 | `#rust安全关键系统---术语表与定义` | 同文件锚点不存在: #rust安全关键系统---术语表与定义 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\09_reference\GLOSSARY_AND_DEFINITIONS.md | *术语建议？提交到项目文档仓库。* | `#术语建议提交到项目文档仓库` | 同文件锚点不存在: #术语建议提交到项目文档仓库 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\09_reference\10_metrics_and_measurement_guide.md | *度量是改进的基础，建议定期回顾和调整。* | `#度量是改进的基础建议定期回顾和调整` | 同文件锚点不存在: #度量是改进的基础建议定期回顾和调整 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\09_reference\10_performance_optimization_guide.md | *性能优化应在保证安全性的前提下进行。* | `#性能优化应在保证安全性的前提下进行` | 同文件锚点不存在: #性能优化应在保证安全性的前提下进行 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\09_reference\PROJECT_TEMPLATES.md | *使用这些模板快速启动您的安全关键Rust项目。* | `#使用这些模板快速启动您的安全关键rust项目` | 同文件锚点不存在: #使用这些模板快速启动您的安全关键rust项目 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\09_reference\QUICK_REFERENCE_CARD.md | 将此卡片打印并放在工作台上，随时查阅 | `#将此卡片打印并放在工作台上随时查阅` | 同文件锚点不存在: #将此卡片打印并放在工作台上随时查阅 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\09_reference\RUST_SAFETY_CRITICAL_CODING_GUIDELINES.md | *所有开发人员必须遵守此规范，审查时作为检查依据。* | `#所有开发人员必须遵守此规范审查时作为检查依据` | 同文件锚点不存在: #所有开发人员必须遵守此规范审查时作为检查依据 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\09_reference\SAFETY_CRITICAL_CHECKLISTS.md | *根据项目实际情况调整使用此检查表。* | `#根据项目实际情况调整使用此检查表` | 同文件锚点不存在: #根据项目实际情况调整使用此检查表 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\09_reference\10_security_audit_guide.md | *安全是持续的过程，不是一次性的活动。* | `#安全是持续的过程不是一次性的活动` | 同文件锚点不存在: #安全是持续的过程不是一次性的活动 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\09_reference\10_supply_chain_security_guide.md | *供应链安全是现代软件开发的关键组成部分。* | `#供应链安全是现代软件开发的关键组成部分` | 同文件锚点不存在: #供应链安全是现代软件开发的关键组成部分 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\09_reference\TOOLCHAIN_SETUP_GUIDE.md | *定期更新此文档以反映工具链的最新发展。* | `#定期更新此文档以反映工具链的最新发展` | 同文件锚点不存在: #定期更新此文档以反映工具链的最新发展 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\09_reference\TOOLS_CONFIGURATION_GUIDE.md | Rust安全关键系统 - 工具配置指南 | `#rust安全关键系统---工具配置指南` | 同文件锚点不存在: #rust安全关键系统---工具配置指南 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\09_reference\TOOLS_CONFIGURATION_GUIDE.md | **维护者**: Rust安全关键系统工作组 | `#维护者-rust安全关键系统工作组` | 同文件锚点不存在: #维护者-rust安全关键系统工作组 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\09_reference\TROUBLESHOOTING_AND_DEBUGGING_GUIDE.md | *持续更新中，欢迎贡献更多故障排除案例。* | `#持续更新中欢迎贡献更多故障排除案例` | 同文件锚点不存在: #持续更新中欢迎贡献更多故障排除案例 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\10_standards\10_do_178c_rust_compliance_pathway.md | *本文档应与DO-178C标准原文配合使用。* | `#本文档应与do-178c标准原文配合使用` | 同文件锚点不存在: #本文档应与do-178c标准原文配合使用 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\10_standards\IEC_61508_RUST_IMPLEMENTATION_GUIDE.md | Table A.1 - 设计和编码技术 | `#table-a1---设计和编码技术` | 同文件锚点不存在: #table-a1---设计和编码技术 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\10_standards\IEC_61508_RUST_IMPLEMENTATION_GUIDE.md | Table A.2 - 数据导向技术 | `#table-a2---数据导向技术` | 同文件锚点不存在: #table-a2---数据导向技术 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\10_standards\IEC_61508_RUST_IMPLEMENTATION_GUIDE.md | *本文档应与IEC 61508标准原文配合使用。* | `#本文档应与iec-61508标准原文配合使用` | 同文件锚点不存在: #本文档应与iec-61508标准原文配合使用 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\10_standards\MISRA_C_2025_ADDENDUM_6_GUIDE.md | MISRA C:2025 Addendum 6 - Rust应用指南 | `#misra-c2025-addendum-6---rust应用指南` | 同文件锚点不存在: #misra-c2025-addendum-6---rust应用指南 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\10_standards\MISRA_C_2025_ADDENDUM_6_GUIDE.md | 7. 指针和数组 (Rules 11.x, 18.x) - 关键章节 | `#7-指针和数组-rules-11x-18x---关键章节` | 同文件锚点不存在: #7-指针和数组-rules-11x-18x---关键章节 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\10_standards\MISRA_C_2025_ADDENDUM_6_GUIDE.md | 8. 内存管理 (Rules 21.x, 22.x) - Rust强项 | `#8-内存管理-rules-21x-22x---rust强项` | 同文件锚点不存在: #8-内存管理-rules-21x-22x---rust强项 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\10_standards\MISRA_C_2025_ADDENDUM_6_GUIDE.md | **基于**: MISRA C:2025 Addendum 6 (March 2025) | `#基于-misra-c2025-addendum-6-march-2025` | 同文件锚点不存在: #基于-misra-c2025-addendum-6-march-2025 |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\10_standards\10_regulatory_landscape_and_approvals.md | *监管环境快速发展，建议定期更新策略。* | `#监管环境快速发展建议定期更新策略` | 同文件锚点不存在: #监管环境快速发展建议定期更新策略 |
| docs\templates\10_versioned_doc_template.md | ⚙️ 配置与选项 | `#️-配置与选项` | 同文件锚点不存在: #️-配置与选项 |
| docs\templates\10_versioned_doc_template.md | ⚠️ 注意事项 | `#️-注意事项` | 同文件锚点不存在: #️-注意事项 |
| docs\templates\10_versioned_doc_template.md | *本文档遵循 Rust 学习项目版本化规范* | `#本文档遵循-rust-学习项目版本化规范` | 同文件锚点不存在: #本文档遵循-rust-学习项目版本化规范 |

### 文件不存在 (636个)

| 源文件 | 链接文本 | 链接路径 | 问题 |
|:---|:---|:---|:---|
| docs\00_meta\analysis\RUST_2026_PROJECT_GOALS_MONTHLY_TRACKING.md | `crates/c03_control_fn/examples/cargo_script_demo.rs` | `../../crates/c03_control_fn/examples/cargo_script_demo.rs` | 文件不存在: docs\crates\c03_control_fn\examples\cargo_script_demo.rs |
| docs\00_meta\analysis\RUST_2026_PROJECT_GOALS_MONTHLY_TRACKING.md | `crates/c10_networks/src/cargo_semver_checks_guide.rs` | `../../crates/c10_networks/src/cargo_semver_checks_guide.rs` | 文件不存在: docs\crates\c10_networks\src\cargo_semver_checks_guide.rs |
| docs\00_meta\analysis\RUST_2026_PROJECT_GOALS_MONTHLY_TRACKING.md | `crates/c03_control_fn/examples/cargo_script_demo.rs` | `../../crates/c03_control_fn/examples/cargo_script_demo.rs` | 文件不存在: docs\crates\c03_control_fn\examples\cargo_script_demo.rs |
| docs\00_meta\analysis\RUST_2026_PROJECT_GOALS_MONTHLY_TRACKING.md | `crates/c10_networks/src/cargo_semver_checks_guide.rs` | `../../crates/c10_networks/src/cargo_semver_checks_guide.rs` | 文件不存在: docs\crates\c10_networks\src\cargo_semver_checks_guide.rs |
| docs\02_reference\quick_reference\process_management_cheatsheet.md | performance_optimization_demo.rs | `../../../crates/c07_process/examples/performance_optimization_demo.rs` | 文件不存在: crates\c07_process\examples\performance_optimization_demo.rs |
| docs\02_reference\quick_reference\testing_cheatsheet.md | `tests/cross_module_integration_tests.rs` | `../../../tests/cross_module_integration_tests.rs` | 文件不存在: tests\cross_module_integration_tests.rs |
| docs\02_reference\quick_reference\threads_concurrency_cheatsheet.md | performance_optimization_demo.rs | `../../../crates/c05_threads/examples/performance_optimization_demo.rs` | 文件不存在: crates\c05_threads\examples\performance_optimization_demo.rs |
| docs\02_reference\quick_reference\wasm_cheatsheet.md | Rust 1.91/1.92 特性演示 | `../../../crates/c12_wasm/examples/rust_191_features_demo.rs` | 文件不存在: crates\c12_wasm\examples\rust_191_features_demo.rs |
| docs\02_reference\quick_reference\wasm_cheatsheet.md | rust_192_features_demo.rs | `../../../crates/c12_wasm/examples/rust_192_features_demo.rs` | 文件不存在: crates\c12_wasm\examples\rust_192_features_demo.rs |
| docs\03_guides\03_libp2p_guide.md | Network Programming | `../crates/c10_networks/` | 文件不存在: docs\crates\c10_networks |
| docs\03_guides\03_quic_http3_guide.md | Network Programming | `../crates/c10_networks/` | 文件不存在: docs\crates\c10_networks |
| docs\06_toolchain\06_parallel_frontend.md | Build Systems | `../concept/07_future/` | 文件不存在: docs\concept\07_future |
| docs\06_toolchain\README.md | Workspace 管理 | `./02_cargo_workspace_guide.md#2-创建和配置-workspace` | 文件不存在: docs\06_toolchain\02_cargo_workspace_guide.md |
| docs\06_toolchain\README.md | 依赖管理 | `./02_cargo_workspace_guide.md#3-依赖管理` | 文件不存在: docs\06_toolchain\02_cargo_workspace_guide.md |
| docs\06_toolchain\README.md | Feature 管理 | `./02_cargo_workspace_guide.md#5-feature-管理` | 文件不存在: docs\06_toolchain\02_cargo_workspace_guide.md |
| docs\06_toolchain\README.md | 构建优化 | `./02_cargo_workspace_guide.md#7-构建优化` | 文件不存在: docs\06_toolchain\02_cargo_workspace_guide.md |
| docs\06_toolchain\README.md | 02_cargo_workspace_guide.md#2 | `./02_cargo_workspace_guide.md#2-创建和配置-workspace` | 文件不存在: docs\06_toolchain\02_cargo_workspace_guide.md |
| docs\06_toolchain\README.md | 02_cargo_workspace_guide.md#3.3 | `./02_cargo_workspace_guide.md#33-依赖版本统一` | 文件不存在: docs\06_toolchain\02_cargo_workspace_guide.md |
| docs\archive\README.md | DOCS_STRUCTURE_OVERVIEW | `../DOCS_STRUCTURE_OVERVIEW.md` | 文件不存在: docs\DOCS_STRUCTURE_OVERVIEW.md |
| docs\archive\README.md | DOCS_STRUCTURE_OVERVIEW | `../DOCS_STRUCTURE_OVERVIEW.md` | 文件不存在: docs\DOCS_STRUCTURE_OVERVIEW.md |
| docs\archive\README.md | FINAL_PUSH_COMPLETE_SUMMARY_2026_01_27.md | `root_completion_reports/FINAL_PUSH_COMPLETE_SUMMARY_2026_01_27.md` | 文件不存在: docs\archive\root_completion_reports\FINAL_PUSH_COMPLETE_SUMMARY_2026_01_27.md |
| docs\archive\2026_03_reorganization\BEST_PRACTICES.md | README.md | `./README.md` | 文件不存在: docs\archive\2026_03_reorganization\README.md |
| docs\archive\2026_03_reorganization\BEST_PRACTICES.md | CONTRIBUTING.md | `./CONTRIBUTING.md` | 文件不存在: docs\archive\2026_03_reorganization\CONTRIBUTING.md |
| docs\archive\2026_03_reorganization\BEST_PRACTICES.md | TROUBLESHOOTING.md | `./TROUBLESHOOTING.md` | 文件不存在: docs\archive\2026_03_reorganization\TROUBLESHOOTING.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | README.md | `./README.md` | 文件不存在: docs\archive\2026_03_reorganization\README.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | READING_GUIDE.md | `./READING_GUIDE.md` | 文件不存在: docs\archive\2026_03_reorganization\READING_GUIDE.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | FINAL_MASTER_INDEX.md | `./FINAL_MASTER_INDEX.md` | 文件不存在: docs\archive\2026_03_reorganization\FINAL_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | MASTER_COMPREHENSIVE_ANALYSIS.md | `./MASTER_COMPREHENSIVE_ANALYSIS.md` | 文件不存在: docs\archive\2026_03_reorganization\MASTER_COMPREHENSIVE_ANALYSIS.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | ownership-deep-dive.md | `01-core-concepts/detailed-concepts/ownership-deep-dive.md` | 文件不存在: docs\archive\2026_03_reorganization\01-core-concepts\detailed-concepts\ownership-deep-dive.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | ownership-concept-card.md | `01-core-concepts/short-concepts/ownership-concept-card.md` | 文件不存在: docs\archive\2026_03_reorganization\01-core-concepts\short-concepts\ownership-concept-card.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | borrowing-in-depth.md | `01-core-concepts/detailed-concepts/borrowing-in-depth.md` | 文件不存在: docs\archive\2026_03_reorganization\01-core-concepts\detailed-concepts\borrowing-in-depth.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | borrowing-concept-card.md | `01-core-concepts/short-concepts/borrowing-concept-card.md` | 文件不存在: docs\archive\2026_03_reorganization\01-core-concepts\short-concepts\borrowing-concept-card.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | lifetimes-mastery.md | `01-core-concepts/detailed-concepts/lifetimes-mastery.md` | 文件不存在: docs\archive\2026_03_reorganization\01-core-concepts\detailed-concepts\lifetimes-mastery.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | lifetime-concept-card.md | `01-core-concepts/short-concepts/lifetime-concept-card.md` | 文件不存在: docs\archive\2026_03_reorganization\01-core-concepts\short-concepts\lifetime-concept-card.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | formal-foundations/models/ | `formal-foundations/models/` | 文件不存在: docs\archive\2026_03_reorganization\formal-foundations\models |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | formal-foundations/semantics/ | `formal-foundations/semantics/` | 文件不存在: docs\archive\2026_03_reorganization\formal-foundations\semantics |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | formal-foundations/proofs/ | `formal-foundations/proofs/` | 文件不存在: docs\archive\2026_03_reorganization\formal-foundations\proofs |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | coq-formalization/ | `coq-formalization/` | 文件不存在: docs\archive\2026_03_reorganization\coq-formalization |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | case-studies/README.md | `case-studies/README.md` | 文件不存在: docs\archive\2026_03_reorganization\case-studies\README.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | case-studies/embedded/README.md | `case-studies/embedded/README.md` | 文件不存在: docs\archive\2026_03_reorganization\case-studies\embedded\README.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | case-studies/blockchain/README.md | `case-studies/blockchain/README.md` | 文件不存在: docs\archive\2026_03_reorganization\case-studies\blockchain\README.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | case-studies/wasm/README.md | `case-studies/wasm/README.md` | 文件不存在: docs\archive\2026_03_reorganization\case-studies\wasm\README.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | ownership-types.md | `formal-foundations/models/ownership-types.md` | 文件不存在: docs\archive\2026_03_reorganization\formal-foundations\models\ownership-types.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | ownership-deep-dive.md | `01-core-concepts/detailed-concepts/ownership-deep-dive.md` | 文件不存在: docs\archive\2026_03_reorganization\01-core-concepts\detailed-concepts\ownership-deep-dive.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | COMPLETE_EXAMPLES_AND_COUNTEREXAMPLES.md | `./COMPLETE_EXAMPLES_AND_COUNTEREXAMPLES.md` | 文件不存在: docs\archive\2026_03_reorganization\COMPLETE_EXAMPLES_AND_COUNTEREXAMPLES.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | borrow-semantics.md | `formal-foundations/models/borrow-semantics.md` | 文件不存在: docs\archive\2026_03_reorganization\formal-foundations\models\borrow-semantics.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | borrowing-in-depth.md | `01-core-concepts/detailed-concepts/borrowing-in-depth.md` | 文件不存在: docs\archive\2026_03_reorganization\01-core-concepts\detailed-concepts\borrowing-in-depth.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | ReborrowComplete.v | `coq-formalization/theories/Advanced/ReborrowComplete.v` | 文件不存在: docs\archive\2026_03_reorganization\coq-formalization\theories\Advanced\ReborrowComplete.v |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | lifetime-logic.md | `formal-foundations/models/lifetime-logic.md` | 文件不存在: docs\archive\2026_03_reorganization\formal-foundations\models\lifetime-logic.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | lifetimes-mastery.md | `01-core-concepts/detailed-concepts/lifetimes-mastery.md` | 文件不存在: docs\archive\2026_03_reorganization\01-core-concepts\detailed-concepts\lifetimes-mastery.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | MetatheoryTermination.v | `coq-formalization/theories/Advanced/MetatheoryTermination.v` | 文件不存在: docs\archive\2026_03_reorganization\coq-formalization\theories\Advanced\MetatheoryTermination.v |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | type-system-formalization.md | `formal-foundations/semantics/type-system-formalization.md` | 文件不存在: docs\archive\2026_03_reorganization\formal-foundations\semantics\type-system-formalization.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | TypeSystem.v | `coq-formalization/theories/Typing/TypeSystem.v` | 文件不存在: docs\archive\2026_03_reorganization\coq-formalization\theories\Typing\TypeSystem.v |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | THEOREM_INTUITIONS.md | `./THEOREM_INTUITIONS.md` | 文件不存在: docs\archive\2026_03_reorganization\THEOREM_INTUITIONS.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | MetatheoryTermination.v | `coq-formalization/theories/Advanced/MetatheoryTermination.v` | 文件不存在: docs\archive\2026_03_reorganization\coq-formalization\theories\Advanced\MetatheoryTermination.v |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | decidability_theorems.md | `theorems/decidability_theorems.md` | 文件不存在: docs\archive\2026_03_reorganization\theorems\decidability_theorems.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | MetatheoryDecidability.v | `coq-formalization/theories/Advanced/MetatheoryDecidability.v` | 文件不存在: docs\archive\2026_03_reorganization\coq-formalization\theories\Advanced\MetatheoryDecidability.v |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | memory-safety-proof.md | `formal-foundations/proofs/memory-safety-proof.md` | 文件不存在: docs\archive\2026_03_reorganization\formal-foundations\proofs\memory-safety-proof.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | MetatheoryKeyProofs.v | `coq-formalization/theories/Advanced/MetatheoryKeyProofs.v` | 文件不存在: docs\archive\2026_03_reorganization\coq-formalization\theories\Advanced\MetatheoryKeyProofs.v |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | std-vec-formal-analysis.md | `case-studies/std-vec-formal-analysis.md` | 文件不存在: docs\archive\2026_03_reorganization\case-studies\std-vec-formal-analysis.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | std-string-formal-analysis.md | `case-studies/std-string-formal-analysis.md` | 文件不存在: docs\archive\2026_03_reorganization\case-studies\std-string-formal-analysis.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | std-hashmap-formal-analysis.md | `case-studies/std-hashmap-formal-analysis.md` | 文件不存在: docs\archive\2026_03_reorganization\case-studies\std-hashmap-formal-analysis.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | std-iterator-formal-analysis.md | `case-studies/std-iterator-formal-analysis.md` | 文件不存在: docs\archive\2026_03_reorganization\case-studies\std-iterator-formal-analysis.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | std-smart-pointers-formal-analysis.md | `case-studies/std-smart-pointers-formal-analysis.md` | 文件不存在: docs\archive\2026_03_reorganization\case-studies\std-smart-pointers-formal-analysis.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | tokio-runtime-formal-analysis.md | `case-studies/tokio-runtime-formal-analysis.md` | 文件不存在: docs\archive\2026_03_reorganization\case-studies\tokio-runtime-formal-analysis.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | async-std-formal-analysis.md | `case-studies/async-std-formal-analysis.md` | 文件不存在: docs\archive\2026_03_reorganization\case-studies\async-std-formal-analysis.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | futures-crate-formal-analysis.md | `case-studies/futures-crate-formal-analysis.md` | 文件不存在: docs\archive\2026_03_reorganization\case-studies\futures-crate-formal-analysis.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/DOCS_STRUCTURE_OVERVIEW.md | `docs/DOCS_STRUCTURE_OVERVIEW.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\DOCS_STRUCTURE_OVERVIEW.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/DOCS_STRUCTURE_OVERVIEW.md | `docs/DOCS_STRUCTURE_OVERVIEW.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\DOCS_STRUCTURE_OVERVIEW.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/01_learning/LEARNING_PATH_PLANNING.md | `docs/01_learning/LEARNING_PATH_PLANNING.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\01_learning\LEARNING_PATH_PLANNING.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c02_type_system/docs/ONE_PAGE_SUMMARY.md | `crates/c02_type_system/docs/ONE_PAGE_SUMMARY.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c02_type_system\docs\ONE_PAGE_SUMMARY.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c04_generic/docs/ONE_PAGE_SUMMARY.md | `crates/c04_generic/docs/ONE_PAGE_SUMMARY.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c04_generic\docs\ONE_PAGE_SUMMARY.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/rust-ownership-decidability/CROSS_REFERENCE_VERIFICATION_SUMMARY.md | `docs/rust-ownership-decidability/CROSS_REFERENCE_VERIFICATION_SUMMARY.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\rust-ownership-decidability\CROSS_REFERENCE_VERIFICATION_SUMMARY.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/rust-ownership-decidability/MASTER_INDEX_AUTO.md | `docs/rust-ownership-decidability/MASTER_INDEX_AUTO.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\rust-ownership-decidability\MASTER_INDEX_AUTO.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/rust-ownership-decidability/MASTER_INDEX_AUTO.md | `docs/rust-ownership-decidability/MASTER_INDEX_AUTO.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\rust-ownership-decidability\MASTER_INDEX_AUTO.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/rust-ownership-decidability/MASTER_INDEX_AUTO.md | `docs/rust-ownership-decidability/MASTER_INDEX_AUTO.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\rust-ownership-decidability\MASTER_INDEX_AUTO.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/rust-ownership-decidability/MASTER_INDEX_AUTO.md | `docs/rust-ownership-decidability/MASTER_INDEX_AUTO.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\rust-ownership-decidability\MASTER_INDEX_AUTO.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/DOCS_STRUCTURE_OVERVIEW.md | `docs/DOCS_STRUCTURE_OVERVIEW.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\DOCS_STRUCTURE_OVERVIEW.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/COMPREHENSIVE_COMPLETION_STATUS_2026_02_23.md | `docs/COMPREHENSIVE_COMPLETION_STATUS_2026_02_23.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\COMPREHENSIVE_COMPLETION_STATUS_2026_02_23.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/DOCS_STRUCTURE_OVERVIEW.md | `docs/DOCS_STRUCTURE_OVERVIEW.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\DOCS_STRUCTURE_OVERVIEW.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | README.en.md | `./README.en.md` | 文件不存在: docs\archive\2026_03_reorganization\README.en.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | README.en.md | `./README.en.md` | 文件不存在: docs\archive\2026_03_reorganization\README.en.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | README.en.md | `./README.en.md` | 文件不存在: docs\archive\2026_03_reorganization\README.en.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c07_process/docs/tier_01_foundations/02_主索引导航.md | `crates/c07_process/docs/tier_01_foundations/02_主索引导航.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c07_process\docs\tier_01_foundations\02_主索引导航.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c09_design_pattern/README.md | `crates/c09_design_pattern/README.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c09_design_pattern\README.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | BROKEN_LINKS_REPORT.md | `./BROKEN_LINKS_REPORT.md` | 文件不存在: docs\archive\2026_03_reorganization\BROKEN_LINKS_REPORT.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c01_ownership_borrow_scope/docs/tier_04_advanced/04_内存布局优化.md | `crates/c01_ownership_borrow_scope/docs/tier_04_advanced/04_内存布局优化.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c01_ownership_borrow_scope\docs\tier_04_advanced\04_内存布局优化.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c02_type_system/docs/00_MASTER_INDEX.en.md | `crates/c02_type_system/docs/00_MASTER_INDEX.en.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c02_type_system\docs\00_MASTER_INDEX.en.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c02_type_system/docs/ONE_PAGE_SUMMARY.md | `crates/c02_type_system/docs/ONE_PAGE_SUMMARY.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c02_type_system\docs\ONE_PAGE_SUMMARY.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c02_type_system/docs/tier_04_advanced/README.md | `crates/c02_type_system/docs/tier_04_advanced/README.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c02_type_system\docs\tier_04_advanced\README.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c01_ownership_borrow_scope/README.md | `crates/c01_ownership_borrow_scope/README.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c01_ownership_borrow_scope\README.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c01_ownership_borrow_scope/README.md | `crates/c01_ownership_borrow_scope/README.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c01_ownership_borrow_scope\README.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md | `crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c01_ownership_borrow_scope\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md | `crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c01_ownership_borrow_scope\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md | `crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c01_ownership_borrow_scope\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c02_type_system/README.md | `crates/c02_type_system/README.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c02_type_system\README.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c02_type_system/README.md | `crates/c02_type_system/README.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c02_type_system\README.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c03_control_fn/README.md | `crates/c03_control_fn/README.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c03_control_fn\README.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c04_generic/README.md | `crates/c04_generic/README.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c04_generic\README.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c04_generic/README.md | `crates/c04_generic/README.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c04_generic\README.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c01_ownership_borrow_scope/docs/README.md | `crates/c01_ownership_borrow_scope/docs/README.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c01_ownership_borrow_scope\docs\README.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/DOCS_STRUCTURE_OVERVIEW.md | `docs/DOCS_STRUCTURE_OVERVIEW.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\DOCS_STRUCTURE_OVERVIEW.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/archive/process_reports/2026_02/TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md | `docs/archive/process_reports/2026_02/TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\archive\process_reports\2026_02\TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/research_notes/FAQ.md | `docs/research_notes/FAQ.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\research_notes\FAQ.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/research_notes/GETTING_STARTED.md | `docs/research_notes/GETTING_STARTED.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\research_notes\GETTING_STARTED.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.en.md | `crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.en.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c01_ownership_borrow_scope\docs\00_MASTER_INDEX.en.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c01_ownership_borrow_scope/docs/ONE_PAGE_SUMMARY.md | `crates/c01_ownership_borrow_scope/docs/ONE_PAGE_SUMMARY.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c01_ownership_borrow_scope\docs\ONE_PAGE_SUMMARY.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/FINAL_LINK_REPAIR_REPORT.md | `docs/FINAL_LINK_REPAIR_REPORT.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\FINAL_LINK_REPAIR_REPORT.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/LINK_REPAIR_STRATEGY.md | `docs/LINK_REPAIR_STRATEGY.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\LINK_REPAIR_STRATEGY.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/01_learning/LEARNING_PATH_PLANNING.md | `docs/01_learning/LEARNING_PATH_PLANNING.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\01_learning\LEARNING_PATH_PLANNING.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/01_learning/LEARNING_PATH_PLANNING.md | `docs/01_learning/LEARNING_PATH_PLANNING.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\01_learning\LEARNING_PATH_PLANNING.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/DOCS_STRUCTURE_OVERVIEW.md | `docs/DOCS_STRUCTURE_OVERVIEW.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\DOCS_STRUCTURE_OVERVIEW.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/DOCS_STRUCTURE_OVERVIEW.md | `docs/DOCS_STRUCTURE_OVERVIEW.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\DOCS_STRUCTURE_OVERVIEW.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c01_ownership_borrow_scope/README.md | `crates/c01_ownership_borrow_scope/README.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c01_ownership_borrow_scope\README.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c02_type_system/README.md | `crates/c02_type_system/README.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c02_type_system\README.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c04_generic/docs/00_MASTER_INDEX.md | `crates/c04_generic/docs/00_MASTER_INDEX.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c04_generic\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c05_threads/README.md | `crates/c05_threads/README.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c05_threads\README.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c05_threads/docs/00_MASTER_INDEX.md | `crates/c05_threads/docs/00_MASTER_INDEX.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c05_threads\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/DOCS_STRUCTURE_OVERVIEW.md | `docs/DOCS_STRUCTURE_OVERVIEW.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\DOCS_STRUCTURE_OVERVIEW.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/DOCS_STRUCTURE_OVERVIEW.md | `docs/DOCS_STRUCTURE_OVERVIEW.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\DOCS_STRUCTURE_OVERVIEW.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/README.md | `docs/README.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\README.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/archive/process_reports/2026_02/CONTENT_IMPROVEMENT_PLAN.md | `docs/archive/process_reports/2026_02/CONTENT_IMPROVEMENT_PLAN.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\archive\process_reports\2026_02\CONTENT_IMPROVEMENT_PLAN.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/archive/process_reports/2026_02/DOCS_STRUCTURE_AND_FORMAT_AUDIT_REPORT.md | `docs/archive/process_reports/2026_02/DOCS_STRUCTURE_AND_FORMAT_AUDIT_REPORT.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\archive\process_reports\2026_02\DOCS_STRUCTURE_AND_FORMAT_AUDIT_REPORT.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c01_ownership_borrow_scope/README.md | `crates/c01_ownership_borrow_scope/README.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c01_ownership_borrow_scope\README.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c02_type_system/README.md | `crates/c02_type_system/README.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c02_type_system\README.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c04_generic/docs/00_MASTER_INDEX.md | `crates/c04_generic/docs/00_MASTER_INDEX.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c04_generic\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c05_threads/README.md | `crates/c05_threads/README.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c05_threads\README.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c05_threads/docs/00_MASTER_INDEX.md | `crates/c05_threads/docs/00_MASTER_INDEX.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c05_threads\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/01_learning/LEARNING_PATH_PLANNING.md | `docs/01_learning/LEARNING_PATH_PLANNING.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\01_learning\LEARNING_PATH_PLANNING.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/01_learning/LEARNING_PATH_PLANNING.md | `docs/01_learning/LEARNING_PATH_PLANNING.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\01_learning\LEARNING_PATH_PLANNING.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/01_learning/LEARNING_PATH_PLANNING.md | `docs/01_learning/LEARNING_PATH_PLANNING.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\01_learning\LEARNING_PATH_PLANNING.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/01_learning/OFFICIAL_RESOURCES_MAPPING.md | `docs/01_learning/OFFICIAL_RESOURCES_MAPPING.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\01_learning\OFFICIAL_RESOURCES_MAPPING.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/DOCS_STRUCTURE_OVERVIEW.md | `docs/DOCS_STRUCTURE_OVERVIEW.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\DOCS_STRUCTURE_OVERVIEW.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/06_toolchain/README.md | `docs/06_toolchain/README.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\06_toolchain\README.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/archive/process_reports/2026_02/FORMAT_AND_CONTENT_ALIGNMENT_PLAN.md | `docs/archive/process_reports/2026_02/FORMAT_AND_CONTENT_ALIGNMENT_PLAN.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\archive\process_reports\2026_02\FORMAT_AND_CONTENT_ALIGNMENT_PLAN.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/archive/process_reports/2026_02/FORMAT_AND_CONTENT_ALIGNMENT_PLAN.md | `docs/archive/process_reports/2026_02/FORMAT_AND_CONTENT_ALIGNMENT_PLAN.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\archive\process_reports\2026_02\FORMAT_AND_CONTENT_ALIGNMENT_PLAN.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/archive/process_reports/2026_02/FORMAT_AND_CONTENT_ALIGNMENT_PLAN.md | `docs/archive/process_reports/2026_02/FORMAT_AND_CONTENT_ALIGNMENT_PLAN.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\archive\process_reports\2026_02\FORMAT_AND_CONTENT_ALIGNMENT_PLAN.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c01_ownership_borrow_scope/README.md | `crates/c01_ownership_borrow_scope/README.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c01_ownership_borrow_scope\README.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.en.md | `crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.en.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c01_ownership_borrow_scope\docs\00_MASTER_INDEX.en.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md | `crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c01_ownership_borrow_scope\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md | `crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c01_ownership_borrow_scope\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md | `crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c01_ownership_borrow_scope\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/research_notes/CONTENT_ENHANCEMENT.md | `docs/research_notes/CONTENT_ENHANCEMENT.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\research_notes\CONTENT_ENHANCEMENT.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/research_notes/FAQ.md | `docs/research_notes/FAQ.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\research_notes\FAQ.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/research_notes/FAQ.md | `docs/research_notes/FAQ.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\research_notes\FAQ.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/research_notes/FAQ.md | `docs/research_notes/FAQ.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\research_notes\FAQ.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/research_notes/FAQ.md | `docs/research_notes/FAQ.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\research_notes\FAQ.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c02_type_system/README.md | `crates/c02_type_system/README.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c02_type_system\README.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c02_type_system/README.md | `crates/c02_type_system/README.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c02_type_system\README.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c02_type_system/docs/00_MASTER_INDEX.en.md | `crates/c02_type_system/docs/00_MASTER_INDEX.en.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c02_type_system\docs\00_MASTER_INDEX.en.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c02_type_system/docs/00_MASTER_INDEX.md | `crates/c02_type_system/docs/00_MASTER_INDEX.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c02_type_system\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c02_type_system/docs/tier_01_foundations/01_项目概览.md | `crates/c02_type_system/docs/tier_01_foundations/01_项目概览.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c02_type_system\docs\tier_01_foundations\01_项目概览.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/DOCS_STRUCTURE_OVERVIEW.md | `docs/DOCS_STRUCTURE_OVERVIEW.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\DOCS_STRUCTURE_OVERVIEW.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/02_reference/ALIGNMENT_GUIDE.md | `docs/02_reference/ALIGNMENT_GUIDE.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\02_reference\ALIGNMENT_GUIDE.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/archive/process_reports/2026_02/TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md | `docs/archive/process_reports/2026_02/TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\archive\process_reports\2026_02\TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/research_notes/GLOSSARY.md | `docs/research_notes/GLOSSARY.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\research_notes\GLOSSARY.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/research_notes/GLOSSARY.md | `docs/research_notes/GLOSSARY.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\research_notes\GLOSSARY.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c02_type_system/README.md | `crates/c02_type_system/README.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c02_type_system\README.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c02_type_system/docs/00_MASTER_INDEX.en.md | `crates/c02_type_system/docs/00_MASTER_INDEX.en.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c02_type_system\docs\00_MASTER_INDEX.en.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c02_type_system/docs/00_MASTER_INDEX.md | `crates/c02_type_system/docs/00_MASTER_INDEX.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c02_type_system\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c02_type_system/docs/tier_01_foundations/01_项目概览.md | `crates/c02_type_system/docs/tier_01_foundations/01_项目概览.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c02_type_system\docs\tier_01_foundations\01_项目概览.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c02_type_system/docs/tier_01_foundations/01_项目概览.md | `crates/c02_type_system/docs/tier_01_foundations/01_项目概览.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c02_type_system\docs\tier_01_foundations\01_项目概览.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/04_thinking/APPLICATIONS_ANALYSIS_VIEW.md | `docs/04_thinking/APPLICATIONS_ANALYSIS_VIEW.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\04_thinking\APPLICATIONS_ANALYSIS_VIEW.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/00_MASTER_INDEX.md | `docs/00_master_index.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/DOCS_STRUCTURE_OVERVIEW.md | `docs/DOCS_STRUCTURE_OVERVIEW.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\DOCS_STRUCTURE_OVERVIEW.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/archive/process_reports/2026_02/TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md | `docs/archive/process_reports/2026_02/TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\archive\process_reports\2026_02\TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/research_notes/GLOSSARY.md | `docs/research_notes/GLOSSARY.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\research_notes\GLOSSARY.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/research_notes/INDEX.md | `docs/research_notes/INDEX.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\research_notes\INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/research_notes/INDEX.md | `docs/research_notes/INDEX.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\research_notes\INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/04_thinking/DECISION_GRAPH_NETWORK.md | `docs/04_thinking/DECISION_GRAPH_NETWORK.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\04_thinking\DECISION_GRAPH_NETWORK.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/04_thinking/MULTI_DIMENSIONAL_CONCEPT_MATRIX.md | `docs/04_thinking/MULTI_DIMENSIONAL_CONCEPT_MATRIX.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\04_thinking\MULTI_DIMENSIONAL_CONCEPT_MATRIX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/04_thinking/README.md | `docs/04_thinking/README.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\04_thinking\README.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/research_notes/ARGUMENTATION_GAP_INDEX.md | `docs/research_notes/ARGUMENTATION_GAP_INDEX.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\research_notes\ARGUMENTATION_GAP_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/research_notes/ARGUMENTATION_GAP_INDEX.md | `docs/research_notes/ARGUMENTATION_GAP_INDEX.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\research_notes\ARGUMENTATION_GAP_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | BROKEN_LINKS_REPORT.md | `./BROKEN_LINKS_REPORT.md` | 文件不存在: docs\archive\2026_03_reorganization\BROKEN_LINKS_REPORT.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c12_wasm/README.md | `crates/c12_wasm/README.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c12_wasm\README.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c12_wasm/README.md | `crates/c12_wasm/README.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c12_wasm\README.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c12_wasm/RUST_192_UPDATE_SUMMARY.md | `crates/c12_wasm/RUST_192_UPDATE_SUMMARY.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c12_wasm\RUST_192_UPDATE_SUMMARY.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c12_wasm/docs/RUST_192_BEST_PRACTICES.md | `crates/c12_wasm/docs/RUST_192_BEST_PRACTICES.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c12_wasm\docs\RUST_192_BEST_PRACTICES.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c02_type_system/README.md | `crates/c02_type_system/README.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c02_type_system\README.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c02_type_system/docs/00_MASTER_INDEX.en.md | `crates/c02_type_system/docs/00_MASTER_INDEX.en.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c02_type_system\docs\00_MASTER_INDEX.en.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c02_type_system/docs/00_MASTER_INDEX.md | `crates/c02_type_system/docs/00_MASTER_INDEX.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c02_type_system\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c02_type_system/docs/tier_01_foundations/01_项目概览.md | `crates/c02_type_system/docs/tier_01_foundations/01_项目概览.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c02_type_system\docs\tier_01_foundations\01_项目概览.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c02_type_system/docs/tier_01_foundations/01_项目概览.md | `crates/c02_type_system/docs/tier_01_foundations/01_项目概览.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c02_type_system\docs\tier_01_foundations\01_项目概览.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c02_type_system/README.md | `crates/c02_type_system/README.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c02_type_system\README.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c02_type_system/README.md | `crates/c02_type_system/README.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c02_type_system\README.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c02_type_system/README.md | `crates/c02_type_system/README.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c02_type_system\README.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c02_type_system/docs/tier_01_foundations/01_项目概览.md | `crates/c02_type_system/docs/tier_01_foundations/01_项目概览.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c02_type_system\docs\tier_01_foundations\01_项目概览.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c02_type_system/docs/tier_01_foundations/01_项目概览.md | `crates/c02_type_system/docs/tier_01_foundations/01_项目概览.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c02_type_system\docs\tier_01_foundations\01_项目概览.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c04_generic/README.md | `crates/c04_generic/README.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c04_generic\README.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c04_generic/docs/tier_01_foundations/01_项目概览.md | `crates/c04_generic/docs/tier_01_foundations/01_项目概览.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c04_generic\docs\tier_01_foundations\01_项目概览.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c04_generic/docs/tier_01_foundations/01_项目概览.md | `crates/c04_generic/docs/tier_01_foundations/01_项目概览.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c04_generic\docs\tier_01_foundations\01_项目概览.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c04_generic/docs/tier_01_foundations/02_主索引导航.md | `crates/c04_generic/docs/tier_01_foundations/02_主索引导航.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c04_generic\docs\tier_01_foundations\02_主索引导航.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c04_generic/docs/tier_01_foundations/02_主索引导航.md | `crates/c04_generic/docs/tier_01_foundations/02_主索引导航.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c04_generic\docs\tier_01_foundations\02_主索引导航.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/DOCS_STRUCTURE_OVERVIEW.md | `docs/DOCS_STRUCTURE_OVERVIEW.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\DOCS_STRUCTURE_OVERVIEW.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/DOCS_STRUCTURE_OVERVIEW.md | `docs/DOCS_STRUCTURE_OVERVIEW.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\DOCS_STRUCTURE_OVERVIEW.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/README.md | `docs/README.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\README.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/README.md | `docs/README.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\README.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/archive/temp/FORMAL_AND_PRACTICAL_NAVIGATION.md | `docs/archive/temp/FORMAL_AND_PRACTICAL_NAVIGATION.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\archive\temp\FORMAL_AND_PRACTICAL_NAVIGATION.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c01_ownership_borrow_scope/README.md | `crates/c01_ownership_borrow_scope/README.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c01_ownership_borrow_scope\README.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md | `crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c01_ownership_borrow_scope\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md | `crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c01_ownership_borrow_scope\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md | `crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c01_ownership_borrow_scope\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md | `crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c01_ownership_borrow_scope\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | README.md | `./README.md` | 文件不存在: docs\archive\2026_03_reorganization\README.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c03_control_fn/README.md | `crates/c03_control_fn/README.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c03_control_fn\README.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c03_control_fn/docs/00_MASTER_INDEX.md | `crates/c03_control_fn/docs/00_MASTER_INDEX.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c03_control_fn\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c03_control_fn/docs/DOCUMENTATION_INDEX.md | `crates/c03_control_fn/docs/DOCUMENTATION_INDEX.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c03_control_fn\docs\DOCUMENTATION_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c03_control_fn/docs/tier_01_foundations/01_项目概览.md | `crates/c03_control_fn/docs/tier_01_foundations/01_项目概览.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c03_control_fn\docs\tier_01_foundations\01_项目概览.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c01_ownership_borrow_scope/README.md | `crates/c01_ownership_borrow_scope/README.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c01_ownership_borrow_scope\README.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md | `crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c01_ownership_borrow_scope\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md | `crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c01_ownership_borrow_scope\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md | `crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c01_ownership_borrow_scope\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md | `crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c01_ownership_borrow_scope\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md | `crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c01_ownership_borrow_scope\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md | `crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c01_ownership_borrow_scope\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md | `crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c01_ownership_borrow_scope\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md | `crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c01_ownership_borrow_scope\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md | `crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c01_ownership_borrow_scope\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c04_generic/docs/00_MASTER_INDEX.en.md | `crates/c04_generic/docs/00_MASTER_INDEX.en.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c04_generic\docs\00_MASTER_INDEX.en.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c04_generic/docs/00_MASTER_INDEX.md | `crates/c04_generic/docs/00_MASTER_INDEX.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c04_generic\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c04_generic/docs/00_MASTER_INDEX.md | `crates/c04_generic/docs/00_MASTER_INDEX.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c04_generic\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c04_generic/docs/00_MASTER_INDEX.md | `crates/c04_generic/docs/00_MASTER_INDEX.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c04_generic\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c04_generic/docs/00_MASTER_INDEX.md | `crates/c04_generic/docs/00_MASTER_INDEX.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c04_generic\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/02_reference/quick_reference/generics_cheatsheet.md | `docs/02_reference/quick_reference/generics_cheatsheet.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\02_reference\quick_reference\generics_cheatsheet.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/02_reference/quick_reference/modules_cheatsheet.md | `docs/02_reference/quick_reference/modules_cheatsheet.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\02_reference\quick_reference\modules_cheatsheet.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/02_reference/quick_reference/type_system.md | `docs/02_reference/quick_reference/type_system.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\02_reference\quick_reference\type_system.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/archive/process_reports/2026_02/FORMAL_PROOF_CRITICAL_ANALYSIS_AND_PLAN_2026_02.md | `docs/archive/process_reports/2026_02/FORMAL_PROOF_CRITICAL_ANALYSIS_AND_PLAN_2026_02.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\archive\process_reports\2026_02\FORMAL_PROOF_CRITICAL_ANALYSIS_AND_PLAN_2026_02.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | docs/research_notes/ARGUMENTATION_GAP_INDEX.md | `docs/research_notes/ARGUMENTATION_GAP_INDEX.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\research_notes\ARGUMENTATION_GAP_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | README.en.md | `./README.en.md` | 文件不存在: docs\archive\2026_03_reorganization\README.en.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c01_ownership_borrow_scope/README.md | `crates/c01_ownership_borrow_scope/README.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c01_ownership_borrow_scope\README.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.en.md | `crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.en.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c01_ownership_borrow_scope\docs\00_MASTER_INDEX.en.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md | `crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c01_ownership_borrow_scope\docs\00_MASTER_INDEX.md |
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | crates/c01_ownership_borrow_scope/docs/FAQ.md | `crates/c01_ownership_borrow_scope/docs/FAQ.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c01_ownership_borrow_scope\docs\FAQ.md |
| docs\archive\2026_03_reorganization\PROJECT_STRUCTURE.md | guides/README.md | `./guides/README.md` | 文件不存在: docs\archive\2026_03_reorganization\guides\README.md |
| docs\archive\2026_03_reorganization\PROJECT_STRUCTURE.md | guides/AI_ASSISTED_RUST_PROGRAMMING_GUIDE_2025.md | `./guides/AI_ASSISTED_RUST_PROGRAMMING_GUIDE_2025.md` | 文件不存在: docs\archive\2026_03_reorganization\guides\AI_ASSISTED_RUST_PROGRAMMING_GUIDE_2025.md |
| docs\archive\2026_03_reorganization\PROJECT_STRUCTURE.md | docs/05_guides/UNSAFE_RUST_GUIDE.md | `./docs/05_guides/UNSAFE_RUST_GUIDE.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\05_guides\UNSAFE_RUST_GUIDE.md |
| docs\archive\2026_03_reorganization\PROJECT_STRUCTURE.md | guides/README.md | `./guides/README.md` | 文件不存在: docs\archive\2026_03_reorganization\guides\README.md |
| docs\archive\2026_03_reorganization\PROJECT_STRUCTURE.md | archive/reports/ | `./archive/reports/` | 文件不存在: docs\archive\2026_03_reorganization\archive\reports |
| docs\archive\2026_03_reorganization\PROJECT_STRUCTURE.md | docs/archive/reports/ | `./docs/archive/reports/` | 文件不存在: docs\archive\2026_03_reorganization\docs\archive\reports |
| docs\archive\2026_03_reorganization\PROJECT_STRUCTURE.md | docs/archive/root_completion_reports/ | `./docs/archive/root_completion_reports/README.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\archive\root_completion_reports\README.md |
| docs\archive\2026_03_reorganization\PROJECT_STRUCTURE.md | docs/archive/process_reports/PLAN_IMPLEMENTATION_COMPLETION_2026_02.md | `./docs/archive/process_reports/PLAN_IMPLEMENTATION_COMPLETION_2026_02.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\archive\process_reports\PLAN_IMPLEMENTATION_COMPLETION_2026_02.md |
| docs\archive\2026_03_reorganization\PROJECT_STRUCTURE.md | exercises/README.md | `./exercises/README.md` | 文件不存在: docs\archive\2026_03_reorganization\exercises\README.md |
| docs\archive\2026_03_reorganization\PROJECT_STRUCTURE.md | README.md | `./README.md` | 文件不存在: docs\archive\2026_03_reorganization\README.md |
| docs\archive\2026_03_reorganization\PROJECT_STRUCTURE.md | C01模块 | `./crates/c01_ownership_borrow_scope/README.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c01_ownership_borrow_scope\README.md |
| docs\archive\2026_03_reorganization\PROJECT_STRUCTURE.md | 学习路径 | `./README.md#学习路径推荐` | 文件不存在: docs\archive\2026_03_reorganization\README.md |
| docs\archive\2026_03_reorganization\PROJECT_STRUCTURE.md | 学习指南 | `./guides/README.md` | 文件不存在: docs\archive\2026_03_reorganization\guides\README.md |
| docs\archive\2026_03_reorganization\PROJECT_STRUCTURE.md | QUICK_REFERENCE.md | `./QUICK_REFERENCE.md` | 文件不存在: docs\archive\2026_03_reorganization\QUICK_REFERENCE.md |
| docs\archive\2026_03_reorganization\PROJECT_STRUCTURE.md | 速查卡目录 | `./docs/02_reference/quick_reference/README.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\02_reference\quick_reference\README.md |
| docs\archive\2026_03_reorganization\PROJECT_STRUCTURE.md | 文档中心 | `./docs/README.md` | 文件不存在: docs\archive\2026_03_reorganization\docs\README.md |
| docs\archive\2026_03_reorganization\PROJECT_STRUCTURE.md | TROUBLESHOOTING.md | `./TROUBLESHOOTING.md#编译错误` | 文件不存在: docs\archive\2026_03_reorganization\TROUBLESHOOTING.md |
| docs\archive\2026_03_reorganization\PROJECT_STRUCTURE.md | TROUBLESHOOTING.md | `./TROUBLESHOOTING.md#运行时错误` | 文件不存在: docs\archive\2026_03_reorganization\TROUBLESHOOTING.md |
| docs\archive\2026_03_reorganization\PROJECT_STRUCTURE.md | TROUBLESHOOTING.md | `./TROUBLESHOOTING.md#性能问题` | 文件不存在: docs\archive\2026_03_reorganization\TROUBLESHOOTING.md |
| docs\archive\2026_03_reorganization\PROJECT_STRUCTURE.md | C09 设计模式 | `./crates/c09_design_pattern/README.md` | 文件不存在: docs\archive\2026_03_reorganization\crates\c09_design_pattern\README.md |
| docs\archive\2026_03_reorganization\PROJECT_STRUCTURE.md | archive/reports/ | `./archive/reports/` | 文件不存在: docs\archive\2026_03_reorganization\archive\reports |
| docs\archive\2026_03_reorganization\PROJECT_STRUCTURE.md | archive/reports/ | `./archive/reports/` | 文件不存在: docs\archive\2026_03_reorganization\archive\reports |
| docs\archive\2026_03_reorganization\PROJECT_STRUCTURE.md | CHANGELOG.md | `./CHANGELOG.md` | 文件不存在: docs\archive\2026_03_reorganization\CHANGELOG.md |
| docs\archive\2026_03_reorganization\PROJECT_STRUCTURE.md | ROADMAP.md | `./ROADMAP.md` | 文件不存在: docs\archive\2026_03_reorganization\ROADMAP.md |
| docs\archive\2026_03_reorganization\PROJECT_STRUCTURE.md | CONTRIBUTING.md | `./CONTRIBUTING.md` | 文件不存在: docs\archive\2026_03_reorganization\CONTRIBUTING.md |
| docs\archive\2026_03_reorganization\PROJECT_STRUCTURE.md | ROADMAP.md | `./ROADMAP.md` | 文件不存在: docs\archive\2026_03_reorganization\ROADMAP.md |
| docs\archive\2026_03_reorganization\PROJECT_STRUCTURE.md | README.md | `./README.md` | 文件不存在: docs\archive\2026_03_reorganization\README.md |
| docs\archive\2026_03_reorganization\PROJECT_STRUCTURE.md | guides/ | `./guides/README.md` | 文件不存在: docs\archive\2026_03_reorganization\guides\README.md |
| docs\archive\2026_03_reorganization\PROJECT_STRUCTURE.md | archive/reports/ | `./archive/reports/` | 文件不存在: docs\archive\2026_03_reorganization\archive\reports |
| docs\archive\2026_03_reorganization\PROJECT_STRUCTURE.md | CONTRIBUTING.md | `./CONTRIBUTING.md` | 文件不存在: docs\archive\2026_03_reorganization\CONTRIBUTING.md |
| docs\archive\2026_03_reorganization\PROJECT_STRUCTURE.md | ROADMAP.md | `./ROADMAP.md` | 文件不存在: docs\archive\2026_03_reorganization\ROADMAP.md |
| docs\archive\2026_03_reorganization\PROJECT_STRUCTURE.md | RESOURCES.md | `./RESOURCES.md` | 文件不存在: docs\archive\2026_03_reorganization\RESOURCES.md |
| docs\archive\2026_05_historical_docs\08_rust_version_evolution_1.89_to_1.93.md | 05_rust_1.93_vs_1.92_comparison.md | `./05_rust_1.93_vs_1.92_comparison.md` | 文件不存在: docs\archive\2026_05_historical_docs\05_rust_1.93_vs_1.92_comparison.md |
| docs\archive\2026_05_historical_docs\08_rust_version_evolution_1.89_to_1.93.md | 06_rust_1.93_compatibility_notes.md | `./06_rust_1.93_compatibility_notes.md` | 文件不存在: docs\archive\2026_05_historical_docs\06_rust_1.93_compatibility_notes.md |
| docs\archive\2026_05_historical_docs\08_rust_version_evolution_1.89_to_1.93.md | Rust 1.93 vs 1.92 对比 | `./05_rust_1.93_vs_1.92_comparison.md` | 文件不存在: docs\archive\2026_05_historical_docs\05_rust_1.93_vs_1.92_comparison.md |
| docs\archive\2026_05_historical_docs\08_rust_version_evolution_1.89_to_1.93.md | Rust 1.93 兼容性注意事项 | `./06_rust_1.93_compatibility_notes.md` | 文件不存在: docs\archive\2026_05_historical_docs\06_rust_1.93_compatibility_notes.md |
| docs\archive\2026_05_historical_docs\08_rust_version_evolution_1.89_to_1.93.md | Rust 1.93 完整变更清单 | `./07_rust_1.93_full_changelog.md` | 文件不存在: docs\archive\2026_05_historical_docs\07_rust_1.93_full_changelog.md |
| docs\archive\2026_05_historical_docs\08_rust_version_evolution_1.89_to_1.93.md | Rust 1.94 完整发布说明 | `../archive/2026_05_historical_docs/16_rust_1.94_release_notes.md` | 文件不存在: docs\archive\archive\2026_05_historical_docs\16_rust_1.94_release_notes.md |
| docs\archive\2026_05_historical_docs\08_rust_version_evolution_1.89_to_1.93.md | Rust 1.94 采用指南 | `../archive/2026_05_historical_docs/18_rust_1.94_adoption_guide.md` | 文件不存在: docs\archive\archive\2026_05_historical_docs\18_rust_1.94_adoption_guide.md |
| docs\archive\2026_05_historical_docs\08_rust_version_evolution_1.89_to_1.93.md | Rust 1.93 vs 1.94 对比 | `../archive/2026_05_historical_docs/17_rust_1.93_vs_1.94_comparison.md` | 文件不存在: docs\archive\archive\2026_05_historical_docs\17_rust_1.93_vs_1.94_comparison.md |
| docs\archive\2026_05_historical_docs\10_rust_1.89_to_1.93_cumulative_features_overview.md | 05_rust_1.93_vs_1.92_comparison.md | `./05_rust_1.93_vs_1.92_comparison.md` | 文件不存在: docs\archive\2026_05_historical_docs\05_rust_1.93_vs_1.92_comparison.md |
| docs\archive\2026_05_historical_docs\10_rust_1.89_to_1.93_cumulative_features_overview.md | 09_rust_1.93_compatibility_deep_dive.md | `./09_rust_1.93_compatibility_deep_dive.md` | 文件不存在: docs\archive\2026_05_historical_docs\09_rust_1.93_compatibility_deep_dive.md |
| docs\archive\2026_05_historical_docs\10_rust_1.89_to_1.93_cumulative_features_overview.md | 07_rust_1.93_full_changelog.md | `./07_rust_1.93_full_changelog.md` | 文件不存在: docs\archive\2026_05_historical_docs\07_rust_1.93_full_changelog.md |
| docs\archive\2026_05_historical_docs\10_rust_1.89_to_1.93_cumulative_features_overview.md | ../07_project/RUST_RELEASE_TRACKING_CHECKLIST.md | `../07_project/RUST_RELEASE_TRACKING_CHECKLIST.md` | 文件不存在: docs\archive\07_project\RUST_RELEASE_TRACKING_CHECKLIST.md |
| docs\archive\2026_05_historical_docs\10_rust_1.89_to_1.93_cumulative_features_overview.md | Rust 1.94 完整发布说明 | `../archive/2026_05_historical_docs/16_rust_1.94_release_notes.md` | 文件不存在: docs\archive\archive\2026_05_historical_docs\16_rust_1.94_release_notes.md |
| docs\archive\2026_05_historical_docs\10_rust_1.89_to_1.93_cumulative_features_overview.md | Rust 1.94 采用指南 | `../archive/2026_05_historical_docs/18_rust_1.94_adoption_guide.md` | 文件不存在: docs\archive\archive\2026_05_historical_docs\18_rust_1.94_adoption_guide.md |
| docs\archive\2026_05_historical_docs\10_rust_1.89_to_1.93_cumulative_features_overview.md | Rust 1.93 vs 1.94 对比 | `../archive/2026_05_historical_docs/17_rust_1.93_vs_1.94_comparison.md` | 文件不存在: docs\archive\archive\2026_05_historical_docs\17_rust_1.93_vs_1.94_comparison.md |
| docs\archive\2026_05_historical_docs\12_rust_1.93.1_vs_1.93.0_comparison.md | borrow_checker_proof | `../research_notes/formal_methods/borrow_checker_proof.md` | 文件不存在: docs\archive\research_notes\formal_methods\borrow_checker_proof.md |
| docs\archive\2026_05_historical_docs\12_rust_1.93.1_vs_1.93.0_comparison.md | ownership_model | `../research_notes/formal_methods/ownership_model.md` | 文件不存在: docs\archive\research_notes\formal_methods\ownership_model.md |
| docs\archive\2026_05_historical_docs\12_rust_1.93.1_vs_1.93.0_comparison.md | borrow_checker_proof | `../research_notes/formal_methods/borrow_checker_proof.md` | 文件不存在: docs\archive\research_notes\formal_methods\borrow_checker_proof.md |
| docs\archive\2026_05_historical_docs\12_rust_1.93.1_vs_1.93.0_comparison.md | WASM_USAGE_GUIDE | `../05_guides/WASM_USAGE_GUIDE.md` | 文件不存在: docs\archive\05_guides\WASM_USAGE_GUIDE.md |
| docs\archive\2026_05_historical_docs\12_rust_1.93.1_vs_1.93.0_comparison.md | wasm_cheatsheet | `../02_reference/quick_reference/wasm_cheatsheet.md` | 文件不存在: docs\archive\02_reference\quick_reference\wasm_cheatsheet.md |
| docs\archive\2026_05_historical_docs\12_rust_1.93.1_vs_1.93.0_comparison.md | type_system_foundations | `../research_notes/type_theory/type_system_foundations.md` | 文件不存在: docs\archive\research_notes\type_theory\type_system_foundations.md |
| docs\archive\2026_05_historical_docs\12_rust_1.93.1_vs_1.93.0_comparison.md | ownership_model | `../research_notes/formal_methods/ownership_model.md` | 文件不存在: docs\archive\research_notes\formal_methods\ownership_model.md |
| docs\archive\2026_05_historical_docs\12_rust_1.93.1_vs_1.93.0_comparison.md | borrow_checker_proof | `../research_notes/formal_methods/borrow_checker_proof.md` | 文件不存在: docs\archive\research_notes\formal_methods\borrow_checker_proof.md |
| docs\archive\2026_05_historical_docs\12_rust_1.93.1_vs_1.93.0_comparison.md | lifetime_formalization | `../research_notes/formal_methods/lifetime_formalization.md` | 文件不存在: docs\archive\research_notes\formal_methods\lifetime_formalization.md |
| docs\archive\2026_05_historical_docs\12_rust_1.93.1_vs_1.93.0_comparison.md | async_state_machine | `../research_notes/formal_methods/async_state_machine.md` | 文件不存在: docs\archive\research_notes\formal_methods\async_state_machine.md |
| docs\archive\2026_05_historical_docs\12_rust_1.93.1_vs_1.93.0_comparison.md | pin_self_referential | `../research_notes/formal_methods/pin_self_referential.md` | 文件不存在: docs\archive\research_notes\formal_methods\pin_self_referential.md |
| docs\archive\2026_05_historical_docs\12_rust_1.93.1_vs_1.93.0_comparison.md | send_sync_formalization | `../research_notes/formal_methods/send_sync_formalization.md` | 文件不存在: docs\archive\research_notes\formal_methods\send_sync_formalization.md |
| docs\archive\2026_05_historical_docs\12_rust_1.93.1_vs_1.93.0_comparison.md | 09_rust_1.93_compatibility_deep_dive | `./09_rust_1.93_compatibility_deep_dive.md` | 文件不存在: docs\archive\2026_05_historical_docs\09_rust_1.93_compatibility_deep_dive.md |
| docs\archive\2026_05_historical_docs\12_rust_1.93.1_vs_1.93.0_comparison.md | 05_rust_1.93_vs_1.92_comparison | `./05_rust_1.93_vs_1.92_comparison.md` | 文件不存在: docs\archive\2026_05_historical_docs\05_rust_1.93_vs_1.92_comparison.md |
| docs\archive\2026_05_historical_docs\12_rust_1.93.1_vs_1.93.0_comparison.md | WASM_USAGE_GUIDE | `../05_guides/WASM_USAGE_GUIDE.md` | 文件不存在: docs\archive\05_guides\WASM_USAGE_GUIDE.md |
| docs\archive\2026_05_historical_docs\12_rust_1.93.1_vs_1.93.0_comparison.md | ownership_model | `../research_notes/formal_methods/ownership_model.md` | 文件不存在: docs\archive\research_notes\formal_methods\ownership_model.md |
| docs\archive\2026_05_historical_docs\12_rust_1.93.1_vs_1.93.0_comparison.md | ownership_model | `../research_notes/formal_methods/ownership_model.md` | 文件不存在: docs\archive\research_notes\formal_methods\ownership_model.md |
| docs\archive\2026_05_historical_docs\12_rust_1.93.1_vs_1.93.0_comparison.md | Rust 1.94 完整发布说明 | `../archive/2026_05_historical_docs/16_rust_1.94_release_notes.md` | 文件不存在: docs\archive\archive\2026_05_historical_docs\16_rust_1.94_release_notes.md |
| docs\archive\2026_05_historical_docs\12_rust_1.93.1_vs_1.93.0_comparison.md | Rust 1.94 采用指南 | `../archive/2026_05_historical_docs/18_rust_1.94_adoption_guide.md` | 文件不存在: docs\archive\archive\2026_05_historical_docs\18_rust_1.94_adoption_guide.md |
| docs\archive\2026_05_historical_docs\12_rust_1.93.1_vs_1.93.0_comparison.md | Rust 1.93 vs 1.94 对比 | `../archive/2026_05_historical_docs/17_rust_1.93_vs_1.94_comparison.md` | 文件不存在: docs\archive\archive\2026_05_historical_docs\17_rust_1.93_vs_1.94_comparison.md |
| docs\archive\2026_05_historical_docs\13_rust_1.94_preview.md | type_system_foundations | `../research_notes/type_theory/type_system_foundations.md` | 文件不存在: docs\archive\research_notes\type_theory\type_system_foundations.md |
| docs\archive\2026_05_historical_docs\13_rust_1.94_preview.md | ownership_model | `../research_notes/formal_methods/ownership_model.md` | 文件不存在: docs\archive\research_notes\formal_methods\ownership_model.md |
| docs\archive\2026_05_historical_docs\13_rust_1.94_preview.md | type_system_foundations | `../research_notes/type_theory/type_system_foundations.md` | 文件不存在: docs\archive\research_notes\type_theory\type_system_foundations.md |
| docs\archive\2026_05_historical_docs\13_rust_1.94_preview.md | ownership_model | `../research_notes/formal_methods/ownership_model.md` | 文件不存在: docs\archive\research_notes\formal_methods\ownership_model.md |
| docs\archive\2026_05_historical_docs\13_rust_1.94_preview.md | type_system_foundations | `../research_notes/type_theory/type_system_foundations.md` | 文件不存在: docs\archive\research_notes\type_theory\type_system_foundations.md |
| docs\archive\2026_05_historical_docs\13_rust_1.94_preview.md | ownership_model | `../research_notes/formal_methods/ownership_model.md` | 文件不存在: docs\archive\research_notes\formal_methods\ownership_model.md |
| docs\archive\2026_05_historical_docs\13_rust_1.94_preview.md | type_system_foundations | `../research_notes/type_theory/type_system_foundations.md` | 文件不存在: docs\archive\research_notes\type_theory\type_system_foundations.md |
| docs\archive\2026_05_historical_docs\13_rust_1.94_preview.md | type_system_foundations | `../research_notes/type_theory/type_system_foundations.md` | 文件不存在: docs\archive\research_notes\type_theory\type_system_foundations.md |
| docs\archive\2026_05_historical_docs\13_rust_1.94_preview.md | ownership_model | `../research_notes/formal_methods/ownership_model.md` | 文件不存在: docs\archive\research_notes\formal_methods\ownership_model.md |
| docs\archive\2026_05_historical_docs\13_rust_1.94_preview.md | FORMAL_CONCEPTS_ENCYCLOPEDIA | `../research_notes/FORMAL_CONCEPTS_ENCYCLOPEDIA.md` | 文件不存在: docs\archive\research_notes\FORMAL_CONCEPTS_ENCYCLOPEDIA.md |
| docs\archive\2026_05_historical_docs\13_rust_1.94_preview.md | COUNTER_EXAMPLES_COMPENDIUM | `../research_notes/COUNTER_EXAMPLES_COMPENDIUM.md` | 文件不存在: docs\archive\research_notes\COUNTER_EXAMPLES_COMPENDIUM.md |
| docs\archive\2026_05_historical_docs\13_rust_1.94_preview.md | RUST_193_FEATURE_MATRIX | `../research_notes/RUST_193_FEATURE_MATRIX.md` | 文件不存在: docs\archive\research_notes\RUST_193_FEATURE_MATRIX.md |
| docs\archive\2026_05_historical_docs\13_rust_1.94_preview.md | 07_rust_1.93_full_changelog | `./07_rust_1.93_full_changelog.md` | 文件不存在: docs\archive\2026_05_historical_docs\07_rust_1.93_full_changelog.md |
| docs\archive\2026_05_historical_docs\16_rust_1.94_release_notes.md | Rust 1.94 迁移指南 | `../05_guides/RUST_194_MIGRATION_GUIDE.md` | 文件不存在: docs\archive\05_guides\RUST_194_MIGRATION_GUIDE.md |
| docs\archive\2026_05_historical_docs\16_rust_1.94_release_notes.md | Rust 1.94 速查卡 | `../02_reference/quick_reference/rust_194_features_cheatsheet.md` | 文件不存在: docs\archive\02_reference\quick_reference\rust_194_features_cheatsheet.md |
| docs\archive\2026_05_historical_docs\16_rust_1.94_release_notes.md | C01 所有权与借用 | `../../crates/c01_ownership_borrow_scope/src/rust_194_features.rs` | 文件不存在: docs\crates\c01_ownership_borrow_scope\src\rust_194_features.rs |
| docs\archive\2026_05_historical_docs\16_rust_1.94_release_notes.md | C02 类型系统 | `../../crates/c02_type_system/src/rust_194_features.rs` | 文件不存在: docs\crates\c02_type_system\src\rust_194_features.rs |
| docs\archive\2026_05_historical_docs\16_rust_1.94_release_notes.md | C03 控制流与函数 | `../../crates/c03_control_fn/src/rust_194_features.rs` | 文件不存在: docs\crates\c03_control_fn\src\rust_194_features.rs |
| docs\archive\2026_05_historical_docs\16_rust_1.94_release_notes.md | C04 泛型编程 | `../../crates/c04_generic/src/rust_194_features.rs` | 文件不存在: docs\crates\c04_generic\src\rust_194_features.rs |
| docs\archive\2026_05_historical_docs\16_rust_1.94_release_notes.md | C05 线程与并发 | `../../crates/c05_threads/src/rust_194_features.rs` | 文件不存在: docs\crates\c05_threads\src\rust_194_features.rs |
| docs\archive\2026_05_historical_docs\16_rust_1.94_release_notes.md | C06 异步编程 | `../../crates/c06_async/src/rust_194_features.rs` | 文件不存在: docs\crates\c06_async\src\rust_194_features.rs |
| docs\archive\2026_05_historical_docs\16_rust_1.94_release_notes.md | C07 进程管理 | `../../crates/c07_process/src/rust_194_features.rs` | 文件不存在: docs\crates\c07_process\src\rust_194_features.rs |
| docs\archive\2026_05_historical_docs\16_rust_1.94_release_notes.md | C08 算法与数据结构 | `../../crates/c08_algorithms/src/rust_194_features.rs` | 文件不存在: docs\crates\c08_algorithms\src\rust_194_features.rs |
| docs\archive\2026_05_historical_docs\16_rust_1.94_release_notes.md | C09 设计模式 | `../../crates/c09_design_pattern/src/rust_194_features.rs` | 文件不存在: docs\crates\c09_design_pattern\src\rust_194_features.rs |
| docs\archive\2026_05_historical_docs\16_rust_1.94_release_notes.md | C10 网络编程 | `../../crates/c10_networks/src/rust_194_features.rs` | 文件不存在: docs\crates\c10_networks\src\rust_194_features.rs |
| docs\archive\2026_05_historical_docs\16_rust_1.94_release_notes.md | C11 宏系统 | `../../crates/c11_macro_system/src/rust_194_features.rs` | 文件不存在: docs\crates\c11_macro_system\src\rust_194_features.rs |
| docs\archive\2026_05_historical_docs\16_rust_1.94_release_notes.md | C12 WebAssembly | `../../crates/c12_wasm/src/rust_194_features.rs` | 文件不存在: docs\crates\c12_wasm\src\rust_194_features.rs |
| docs\archive\2026_05_historical_docs\17_rust_1.93_vs_1.94_comparison.md | Rust 1.94 迁移指南 | `../05_guides/RUST_194_MIGRATION_GUIDE.md` | 文件不存在: docs\archive\05_guides\RUST_194_MIGRATION_GUIDE.md |
| docs\archive\2026_05_historical_docs\18_rust_1.94_adoption_guide.md | Rust 1.94 迁移指南 | `../05_guides/RUST_194_MIGRATION_GUIDE.md` | 文件不存在: docs\archive\05_guides\RUST_194_MIGRATION_GUIDE.md |
| docs\archive\2026_05_historical_docs\RUST_194_COMPREHENSIVE_GUIDE.md | 所有权与借用 1.94特性 | `../crates/c01_ownership_borrow_scope/src/rust_194_features.rs` | 文件不存在: docs\archive\crates\c01_ownership_borrow_scope\src\rust_194_features.rs |
| docs\archive\2026_05_historical_docs\RUST_194_COMPREHENSIVE_GUIDE.md | 类型系统 1.94特性 | `../crates/c02_type_system/src/rust_194_features.rs` | 文件不存在: docs\archive\crates\c02_type_system\src\rust_194_features.rs |
| docs\archive\2026_05_historical_docs\RUST_194_COMPREHENSIVE_GUIDE.md | 控制流 1.94特性 | `../crates/c03_control_fn/src/rust_194_features.rs` | 文件不存在: docs\archive\crates\c03_control_fn\src\rust_194_features.rs |
| docs\archive\2026_05_historical_docs\RUST_194_COMPREHENSIVE_GUIDE.md | 版本索引 | `../VERSION_INDEX.md` | 文件不存在: docs\archive\VERSION_INDEX.md |
| docs\archive\2026_05_historical_docs\rust_194_features_cheatsheet.md | RUST_194_MIGRATION_GUIDE.md | `../../05_guides/RUST_194_MIGRATION_GUIDE.md` | 文件不存在: docs\05_guides\RUST_194_MIGRATION_GUIDE.md |
| docs\archive\deprecated\README.md | TASK_ORCHESTRATION_MASTER_PLAN | `../../../TASK_ORCHESTRATION_MASTER_PLAN.md` | 文件不存在: TASK_ORCHESTRATION_MASTER_PLAN.md |
| docs\archive\deprecated_20260318\00_rust_2024_edition_learning_impact.md | Rust 1.93 vs 1.92 对比 | `./05_rust_1.93_vs_1.92_comparison.md` | 文件不存在: docs\archive\deprecated_20260318\05_rust_1.93_vs_1.92_comparison.md |
| docs\archive\deprecated_20260318\00_rust_2024_edition_learning_impact.md | Rust 1.93 兼容性深度解析 | `./09_rust_1.93_compatibility_deep_dive.md` | 文件不存在: docs\archive\deprecated_20260318\09_rust_1.93_compatibility_deep_dive.md |
| docs\archive\deprecated_20260318\00_rust_2024_edition_learning_impact.md | Unsafe Rust 指南 | `../05_guides/UNSAFE_RUST_GUIDE.md` | 文件不存在: docs\archive\05_guides\UNSAFE_RUST_GUIDE.md |
| docs\archive\deprecated_20260318\01_safe_23_catalog.md | factory_method | `../01_design_patterns_formal/01_creational/factory_method.md` | 文件不存在: docs\archive\01_design_patterns_formal\01_creational\factory_method.md |
| docs\archive\deprecated_20260318\01_safe_23_catalog.md | abstract_factory | `../01_design_patterns_formal/01_creational/abstract_factory.md` | 文件不存在: docs\archive\01_design_patterns_formal\01_creational\abstract_factory.md |
| docs\archive\deprecated_20260318\01_safe_23_catalog.md | builder | `../01_design_patterns_formal/01_creational/builder.md` | 文件不存在: docs\archive\01_design_patterns_formal\01_creational\builder.md |
| docs\archive\deprecated_20260318\01_safe_23_catalog.md | prototype | `../01_design_patterns_formal/01_creational/prototype.md` | 文件不存在: docs\archive\01_design_patterns_formal\01_creational\prototype.md |
| docs\archive\deprecated_20260318\01_safe_23_catalog.md | singleton | `../01_design_patterns_formal/01_creational/singleton.md` | 文件不存在: docs\archive\01_design_patterns_formal\01_creational\singleton.md |
| docs\archive\deprecated_20260318\01_safe_23_catalog.md | adapter | `../01_design_patterns_formal/02_structural/adapter.md` | 文件不存在: docs\archive\01_design_patterns_formal\02_structural\adapter.md |
| docs\archive\deprecated_20260318\01_safe_23_catalog.md | bridge | `../01_design_patterns_formal/02_structural/bridge.md` | 文件不存在: docs\archive\01_design_patterns_formal\02_structural\bridge.md |
| docs\archive\deprecated_20260318\01_safe_23_catalog.md | composite | `../01_design_patterns_formal/02_structural/composite.md` | 文件不存在: docs\archive\01_design_patterns_formal\02_structural\composite.md |
| docs\archive\deprecated_20260318\01_safe_23_catalog.md | decorator | `../01_design_patterns_formal/02_structural/decorator.md` | 文件不存在: docs\archive\01_design_patterns_formal\02_structural\decorator.md |
| docs\archive\deprecated_20260318\01_safe_23_catalog.md | facade | `../01_design_patterns_formal/02_structural/facade.md` | 文件不存在: docs\archive\01_design_patterns_formal\02_structural\facade.md |
| docs\archive\deprecated_20260318\01_safe_23_catalog.md | flyweight | `../01_design_patterns_formal/02_structural/flyweight.md` | 文件不存在: docs\archive\01_design_patterns_formal\02_structural\flyweight.md |
| docs\archive\deprecated_20260318\01_safe_23_catalog.md | proxy | `../01_design_patterns_formal/02_structural/proxy.md` | 文件不存在: docs\archive\01_design_patterns_formal\02_structural\proxy.md |
| docs\archive\deprecated_20260318\01_safe_23_catalog.md | chain_of_responsibility | `../01_design_patterns_formal/03_behavioral/chain_of_responsibility.md` | 文件不存在: docs\archive\01_design_patterns_formal\03_behavioral\chain_of_responsibility.md |
| docs\archive\deprecated_20260318\01_safe_23_catalog.md | command | `../01_design_patterns_formal/03_behavioral/command.md` | 文件不存在: docs\archive\01_design_patterns_formal\03_behavioral\command.md |
| docs\archive\deprecated_20260318\01_safe_23_catalog.md | interpreter | `../01_design_patterns_formal/03_behavioral/interpreter.md` | 文件不存在: docs\archive\01_design_patterns_formal\03_behavioral\interpreter.md |
| docs\archive\deprecated_20260318\01_safe_23_catalog.md | iterator | `../01_design_patterns_formal/03_behavioral/iterator.md` | 文件不存在: docs\archive\01_design_patterns_formal\03_behavioral\iterator.md |
| docs\archive\deprecated_20260318\01_safe_23_catalog.md | mediator | `../01_design_patterns_formal/03_behavioral/mediator.md` | 文件不存在: docs\archive\01_design_patterns_formal\03_behavioral\mediator.md |
| docs\archive\deprecated_20260318\01_safe_23_catalog.md | memento | `../01_design_patterns_formal/03_behavioral/memento.md` | 文件不存在: docs\archive\01_design_patterns_formal\03_behavioral\memento.md |
| docs\archive\deprecated_20260318\01_safe_23_catalog.md | observer | `../01_design_patterns_formal/03_behavioral/observer.md` | 文件不存在: docs\archive\01_design_patterns_formal\03_behavioral\observer.md |
| docs\archive\deprecated_20260318\01_safe_23_catalog.md | state | `../01_design_patterns_formal/03_behavioral/state.md` | 文件不存在: docs\archive\01_design_patterns_formal\03_behavioral\state.md |
| docs\archive\deprecated_20260318\01_safe_23_catalog.md | strategy | `../01_design_patterns_formal/03_behavioral/strategy.md` | 文件不存在: docs\archive\01_design_patterns_formal\03_behavioral\strategy.md |
| docs\archive\deprecated_20260318\01_safe_23_catalog.md | template_method | `../01_design_patterns_formal/03_behavioral/template_method.md` | 文件不存在: docs\archive\01_design_patterns_formal\03_behavioral\template_method.md |
| docs\archive\deprecated_20260318\01_safe_23_catalog.md | visitor | `../01_design_patterns_formal/03_behavioral/visitor.md` | 文件不存在: docs\archive\01_design_patterns_formal\03_behavioral\visitor.md |
| docs\archive\deprecated_20260318\01_safe_23_catalog.md | singleton | `../01_design_patterns_formal/01_creational/singleton.md` | 文件不存在: docs\archive\01_design_patterns_formal\01_creational\singleton.md |
| docs\archive\deprecated_20260318\01_safe_23_catalog.md | builder | `../01_design_patterns_formal/01_creational/builder.md` | 文件不存在: docs\archive\01_design_patterns_formal\01_creational\builder.md |
| docs\archive\deprecated_20260318\01_safe_23_catalog.md | prototype | `../01_design_patterns_formal/01_creational/prototype.md` | 文件不存在: docs\archive\01_design_patterns_formal\01_creational\prototype.md |
| docs\archive\deprecated_20260318\01_safe_23_catalog.md | ownership_model | `../../formal_methods/ownership_model.md` | 文件不存在: docs\formal_methods\ownership_model.md |
| docs\archive\deprecated_20260318\01_safe_23_catalog.md | composite | `../01_design_patterns_formal/02_structural/composite.md` | 文件不存在: docs\archive\01_design_patterns_formal\02_structural\composite.md |
| docs\archive\deprecated_20260318\01_safe_23_catalog.md | async_state_machine | `../../formal_methods/async_state_machine.md` | 文件不存在: docs\formal_methods\async_state_machine.md |
| docs\archive\deprecated_20260318\01_safe_23_catalog.md | borrow_checker_proof | `../../formal_methods/borrow_checker_proof.md` | 文件不存在: docs\formal_methods\borrow_checker_proof.md |
| docs\archive\deprecated_20260318\01_safe_23_catalog.md | mediator | `../01_design_patterns_formal/03_behavioral/mediator.md` | 文件不存在: docs\archive\01_design_patterns_formal\03_behavioral\mediator.md |
| docs\archive\deprecated_20260318\01_safe_23_catalog.md | chain_of_responsibility | `../01_design_patterns_formal/03_behavioral/chain_of_responsibility.md` | 文件不存在: docs\archive\01_design_patterns_formal\03_behavioral\chain_of_responsibility.md |
| docs\archive\deprecated_20260318\01_safe_23_catalog.md | memento | `../01_design_patterns_formal/03_behavioral/memento.md` | 文件不存在: docs\archive\01_design_patterns_formal\03_behavioral\memento.md |
| docs\archive\deprecated_20260318\01_safe_23_catalog.md | borrow_checker_proof | `../../formal_methods/borrow_checker_proof.md` | 文件不存在: docs\formal_methods\borrow_checker_proof.md |
| docs\archive\deprecated_20260318\01_safe_23_catalog.md | ownership_model | `../../formal_methods/ownership_model.md` | 文件不存在: docs\formal_methods\ownership_model.md |
| docs\archive\deprecated_20260318\01_safe_23_catalog.md | 01_creational | `../01_design_patterns_formal/01_creational/README.md` | 文件不存在: docs\archive\01_design_patterns_formal\01_creational\README.md |
| docs\archive\deprecated_20260318\01_safe_23_catalog.md | borrow_checker_proof | `../../formal_methods/borrow_checker_proof.md` | 文件不存在: docs\formal_methods\borrow_checker_proof.md |
| docs\archive\deprecated_20260318\01_safe_23_catalog.md | 02_structural | `../01_design_patterns_formal/02_structural/README.md` | 文件不存在: docs\archive\01_design_patterns_formal\02_structural\README.md |
| docs\archive\deprecated_20260318\01_safe_23_catalog.md | async_state_machine | `../../formal_methods/async_state_machine.md` | 文件不存在: docs\formal_methods\async_state_machine.md |
| docs\archive\deprecated_20260318\01_safe_23_catalog.md | 03_behavioral | `../01_design_patterns_formal/03_behavioral/README.md` | 文件不存在: docs\archive\01_design_patterns_formal\03_behavioral\README.md |
| docs\archive\deprecated_20260318\01_safe_23_catalog.md | 02_complete_43_catalog | `./02_complete_43_catalog.md` | 文件不存在: docs\archive\deprecated_20260318\02_complete_43_catalog.md |
| docs\archive\deprecated_20260318\01_safe_23_catalog.md | THEORETICAL_AND_ARGUMENTATION_SYSTEM_ARCHITECTURE | `../../THEORETICAL_AND_ARGUMENTATION_SYSTEM_ARCHITECTURE.md` | 文件不存在: docs\THEORETICAL_AND_ARGUMENTATION_SYSTEM_ARCHITECTURE.md |
| docs\archive\deprecated_20260318\01_safe_23_catalog.md | ownership_model | `../../formal_methods/ownership_model.md` | 文件不存在: docs\formal_methods\ownership_model.md |
| docs\archive\deprecated_20260318\01_safe_23_catalog.md | borrow_checker_proof | `../../formal_methods/borrow_checker_proof.md` | 文件不存在: docs\formal_methods\borrow_checker_proof.md |
| docs\archive\deprecated_20260318\01_safe_23_catalog.md | type_system_foundations | `../../type_theory/type_system_foundations.md` | 文件不存在: docs\type_theory\type_system_foundations.md |
| docs\archive\deprecated_20260318\01_safe_23_catalog.md | Rust 1.94 迁移指南 | `../05_guides/RUST_194_MIGRATION_GUIDE.md` | 文件不存在: docs\archive\05_guides\RUST_194_MIGRATION_GUIDE.md |
| docs\archive\deprecated_20260318\01_safe_23_catalog.md | Rust 1.94 特性速查 | `../02_reference/quick_reference/rust_194_features_cheatsheet.md` | 文件不存在: docs\archive\02_reference\quick_reference\rust_194_features_cheatsheet.md |
| docs\archive\deprecated_20260318\01_safe_23_catalog.md | 性能调优指南 | `../05_guides/PERFORMANCE_TUNING_GUIDE.md` | 文件不存在: docs\archive\05_guides\PERFORMANCE_TUNING_GUIDE.md |
| docs\archive\deprecated_20260318\01_workflow_state_machine.md | 工作流概念族谱 | `../../WORKFLOW_CONCEPT_MINDMAP.md` | 文件不存在: docs\WORKFLOW_CONCEPT_MINDMAP.md |
| docs\archive\deprecated_20260318\01_workflow_state_machine.md | Saga 模式 | `../05_distributed/01_saga_pattern.md` | 文件不存在: docs\archive\05_distributed\01_saga_pattern.md |
| docs\archive\deprecated_20260318\01_workflow_state_machine.md | Rust 1.94 迁移指南 | `../05_guides/RUST_194_MIGRATION_GUIDE.md` | 文件不存在: docs\archive\05_guides\RUST_194_MIGRATION_GUIDE.md |
| docs\archive\deprecated_20260318\01_workflow_state_machine.md | Rust 1.94 特性速查 | `../02_reference/quick_reference/rust_194_features_cheatsheet.md` | 文件不存在: docs\archive\02_reference\quick_reference\rust_194_features_cheatsheet.md |
| docs\archive\deprecated_20260318\01_workflow_state_machine.md | 性能调优指南 | `../05_guides/PERFORMANCE_TUNING_GUIDE.md` | 文件不存在: docs\archive\05_guides\PERFORMANCE_TUNING_GUIDE.md |
| docs\archive\deprecated_20260318\02_cargo_workspace_guide.md | 01_compiler_features.md | `./01_compiler_features.md` | 文件不存在: docs\archive\deprecated_20260318\01_compiler_features.md |
| docs\archive\deprecated_20260318\02_cargo_workspace_guide.md | 03_rustdoc_advanced.md | `./03_rustdoc_advanced.md` | 文件不存在: docs\archive\deprecated_20260318\03_rustdoc_advanced.md |
| docs\archive\deprecated_20260318\02_cargo_workspace_guide.md | Rust 1.94 完整发布说明 | `./16_rust_1.94_release_notes.md` | 文件不存在: docs\archive\deprecated_20260318\16_rust_1.94_release_notes.md |
| docs\archive\deprecated_20260318\02_cargo_workspace_guide.md | Rust 1.94 采用指南 | `./18_rust_1.94_adoption_guide.md` | 文件不存在: docs\archive\deprecated_20260318\18_rust_1.94_adoption_guide.md |
| docs\archive\deprecated_20260318\02_cargo_workspace_guide.md | Rust 1.93 vs 1.94 对比 | `./17_rust_1.93_vs_1.94_comparison.md` | 文件不存在: docs\archive\deprecated_20260318\17_rust_1.93_vs_1.94_comparison.md |
| docs\archive\deprecated_20260318\02_compensation_chain.md | Saga 模式 | `../05_distributed/01_saga_pattern.md` | 文件不存在: docs\archive\05_distributed\01_saga_pattern.md |
| docs\archive\deprecated_20260318\02_compensation_chain.md | Rust 1.94 迁移指南 | `../05_guides/RUST_194_MIGRATION_GUIDE.md` | 文件不存在: docs\archive\05_guides\RUST_194_MIGRATION_GUIDE.md |
| docs\archive\deprecated_20260318\02_compensation_chain.md | Rust 1.94 特性速查 | `../02_reference/quick_reference/rust_194_features_cheatsheet.md` | 文件不存在: docs\archive\02_reference\quick_reference\rust_194_features_cheatsheet.md |
| docs\archive\deprecated_20260318\02_compensation_chain.md | 性能调优指南 | `../05_guides/PERFORMANCE_TUNING_GUIDE.md` | 文件不存在: docs\archive\05_guides\PERFORMANCE_TUNING_GUIDE.md |
| docs\archive\deprecated_20260318\03_long_running_transaction.md | Saga 模式 | `../05_distributed/01_saga_pattern.md` | 文件不存在: docs\archive\05_distributed\01_saga_pattern.md |
| docs\archive\deprecated_20260318\03_long_running_transaction.md | 工作流概念族谱 | `../../WORKFLOW_CONCEPT_MINDMAP.md` | 文件不存在: docs\WORKFLOW_CONCEPT_MINDMAP.md |
| docs\archive\deprecated_20260318\03_long_running_transaction.md | Rust 1.94 迁移指南 | `../05_guides/RUST_194_MIGRATION_GUIDE.md` | 文件不存在: docs\archive\05_guides\RUST_194_MIGRATION_GUIDE.md |
| docs\archive\deprecated_20260318\03_long_running_transaction.md | Rust 1.94 特性速查 | `../02_reference/quick_reference/rust_194_features_cheatsheet.md` | 文件不存在: docs\archive\02_reference\quick_reference\rust_194_features_cheatsheet.md |
| docs\archive\deprecated_20260318\03_long_running_transaction.md | 性能调优指南 | `../05_guides/PERFORMANCE_TUNING_GUIDE.md` | 文件不存在: docs\archive\05_guides\PERFORMANCE_TUNING_GUIDE.md |
| docs\archive\deprecated_20260318\03_semantic_boundary_map.md | SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS | `../../SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS.md` | 文件不存在: docs\SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS.md |
| docs\archive\deprecated_20260318\03_semantic_boundary_map.md | 05_boundary_system | `../05_boundary_system/README.md` | 文件不存在: docs\archive\05_boundary_system\README.md |
| docs\archive\deprecated_20260318\03_semantic_boundary_map.md | SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS | `../../SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS.md` | 文件不存在: docs\SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS.md |
| docs\archive\deprecated_20260318\03_semantic_boundary_map.md | supported_unsupported_matrix | `../05_boundary_system/supported_unsupported_matrix.md` | 文件不存在: docs\archive\05_boundary_system\supported_unsupported_matrix.md |
| docs\archive\deprecated_20260318\03_semantic_boundary_map.md | expressive_inexpressive_matrix | `../05_boundary_system/expressive_inexpressive_matrix.md` | 文件不存在: docs\archive\05_boundary_system\expressive_inexpressive_matrix.md |
| docs\archive\deprecated_20260318\03_semantic_boundary_map.md | SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS | `../../SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS.md` | 文件不存在: docs\SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS.md |
| docs\archive\deprecated_20260318\03_semantic_boundary_map.md | 01_design_patterns_formal §23 模式多维对比矩阵 | `../01_design_patterns_formal/README.md#23-模式多维对比矩阵` | 文件不存在: docs\archive\01_design_patterns_formal\README.md |
| docs\archive\deprecated_20260318\03_semantic_boundary_map.md | ownership_model | `../../formal_methods/ownership_model.md` | 文件不存在: docs\formal_methods\ownership_model.md |
| docs\archive\deprecated_20260318\03_semantic_boundary_map.md | borrow_checker_proof | `../../formal_methods/borrow_checker_proof.md` | 文件不存在: docs\formal_methods\borrow_checker_proof.md |
| docs\archive\deprecated_20260318\03_semantic_boundary_map.md | LANGUAGE_SEMANTICS_EXPRESSIVENESS | `../../LANGUAGE_SEMANTICS_EXPRESSIVENESS.md` | 文件不存在: docs\LANGUAGE_SEMANTICS_EXPRESSIVENESS.md |
| docs\archive\deprecated_20260318\03_semantic_boundary_map.md | 05_boundary_system | `../05_boundary_system/README.md` | 文件不存在: docs\archive\05_boundary_system\README.md |
| docs\archive\deprecated_20260318\03_semantic_boundary_map.md | 执行模型边界 | `../03_execution_models/06_boundary_analysis.md` | 文件不存在: docs\archive\03_execution_models\06_boundary_analysis.md |
| docs\archive\deprecated_20260318\03_semantic_boundary_map.md | Rust 1.94 迁移指南 | `../05_guides/RUST_194_MIGRATION_GUIDE.md` | 文件不存在: docs\archive\05_guides\RUST_194_MIGRATION_GUIDE.md |
| docs\archive\deprecated_20260318\03_semantic_boundary_map.md | Rust 1.94 特性速查 | `../02_reference/quick_reference/rust_194_features_cheatsheet.md` | 文件不存在: docs\archive\02_reference\quick_reference\rust_194_features_cheatsheet.md |
| docs\archive\deprecated_20260318\03_semantic_boundary_map.md | 性能调优指南 | `../05_guides/PERFORMANCE_TUNING_GUIDE.md` | 文件不存在: docs\archive\05_guides\PERFORMANCE_TUNING_GUIDE.md |
| docs\archive\deprecated_20260318\04_rust_1.91_vs_1.90_comparison.md | Rust 1.94 完整发布说明 | `./16_rust_1.94_release_notes.md` | 文件不存在: docs\archive\deprecated_20260318\16_rust_1.94_release_notes.md |
| docs\archive\deprecated_20260318\04_rust_1.91_vs_1.90_comparison.md | Rust 1.94 采用指南 | `./18_rust_1.94_adoption_guide.md` | 文件不存在: docs\archive\deprecated_20260318\18_rust_1.94_adoption_guide.md |
| docs\archive\deprecated_20260318\04_rust_1.91_vs_1.90_comparison.md | Rust 1.93 vs 1.94 对比 | `./17_rust_1.93_vs_1.94_comparison.md` | 文件不存在: docs\archive\deprecated_20260318\17_rust_1.93_vs_1.94_comparison.md |
| docs\archive\deprecated_20260318\06_rust_1.93_compatibility_notes.md | 12_rust_1.93.1_vs_1.93.0_comparison | `./12_rust_1.93.1_vs_1.93.0_comparison.md` | 文件不存在: docs\archive\deprecated_20260318\12_rust_1.93.1_vs_1.93.0_comparison.md |
| docs\archive\deprecated_20260318\06_rust_1.93_compatibility_notes.md | Rust 1.93 vs 1.92 对比 | `./05_rust_1.93_vs_1.92_comparison.md` | 文件不存在: docs\archive\deprecated_20260318\05_rust_1.93_vs_1.92_comparison.md |
| docs\archive\deprecated_20260318\08_fallback_pattern.md | Circuit Breaker | `./03_circuit_breaker.md` | 文件不存在: docs\archive\deprecated_20260318\03_circuit_breaker.md |
| docs\archive\deprecated_20260318\08_fallback_pattern.md | 超时模式 | `./06_timeout_pattern.md` | 文件不存在: docs\archive\deprecated_20260318\06_timeout_pattern.md |
| docs\archive\deprecated_20260318\08_fallback_pattern.md | 重试模式 | `./07_retry_pattern.md` | 文件不存在: docs\archive\deprecated_20260318\07_retry_pattern.md |
| docs\archive\deprecated_20260318\08_fallback_pattern.md | Rust 1.94 迁移指南 | `../05_guides/RUST_194_MIGRATION_GUIDE.md` | 文件不存在: docs\archive\05_guides\RUST_194_MIGRATION_GUIDE.md |
| docs\archive\deprecated_20260318\08_fallback_pattern.md | Rust 1.94 特性速查 | `../02_reference/quick_reference/rust_194_features_cheatsheet.md` | 文件不存在: docs\archive\02_reference\quick_reference\rust_194_features_cheatsheet.md |
| docs\archive\deprecated_20260318\08_fallback_pattern.md | 性能调优指南 | `../05_guides/PERFORMANCE_TUNING_GUIDE.md` | 文件不存在: docs\archive\05_guides\PERFORMANCE_TUNING_GUIDE.md |
| docs\archive\deprecated_20260318\ANTI_PATTERN_TEMPLATE.md | testing_cheatsheet | `./testing_cheatsheet.md` | 文件不存在: docs\archive\deprecated_20260318\testing_cheatsheet.md |
| docs\archive\deprecated_20260318\DEEP_DIVE_COMPLETION_REPORT.md | README.md | `./12-concurrency-patterns/README.md` | 文件不存在: docs\archive\deprecated_20260318\12-concurrency-patterns\README.md |
| docs\archive\deprecated_20260318\DEEP_DIVE_COMPLETION_REPORT.md | RUST_1.94_UPDATE_REPORT.md | `./08-advanced-topics/RUST_1.94_UPDATE_REPORT.md` | 文件不存在: docs\archive\deprecated_20260318\08-advanced-topics\RUST_1.94_UPDATE_REPORT.md |
| docs\archive\deprecated_20260318\DESIGN_PATTERNS_BOUNDARY_MATRIX.md | singleton.md | `01_creational/singleton.md` | 文件不存在: docs\archive\deprecated_20260318\01_creational\singleton.md |
| docs\archive\deprecated_20260318\DESIGN_PATTERNS_BOUNDARY_MATRIX.md | factory_method.md | `01_creational/factory_method.md` | 文件不存在: docs\archive\deprecated_20260318\01_creational\factory_method.md |
| docs\archive\deprecated_20260318\DESIGN_PATTERNS_BOUNDARY_MATRIX.md | abstract_factory.md | `01_creational/abstract_factory.md` | 文件不存在: docs\archive\deprecated_20260318\01_creational\abstract_factory.md |
| docs\archive\deprecated_20260318\DESIGN_PATTERNS_BOUNDARY_MATRIX.md | builder.md | `01_creational/builder.md` | 文件不存在: docs\archive\deprecated_20260318\01_creational\builder.md |
| docs\archive\deprecated_20260318\DESIGN_PATTERNS_BOUNDARY_MATRIX.md | prototype.md | `01_creational/prototype.md` | 文件不存在: docs\archive\deprecated_20260318\01_creational\prototype.md |
| docs\archive\deprecated_20260318\DESIGN_PATTERNS_BOUNDARY_MATRIX.md | adapter.md | `02_structural/adapter.md` | 文件不存在: docs\archive\deprecated_20260318\02_structural\adapter.md |
| docs\archive\deprecated_20260318\DESIGN_PATTERNS_BOUNDARY_MATRIX.md | bridge.md | `02_structural/bridge.md` | 文件不存在: docs\archive\deprecated_20260318\02_structural\bridge.md |
| docs\archive\deprecated_20260318\DESIGN_PATTERNS_BOUNDARY_MATRIX.md | composite.md | `02_structural/composite.md` | 文件不存在: docs\archive\deprecated_20260318\02_structural\composite.md |
| docs\archive\deprecated_20260318\DESIGN_PATTERNS_BOUNDARY_MATRIX.md | decorator.md | `02_structural/decorator.md` | 文件不存在: docs\archive\deprecated_20260318\02_structural\decorator.md |
| docs\archive\deprecated_20260318\DESIGN_PATTERNS_BOUNDARY_MATRIX.md | facade.md | `02_structural/facade.md` | 文件不存在: docs\archive\deprecated_20260318\02_structural\facade.md |
| docs\archive\deprecated_20260318\DESIGN_PATTERNS_BOUNDARY_MATRIX.md | flyweight.md | `02_structural/flyweight.md` | 文件不存在: docs\archive\deprecated_20260318\02_structural\flyweight.md |
| docs\archive\deprecated_20260318\DESIGN_PATTERNS_BOUNDARY_MATRIX.md | proxy.md | `02_structural/proxy.md` | 文件不存在: docs\archive\deprecated_20260318\02_structural\proxy.md |
| docs\archive\deprecated_20260318\DESIGN_PATTERNS_BOUNDARY_MATRIX.md | observer.md | `03_behavioral/observer.md` | 文件不存在: docs\archive\deprecated_20260318\03_behavioral\observer.md |
| docs\archive\deprecated_20260318\DESIGN_PATTERNS_BOUNDARY_MATRIX.md | strategy.md | `03_behavioral/strategy.md` | 文件不存在: docs\archive\deprecated_20260318\03_behavioral\strategy.md |
| docs\archive\deprecated_20260318\DESIGN_PATTERNS_BOUNDARY_MATRIX.md | state.md | `03_behavioral/state.md` | 文件不存在: docs\archive\deprecated_20260318\03_behavioral\state.md |
| docs\archive\deprecated_20260318\DESIGN_PATTERNS_BOUNDARY_MATRIX.md | command.md | `03_behavioral/command.md` | 文件不存在: docs\archive\deprecated_20260318\03_behavioral\command.md |
| docs\archive\deprecated_20260318\DESIGN_PATTERNS_BOUNDARY_MATRIX.md | iterator.md | `03_behavioral/iterator.md` | 文件不存在: docs\archive\deprecated_20260318\03_behavioral\iterator.md |
| docs\archive\deprecated_20260318\DESIGN_PATTERNS_BOUNDARY_MATRIX.md | template_method.md | `03_behavioral/template_method.md` | 文件不存在: docs\archive\deprecated_20260318\03_behavioral\template_method.md |
| docs\archive\deprecated_20260318\DESIGN_PATTERNS_BOUNDARY_MATRIX.md | mediator.md | `03_behavioral/mediator.md` | 文件不存在: docs\archive\deprecated_20260318\03_behavioral\mediator.md |
| docs\archive\deprecated_20260318\DESIGN_PATTERNS_BOUNDARY_MATRIX.md | memento.md | `03_behavioral/memento.md` | 文件不存在: docs\archive\deprecated_20260318\03_behavioral\memento.md |
| docs\archive\deprecated_20260318\DESIGN_PATTERNS_BOUNDARY_MATRIX.md | chain_of_responsibility.md | `03_behavioral/chain_of_responsibility.md` | 文件不存在: docs\archive\deprecated_20260318\03_behavioral\chain_of_responsibility.md |
| docs\archive\deprecated_20260318\DESIGN_PATTERNS_BOUNDARY_MATRIX.md | visitor.md | `03_behavioral/visitor.md` | 文件不存在: docs\archive\deprecated_20260318\03_behavioral\visitor.md |
| docs\archive\deprecated_20260318\DESIGN_PATTERNS_BOUNDARY_MATRIX.md | interpreter.md | `03_behavioral/interpreter.md` | 文件不存在: docs\archive\deprecated_20260318\03_behavioral\interpreter.md |
| docs\archive\deprecated_20260318\DESIGN_PATTERNS_BOUNDARY_MATRIX.md | 01_creational | `01_creational/README.md` | 文件不存在: docs\archive\deprecated_20260318\01_creational\README.md |
| docs\archive\deprecated_20260318\DESIGN_PATTERNS_BOUNDARY_MATRIX.md | 02_structural | `02_structural/README.md` | 文件不存在: docs\archive\deprecated_20260318\02_structural\README.md |
| docs\archive\deprecated_20260318\DESIGN_PATTERNS_BOUNDARY_MATRIX.md | 03_behavioral | `03_behavioral/README.md` | 文件不存在: docs\archive\deprecated_20260318\03_behavioral\README.md |
| docs\archive\deprecated_20260318\DESIGN_PATTERNS_BOUNDARY_MATRIX.md | ANTI_PATTERN_TEMPLATE | `../../../02_reference/quick_reference/ANTI_PATTERN_TEMPLATE.md` | 文件不存在: 02_reference\quick_reference\ANTI_PATTERN_TEMPLATE.md |
| docs\archive\deprecated_20260318\DESIGN_PATTERNS_BOUNDARY_MATRIX.md | Rust 设计模式实践指南 | `../../../05_guides/DESIGN_PATTERNS_USAGE_GUIDE.md` | 文件不存在: 05_guides\DESIGN_PATTERNS_USAGE_GUIDE.md |
| docs\archive\deprecated_20260318\DESIGN_PATTERNS_BOUNDARY_MATRIX.md | 所有权系统详解 | `../../../research_notes/formal_methods/ownership_model.md` | 文件不存在: research_notes\formal_methods\ownership_model.md |
| docs\archive\deprecated_20260318\DESIGN_PATTERNS_BOUNDARY_MATRIX.md | 类型状态模式指南 | `../06_rust_idioms.md` | 文件不存在: docs\archive\06_rust_idioms.md |
| docs\archive\deprecated_20260318\DESIGN_PATTERNS_BOUNDARY_MATRIX.md | 零成本抽象实践 | `../../../02_reference/quick_reference/generics_cheatsheet.md` | 文件不存在: 02_reference\quick_reference\generics_cheatsheet.md |
| docs\archive\deprecated_20260318\DESIGN_PATTERNS_BOUNDARY_MATRIX.md | Rust 1.94 迁移指南 | `../05_guides/RUST_194_MIGRATION_GUIDE.md` | 文件不存在: docs\archive\05_guides\RUST_194_MIGRATION_GUIDE.md |
| docs\archive\deprecated_20260318\DESIGN_PATTERNS_BOUNDARY_MATRIX.md | Rust 1.94 特性速查 | `../02_reference/quick_reference/rust_194_features_cheatsheet.md` | 文件不存在: docs\archive\02_reference\quick_reference\rust_194_features_cheatsheet.md |
| docs\archive\deprecated_20260318\DESIGN_PATTERNS_BOUNDARY_MATRIX.md | 性能调优指南 | `../05_guides/PERFORMANCE_TUNING_GUIDE.md` | 文件不存在: docs\archive\05_guides\PERFORMANCE_TUNING_GUIDE.md |
| docs\archive\deprecated_20260318\design_patterns_cheatsheet.md | 类型系统速查卡 | `./type_system.md` | 文件不存在: docs\archive\deprecated_20260318\type_system.md |
| docs\archive\deprecated_20260318\design_patterns_cheatsheet.md | 所有权系统速查卡 | `./ownership_cheatsheet.md` | 文件不存在: docs\archive\deprecated_20260318\ownership_cheatsheet.md |
| docs\archive\deprecated_20260318\design_patterns_cheatsheet.md | 泛型编程速查卡 | `./generics_cheatsheet.md` | 文件不存在: docs\archive\deprecated_20260318\generics_cheatsheet.md |
| docs\archive\deprecated_20260318\design_patterns_cheatsheet.md | 智能指针速查卡 | `./smart_pointers_cheatsheet.md` | 文件不存在: docs\archive\deprecated_20260318\smart_pointers_cheatsheet.md |
| docs\archive\deprecated_20260318\DESIGN_PATTERNS_MATRIX.md | Rust 1.94 迁移指南 | `../05_guides/RUST_194_MIGRATION_GUIDE.md` | 文件不存在: docs\archive\05_guides\RUST_194_MIGRATION_GUIDE.md |
| docs\archive\deprecated_20260318\DESIGN_PATTERNS_MATRIX.md | Rust 1.94 特性速查 | `../02_reference/quick_reference/rust_194_features_cheatsheet.md` | 文件不存在: docs\archive\02_reference\quick_reference\rust_194_features_cheatsheet.md |
| docs\archive\deprecated_20260318\DESIGN_PATTERNS_MATRIX.md | 性能调优指南 | `../05_guides/PERFORMANCE_TUNING_GUIDE.md` | 文件不存在: docs\archive\05_guides\PERFORMANCE_TUNING_GUIDE.md |
| docs\archive\deprecated_20260318\FORMAL_VERIFICATION_PRACTICAL_GUIDE.md | RUST_194_RESEARCH_UPDATE | `./RUST_194_RESEARCH_UPDATE.md` | 文件不存在: docs\archive\deprecated_20260318\RUST_194_RESEARCH_UPDATE.md |
| docs\archive\deprecated_20260318\FORMAL_VERIFICATION_PRACTICAL_GUIDE.md | Rust 1.94 迁移指南 | `../05_guides/RUST_194_MIGRATION_GUIDE.md` | 文件不存在: docs\archive\05_guides\RUST_194_MIGRATION_GUIDE.md |
| docs\archive\deprecated_20260318\FORMAL_VERIFICATION_PRACTICAL_GUIDE.md | Rust 1.94 特性速查 | `../02_reference/quick_reference/rust_194_features_cheatsheet.md` | 文件不存在: docs\archive\02_reference\quick_reference\rust_194_features_cheatsheet.md |
| docs\archive\deprecated_20260318\FORMAL_VERIFICATION_PRACTICAL_GUIDE.md | 性能调优指南 | `../05_guides/PERFORMANCE_TUNING_GUIDE.md` | 文件不存在: docs\archive\05_guides\PERFORMANCE_TUNING_GUIDE.md |
| docs\archive\deprecated_20260318\macros_cheatsheet.md | Rust 1.91 特性演示 | `../../../crates/c11_macro_system/examples/rust_191_features_demo.rs` | 文件不存在: crates\c11_macro_system\examples\rust_191_features_demo.rs |
| docs\archive\deprecated_20260318\macros_cheatsheet.md | Rust 1.92 特性演示 | `../../../crates/c11_macro_system/examples/rust_192_features_demo.rs` | 文件不存在: crates\c11_macro_system\examples\rust_192_features_demo.rs |
| docs\archive\deprecated_20260318\macros_cheatsheet.md | 类型系统速查卡 | `./type_system.md` | 文件不存在: docs\archive\deprecated_20260318\type_system.md |
| docs\archive\deprecated_20260318\macros_cheatsheet.md | 泛型编程速查卡 | `./generics_cheatsheet.md` | 文件不存在: docs\archive\deprecated_20260318\generics_cheatsheet.md |
| docs\archive\deprecated_20260318\macros_cheatsheet.md | 模块系统速查卡 | `./modules_cheatsheet.md` | 文件不存在: docs\archive\deprecated_20260318\modules_cheatsheet.md |
| docs\archive\deprecated_20260318\macros_cheatsheet.md | 测试速查卡 | `./testing_cheatsheet.md` | 文件不存在: docs\archive\deprecated_20260318\testing_cheatsheet.md |
| docs\archive\deprecated_20260318\MIND_REPRESENTATION_COMPLETION_PLAN.md | Rust 1.94 迁移指南 | `../05_guides/RUST_194_MIGRATION_GUIDE.md` | 文件不存在: docs\archive\05_guides\RUST_194_MIGRATION_GUIDE.md |
| docs\archive\deprecated_20260318\MIND_REPRESENTATION_COMPLETION_PLAN.md | Rust 1.94 特性速查 | `../02_reference/quick_reference/rust_194_features_cheatsheet.md` | 文件不存在: docs\archive\02_reference\quick_reference\rust_194_features_cheatsheet.md |
| docs\archive\deprecated_20260318\MIND_REPRESENTATION_COMPLETION_PLAN.md | 性能调优指南 | `../05_guides/PERFORMANCE_TUNING_GUIDE.md` | 文件不存在: docs\archive\05_guides\PERFORMANCE_TUNING_GUIDE.md |
| docs\archive\deprecated_20260318\RUST_194_MIGRATION_GUIDE.md | Rust 1.94 发布说明 | `../06_toolchain/16_rust_1.94_release_notes.md` | 文件不存在: docs\archive\06_toolchain\16_rust_1.94_release_notes.md |
| docs\archive\deprecated_20260318\RUST_194_MIGRATION_GUIDE.md | Rust 1.94 采用指南 | `../06_toolchain/18_rust_1.94_adoption_guide.md` | 文件不存在: docs\archive\06_toolchain\18_rust_1.94_adoption_guide.md |
| docs\archive\deprecated_20260318\RUST_194_MIGRATION_GUIDE.md | Rust 1.94 速查卡 | `../02_reference/quick_reference/rust_194_features_cheatsheet.md` | 文件不存在: docs\archive\02_reference\quick_reference\rust_194_features_cheatsheet.md |
| docs\archive\deprecated_20260318\RUST_194_MIGRATION_GUIDE.md | Rust 1.94 特性示例 | `../../crates/c01_ownership_borrow_scope/src/rust_194_features.rs` | 文件不存在: docs\crates\c01_ownership_borrow_scope\src\rust_194_features.rs |
| docs\archive\deprecated_20260318\UNSAFE_PATTERNS_GUIDE.md | UNSAFE_RUST_GUIDE.md | `./UNSAFE_RUST_GUIDE.md` | 文件不存在: docs\archive\deprecated_20260318\UNSAFE_RUST_GUIDE.md |
| docs\archive\deprecated_20260318\UNSAFE_PATTERNS_GUIDE.md | INLINE_ASSEMBLY_GUIDE.md | `./INLINE_ASSEMBLY_GUIDE.md` | 文件不存在: docs\archive\deprecated_20260318\INLINE_ASSEMBLY_GUIDE.md |
| docs\archive\deprecated_20260318\WORKFLOW_ENGINE_DECISION_TREE.md | Rust 1.94 迁移指南 | `../05_guides/RUST_194_MIGRATION_GUIDE.md` | 文件不存在: docs\archive\05_guides\RUST_194_MIGRATION_GUIDE.md |
| docs\archive\deprecated_20260318\WORKFLOW_ENGINE_DECISION_TREE.md | Rust 1.94 特性速查 | `../02_reference/quick_reference/rust_194_features_cheatsheet.md` | 文件不存在: docs\archive\02_reference\quick_reference\rust_194_features_cheatsheet.md |
| docs\archive\deprecated_20260318\WORKFLOW_ENGINE_DECISION_TREE.md | 性能调优指南 | `../05_guides/PERFORMANCE_TUNING_GUIDE.md` | 文件不存在: docs\archive\05_guides\PERFORMANCE_TUNING_GUIDE.md |
| docs\archive\reports\rust_194\RUST_194_COMPLETION_REPORT.md | 发布说明 | `./06_toolchain/16_rust_1.94_release_notes.md` | 文件不存在: docs\archive\reports\rust_194\06_toolchain\16_rust_1.94_release_notes.md |
| docs\archive\reports\rust_194\RUST_194_COMPLETION_REPORT.md | 版本对比 | `./06_toolchain/17_rust_1.93_vs_1.94_comparison.md` | 文件不存在: docs\archive\reports\rust_194\06_toolchain\17_rust_1.93_vs_1.94_comparison.md |
| docs\archive\reports\rust_194\RUST_194_COMPLETION_REPORT.md | 采用指南 | `./06_toolchain/18_rust_1.94_adoption_guide.md` | 文件不存在: docs\archive\reports\rust_194\06_toolchain\18_rust_1.94_adoption_guide.md |
| docs\archive\reports\rust_194\RUST_194_COMPLETION_REPORT.md | 迁移指南 | `./05_guides/RUST_194_MIGRATION_GUIDE.md` | 文件不存在: docs\archive\reports\rust_194\05_guides\RUST_194_MIGRATION_GUIDE.md |
| docs\archive\reports\rust_194\RUST_194_COMPLETION_REPORT.md | 速查卡 | `./02_reference/quick_reference/rust_194_features_cheatsheet.md` | 文件不存在: docs\archive\reports\rust_194\02_reference\quick_reference\rust_194_features_cheatsheet.md |
| docs\archive\reports\rust_194\RUST_194_COMPLETION_REPORT.md | 研究笔记 | `./research_notes/RUST_194_RESEARCH_UPDATE.md` | 文件不存在: docs\archive\reports\rust_194\research_notes\RUST_194_RESEARCH_UPDATE.md |
| docs\archive\reports\rust_194\RUST_194_COMPLETION_REPORT.md | c01 rust_194_features.rs | `../crates/c01_ownership_borrow_scope/src/rust_194_features.rs` | 文件不存在: docs\archive\reports\crates\c01_ownership_borrow_scope\src\rust_194_features.rs |
| docs\archive\reports\rust_194\RUST_194_COMPLETION_REPORT.md | c02 rust_194_features.rs | `../crates/c02_type_system/src/rust_194_features.rs` | 文件不存在: docs\archive\reports\crates\c02_type_system\src\rust_194_features.rs |
| docs\archive\reports\rust_194\RUST_194_DOCUMENTATION_COMPLETION_REPORT.md | 16_rust_1.94_release_notes.md | `./06_toolchain/16_rust_1.94_release_notes.md` | 文件不存在: docs\archive\reports\rust_194\06_toolchain\16_rust_1.94_release_notes.md |
| docs\archive\reports\rust_194\RUST_194_DOCUMENTATION_COMPLETION_REPORT.md | 17_rust_1.93_vs_1.94_comparison.md | `./06_toolchain/17_rust_1.93_vs_1.94_comparison.md` | 文件不存在: docs\archive\reports\rust_194\06_toolchain\17_rust_1.93_vs_1.94_comparison.md |
| docs\archive\reports\rust_194\RUST_194_DOCUMENTATION_COMPLETION_REPORT.md | 18_rust_1.94_adoption_guide.md | `./06_toolchain/18_rust_1.94_adoption_guide.md` | 文件不存在: docs\archive\reports\rust_194\06_toolchain\18_rust_1.94_adoption_guide.md |
| docs\archive\reports\rust_194\RUST_194_DOCUMENTATION_COMPLETION_REPORT.md | README.md | `./06_toolchain/README.md` | 文件不存在: docs\archive\reports\rust_194\06_toolchain\README.md |
| docs\archive\reports\rust_194\RUST_194_DOCUMENTATION_COMPLETION_REPORT.md | RUST_194_MIGRATION_GUIDE.md | `./05_guides/RUST_194_MIGRATION_GUIDE.md` | 文件不存在: docs\archive\reports\rust_194\05_guides\RUST_194_MIGRATION_GUIDE.md |
| docs\archive\reports\rust_194\RUST_194_DOCUMENTATION_COMPLETION_REPORT.md | RUST_194_RESEARCH_UPDATE.md | `./research_notes/RUST_194_RESEARCH_UPDATE.md` | 文件不存在: docs\archive\reports\rust_194\research_notes\RUST_194_RESEARCH_UPDATE.md |
| docs\archive\reports\rust_194\RUST_194_DOCUMENTATION_COMPLETION_REPORT.md | rust_194_features_cheatsheet.md | `./02_reference/quick_reference/rust_194_features_cheatsheet.md` | 文件不存在: docs\archive\reports\rust_194\02_reference\quick_reference\rust_194_features_cheatsheet.md |
| docs\archive\reports\rust_194\RUST_194_DOCUMENTATION_COMPLETION_REPORT.md | README.md | `./02_reference/quick_reference/README.md` | 文件不存在: docs\archive\reports\rust_194\02_reference\quick_reference\README.md |
| docs\archive\reports\rust_194\RUST_194_DOCUMENTATION_UPDATE_REPORT.md | Rust 1.94 发布说明 | `./06_toolchain/16_rust_1.94_release_notes.md` | 文件不存在: docs\archive\reports\rust_194\06_toolchain\16_rust_1.94_release_notes.md |
| docs\archive\reports\rust_194\RUST_194_DOCUMENTATION_UPDATE_REPORT.md | Rust 1.93 vs 1.94 对比 | `./06_toolchain/17_rust_1.93_vs_1.94_comparison.md` | 文件不存在: docs\archive\reports\rust_194\06_toolchain\17_rust_1.93_vs_1.94_comparison.md |
| docs\archive\reports\rust_194\RUST_194_DOCUMENTATION_UPDATE_REPORT.md | Rust 1.94 采用指南 | `./06_toolchain/18_rust_1.94_adoption_guide.md` | 文件不存在: docs\archive\reports\rust_194\06_toolchain\18_rust_1.94_adoption_guide.md |
| docs\archive\reports\rust_194\RUST_194_DOCUMENTATION_UPDATE_REPORT.md | Rust 1.94 迁移指南 | `./05_guides/RUST_194_MIGRATION_GUIDE.md` | 文件不存在: docs\archive\reports\rust_194\05_guides\RUST_194_MIGRATION_GUIDE.md |
| docs\archive\reports\rust_194\RUST_194_DOCUMENTATION_UPDATE_REPORT.md | Rust 1.94 研究笔记 | `./research_notes/RUST_194_RESEARCH_UPDATE.md` | 文件不存在: docs\archive\reports\rust_194\research_notes\RUST_194_RESEARCH_UPDATE.md |
| docs\archive\reports\rust_194\RUST_194_DOCUMENTATION_UPDATE_REPORT.md | Rust 1.94 速查卡 | `./02_reference/quick_reference/rust_194_features_cheatsheet.md` | 文件不存在: docs\archive\reports\rust_194\02_reference\quick_reference\rust_194_features_cheatsheet.md |
| docs\archive\reports\rust_194\RUST_194_DOCUMENTATION_UPDATE_REPORT.md | c01 Rust 1.94 特性 | `../crates/c01_ownership_borrow_scope/src/rust_194_features.rs` | 文件不存在: docs\archive\reports\crates\c01_ownership_borrow_scope\src\rust_194_features.rs |
| docs\archive\reports\rust_194\RUST_194_DOCUMENTATION_UPDATE_REPORT.md | c02 Rust 1.94 特性 | `../crates/c02_type_system/src/rust_194_features.rs` | 文件不存在: docs\archive\reports\crates\c02_type_system\src\rust_194_features.rs |
| docs\archive\reports\rust_194\RUST_194_DOCUMENTATION_UPDATE_REPORT.md | c06 Rust 1.94 特性 | `../crates/c06_async/src/rust_194_features.rs` | 文件不存在: docs\archive\reports\crates\c06_async\src\rust_194_features.rs |
| docs\archive\rust-ownership-chinese\rust_go_cpp_c_comprehensive_comparison.md | T Drawable | `item T` | 文件不存在: docs\archive\rust-ownership-chinese\item T |
| docs\archive\rust-ownership-chinese\rust_vs_go_comprehensive_analysis.md | T any | `x T` | 文件不存在: docs\archive\rust-ownership-chinese\x T |
| docs\archive\rust-ownership-chinese\rust_vs_go_comprehensive_analysis.md | T Drawable | `item T` | 文件不存在: docs\archive\rust-ownership-chinese\item T |
| docs\archive\rust-ownership-chinese\rust_vs_go_comprehensive_analysis.md | T Cloneable | `item T` | 文件不存在: docs\archive\rust-ownership-chinese\item T |
| docs\archive\rust-ownership-chinese\rust_vs_go_comprehensive_analysis.md | T Number | `numbers []T` | 文件不存在: docs\archive\rust-ownership-chinese\numbers []T |
| docs\archive\temp\FORMAL_AND_PRACTICAL_NAVIGATION.md | Cargo 工作空间指南 | `../../06_toolchain/02_cargo_workspace_guide.md` | 文件不存在: docs\06_toolchain\02_cargo_workspace_guide.md |
| docs\archive\temp\FORMAL_AND_PRACTICAL_NAVIGATION.md | 完整度报告 | `../../archive/root_completion_reports/FINAL_100_PERCENT_COMPLETION_REPORT_2026_01_27.md` | 文件不存在: docs\archive\root_completion_reports\FINAL_100_PERCENT_COMPLETION_REPORT_2026_01_27.md |
| docs\archive\temp\QUICK_START_SPELL_CHECK.md | SPELL_CHECK_CONFIGURATION.md | `../spell_check/SPELL_CHECK_CONFIGURATION.md` | 文件不存在: docs\archive\spell_check\SPELL_CHECK_CONFIGURATION.md |
| docs\content\ecosystem\README.md | Axum 基础 | `axum_deep_dive.md#基础` | 文件不存在: docs\content\ecosystem\axum_deep_dive.md |
| docs\content\ecosystem\README.md | 提取器详解 | `axum_deep_dive.md#提取器` | 文件不存在: docs\content\ecosystem\axum_deep_dive.md |
| docs\content\ecosystem\README.md | 中间件系统 | `axum_deep_dive.md#中间件` | 文件不存在: docs\content\ecosystem\axum_deep_dive.md |
| docs\content\ecosystem\README.md | 错误处理 | `axum_deep_dive.md#错误处理` | 文件不存在: docs\content\ecosystem\axum_deep_dive.md |
| docs\content\ecosystem\README.md | 性能优化 | `axum_deep_dive.md#性能优化` | 文件不存在: docs\content\ecosystem\axum_deep_dive.md |
| docs\research_notes\VISUALIZATION_INDEX.md | TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md | `../archive/process_reports/2026_02/TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md#思维导图任务关系网络` | 文件不存在: docs\archive\process_reports\2026_02\TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md |
| docs\research_notes\VISUALIZATION_INDEX.md | TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md | `../archive/process_reports/2026_02/TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md#概念对比矩阵` | 文件不存在: docs\archive\process_reports\2026_02\TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md |
| docs\research_notes\VISUALIZATION_INDEX.md | TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md | `../archive/process_reports/2026_02/TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md#概念对比矩阵` | 文件不存在: docs\archive\process_reports\2026_02\TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md |
| docs\research_notes\VISUALIZATION_INDEX.md | TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md | `../archive/process_reports/2026_02/TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md#概念对比矩阵` | 文件不存在: docs\archive\process_reports\2026_02\TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md |
| docs\research_notes\VISUALIZATION_INDEX.md | TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md | `../archive/process_reports/2026_02/TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md#决策树任务优先级决策` | 文件不存在: docs\archive\process_reports\2026_02\TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md |
| docs\research_notes\VISUALIZATION_INDEX.md | TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md | `../archive/process_reports/2026_02/TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md#进度跟踪矩阵` | 文件不存在: docs\archive\process_reports\2026_02\TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md |
| docs\research_notes\VISUALIZATION_INDEX.md | TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md | `../archive/process_reports/2026_02/TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md#进度跟踪矩阵` | 文件不存在: docs\archive\process_reports\2026_02\TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md |
| docs\research_notes\formal_methods\10_control_flow_decision_tree.md | ControlFlow 示例 | `../../../../examples/rust_194_control_flow_demo.rs` | 文件不存在: E:\_src\examples\rust_194_control_flow_demo.rs |
| docs\research_notes\software_design_theory\README.md | 03_semantic_boundary_map 场景 7–9 | `02_workflow_safe_complete_models/03_semantic_boundary_map.md#场景化-safe-决策-3-例` | 文件不存在: docs\research_notes\software_design_theory\02_workflow_safe_complete_models\03_semantic_boundary_map.md |
| docs\research_notes\software_design_theory\01_design_patterns_formal\README.md | 03_semantic_boundary_map §按需求反向查模式 | `../02_workflow_safe_complete_models/03_semantic_boundary_map.md#按需求反向查模式` | 文件不存在: docs\research_notes\software_design_theory\02_workflow_safe_complete_models\03_semantic_boundary_map.md |
| docs\research_notes\software_design_theory\05_boundary_system\README.md | 03_semantic_boundary_map 示例 1 | `../02_workflow_safe_complete_models/03_semantic_boundary_map.md#示例-1跨平台-ui-组件族` | 文件不存在: docs\research_notes\software_design_theory\02_workflow_safe_complete_models\03_semantic_boundary_map.md |
| docs\rust-ownership-decidability\CROSS_REFERENCE_VERIFICATION_REPORT.md | formal-foundations/models/ | `formal-foun... \|
\| MASTER_INDEX_AUTO.md \| `formal-foundations/semantics/` \| 54 \| \\| Semantics \\| [formal-foundations/semantics/](formal-found... \|
\| MASTER_INDEX_AUTO.md \| `formal-foundations/proofs/` \| 55 \| \\| Proofs \\| [formal-foundations/proofs/](formal-foundations... \|
\| MASTER_INDEX_AUTO.md \| `coq-formalization/` \| 56 \| \\| Coq Formalization \\| [coq-formalization/](coq-formalizati... \|
\| MASTER_INDEX_AUTO.md \| `formal-foundations/models/ownership-types.md` \| 73 \| - **Theory**: [ownership-types.md](formal-foundations/models... \|
\| MASTER_INDEX_AUTO.md \| `formal-foundations/models/borrow-semantics.md` \| 79 \| - **Theory**: [borrow-semantics.md](formal-foundations/model... \|
\| MASTER_INDEX_AUTO.md \| `formal-foundations/models/lifetime-logic.md` \| 85 \| - **Theory**: [lifetime-logic.md](formal-foundations/models/... \|
\| README.md \| `CROSS_REFERENCE_VERIFICATION_REPORT.md` \| 56 \| \\| [CROSS_REFERENCE_VERIFICATION_REPORT.md](CROSS_REFERENCE_... \|
\| README.md \| `formal-foundations/README.md` \| 65 \| \\| 形式化理论 \\| 形式化基础 (待补充` | 文件不存在: docs\rust-ownership-decidability\formal-foun... \|
\| MASTER_INDEX_AUTO.md \| `formal-foundations\semantics\` \| 54 \| \\| Semantics \\| [formal-foundations\semantics\](formal-found... \|
\| MASTER_INDEX_AUTO.md \| `formal-foundations\proofs\` \| 55 \| \\| Proofs \\| [formal-foundations\proofs\](formal-foundations... \|
\| MASTER_INDEX_AUTO.md \| `coq-formalization\` \| 56 \| \\| Coq Formalization \\| [coq-formalization\](coq-formalizati... \|
\| MASTER_INDEX_AUTO.md \| `formal-foundations\models\ownership-types.md` \| 73 \| - **Theory**: [ownership-types.md](formal-foundations\models... \|
\| MASTER_INDEX_AUTO.md \| `formal-foundations\models\borrow-semantics.md` \| 79 \| - **Theory**: [borrow-semantics.md](formal-foundations\model... \|
\| MASTER_INDEX_AUTO.md \| `formal-foundations\models\lifetime-logic.md` \| 85 \| - **Theory**: [lifetime-logic.md](formal-foundations\models\... \|
\| README.md \| `CROSS_REFERENCE_VERIFICATION_REPORT.md` \| 56 \| \\| [CROSS_REFERENCE_VERIFICATION_REPORT.md](CROSS_REFERENCE_... \|
\| README.md \| `formal-foundations\README.md` \| 65 \| \\| 形式化理论 \\| 形式化基础 (待补充 |
| docs\rust-ownership-decidability\CROSS_REFERENCE_VERIFICATION_REPORT.md | Coq代码 | `... \|
\| README.md \| `CROSS_REFERENCE_VERIFICATION_REPORT.md` \| 243 \| - [x] 完整的交叉引用 ([验证报告](CROSS_REFERENCE_VERIFICATION_REPORT.md... \|
<!-- markdown-link-check-enable -->

## Missing Cross-References

Files that mention key concepts but don't link to them:

\| Source File \| Concept \| Suggested Link \|
\|-------------\|---------\|----------------\|
\| 00-foundations/00-03-separation-logic.md \| ownership \| 01-core-concepts/detailed-concepts/ownership-deep-dive.md, 01-core-concepts/short-concepts/ownership-concept-card.md \|
\| 00-foundations/00-04-theory-connections.md \| ownership \| 01-core-concepts/detailed-concepts/ownership-deep-dive.md, 01-core-concepts/short-concepts/ownership-concept-card.md \|
\| 00-foundations/README.md \| formal \| formal-foundations/README.md \|
\| 01-core-concepts/01-01-ownership-rules.md \| ownership \| 01-core-concepts/detailed-concepts/ownership-deep-dive.md, 01-core-concepts/short-concepts/ownership-concept-card.md \|
\| 01-core-concepts/01-02-borrowing-system.md \| borrowing \| 01-core-concepts/detailed-concepts/borrowing-in-depth.md, 01-core-concepts/short-concepts/borrowing-concept-card.md \|
\| 01-core-concepts/01-02-borrowing-system.md \| lifetimes \| 01-core-concepts/detailed-concepts/lifetimes-mastery.md, 01-core-concepts/short-concepts/lifetime-concept-card.md \|
\| 01-core-concepts/01-03-lifetimes.md \| lifetimes \| 01-core-concepts/detailed-concepts/lifetimes-mastery.md, 01-core-concepts/short-concepts/lifetime-concept-card.md \|
\| 01-core-concepts/01-04-runtime-vs-compile-time.md \| ownership \| 01-core-concepts/detailed-concepts/ownership-deep-dive.md, 01-core-concepts/short-concepts/ownership-concept-card.md \|
\| 01-core-concepts/README.md \| ownership \| 01-core-concepts/detailed-concepts/ownership-deep-dive.md, 01-core-concepts/short-concepts/ownership-concept-card.md \|
\| 01-core-concepts/README.md \| borrowing \| 01-core-concepts/detailed-concepts/borrowing-in-depth.md, 01-core-concepts/short-concepts/borrowing-concept-card.md \|
\| 01-core-concepts/README.md \| lifetimes \| 01-core-concepts/detailed-concepts/lifetimes-mastery.md, 01-core-concepts/short-concepts/lifetime-concept-card.md \|
\| 01-core-concepts/detailed-concepts/borrowing-in-depth.md \| ownership \| 01-core-concepts/detailed-concepts/ownership-deep-dive.md, 01-core-concepts/short-concepts/ownership-concept-card.md \|
\| 01-core-concepts/ownership-counterexamples.md \| ownership \| 01-core-concepts/detailed-concepts/ownership-deep-dive.md, 01-core-concepts/short-concepts/ownership-concept-card.md \|
\| 01-core-concepts/ownership-counterexamples.md \| examples \| COMPLETE_EXAMPLES_AND_COUNTEREXAMPLES.md \|
\| 01-core-concepts/short-concepts/borrowing-concept-card.md \| lifetimes \| 01-core-concepts/detailed-concepts/lifetimes-mastery.md, 01-core-concepts/short-concepts/lifetime-concept-card.md \|
\| 03-verification-tools/03-01-verification-overview.md \| formal \| formal-foundations/README.md \|
\| 03-verification-tools/03-01-verification-overview.md \| coq \| coq-formalization/README.md \|
\| 03-verification-tools/03-02-creusot-deep-dive.md \| formal \| formal-foundations/README.md \|
\| 04-decidability-analysis/04-01-type-inference.md \| lifetimes \| 01-core-concepts/detailed-concepts/lifetimes-mastery.md, 01-core-concepts/short-concepts/lifetime-concept-card.md \|
\| 04-decidability-analysis/04-01-type-inference.md \| formal \| formal-foundations/README.md \|
\| 04-decidability-analysis/04-02-borrow-checking.md \| lifetimes \| 01-core-concepts/detailed-concepts/lifetimes-mastery.md, 01-core-concepts/short-concepts/lifetime-concept-card.md \|
\| 04-decidability-analysis/04-02-borrow-checking.md \| formal \| formal-foundations/README.md \|
\| 06-visualizations/06-01-concept-matrix.md \| coq \| coq-formalization/README.md \|
\| 06-visualizations/06-03-architecture-diagrams.md \| ownership \| 01-core-concepts/detailed-concepts/ownership-deep-dive.md, 01-core-concepts/short-concepts/ownership-concept-card.md \|
\| 06-visualizations/06-03-architecture-diagrams.md \| borrowing \| 01-core-concepts/detailed-concepts/borrowing-in-depth.md, 01-core-concepts/short-concepts/borrowing-concept-card.md \|
\| 06-visualizations/06-03-architecture-diagrams.md \| coq \| coq-formalization/README.md \|
\| 07-references/README.md \| formal \| formal-foundations/README.md \|
\| 07-references/academic-papers.md \| ownership \| 01-core-concepts/detailed-concepts/ownership-deep-dive.md, 01-core-concepts/short-concepts/ownership-concept-card.md \|
\| 07-references/academic-papers.md \| borrowing \| 01-core-concepts/detailed-concepts/borrowing-in-depth.md, 01-core-concepts/short-concepts/borrowing-concept-card.md \|
\| 07-references/academic-papers.md \| lifetimes \| 01-core-concepts/detailed-concepts/lifetimes-mastery.md, 01-core-concepts/short-concepts/lifetime-concept-card.md \|
\| 07-references/academic-papers.md \| formal \| formal-foundations/README.md \|
\| 07-references/bibliography.md \| borrowing \| 01-core-concepts/detailed-concepts/borrowing-in-depth.md, 01-core-concepts/short-concepts/borrowing-concept-card.md \|
\| 07-references/bibliography.md \| lifetimes \| 01-core-concepts/detailed-concepts/lifetimes-mastery.md, 01-core-concepts/short-concepts/lifetime-concept-card.md \|
\| 07-references/bibliography.md \| formal \| formal-foundations/README.md \|
\| 07-references/books-resources.md \| formal \| formal-foundations/README.md \|
\| 07-references/books-resources.md \| coq \| coq-formalization/README.md \|
\| 07-references/online-courses.md \| formal \| formal-foundations/README.md \|
\| 07-references/online-courses.md \| coq \| coq-formalization/README.md \|
\| 07-references/tools-libraries.md \| coq \| coq-formalization/README.md \|
\| 08-advanced-topics/08-04-proc-macros.md \| lifetimes \| 01-core-concepts/detailed-concepts/lifetimes-mastery.md, 01-core-concepts/short-concepts/lifetime-concept-card.md \|
\| 08-advanced-topics/RUST_1.94_UPDATE_REPORT.md \| ownership \| 01-core-concepts/detailed-concepts/ownership-deep-dive.md, 01-core-concepts/short-concepts/ownership-concept-card.md \|
\| 10-research-frontiers/10-01-future-directions.md \| ownership \| 01-core-concepts/detailed-concepts/ownership-deep-dive.md, 01-core-concepts/short-concepts/ownership-concept-card.md \|
\| 10-research-frontiers/10-01-future-directions.md \| borrowing \| 01-core-concepts/detailed-concepts/borrowing-in-depth.md, 01-core-concepts/short-concepts/borrowing-concept-card.md \|
\| 10-research-frontiers/10-01-future-directions.md \| formal \| formal-foundations/README.md \|
\| 10-research-frontiers/10-01-future-directions.md \| coq \| coq-formalization/README.md \|
\| 10-research-frontiers/10-02-type-system-extensions.md \| coq \| coq-formalization/README.md \|
\| 10-research-frontiers/10-03-verification-advancements.md \| coq \| coq-formalization/README.md \|
\| 10-research-frontiers/10-04-ownership-variations.md \| ownership \| 01-core-concepts/detailed-concepts/ownership-deep-dive.md, 01-core-concepts/short-concepts/ownership-concept-card.md \|
\| 10-research-frontiers/10-04-ownership-variations.md \| lifetimes \| 01-core-concepts/detailed-concepts/lifetimes-mastery.md, 01-core-concepts/short-concepts/lifetime-concept-card.md \|
\| 10-research-frontiers/10-05-ai-integration.md \| ownership \| 01-core-concepts/detailed-concepts/ownership-deep-dive.md, 01-core-concepts/short-concepts/ownership-concept-card.md \|

## Recommendations

### For Improving Navigation

1. **Add 'See Also' sections** to key documents linking related concepts
2. **Create topic hubs** for major themes (ownership, borrowing, lifetimes` | 文件不存在: docs\rust-ownership-decidability\... \|
\| README.md \| `CROSS_REFERENCE_VERIFICATION_REPORT.md` \| 243 \| - [x] 完整的交叉引用 ([验证报告](CROSS_REFERENCE_VERIFICATION_REPORT.md... \|
<!-- markdown-link-check-enable -->

 |
| docs\rust-ownership-decidability\05-comparative-study\05-03-rust-vs-go.md | T Number | `values []T` | 文件不存在: docs\rust-ownership-decidability\05-comparative-study\values []T |
| docs\rust-ownership-decidability\11-design-patterns\structural\decorator.md | B_behavior | `ConcreteDecoratorA[A](ConcreteComponent` | 文件不存在: docs\rust-ownership-decidability\11-design-patterns\structural\ConcreteDecoratorA[A](ConcreteComponent |
| docs\rust-ownership-decidability\16-program-semantics\workflow-patterns\08-multi-merge.md | i | `Branch(i` | 文件不存在: docs\rust-ownership-decidability\16-program-semantics\workflow-patterns\Branch(i |
| docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\09_reference\FAQ_AND_TROUBLESHOOTING.md | Ferrocene支持 | `mailto:support@ferrous-systems.com` | 文件不存在: docs\RUST_SAFETY_CRITICAL_ECOSYSTEM\09_reference\mailto:support@ferrous-systems.com |

## 修复建议

> **[来源: [TRPL](https://doc.rust-lang.org/book/)]** · **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

### 1. 文件不存在问题

- 检查链接路径是否正确
- 确认目标文件是否已被移动或删除
- 更新链接指向正确的文件位置

### 2. 锚点不存在问题

- 检查锚点ID是否与目标文件中的标题匹配
- GitHub风格锚点：将标题转换为小写，空格替换为连字符，移除标点
- 示例：`## Hello World!` -> `#hello-world`

### 3. 同文件锚点问题

- 检查文档中是否存在对应的标题
- 可能是文档结构已更改但目录未更新

## 源文件问题统计

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]** · **[来源: [TRPL](https://doc.rust-lang.org/book/)]**

| 源文件 | 损坏链接数 |
|:---|:---:|
| docs\archive\2026_03_reorganization\MASTER_INDEX_AUTO.md | 293 |
| docs\02_reference\ERROR_CODE_MAPPING.md | 58 |
| docs\archive\deprecated_20260318\01_safe_23_catalog.md | 49 |
| docs\archive\2026_03_reorganization\PROJECT_STRUCTURE.md | 40 |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | 40 |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | 34 |
| docs\archive\deprecated_20260318\DESIGN_PATTERNS_BOUNDARY_MATRIX.md | 34 |
| docs\02_reference\quick_reference\smart_pointers_cheatsheet.md | 28 |
| docs\02_reference\quick_reference\ownership_cheatsheet.md | 24 |
| docs\02_reference\quick_reference\type_system.md | 24 |
| docs\02_reference\quick_reference\error_handling_cheatsheet.md | 22 |
| docs\05_guides\BEST_PRACTICES.md | 22 |
| docs\archive\2026_05_historical_docs\12_rust_1.93.1_vs_1.93.0_comparison.md | 20 |
| docs\archive\2026_05_historical_docs\16_rust_1.94_release_notes.md | 19 |
| docs\archive\deprecated_20260318\03_semantic_boundary_map.md | 18 |
| docs\rust-ownership-decidability\case-studies\dashmap-formal-analysis.md | 17 |
| docs\rust-ownership-decidability\case-studies\tokio-runtime-formal-analysis.md | 17 |
| docs\02_reference\quick_reference\async_patterns.md | 16 |
| docs\research_notes\PROOF_INDEX.md | 16 |
| docs\research_notes\RUST_194_DEEP_SEMANTIC_ANALYSIS.md | 16 |
| docs\rust-ownership-decidability\00-foundations\00-01-linear-logic-deep.md | 16 |
| docs\archive\2026_05_historical_docs\13_rust_1.94_preview.md | 15 |
| docs\rust-ownership-decidability\case-studies\chrono-formal-analysis.md | 15 |
| docs\rust-ownership-decidability\case-studies\diesel-formal-analysis.md | 15 |
| docs\00_meta\analysis\RUST_2026_PROJECT_GOALS_MONTHLY_TRACKING.md | 14 |
| docs\02_reference\quick_reference\strings_formatting_cheatsheet.md | 14 |
| docs\archive\deprecated_20260318\axum-formal-analysis.md | 14 |
| docs\archive\version_reports\RUST_192_EXAMPLE_COMPATIBILITY_REPORT.md | 14 |
| docs\research_notes\CROSS_REFERENCE_INDEX.md | 14 |
| docs\research_notes\INTERVIEW_QUESTIONS_COLLECTION.md | 14 |
| docs\research_notes\software_design_theory\04_compositional_engineering\03_integration_theory.md | 14 |
| docs\rust-ownership-decidability\case-studies\pin-project-formal-analysis.md | 14 |
| docs\rust-ownership-decidability\case-studies\pyo3-formal-analysis.md | 14 |
| docs\rust-ownership-decidability\case-studies\smoltcp-formal-analysis.md | 14 |
| docs\rust-ownership-decidability\case-studies\tokio-stream-formal-analysis.md | 14 |
| docs\rust-ownership-decidability\case-studies\tower-formal-analysis.md | 14 |
| docs\00_meta\analysis\RUST_GLOBAL_ALIGNMENT_SYMMETRIC_DIFFERENCE_ANALYSIS_2026.md | 13 |
| docs\archive\deprecated_20260318\sea-orm-formal-analysis.md | 13 |
| docs\rust-ownership-decidability\DOCUMENT_INDEX_MASTER.md | 13 |
| docs\rust-ownership-decidability\case-studies\clap-formal-analysis.md | 13 |
| docs\rust-ownership-decidability\case-studies\embedded-storage-formal-analysis.md | 13 |
| docs\rust-ownership-decidability\case-studies\rtic-formal-analysis.md | 13 |
| docs\rust-ownership-decidability\case-studies\tonic-formal-analysis.md | 13 |
| docs\rust-ownership-decidability\progress\2026-03-06_TRUE_100_PERCENT_COMPLETION_CERTIFICATION.md | 13 |
| docs\02_reference\quick_reference\collections_iterators_cheatsheet.md | 12 |
| docs\04_thinking\PROOF_GRAPH_NETWORK.md | 12 |
| docs\04_thinking\THINKING_REPRESENTATION_METHODS.md | 12 |
| docs\research_notes\TEMPLATE.md | 12 |
| docs\rust-ownership-decidability\AUTHORITY_ALIGNMENT_GAP_ANALYSIS.md | 12 |
| docs\rust-ownership-decidability\COMPREHENSIVE_KNOWLEDGE_SYNTHESIS.md | 12 |
| ... 还有 929 个文件 | |

**总计 979 个文件包含损坏链接**

---

## 来源与延伸阅读

| 来源 | 链接 | 说明 |
|:---|:---|:---|
| Rust Reference | <https://doc.rust-lang.org/reference/> | Rust 语言官方参考文档 |
| The Rust Programming Language (TRPL) | <https://doc.rust-lang.org/book/> | Rust 官方教程 |
| Rust Standard Library | <https://doc.rust-lang.org/std/> | Rust 标准库文档 |
| Rustonomicon | <https://doc.rust-lang.org/nomicon/> | Rust 高级/Unsafe 编程指南 |
| RFCs - github.com/rust-lang/rfcs | <https://github.com/rust-lang/rfcs> | Rust 语言 RFC 仓库 |

> 相关文档: [概念知识体系](../concept/README.md)
