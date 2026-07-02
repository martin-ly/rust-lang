# 语义表征与国际化对齐 Q3-Q4 2026 执行检查清单

> **对应计划**：`C:\Users\luyan\.kimi\plans\jean-grey-pantha-psylocke.md`
> **方案**：推荐方案 A — P0 先行 + i18n 并行 + 工具链逐步落地
> **启动日期**：2026-06-27
> **状态**：🔄 进行中

---

## P0 任务（2026 Q3，立即执行）

| ID | 任务 | 目标文件 | 状态 | 负责人 | 完成日期 |
|:---|:---|:---|:---:|:---|:---:|
| P0-1 | KG 升级到 RDF 1.2 / RDF-star | `concept/00_meta/kg_ontology_v2.md` | ✅ | AI | 2026-06-27 |
| P0-2 | `kg_data.json` 引入 SKOS 多语言标签 | `concept/00_meta/kg_data_v2.json` | ✅ | AI | 2026-06-27 |
| P0-3 | 设计 SHACL shapes | `concept/00_meta/kg_shapes.ttl` | ✅ | AI | 2026-06-27 |
| P0-4 | 通用 PL 基座：变量模型 | `concept/01_foundation/20_variable_model.md` | ✅ | AI | 2026-06-27 |
| P0-5 | 通用 PL 基座：求值策略 | `concept/04_formal/18_evaluation_strategies.md` | ✅ | AI | 2026-06-27 |
| P0-6 | 通用 PL 基座：副作用与纯度 | `concept/01_foundation/21_effects_and_purity.md` | ✅ | AI | 2026-06-27 |
| P0-7 | C/C++ 工程层：ABI 与对象模型 | `concept/05_comparative/02_cpp_abi_object_model.md` | ✅ | AI | 2026-06-27 |
| P0-8 | C/C++ 工程层：Move 语义系统对比 | 扩展 `concept/05_comparative/01_rust_vs_cpp.md` | ✅ | AI | 2026-06-27 |
| P0-9 | C/C++ 工程层：异常安全深度对比 | 扩展 `concept/02_intermediate/04_error_handling.md` | ✅ | AI | 2026-06-27 |

## P1 任务（2026 Q3-Q4）

| ID | 任务 | 目标文件 | 状态 | 负责人 | 完成日期 |
|:---|:---|:---|:---:|:---|:---:|
| P1-1 | Rust 语义 Web 工具链 crate | `crates/c14_semantic_web/` | ✅ | AI | 2026-06-27 |
| P1-2 | 概念依赖推理脚本 | `scripts/kg_reasoning.py` | ✅ | AI | 2026-06-27 |
| P1-3 | 术语一致性脚本升级 | `scripts/add_bilingual_annotations.py` | ✅ | AI | 2026-06-27 |
| P1-4 | 控制流理论深化 | 扩展 `concept/03_control_flow/07_control_flow.md` | ⬜ | AI | - |
| P1-5 | 数据抽象谱系 | `concept/01_foundation/22_data_abstraction_spectrum.md` | ✅ | AI | 2026-06-27 |
| P1-6 | 模式组合代数 | `concept/06_ecosystem/99_pattern_composition_algebra.md` | ⬜ | AI | - |
| P1-7 | 算法-模式-工作流语义桥 | 扩展 `concept/00_meta/semantic_bridge_algorithms_patterns.md` | ⬜ | AI | - |
| P1-8 | SFINAE / C++20 Concepts vs Trait Bounds | 扩展 `concept/02_intermediate/01_traits.md` | ⬜ | AI | - |

## P2 任务（2026 Q4 及以后）

| ID | 任务 | 目标文件 | 状态 | 负责人 | 完成日期 |
|:---|:---|:---|:---:|:---|:---:|
| P2-1 | 向量语义与 KG-RAG | `tools/kg_rag/` | ⬜ | AI | - |
| P2-2 | 多语言 KG 对齐自动化 | `scripts/multilingual_alignment.py` | ⬜ | AI | - |
| P2-3 | 顶层本体（TLO）对齐 | `concept/00_meta/kg_tlo_alignment.md` | ⬜ | AI | - |
| P2-4 | OWL 2 一致性检查 | `scripts/owl_consistency_check.py` | ⬜ | AI | - |
| P2-5 | 交互式知识图谱浏览器 | `tools/kg_browser/` | ⬜ | AI | - |
| P2-6 | 形式化证明机械验证 | `docs/rust-ownership-decidability/coq-formalization/` | ⬜ | AI | - |

## i18n 任务（2026 Q4）

| ID | 任务 | 验收标准 | 状态 | 负责人 | 完成日期 |
|:---|:---|:---|:---:|:---|:---:|
| i18n-1 | 英文骨架模板冻结 | `concept/00_meta/bilingual_template.md` 定稿 | ✅ | AI | 2026-06-27 |
| i18n-2 | concept/ 英文骨架覆盖 80% | 313 文件 EN 骨架元数据已补全 | ✅ | AI | 2026-06-27 |
| i18n-3 | 术语表强制执行 | 脚本运行无未标注术语 | ⬜ | AI | - |
| i18n-4 | TRPL 3rd Ed 逐章对照 | `LEARNING_MVP_PATH.md` 含 TRPL Ch1-Ch21 映射 | ⬜ | AI | - |
| i18n-5 | Brown Book Ownership Inventory 练习国际化 | `exercises/src/ownership_borrowing/brown_inventories/` 新增 8 练习 | ⬜ | AI | - |
| i18n-6 | 多语言术语漂移检测 | `scripts/multilingual_alignment.py` 输出待审校清单 | ⬜ | AI | - |
| i18n-7 | 可用性测试 | `reports/I18N_USABILITY_TEST_Q4_2026.md` | ⬜ | AI | - |
| i18n-8 | 教师/讲师反馈 | `reports/I18N_EDUCATOR_FEEDBACK_Q4_2026.md` | ⬜ | AI | - |

---

## 里程碑

| 日期 | 里程碑 | 状态 |
|:---|:---|:---:|
| 2026-07-31 | P0 基座补全 | ⬜ |
| 2026-08-31 | KG 标准升级 | ⬜ |
| 2026-09-30 | Rust 语义 Web 工具链落地 | ⬜ |
| 2026-10-31 | i18n 基础设施冻结 | ⬜ |
| 2026-11-30 | 英文骨架 80% + TRPL 对照 | ⬜ |
| 2026-12-31 | 验证与 KG-RAG 原型 | ⬜ |

---

**最后更新**：2026-06-27
