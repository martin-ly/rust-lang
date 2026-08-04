# WS-G AI Ontology 语义对齐报告

**EN**: WS-G AI Ontology Semantic Alignment Report
**Summary**: Alignment of the Rust knowledge graph ontology with OWL2/SKOS/SHACL standards, LLM semantic retrieval architecture, and GraphRAG patterns.

> **Rust 版本**: 1.97.0+ (Edition 2024)
> **工作流**: WS-G AI ontology
> **日期**: 2026-08-04
> **治理依据**: AGENTS.md §2 Canonical、§3 去重、§5 质量门、§6 红线

---

## 一、范围与目标

本次工作流聚焦 `concept/00_meta/knowledge_topology/kg_ontology_v2.md` 与 `tools/kg_rag/`，目标：

1. 将项目 KG 本体显式映射到 OWL2/SKOS/SHACL 三层标准。
2. 定义 LLM 语义检索架构（ dense + graph + hybrid ）。
3. 定义四种 GraphRAG 模式并给出决策树。
4. 引入来源链路谓词：`ex:explainedByLLM`、`ex:verifiedByCompiler`、`ex:derivedFromRFC` 等。
5. 提供可运行的 `llm_semantic_retriever.py` 原型。

---

## 二、权威来源清单

| 级别 | 来源 | 用途 |
|:---|:---|:---|
| P0 | [W3C RDF 1.2 / RDF-star](https://www.w3.org/TR/rdf12-concepts/) | 三元组模型与来源注解 |
| P0 | [W3C SKOS Reference](https://www.w3.org/TR/skos-reference/) | 多语言概念组织 |
| P0 | [W3C SHACL](https://www.w3.org/TR/shacl/) | 数据形状验证 |
| P0 | [W3C JSON-LD 1.1](https://www.w3.org/TR/json-ld11/) | 机器可读序列化 |
| P1 | [Hogan et al. — Knowledge Graphs (ACM Comput. Surv. 2021)](https://dl.acm.org/doi/10.1145/3447772) | KG 综述与方法论 |
| P1 | [Baader et al. — The Description Logic Handbook, 2nd ed.](https://doi.org/10.1017/CBO9780511711787) | OWL/描述逻辑形式化 |
| P2 | [Microsoft GraphRAG](https://microsoft.github.io/graphrag/) | GraphRAG 架构模式 |
| P2 | [OpenAI Function Calling](https://platform.openai.com/docs/guides/function-calling) | LLM 结构化输出 |
| P2 | [LangChain Graph RAG](https://python.langchain.com/docs/use_cases/graph/) | 检索编排参考 |

---

## 三、语义对齐表

| 维度 | 本地状态（P7 前） | 权威来源状态 | 差异 | 修复动作 |
|:---|:---|:---|:---|:---|
| **OWL2 类映射** | `ex:Concept` 等未显式声明为 `owl:Class` | OWL2 要求类、属性、特征显式声明 | 缺少 OWL 特征矩阵 | 在 `kg_ontology_v2.md` §10.2 补充类/属性映射表 |
| **SKOS 映射** | 已使用 `skos:prefLabel`/`definition` | SKOS 完整标签体系：pref/alt/hidden/broader/narrower/related | `broader`/`narrower` 与 `ex:refines` 映射未显式 | 在 §10.3 给出映射表与一致性规则 |
| **SHACL 形状** | 已有 `kg_shapes.ttl` 入口 | SHACL 标准约束 | 新增谓词未在形状中覆盖 | 在 §10.4 给出示例 shape；计划 KG 刷新时同步 |
| **LLM 来源谓词** | 缺失 | LLM+KG 需要区分“生成解释”与“权威事实” | 无 `explainedByLLM` | 在 §13 定义为 `owl:ObjectProperty` |
| **编译器验证谓词** | 缺失 | 安全主张需机器验证 | 无 `verifiedByCompiler` | 在 §13 定义，并写入反例要求 |
| **RFC 溯源谓词** | 使用 `prov:wasDerivedFrom` 文本 URL | 需要结构化 RFC 节点 | 仅有 URL，无 `ex:RFC` 类型节点 | 在 §13 定义 `ex:derivedFromRFC` |
| **形式化工具验证** | 缺失 | RustBelt/Kani/Prusti 等 | 无 `verifiedByFormalTool` | 在 §13 定义 |
| **权威页链接** | 缺失 | canonical 规则要求概念→权威页 | 无 `ex:canonicalPage` | 在 §13 定义 |
| **检索架构** | 仅有高层文字描述 | GraphRAG 需要实体链接、子图扩展、社区摘要、来源过滤 | 缺少组件职责矩阵与模式化描述 | 在 §11–§12 补充架构图、矩阵、四种模式 |
| **决策树** | 缺失 | 需要根据查询类型选择检索策略 | 无判定流程 | 在 §14 提供 mermaid flowchart |
| **推理示例** | 缺失 | 需展示 KG 如何支撑正/反向推理 | 无示例 | 在 §15 给出 RFC 推导与问题溯源示例 |
| **反例** | 较少 | 需说明 LLM 解释不能替代编译器/RFC | 无系统反例 | 在 §16 给出 4 个反例 |

---

## 四、新增/修改文件

| 路径 | 动作 | 说明 |
|:---|:---:|:---|
| `concept/00_meta/knowledge_topology/kg_ontology_v2.md` | 增强 | 新增 §10–§18：OWL2/SKOS/SHACL 映射、LLM 检索架构、GraphRAG、新谓词、决策树、推理示例、反例、语义对齐矩阵；补充前置/后置概念与认知路径 |
| `tools/kg_rag/llm_semantic_retriever.py` | 新增 | KG-RAG 检索器原型：实体链接、谓词约束多跳、RDF-star 引用、可选向量混合检索 |
| `tools/kg_rag/README.md` | 增强 | 补充 `llm_semantic_retriever.py` 模块说明 |
| `reports/AI_ONTOLOGY_AUTHORITY_ALIGNMENT_2026_08.md` | 新增 | 本报告 |

### 4.1 `kg_ontology_v2.md` 主要新增内容

- **§10 OWL2/SKOS/SHACL 显式映射**：mindmap、三层映射表、OWL 类/属性映射表、SKOS 映射表、SHACL shape 示例、映射一致性规则。
- **§11 LLM 语义检索架构**：mermaid 架构图、组件职责矩阵、数据流 JSON-LD 示例、来源可解释性要求。
- **§12 GraphRAG 模式**：与传统 RAG 对比矩阵、实体中心子图、谓词约束多跳、社区摘要、RDF-star 来源感知四种模式。
- **§13 新谓词与来源链路**：`ex:explainedByLLM`、`ex:verifiedByCompiler`、`ex:derivedFromRFC`、`ex:verifiedByFormalTool`、`ex:documentedIn`、`ex:canonicalPage`、`ex:hasRustVersion`、`ex:reviewStatus`、`ex:confidence`；含 OWL 声明、Rust 可编译示例、工具集成说明。
- **§14 检索策略决策树**：mermaid flowchart，区分可验证/非可验证、实体识别、来源过滤、多跳/综述路径。
- **§15 正向/反向推理示例**：RFC → 概念、用户问题 → 权威来源、反事实缺失来源谓词。
- **§16 反例与边界**：LLM 解释直接当权威、忽略置信度、混淆 SKOS related 与 dependsOn、LLM 不能替代编译器。
- **§17 语义对齐矩阵**：维度、本地状态、权威状态、差异、修复动作汇总。
- **§18 演进与质量门**：KG 刷新计划、`kg_shapes.ttl` 更新、`llm_semantic_retriever.py` 集成、季度审计、相关质量门状态。

### 4.2 `llm_semantic_retriever.py` 能力

- **Graph-only 模式**：无需 numpy/sentence-transformers，仅依赖 `kg_core.py`。
- **Hybrid 模式**：`--vector` 调用 `kg_rag.py` 的 `build_index`/`hybrid_search`。
- **SKOS 实体链接**：基于 `prefLabel`/`altLabel`/`hiddenLabel` 的轻量匹配。
- **谓词约束多跳**：默认沿 `dependsOn`/`entails`/`mutexWith`/`refines`/`equivalentTo`/`counterExample` 扩展。
- **RDF-star 来源**：从 `kg_data_v3.json` 的 `@annotation` 提取 `ex:source`、`ex:confidence` 等并生成 `[source: ...]` 引用。

---

## 五、验证结果

| 检查项 | 命令 | 结果 |
|:---|:---|:---:|
| Rust 代码块编译 | `rustc --edition 2024` on extracted snippet | ✅ 通过 |
| Python 语法检查 | `python -m py_compile tools/kg_rag/llm_semantic_retriever.py` | ✅ 通过 |
| 检索器 graph-only 运行 | `python tools/kg_rag/llm_semantic_retriever.py --query ownership --top-k 3 --hops 1` | ✅ 输出上下文与三元组 |
| 内容重叠检测 | `python scripts/detect_content_overlap.py` | ✅ 未发现 `kg_ontology_v2.md` 新内容重复 |
| 命名规范 lint | `python scripts/check_naming_convention.py --strict` | ✅ ERROR=0 |
| 知识体系审计 | `python scripts/kb_auditor.py --link-check` | ✅ `kg_ontology_v2.md` 行内/跨层检查通过；死链与跨层问题来自其他 WS 文件 |
| KG 形状 | `python scripts/check_kg_shapes.py --strict` | ✅ K1–K7=0 |
| 关系精度 | `python scripts/check_kg_relation_precision.py --strict` | ✅ generic_ratio=0.00% |
| 概念代码块 | `python scripts/check_concept_code_blocks.py --strict` | ⚠️ 未命中 `kg_ontology_v2.md`；手动 `rustc --edition 2024` 验证 Rust 示例通过；全库抽样发现 5 处 rot（其他文件既有问题） |
| 元数据一致性 | `python scripts/check_metadata_consistency.py --strict` | ⚠️ D5=1（`concept/06_ecosystem/16_algorithm_patterns/08_data_structures_in_rust.md`），与本次无关 |

---

## 六、待完成/依赖

1. **KG 刷新**：下一轮 `scripts/generate_kg_v3.py` / `apply_kg_semantic_predicates.py` 需把 `ex:explainedByLLM`、`ex:verifiedByCompiler`、`ex:derivedFromRFC` 等谓词实例化到 `kg_data_v3.json`。
2. **SHACL 更新**：`concept/00_meta/kg_shapes.ttl` 需补充新增谓词的 `NodeShape`/`PropertyShape`。
3. **全质量门复跑**：P7 集成阶段需运行全部 23 阻断门 + 5 观察门，确认 `generic_ratio` 仍为 0%。
4. ~~README 更新~~：已补充 `tools/kg_rag/README.md` 模块说明。

---

## 七、结论

WS-G AI ontology 工作流已完成 `kg_ontology_v2.md` 的 P7 增强与 `llm_semantic_retriever.py` 原型交付。新增内容覆盖 OWL2/SKOS/SHACL 显式映射、LLM 语义检索架构、GraphRAG 四种模式、9 个新来源/验证谓词、决策树、正反推理示例与系统反例，符合 AGENTS.md 的 canonical、元数据、思维表征与代码块规范。待 KG 刷新与质量门集成验证。
