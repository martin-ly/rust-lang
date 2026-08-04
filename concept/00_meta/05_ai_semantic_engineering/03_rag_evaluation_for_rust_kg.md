# 面向 Rust 知识图谱的 RAG 评估

> **EN**: RAG Evaluation for the Rust Knowledge Graph
> **Summary**: A production-oriented guide to evaluating retrieval-augmented generation over the Rust knowledge graph, covering IR metrics (recall@k, MRR, NDCG), embedding providers (local sentence-transformers and OpenAI-compatible APIs), source attribution, and the `semantic_alignment_pipeline.py` tooling.
>
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **Bloom 层级**: L0 / Meta
> **受众**: [研究者] / [维护者]
> **内容分级**: [研究者级]
> **A/S/P 标记**: **S** — Semantic engineering / **P** — Procedure
> **权威来源**: 本文件为 `concept/` 权威页。
> **前置概念**: [`concept/00_meta/05_ai_semantic_engineering/01_knowledge_graph_design.md`](01_knowledge_graph_design.md)、[`concept/00_meta/05_ai_semantic_engineering/02_llm_rag_for_rust.md`](02_llm_rag_for_rust.md)、[`concept/00_meta/knowledge_topology/kg_ontology_v2.md`](../knowledge_topology/kg_ontology_v2.md)
> **后置概念**: [`tools/kg_rag/semantic_alignment_pipeline.py`](../../../tools/kg_rag/semantic_alignment_pipeline.py)、[`reports/RAG_EVALUATION_BASELINE_2026_08.md`](../../../reports/RAG_EVALUATION_BASELINE_2026_08.md)
> **对齐来源**: [RAGAS] · [BEIR] · [MS MARCO] · [OpenAI Embeddings] · [sentence-transformers] · [W3C SKOS] · [W3C RDF-star] · [The Rust Reference](https://doc.rust-lang.org/reference/)

---

## 〇、认知路径

本页把 RAG 评估从"凭感觉看回答好坏"推进到**可量化、可回归、可 CI 化**的工程实践。阅读路径：

1. 明确 Rust KG 上 RAG 评估的独特约束（概念密集、来源敏感、多跳关系）；
2. 掌握召回、排序与归因三类指标（recall@k、MRR、NDCG、source recall）；
3. 理解本地嵌入模型与 OpenAI 兼容 API 两种生产部署方式；
4. 学会运行 `semantic_alignment_pipeline.py` 并解读基线报告。

---

## 一、为什么 Rust KG 需要专门的 RAG 评估

通用 RAG 基准（如 Natural Questions、MS MARCO）关注的是**开放域事实问答**。Rust 知识图谱上的 RAG 有额外要求：

| 特征 | 对评估的影响 |
|---|---|
| **概念高度交织** | 单个查询往往涉及所有权 + 生命周期 + Trait 多跳推理，需要评估图扩展深度（hops） |
| **版本敏感** | 答案必须引用正确 Rust 版本的权威页；source recall 与来源新鲜度是关键指标 |
| **形式化精确** | 概念定义错误可能导致编译器行为理解错误；NDCG 可区分"相关但排序差"的检索结果 |
| **多语言实体** | KG 实体有中英 SKOS 标签；评估必须对中文查询与英文标签都做归一化 |

因此 Rust KG 的 RAG 评估需要同时度量：

- **概念召回**：检索到的实体是否覆盖了人工标注的黄金概念；
- **来源召回**：检索结果能否追溯到 `concept/` 权威页；
- **排序质量**：高相关实体是否排在前面（MRR、NDCG）；
- **可解释性**：检索路径是否可通过 KG 谓词解释。

---

## 二、评估指标

### 2.1 概念召回与精确率（recall@k / precision@k）

设查询 $q$ 的黄金概念集合为 $C_q^*$，检索系统返回的排序概念列表为 $C_q@k$：

$$
\text{recall@k} = \frac{|C_q@k \cap C_q^*|}{|C_q^*|}
\qquad
\text{precision@k} = \frac{|C_q@k \cap C_q^*|}{k}
$$

在 Rust KG 中，$C_q^*$ 由人工标注的 `expected_concepts` 给出，$C_q@k$ 由 `entity_linking` 和 `graph_retrieval` 共同产生。recall@k 回答"有没有找全"，precision@k 回答"前 k 个有多准"。

### 2.2 平均排序倒数（MRR）

MRR 衡量第一个相关结果出现的位置：

$$
\text{MRR} = \frac{1}{|Q|} \sum_{q \in Q} \frac{1}{\text{rank}_q}
$$

其中 $\text{rank}_q$ 是第一个命中黄金概念的排序位置。若没有命中，则该项为 0。MRR 对 RAG 很重要，因为 LLM 的上下文窗口有限，第一个相关实体越早出现越好。

### 2.3 归一化折损累积增益（NDCG@k）

NDCG 考虑相关实体在排序中的位置：

$$
\text{DCG@k} = \sum_{i=1}^{k} \frac{2^{rel_i} - 1}{\log_2(i+1)}
\qquad
\text{NDCG@k} = \frac{\text{DCG@k}}{\text{IDCG@k}}
$$

在本知识库评估中，$rel_i \in \{0, 1\}$（命中黄金概念为 1，否则为 0）。IDCG 按所有黄金概念都排在最前的理想情况计算。NDCG@k 比 recall@k 更严格：它不仅要求"找全"，还要求"排对"。

### 2.4 来源召回（source recall / faithfulness）

来源召回衡量检索结果是否覆盖了人工标注的权威页：

$$
\text{source recall@k} = \frac{|S_q@k \cap S_q^*|}{|S_q^*|}
$$

其中 $S_q^*$ 是 `expected_sources` 中的 `concept/` 路径，$S_q@k$ 是检索实体关联的 `ex:path` 与 RDF-star `ex:source`。该指标直接对应 RAG 的**忠实度（faithfulness）**：检索到的上下文是否足以支撑正确引用来源。

---

## 三、嵌入模型部署方式

`tools/kg_rag/semantic_alignment_pipeline.py` 支持两种可插拔的嵌入提供者。

### 3.1 本地 sentence-transformers 模型

适合离线、无 API 依赖、可复现的场景。默认使用 `all-MiniLM-L6-v2`（384 维）。

```bash
cd tools/kg_rag
python -m venv .venv
.venv/Scripts/pip install -r requirements.txt

.venv/Scripts/python semantic_alignment_pipeline.py \
  --kg ../../concept/00_meta/kg_data_v3.json \
  --eval eval/rag_eval_set.json \
  --embed-provider sentence-transformers \
  --embed-model all-MiniLM-L6-v2 \
  --top-k 10 \
  --markdown ../../reports/RAG_EVAL_2026_08_04.md
```

### 3.2 OpenAI 兼容 API

支持 OpenAI、Azure OpenAI、vLLM、Ollama（开启 OpenAI 兼容模式）等任何实现 `/embeddings` 端点的服务。通过环境变量或命令行参数配置：

```bash
export OPENAI_API_KEY=sk-...
export OPENAI_BASE_URL=https://api.openai.com/v1

tools/kg_rag/.venv/Scripts/python tools/kg_rag/semantic_alignment_pipeline.py \
  --kg concept/00_meta/kg_data_v3.json \
  --eval tools/kg_rag/eval/rag_eval_set.json \
  --embed-provider openai \
  --embed-model text-embedding-3-small \
  --top-k 10 \
  --markdown reports/RAG_EVAL_2026_08_04.md
```

> 标注 `ignore`：本命令需要有效的 API 密钥与网络连接，仅在配置了 OpenAI 兼容端点的环境中运行。

```bash
# ignore
export OPENAI_API_KEY=sk-...
export OPENAI_BASE_URL=https://api.openai.com/v1

tools/kg_rag/.venv/Scripts/python tools/kg_rag/semantic_alignment_pipeline.py \
  --kg concept/00_meta/kg_data_v3.json \
  --eval tools/kg_rag/eval/rag_eval_set.json \
  --embed-provider openai \
  --embed-model text-embedding-3-small \
  --top-k 10 \
  --markdown reports/RAG_EVAL_2026_08_04.md
```

### 3.3 无向量模式（结构检索）

当依赖不可用时，脚本自动回退到基于 SKOS 标签 token 重叠的结构化实体链接。这是 CI 冒烟测试与快速回归的标准模式：

```bash
python tools/kg_rag/semantic_alignment_pipeline.py \
  --builtin \
  --embed-provider none \
  --kg concept/00_meta/kg_data_v3.json
```

---

## 四、评估数据集格式

评估集为 JSON，顶层包含 `samples` 数组。每个样本必须包含：

```json
{
  "query": "how does ownership prevent data races",
  "expected_concepts": ["ownership", "borrowing", "data race"],
  "expected_sources": [
    "concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md",
    "concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md"
  ]
}
```

- `expected_concepts`：查询应覆盖的核心概念英文标签，评估时会做大小写、空格、下划线归一化；
- `expected_sources`：权威页路径，支持 `concept/...` 或 `01_foundation/...` 两种写法，脚本会自动归一化。

---

## 五、运行基线评估

项目内置了一个最小评估集（`--builtin`），用于在无外部数据集时快速验证脚本可用性。生成月度基线报告的推荐命令：

```bash
python tools/kg_rag/semantic_alignment_pipeline.py \
  --builtin \
  --kg concept/00_meta/kg_data_v3.json \
  --top-k 10 \
  --hops 2 \
  --markdown reports/RAG_EVALUATION_BASELINE_2026_08.md
```

输出报告包含：

- 聚合指标（recall@1/3/5/10、precision@k、NDCG@k、MRR）
- 每个查询的详细检索实体与来源
- 嵌入提供者名称（用于可追溯性）

---

## 六、指标解读与调优方向

| 指标偏低 | 可能原因 | 调优方向 |
|---|---|---|
| recall@k 低 | 实体链接未命中关键概念 | 增加向量检索、扩充 `skos:altLabel` |
| precision@k 低 | 前 k 结果混入大量弱相关实体 | 提高向量模型与 KG 混合权重、增加重排序 |
| MRR / NDCG 低 | 相关实体排得靠后 | 调优 `alpha`（向量/图信号权重）、缩短 hops |
| source recall 低 | 图扩展未到达权威页 | 确保关系上有 `ex:source` 注解、增加 hops |
| 来源陈旧 | 概念页已更新但 KG 未刷新 | 运行 `scripts/generate_kg_index.py` 与 `scripts/generate_kg_v3.py` 重建索引 |

---

## 七、与质量门的集成

RAG 评估产出应作为项目语义健康度量的补充观察项：

1. **不阻断 PR**：RAG 评估依赖可选 Python 依赖与可能的 API 调用，不适合作为 CI 阻断门；
2. **月度基线**：每月运行并归档 `reports/RAG_EVALUATION_BASELINE_YYYY_MM.md`；
3. **退化告警**：当 `concept_recall@5` 或 `source_recall@5` 较上月下降 ≥10% 时触发人工复核；
4. **KG 谓词精度**：每次 KG 刷新后必须保持 `scripts/check_kg_relation_precision.py --strict` 核心 generic_ratio = 0%，因为通用谓词会直接降低图扩展的可解释性。

---

## 八、常见反例

### 8.1 用 LLM 自动生成黄金标注却不校验

自动标注容易把"相关"当作"必需"，导致 recall 被人为抬高。黄金标注应由维护者按 AGENTS.md canonical 规则逐条确认。

### 8.2 只看 aggregate 忽略 per-sample

某些概念（如 `unsafe`、`Pin`）的检索难度远高于所有权。aggregate 达标可能掩盖特定主题的持续失败，应同时检查 per-sample 表格。

### 8.3 混合不同嵌入模型却用同一基线对比

`all-MiniLM-L6-v2` 与 `text-embedding-3-large` 的维度、训练分布不同，不能直接比较同一基线。每次基线报告必须注明嵌入提供者。

---

## 九、延伸阅读

- 概念权威页：[`concept/00_meta/05_ai_semantic_engineering/02_llm_rag_for_rust.md`](02_llm_rag_for_rust.md)
- 工具脚本：[`tools/kg_rag/semantic_alignment_pipeline.py`](../../../tools/kg_rag/semantic_alignment_pipeline.py)
- 当前基线：[`reports/RAG_EVALUATION_BASELINE_2026_08.md`](../../../reports/RAG_EVALUATION_BASELINE_2026_08.md)
- KG 谓词精度观察门：[`scripts/check_kg_relation_precision.py`](../../../scripts/check_kg_relation_precision.py)
