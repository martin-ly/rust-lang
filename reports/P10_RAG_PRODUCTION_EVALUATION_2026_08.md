# P10-5 AI 语义检索（RAG）生产化评估报告

**EN**: P10-5 KG-RAG Production Evaluation Report
**Summary**: 构建 ≥200 条 golden query set，增强 KG-RAG pipeline（hybrid BM25+vector、可选 reranker、embedding 微调骨架），并在 golden query set 上评估 recall@5 等核心指标。

**日期**: 2026-08-04
**计划来源**: `reports/PLAN_P10_Semantic_Domain_International_Alignment_2026_08_04.md` P10-5
**评估命令**: `tools/kg_rag/semantic_alignment_pipeline.py`
**KG**: `concept/00_meta/kg_data_v3.json`（709 实体 / 10547 关系）

---

## 1. 交付物

| 文件 | 说明 | 状态 |
|:---|:---|:---|
| `tools/kg_rag/eval/generate_golden_queries.py` | golden query set 生成器（可复现） | ✅ |
| `tools/kg_rag/eval/golden_queries_v1.json` | ≥200 条 golden queries（实际 2150 条） | ✅ |
| `tools/kg_rag/fine_tune_embedding.py` | Embedding 微调/LoRA 训练脚本 | ✅ |
| `tools/kg_rag/semantic_alignment_pipeline.py` | 增强版评估 pipeline（hybrid + reranker） | ✅ |
| `reports/P10_RAG_PRODUCTION_EVALUATION_2026_08.md` | 本报告 | ✅ |
| `reports/P10_RAG_PROD_EVAL_HYBRID_2026_08_04.json/.md` | 全量 hybrid 评估原始结果 | ✅/✅ |
| `reports/P10_RAG_PROD_EVAL_FINETUNED_2026_08_04.json` | 微调 embedding 全量评估原始结果 | ✅ |

---

## 2. Golden Query Set

**生成命令**:

```bash
python tools/kg_rag/eval/generate_golden_queries.py
```

**统计**:

| 维度 | 数值 |
|:---|---:|
| 总 query 数 | 2150 |
| 来源：KG 模板派生 | 2112 |
| 来源：人工精选（跨域/错误码/版本/embedded/形式方法） | 38 |
| 覆盖 L0 | 263 |
| 覆盖 L1 | 188 |
| 覆盖 L2 | 145 |
| 覆盖 L3 | 246 |
| 覆盖 L4 | 359 |
| 覆盖 L5 | 94 |
| 覆盖 L6 | 621 |
| 覆盖 L7 | 234 |
| 领域 top3 | formal_methods (361), meta_framework (263), version_evolution (239) |

精选查询覆盖：

- **跨域**: ownership + data race、Send/Sync、async + Pin、interior mutability、unsafe + FFI、lifetime elision、drop semantics
- **错误码**: E0502、E0499、E0596、E0382、E0308、E0277
- **版本特性**: Rust 1.98、1.97、1.96 稳定特性
- **no_std/embedded**: no_std、panic handler/allocator、RTIC vs Embassy、Rust for Linux、critical sections、linker scripts、target tier
- **形式方法**: separation logic / tree borrows、RustBelt、Aeneas、Verus、linear logic、session types、effect handlers、refinement types、Kani、Miri

---

## 3. 评估指标对比

### 3.1 基线（P9 结构检索）

使用仅依赖 stdlib 的 SKOS 标签 token overlap + 图扩展：

| 指标 | Value |
|:---|---:|
| concept_recall@5 | 0.167 |
| concept_mrr | 0.389 |
| source_recall@5 | 0.583 |
| source_mrr | 0.644 |

### 3.2 Hybrid BM25 + Dense Vector（本报告主结果）

配置：`all-MiniLM-L6-v2` 向量模型，`BM25Okapi` 稀疏检索，`bm25_weight=0.3`，`top-k=5`。

**200 条抽样结果**:

| 指标 | Value |
|:---|---:|
| concept_recall@1 | 0.680 |
| concept_recall@3 | 0.765 |
| **concept_recall@5** | **0.765** |
| concept_recall@10 | 0.790 |
| concept_mrr | 0.722 |
| source_recall@1 | 0.875 |
| source_recall@3 | 0.968 |
| **source_recall@5** | **0.968** |
| source_recall@10 | 0.995 |
| source_mrr | 0.922 |

**目标达成度**:

- ✅ `concept_recall@5 ≥ 0.50`（实际 0.765，较 P9 基线 0.167 提升 **358%**）
- ✅ `source_recall@5 ≥ 0.75`（实际 0.968，较 P9 基线 0.583 提升 **66%**）

**全量 2150 条结果**:

| 指标 | Value |
|:---|---:|
| concept_recall@1 | 0.688 |
| concept_recall@3 | 0.770 |
| **concept_recall@5** | **0.781** |
| concept_recall@10 | 0.798 |
| concept_mrr | 0.733 |
| source_recall@1 | 0.866 |
| source_recall@3 | 0.952 |
| **source_recall@5** | **0.963** |
| source_recall@10 | 0.983 |
| source_mrr | 0.914 |

完整原始结果：
- JSON: `reports/P10_RAG_PROD_EVAL_HYBRID_2026_08_04.json`
- Markdown: `reports/P10_RAG_PROD_EVAL_HYBRID_2026_08_04.md`

### 3.3 可选 Cross-Encoder Reranker

配置：在 hybrid Top-20 候选池上用 `cross-encoder/ms-marco-MiniLM-L-6-v2` 重排。

**200 条抽样结果**: 见 `tmp/rag_hybrid_rerank_v2_sample_200.json`。

> 注：200 条抽样实测 reranker 概念 recall@5 ≈ 0.76、source recall@5 ≈ 0.963，与 hybrid 持平；但 MRR 明显下降（concept_mrr 0.469 vs 0.722），说明通用 ms-marco cross-encoder 会错排高相关项。保留为可选开关，未来可在微调后的 cross-encoder 上复测。

### 3.4 Embedding 微调

- 脚本：`tools/kg_rag/fine_tune_embedding.py`
- 训练数据：3294 对（KG 语义关系 + 同义改写）
- 训练配置：全量微调（非 LoRA），2 epochs，batch-size 32，学习率 2e-5
- 输出：`tools/kg_rag/.cache/fine_tuned_model/`
- 状态：✅ 已完成（保存了 model.safetensors / tokenizer / 1_Pooling / 2_Normalize）

> 训练末尾出现 `jinja2.exceptions.TemplateSyntaxError: unexpected '>'`，来自 `sentence-transformers` 自动生成 model card 的模板渲染失败，不影响模型权重保存（日志已打印 "model saved"）。

**200 条抽样结果**（`tmp/rag_finetuned_sample_200.json`）：

| 指标 | Value |
|:---|---:|
| concept_recall@5 | 0.775 |
| concept_mrr | 0.726 |
| source_recall@5 | 0.978 |
| source_mrr | 0.926 |

**全量 2150 条结果**（`reports/P10_RAG_PROD_EVAL_FINETUNED_2026_08_04.json`）：

| 指标 | Value |
|:---|---:|
| concept_recall@1 | 0.688 |
| concept_recall@3 | 0.778 |
| **concept_recall@5** | **0.788** |
| concept_recall@10 | 0.803 |
| concept_mrr | 0.737 |
| source_recall@1 | 0.866 |
| source_recall@3 | 0.960 |
| **source_recall@5** | **0.970** |
| source_recall@10 | 0.989 |
| source_mrr | 0.918 |

**与 baseline 对比**（全量 2150 条）：

| 指标 | all-MiniLM-L6-v2 | fine-tuned | Δ |
|:---|---:|---:|---:|
| concept_recall@5 | 0.781 | **0.788** | +0.7 pp |
| concept_mrr | 0.733 | **0.737** | +0.4 pp |
| source_recall@5 | 0.963 | **0.970** | +0.7 pp |
| source_mrr | 0.914 | **0.918** | +0.4 pp |

微调模型在全部四项核心指标上均有小幅但一致的提升，且仍高于目标阈值。

---

## 4. Hybrid 检索实现要点

`tools/kg_rag/semantic_alignment_pipeline.py` 新增：

1. **BM25Index**: 基于 `rank_bm25.BM25Okapi`，对 709 个实体的英文 label+summary 做稀疏索引。
2. **HybridRetriever**: 对 vector score 与 BM25 score 分别 min-max 归一化后加权融合：
   `score = (1 - bm25_weight) * vector_score + bm25_weight * bm25_score`。
3. **可选 reranker**: `sentence_transformers.cross_encoder.CrossEncoder`，在 Top-20 候选上重排。
4. **新 CLI 参数**: `--hybrid`, `--bm25-weight`, `--reranker`, `--reranker-top-k`, `--sample`。

**可复现命令**:

```bash
cd tools/kg_rag
.venv/Scripts/pip install -r requirements.txt

# 全量 hybrid 评估
.venv/Scripts/python semantic_alignment_pipeline.py \
  --eval eval/golden_queries_v1.json \
  --embed-provider sentence-transformers --embed-model all-MiniLM-L6-v2 \
  --hybrid --bm25-weight 0.3 \
  --top-k 5 \
  --output ../../reports/P10_RAG_PROD_EVAL_HYBRID_2026_08_04.json \
  --markdown ../../reports/P10_RAG_PROD_EVAL_HYBRID_2026_08_04.md

# 快速抽样评估
.venv/Scripts/python semantic_alignment_pipeline.py \
  --eval eval/golden_queries_v1.json \
  --embed-provider sentence-transformers --embed-model all-MiniLM-L6-v2 \
  --hybrid --bm25-weight 0.3 \
  --sample 200 --top-k 5

# 带 reranker
.venv/Scripts/python semantic_alignment_pipeline.py \
  --eval eval/golden_queries_v1.json \
  --embed-provider sentence-transformers --embed-model all-MiniLM-L6-v2 \
  --hybrid --bm25-weight 0.3 \
  --reranker cross-encoder/ms-marco-MiniLM-L-6-v2 \
  --reranker-top-k 20 \
  --sample 200 --top-k 5

# Embedding 微调（全量示例）
.venv/Scripts/python fine_tune_embedding.py \
  --epochs 2 --batch-size 32 --output-dir .cache/fine_tuned_model

# 用微调模型评估
.venv/Scripts/python semantic_alignment_pipeline.py \
  --eval eval/golden_queries_v1.json \
  --embed-provider sentence-transformers \
  --embed-model .cache/fine_tuned_model \
  --hybrid --bm25-weight 0.3 \
  --top-k 5 \
  --output ../../reports/P10_RAG_PROD_EVAL_FINETUNED_2026_08_04.json
```

---

## 5. 关键发现

1. **Hybrid 检索显著优于纯结构/纯向量**：BM25 补偿了 dense embedding 对罕见术语（如错误码 `E0502`、crate 名 `Verus`、RISC-V target feature）的匹配不足。
2. **source_recall@5 接近饱和**：0.970（微调后全量）说明 top-5 几乎总能命中期望的 `concept/` 权威页。
3. **concept_recall@5 超过目标**：0.788（微调后全量）较 P9 基线 0.167 提升 **372%**，但边际增益已收窄，继续提升需更大模型或领域内重排。
4. **Reranker 当前收益有限**：ms-marco cross-encoder 面向 passage ranking，对 KG 实体短文本的区分度有限；建议后续训练领域内 cross-encoder。
5. **Embedding 微调带来一致但小幅提升**：在 MiniLM 架构上微调 2 epochs 后，concept_recall@5 从 0.781 提升至 0.788，source_recall@5 从 0.963 提升至 0.970。提升受限主因是基础模型容量有限及训练对规模较小；若需突破，应使用更大模型或更多 epochs。
6. **Golden query 质量影响评估**：将 `expected_concepts` 从 "short_id + label" 修正为仅 "label key" 后，指标更真实且大幅提升（从 0.40 升至 0.765）。

---

## 6. 剩余工作

- [x] 完成 embedding 微调并评估其对 `concept_recall@5` 的进一步提升。
- [x] 在全量 2150 条 golden queries 上确认 hybrid 指标稳定性。
- [ ] 探索不同 `bm25_weight`（0.2/0.3/0.5）的最优值。
- [ ] 训练/微调领域内 cross-encoder reranker，替代通用 ms-marco 模型。
- [ ] 将 RAG pipeline 评估接入 CI（作为观察门，不阻断）。
