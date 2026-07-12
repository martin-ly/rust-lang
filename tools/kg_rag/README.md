# KG-RAG 语义搜索工具

基于 `concept/00_meta/kg_data_v3.json` 的轻量级混合检索原型。

## 环境

使用项目内独立虚拟环境：

```bash
cd tools/kg_rag
python -m venv .venv
.venv/Scripts/pip install -r requirements.txt
```

依赖：

- `sentence-transformers`
- `numpy`
- `scikit-learn`

## 用法

```bash
# 基本查询
.venv/Scripts/python tools/kg_rag/query.py \
  --query "how does ownership relate to borrowing" \
  --top-k 5

# JSON 输出
.venv/Scripts/python tools/kg_rag/query.py \
  --query "async runtime" --top-k 5 --json

# 强制重建索引
.venv/Scripts/python tools/kg_rag/query.py \
  --query "lifetime elision" --rebuild
```

首次运行会自动下载 `all-MiniLM-L6-v2` 模型并缓存到 `tools/kg_rag/.cache/`。

## 设计

- 使用英文 `skos:prefLabel` + `skos:definition` 生成向量嵌入。
- 向量索引使用 L2 归一化的 numpy 矩阵，通过点积计算余弦相似度。
- hybrid score：`alpha * vector_score + (1 - alpha) * graph_score`，其中
  `graph_score` 为 `dependsOn` / `equivalentTo` 邻居的平均向量相似度。

## 模块与测试

- `kg_core.py` — stdlib-only v3 KG 数据访问层（加载、实体展开、类型化边
  邻接表、路径遍历），不依赖 numpy / sentence-transformers。
- `kg_rag.py` — 向量索引与混合检索。缓存键包含 KG 文件 mtime 与实体数，
  KG 重新生成后自动重建索引。
- `smoke_test.py` — 可复跑冒烟测试（2026-07-12 新增）：

```bash
# 结构检查（stdlib，任意 Python 可跑；向量检索自动 SKIP）
python tools/kg_rag/smoke_test.py
# 完整检查（含向量检索，用 venv）
tools/kg_rag/.venv/Scripts/python tools/kg_rag/smoke_test.py
```

覆盖：v3 数据规模、实体查询、`instanceOf`/`appliesTo`/`equivalentTo`
类型化边遍历、多跳路径、关系端点完整性、混合检索排序。
