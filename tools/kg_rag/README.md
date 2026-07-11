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
