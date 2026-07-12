# KG 浏览器

基于 `concept/00_meta/kg_data_v3.json` 的静态知识图谱可视化（D3.js 力导向图，
单文件 `index.html`，可直接 `file://` 打开）。

## 用法

```bash
# 1. 生成 实体 -> Markdown 链接映射（使用 v3 实体 ex:path 字段）
python tools/kg_browser/generate_links.py

# 2. 验证全部链接指向存在的 concept 文件（2026-07-12 新增）
python tools/kg_browser/validate_links.py

# 3. 构建内嵌数据的单文件浏览器
python tools/kg_browser/build.py
```

- `generate_links.py` — 输出 `kg_links.json`（491 实体）。
- `validate_links.py` — 校验 `kg_links.json` 每条非空链接存在于磁盘、
  且实体仍存在于 KG 中；exit 非 0 表示需要重新生成或修复 `ex:path`。
- `build.py` — 将 KG + 链接内嵌进 `index.html`，避免 file:// CORS。

> `index.html` 为构建产物，KG 更新后需重跑以上三步。
