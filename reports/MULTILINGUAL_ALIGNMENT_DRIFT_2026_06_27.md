# 多语言术语对齐漂移检测报告

- 生成时间：2026-06-27T17:34:47
- 知识图谱：E:\_src\rust-lang\concept\00_meta\kg_data_v2.json
- 对齐模型：sentence-transformers/paraphrase-multilingual-MiniLM-L12-v2
- 漂移阈值：0.7

## 摘要

- 总术语对数：**21**
- 缺少英文或中文标签：**0**
- 低于阈值的漂移对数：**6**
- 平均相似度：**0.8170**
- 最低相似度：**0.1659**
- 最高相似度：**1.0000**

## 漂移术语对（需人工审校）

| 实体 ID | 类别 | 英文标签 | 中文标签 | 相似度 | 建议操作 |
| --- | --- | --- | --- | --- | --- |
| AsyncAwait | concepts | Async/Await | 异步 | 0.1659 | 检查翻译一致性 |
| Borrowing | concepts | Borrowing | 借用 | 0.4577 | 检查翻译一致性 |
| AXM | rules | Alias-XOR-Mutation Rule | AXM 规则 | 0.4814 | 检查翻译一致性 |
| Generics | concepts | Generics | 泛型 | 0.5459 | 复核术语对应关系 |
| Elision | rules | Lifetime Elision | 生命周期省略 | 0.6183 | 复核术语对应关系 |
| Concurrency | concepts | Concurrency | 并发 | 0.6815 | 复核术语对应关系 |

## 统计方法

1. 使用 `paraphrase-multilingual-MiniLM-L12-v2`（基于 XLM-R 蒸馏）分别编码每对实体的英文和中文 `skos:prefLabel`。
2. 对 embedding 做 L2 归一化，计算余弦相似度。
3. 相似度低于阈值 `0.7` 的术语对标记为漂移，需人工审校。
