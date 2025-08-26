# 01. 知识图谱模块总览（Index）

- 文档版本: 1.0
- Rust 版本基线: 1.89
- 维护: formal_rust 项目组
- 状态: 持续更新

## 1. 目的与范围

本模块统一承载 Rust 形式化工程体系的知识图谱与导航：

- 全局知识图谱（中文/英文）
- 分层知识图谱（中文）
- 与各重构子模块的双向交叉链接与锚点导航

## 2. 子文档

1. 01.1 全局知识图谱（中文/英文）
   - 入口: `01_global_graph.md`
2. 01.2 分层知识图谱（中文）
   - 入口: `02_layered_graph.md`

## 3. 原始来源（保留与引用）

- 原文（中文）: `docs/KNOWLEDGE_GRAPH.md`
- 原文（英文）: `docs/KNOWLEDGE_GRAPH_EN.md`
- 原文（分层）: `docs/KNOWLEDGE_GRAPH_LAYERED.md`

> 处理原则: 完整保留原始图谱的结构与语义关系；在本模块中仅进行编号化、导航化与交叉链接增强，不删减信息。

## 4. 交叉链接（Cross-links）

- 核心理论: `../01_core_theory/00_core_theory_index.md`
- 应用领域: `../04_application_domains/00_index.md`
- 并发语义: `../09_concurrency_semantics/00_index.md`
- 形式化验证: `../08_formal_verification/00_index.md`
- 性能优化: `../05_performance_optimization/00_index.md`

## 5. 维护说明

- 图谱更新采用“先来源后汇聚”的流程：先在 `docs/` 更新，再在本模块同步。
- 同步原则：语义等价、编号规范、锚点稳定。

## 6. 差异与引用说明

- 本模块中的图谱内容与 `docs/` 原文保持语义对齐；如有微调（如节点命名规范化、拼写统一、编号添加），均在不改变关系语义的前提下进行。
- 若未来与来源出现差异，以 `docs/` 为准，同时在此模块更新并在本小节记录差异原因与日期。
