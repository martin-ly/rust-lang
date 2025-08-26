# PROCESS_CONTEXT（进程上下文，可中断续作）

- 文档版本: 1.0
- 负责: formal_rust 项目组
- 更新频率: 每次批次提交后

## A. 当前批次目标

- 将 `docs/` 中知识图谱文档汇聚为模块 `01_knowledge_graph/`，提供全局与分层导航，并建立到各模块的交叉链接。

## B. 已完成

- 新增模块目录 `formal_rust/refactor/01_knowledge_graph/`
- 创建 `00_index.md`, `01_global_graph.md`, `02_layered_graph.md`
- 在 `00_master_index.md` 注册模块与说明
- 新增节点映射 `node_link_map.md`
- 在两张图中补充“节点链接索引”与“系统编程专题深链索引”
- 创建导出指引 `README_EXPORT.md`
- 更新综合快照日期 `COMPREHENSIVE_KNOWLEDGE_GRAPH.md`

## C. 下一步（可直接继续）

1. 对并发、内存、安全验证等节点继续补充分项到具体章节的锚点。
2. 可选：在 CI 中集成 Mermaid 导出任务，将 SVG/PNG 产物发布到构件仓或 Pages。
3. 可选：在 `01_core_theory/00_core_theory_index.md` 等处反向添加“回到图谱”导航。

## D. 参考与链接

- 主索引: `formal_rust/refactor/00_master_index.md`
- 知识图谱索引: `formal_rust/refactor/01_knowledge_graph/00_index.md`
- 节点映射: `formal_rust/refactor/01_knowledge_graph/node_link_map.md`
- 来源文档: `docs/KNOWLEDGE_GRAPH.md`, `docs/KNOWLEDGE_GRAPH_EN.md`, `docs/KNOWLEDGE_GRAPH_LAYERED.md`

> 规则：保持语义一致、编号稳定、双向链接；保留原文结构与信息，无损汇聚。
