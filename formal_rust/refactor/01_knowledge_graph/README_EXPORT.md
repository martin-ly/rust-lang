# Mermaid 图谱导出指引

## 本地导出（Node.js 环境）

1. 安装 CLI：
   - `npm install -g @mermaid-js/mermaid-cli`
2. 导出示例：
   - `mmdc -i 01_global_graph.md -o global_graph.svg`
   - `mmdc -i 02_layered_graph.md -o layered_graph.svg`

> 若仓库 CI 支持，可在 CI 中自动导出并发布制品。
