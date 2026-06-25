# 链接有效性检查报告

## 统计
| 类别 | 数量 |
|:---|:---:|
| 总链接数 | 91930 |
| 有效链接 | 32993 |
| 损坏链接 | 10 |
| 外部链接 | 58918 |
| 仅锚点链接 | 27857 |

## 损坏链接清单（按问题类型分组）

### 锚点不存在 (10个)

| 源文件 | 链接文本 | 链接路径 | 问题 |
|:---|:---|:---|:---|
| docs\05_guides\05_unsafe_fields_preview.md | ⚖️ 与当前  块的对比 | `#️-与当前-unsafe-块的对比` | 同文件锚点不存在: #️-与当前-unsafe-块的对比 |
| docs\rust-ownership-decidability\COMPARATIVE_ANALYSIS.md | **下一篇**：阅读  了解设计决策背后的原理 | `#下一篇阅读-design_rationalemd-了解设计决策背后的原理` | 同文件锚点不存在: #下一篇阅读-design_rationalemd-了解设计决策背后的原理 |
| docs\rust-ownership-decidability\HORIZONTAL_CONNECTIONS.md | **下一篇**：阅读  了解理论的历史演化 | `#下一篇阅读-historical_evolutionmd-了解理论的历史演化` | 同文件锚点不存在: #下一篇阅读-historical_evolutionmd-了解理论的历史演化 |
| docs\rust-ownership-decidability\NATURAL_LANGUAGE_ARGUMENTATION_INDEX.md | **开始探索**：建议从  开始阅读 | `#开始探索建议从-overview_and_intuitionmd-开始阅读` | 同文件锚点不存在: #开始探索建议从-overview_and_intuitionmd-开始阅读 |
| docs\rust-ownership-decidability\01-core-concepts\ownership-counterexamples.md | **对齐版本**: Rust 1.96.0+ (Edition 2024) \| 对齐日期: 2026-05-12 | `#对齐版本-rust-1960-edition-2024--对齐日期-2026-05-12` | 同文件锚点不存在: #对齐版本-rust-1960-edition-2024--对齐日期-2026-05-12 |
| docs\rust-ownership-decidability\03-verification-tools\03-03-miri-deep-dive.md | *文档版本: 2.0.0* \| *最后更新: 2026-03* | `#文档版本-200--最后更新-2026-03` | 同文件锚点不存在: #文档版本-200--最后更新-2026-03 |
| docs\rust-ownership-decidability\03-verification-tools\03-06-verus-guide.md | *文档版本: 2.0.0* \| *Verus 版本: 0.1.x* \| *最后更新: 2026-03* | `#文档版本-200--verus-版本-01x--最后更新-2026-03` | 同文件锚点不存在: #文档版本-200--verus-版本-01x--最后更新-2026-03 |
| docs\rust-ownership-decidability\16-program-semantics\04-control-data-flow.md | *本文档是 Rust 所有权可判定性研究系列的一部分，与  保持一致的语义框架。* | `#本文档是-rust-所有权可判定性研究系列的一部分与-00-semantic-frameworkmd-保持一致的语义框架` | 同文件锚点不存在: #本文档是-rust-所有权可判定性研究系列的一部分与-00-semantic-frameworkmd-保持一致的语义框架 |
| docs\rust-ownership-decidability\16-program-semantics\rust-194-features\04-precise-capturing-semantics.md | 通过 ，开发者可以编写出生命周期约束更精确、API 更灵活的 Rust 代码 | `#通过-uselt开发者可以编写出生命周期约束更精确api-更灵活的-rust-代码` | 同文件锚点不存在: #通过-uselt开发者可以编写出生命周期约束更精确api-更灵活的-rust-代码 |
| docs\rust-ownership-decidability\case-studies\chrono-formal-analysis.md | 定义 TIME-2 (  ) | `#定义-time-2--datetimetz-` | 同文件锚点不存在: #定义-time-2--datetimetz- |

## 修复建议

### 1. 文件不存在问题
- 检查链接路径是否正确
- 确认目标文件是否已被移动或删除
- 更新链接指向正确的文件位置

### 2. 锚点不存在问题
- 检查锚点ID是否与目标文件中的标题匹配
- GitHub风格锚点：将标题转换为小写，空格替换为连字符，移除标点
- 示例：`## Hello World!` -> `#hello-world`

### 3. 同文件锚点问题
- 检查文档中是否存在对应的标题
- 可能是文档结构已更改但目录未更新

## 源文件问题统计

| 源文件 | 损坏链接数 |
|:---|:---:|
| docs\05_guides\05_unsafe_fields_preview.md | 1 |
| docs\rust-ownership-decidability\COMPARATIVE_ANALYSIS.md | 1 |
| docs\rust-ownership-decidability\HORIZONTAL_CONNECTIONS.md | 1 |
| docs\rust-ownership-decidability\NATURAL_LANGUAGE_ARGUMENTATION_INDEX.md | 1 |
| docs\rust-ownership-decidability\01-core-concepts\ownership-counterexamples.md | 1 |
| docs\rust-ownership-decidability\03-verification-tools\03-03-miri-deep-dive.md | 1 |
| docs\rust-ownership-decidability\03-verification-tools\03-06-verus-guide.md | 1 |
| docs\rust-ownership-decidability\16-program-semantics\04-control-data-flow.md | 1 |
| docs\rust-ownership-decidability\16-program-semantics\rust-194-features\04-precise-capturing-semantics.md | 1 |
| docs\rust-ownership-decidability\case-studies\chrono-formal-analysis.md | 1 |

**总计 10 个文件包含损坏链接**