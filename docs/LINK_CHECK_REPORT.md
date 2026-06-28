# 链接有效性检查报告

## 统计
| 类别 | 数量 |
|:---|:---:|
| 总链接数 | 91836 |
| 有效链接 | 32855 |
| 损坏链接 | 14 |
| 外部链接 | 58953 |
| 仅锚点链接 | 27731 |

## 损坏链接清单（按问题类型分组）

### 锚点不存在 (12个)

| 源文件 | 链接文本 | 链接路径 | 问题 |
|:---|:---|:---|:---|
| docs\rust-ownership-decidability\10-research-frontiers\10-05-ai-integration.md | *本文档是 Rust 所有权与可判定性研究系列第十章的一部分。* | `#本文档是-rust-所有权与可判定性研究系列第十章的一部分` | 同文件锚点不存在: #本文档是-rust-所有权与可判定性研究系列第十章的一部分 |
| docs\rust-ownership-decidability\10-research-frontiers\rust-1.93-features-analysis.md | **对齐版本**: Rust 1.93.1 | `#对齐版本-rust-1931` | 同文件锚点不存在: #对齐版本-rust-1931 |
| docs\rust-ownership-decidability\12-concurrency-patterns\12-03-message-passing-deep.md | **Document Version**: 1.0.0 | `#document-version-100` | 同文件锚点不存在: #document-version-100 |
| docs\rust-ownership-decidability\12-concurrency-patterns\12-04-lock-free-patterns.md | （继续...） | `#继续` | 同文件锚点不存在: #继续 |
| docs\rust-ownership-decidability\12-concurrency-patterns\12-05-async-patterns-deep.md | *This document is part of the Rust Ownership \& Decidability documentation series. For questions or contributions, refer to the project repository.* | `#this-document-is-part-of-the-rust-ownership--decidability-documentation-series-for-questions-or-contributions-refer-to-the-project-repository` | 同文件锚点不存在: #this-document-is-part-of-the-rust-ownership--decidability-documentation-series-for-questions-or-contributions-refer-to-the-project-repository |
| docs\rust-ownership-decidability\12-concurrency-patterns\12-05-async-patterns.md | （继续...） | `#继续` | 同文件锚点不存在: #继续 |
| docs\rust-ownership-decidability\12-concurrency-patterns\12-06-data-parallelism.md | （继续...） | `#继续` | 同文件锚点不存在: #继续 |
| docs\rust-ownership-decidability\15-application-domains\data-engineering.md | 通过本文档介绍的技术，开发者可以构建高性能、高可靠性的数据处理系统 | `#通过本文档介绍的技术开发者可以构建高性能高可靠性的数据处理系统` | 同文件锚点不存在: #通过本文档介绍的技术开发者可以构建高性能高可靠性的数据处理系统 |
| docs\rust-ownership-decidability\15-application-domains\web-development.md | 通过本文档介绍的技术和最佳实践，开发者可以构建高性能、高可靠性的 Web 应用 | `#通过本文档介绍的技术和最佳实践开发者可以构建高性能高可靠性的-web-应用` | 同文件锚点不存在: #通过本文档介绍的技术和最佳实践开发者可以构建高性能高可靠性的-web-应用 |
| docs\rust-ownership-decidability\16-program-semantics\02-concurrency-semantics.md | 8.1.1 Arc\<Mutex\> 语义 | `#811-arcmutex-语义` | 同文件锚点不存在: #811-arcmutex-语义 |
| docs\rust-ownership-decidability\case-studies\tokio-runtime-analysis.md | *最后更新: 2026-03-04* | `#最后更新-2026-03-04` | 同文件锚点不存在: #最后更新-2026-03-04 |
| docs\rust-ownership-decidability\exercises\ADVANCED_OWNERSHIP_WORKSHOP.md | **完成度**: 0/5 练习 | `#完成度-05-练习` | 同文件锚点不存在: #完成度-05-练习 |

### 文件不存在 (2个)

| 源文件 | 链接文本 | 链接路径 | 问题 |
|:---|:---|:---|:---|
| docs\archive\c_class_audit_2026_06_08\content\README.md | Coq 形式化验证指南 | `../../../content/academic/10_coq_formalization_guide.md` | 文件不存在: docs\content\academic\10_coq_formalization_guide.md |
| docs\content\academic\README.md | Coq 形式化指南 | `./10_coq_formalization_guide.md` | 文件不存在: docs\content\academic\10_coq_formalization_guide.md |

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
| docs\archive\c_class_audit_2026_06_08\content\README.md | 1 |
| docs\content\academic\README.md | 1 |
| docs\rust-ownership-decidability\10-research-frontiers\10-05-ai-integration.md | 1 |
| docs\rust-ownership-decidability\10-research-frontiers\rust-1.93-features-analysis.md | 1 |
| docs\rust-ownership-decidability\12-concurrency-patterns\12-03-message-passing-deep.md | 1 |
| docs\rust-ownership-decidability\12-concurrency-patterns\12-04-lock-free-patterns.md | 1 |
| docs\rust-ownership-decidability\12-concurrency-patterns\12-05-async-patterns-deep.md | 1 |
| docs\rust-ownership-decidability\12-concurrency-patterns\12-05-async-patterns.md | 1 |
| docs\rust-ownership-decidability\12-concurrency-patterns\12-06-data-parallelism.md | 1 |
| docs\rust-ownership-decidability\15-application-domains\data-engineering.md | 1 |
| docs\rust-ownership-decidability\15-application-domains\web-development.md | 1 |
| docs\rust-ownership-decidability\16-program-semantics\02-concurrency-semantics.md | 1 |
| docs\rust-ownership-decidability\case-studies\tokio-runtime-analysis.md | 1 |
| docs\rust-ownership-decidability\exercises\ADVANCED_OWNERSHIP_WORKSHOP.md | 1 |

**总计 14 个文件包含损坏链接**