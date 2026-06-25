# Rust 所有权可判定性研究项目

> **内容分级**: [归档级]
> **状态**: 研究综述 / 历史参考 / **已归档**
>
> ⚠️ **归档声明**：本目录自 2026-06-25 起整体标记为归档。核心教学结论与可运行示例已迁移至 `concept/04_formal/`、`knowledge/` 与 crates 中的 Kani/Verus 示例。本目录仅作为历史研究参考保留，不再主动更新。

本目录是 Rust 所有权与借用系统形式化研究的早期工作区，包含线性逻辑、分离逻辑、借用检查可判定性、形式化验证工具对照等主题。

## 导航

| 目录 | 内容 |
|---|---|
| [00-foundations](./00-foundations/) | 线性逻辑、仿射类型、分离逻辑基础 |
| [01-core-concepts](./01-core-concepts/) | 所有权规则、借用系统、生命周期 |
| [03-verification-tools](./03-verification-tools/) | Kani、Miri、Creusot、Verus、RefinedRust 等工具 |
| [04-decidability-analysis](./04-decidability-analysis/) | 类型推断与借用检查可判定性分析 |
| [05-comparative-study](./05-comparative-study/) | 与其他语言的对比研究 |
| [07-references](./07-references/) | 论文、书籍、在线课程、工具库 |
| [10-research-frontiers](./10-research-frontiers/) | 研究前沿与展望 |
| [16-program-semantics](./16-program-semantics/) | 程序语义与操作语义基础 |

## 重要说明

- 本目录大量文件属于**研究笔记性质**，部分内容尚未完成或需要更新。
- 核心教学结论已迁移至 `concept/04_formal/` 与 `knowledge/`。
- 最新执行计划请参阅 `.kimi/EXECUTION_CHECKLIST_2026_06_22.md` 与 `reports/C_CLASS_GOVERNANCE_PLAN_2026_06_09.md`。

## 关键索引

- [EXECUTIVE_SUMMARY_AND_RECOMMENDATIONS.md](./EXECUTIVE_SUMMARY_AND_RECOMMENDATIONS.md)
- [AUDIT_REPORTS_INDEX.md](./AUDIT_REPORTS_INDEX.md)
- [COMPLETION_100_PERCENT_SUMMARY.md](./COMPLETION_100_PERCENT_SUMMARY.md)
