# async-std 引用清理清单

> **生成日期**: 2026-06-22
> **扫描范围**: 全仓库 Markdown (*.md) + Cargo 清单 (*.toml) + Rust 源码 (*.rs)
> **状态**: 代码层已清零，活跃文档已加 `[已归档]` 标记，历史/归档文档保留原样

---

## 扫描结果摘要

| 类别 | 文件数 | 处理建议 |
|:---|:---|:---|
| Cargo.toml / Cargo.lock 实际依赖 | 0 | ✅ 无需处理 |
| 活跃概念/知识/文档中的对比引用（已标注 `[已归档]`） | ~15 | ✅ 保持现状，作为历史对比 |
| 历史报告/归档文档/审计报告 | ~40 | ✅ 保持原样，仅顶部已有警告提示 |
| 计划/roadmap 文件 | ~8 | ✅ 保持原样，作为执行记录 |
| 疑似需要清理的残留 | 0 | 🟢 无 |

---

## 关键发现

### 1. 代码层已清零

- `Cargo.toml` 中无 `async-std` 依赖项。
- `Cargo.lock` 中无 `async-std` 包。
- `crates/c06_async`、`crates/c10_networks` 等异步相关 crate 已使用 Tokio / 原生 `async fn` / AFIT。

### 2. 活跃文档状态

以下活跃文档仍提及 `async-std`，但均已正确标注 `[已归档]` 或 `[已停止维护]`，用于运行时对比教学：

- `knowledge/06_ecosystem/deep_dives/02_tokio_deep_dive.md`
- `content/ecosystem/async_runtimes/tokio_deep_dive.md`
- `docs/04_rust_language_feature_comprehensive_inventory_2026.md`
- `knowledge/03_advanced/async/01_async_await.md`
- `concept/07_future/28_rust_for_webassembly.md`

**建议**: 保留这些引用，因为它们在教授 "为什么 Tokio 成为事实标准" 时具有历史价值。

### 3. 历史/归档文档

以下文件为历史报告或归档内容，顶部已有 `⚠️ 历史文档提示` 横幅：

- `archive/verification_reports/RUST_194_12_MODULES_AUDIT_REPORT.md`
- `archive/reports/2026_Q1/RUST_195_EVOLUTION_SYMMETRIC_DIFFERENCE_ANALYSIS_2026_05_07.md`
- `archive/reports/2025-12-25/DECISION_GRAPH_NETWORK.md`
- `archive/LINK_CHECK_REPORT_FULL.md`
- `concept/archive/03_advanced_02_async_original.md`
- `concept/archive/rust_effect_system_encyclopedia.md`
- `docs/rust-ownership-decidability/visualizations/scenario-tree.md`
- `docs/rust-ownership-decidability/visualizations/KNOWLEDGE_GRAPH_MINDMAP.md`

**建议**: 不修改。

### 4. 计划/Roadmap 文件

以下文件为执行计划，提及 `async-std` 作为已完成/待完成任务：

- `.kimi/EXECUTION_PLAN_CONFIRMED_2026_06_03.md`
- `.kimi/EXECUTION_PLAN_CONFIRMED_2026_05_29.md`
- `.kimi/EXECUTION_PLAN_2026_06_02.md`
- `.kimi/CRITICAL_ASSESSMENT_AND_ROADMAP_2026_05_29.md`
- `.kimi/COMPREHENSIVE_EXTERNAL_AUDIT_2026_05_29.md`
- `reports/SYMMETRIC_DIFFERENCE_GLOBAL_AUDIT_2026_06_08.md`
- `reports/SYMMETRIC_DIFFERENCE_FOLLOWUP_PLAN_2026_05_21.md`
- `reports/MIGRATION_SCOPE_ASSESSMENT_2026_05_31.md`

**建议**: 不修改，作为项目历史决策记录。

### 5. 注意事项

- `crates/c07_process/Cargo.toml:81` 出现 `name = "async_stdio_demo"`，这是 "async stdio"（异步标准输入输出）演示，**不是** `async-std` crate 依赖，无需处理。

---

## 结论与下一步

- **async-std 清理目标已达成**：代码层无依赖，活跃文档已正确标注归档状态。
- **无需进一步大规模清理**。
- 后续仅需在新增/修改文档时保持一致性：
  - 不再将 `async-std` 作为推荐运行时
  - 若必须提及，使用 `async-std [已归档 2025-03]` 并建议 Tokio 或 smol

---

## 扫描命令

```bash
# Markdown
grep -r "async-std\|async_std" --include="*.md" .

# Cargo
grep -r "async-std\|async_std" --include="*.toml" .

# Rust source
grep -r "async-std\|async_std" --include="*.rs" .
```
