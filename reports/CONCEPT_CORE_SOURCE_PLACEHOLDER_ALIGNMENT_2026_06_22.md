# concept/ 核心概念页精确链接占位修复报告

**日期**: 2026-06-22
**范围**: `concept/01_foundation/` 至 `07_future/`（不含 `00_meta/`，该层已在前期修复）
**目标**: 将 `[The Rust Programming Language](https://doc.rust-lang.org/book/)`、`[Rust Reference: Topic](https://doc.rust-lang.org/reference/)`、`[RFC NNNN]`、`[Wikipedia: Topic]` 等未带 URL 的占位引用转换为可点击链接

## 执行动作

1. 新建并迭代 `scripts/fix_concept_source_placeholders.py`
   - 第一轮：匹配未链接的括号来源占位符，映射 TRPL 章节、Rust Reference、Rustonomicon、Cargo Book、Async Book、Miri Book、Wikipedia、RFC、RustBelt、Tree/Stacked Borrows、Project Goals 等
   - 第二轮：扩展支持 `来源：A / B / C`、`来源：A; B; C`、`Wikipedia — Topic`、`RFC: Title`、`POPL 2018 RustBelt`、`Jung et al. ... RustBelt` 等组合与非标准写法
   - 第三轮：处理嵌套 `[来源: [Source]]`、多分隔符列表、Lang Team Blog 等剩余模式
2. 最终统计：
   - 约 **150+** 个文件参与修复
   - 未自动映射的占位符从 471 → 167 → 31 → **0**
   - 剩余 2 处为 Mermaid 流程图节点标签（如 `04 RustBelt<br/>分离逻辑验证`），不影响来源审计

## 验证结果

运行 `scripts/audit_concept_metadata.py`：

| 指标 | 数量 | 占比 |
|:---|---:|---:|
| 有英文标题 (EN) | 345 | 100.0% |
| 英文标题为占位符 | 0 | 0.0% |
| 有英文摘要 (Summary) | 345 | 100.0% |
| 英文摘要为占位符 | 0 | 0.0% |
| 有权威来源链接 | 345 | 100.0% |

构建与测试：

- `cargo check --workspace` ✅
- `cargo test --test l3_ecosystem_alignment` ✅（12 项全部通过）

## 典型修复示例

| 原文 | 修复后 |
|:---|:---|
| `[The Rust Programming Language](https://doc.rust-lang.org/book/)` | `[TRPL: Ch4.1](https://doc.rust-lang.org/book/ch04-01-what-is-ownership.html)` |
| `来源: [RustBelt](https://plv.mpi-sws.org/rustbelt/)` | `来源: [RustBelt: POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/)` |
| `[来源: Wikipedia: Linear logic]` | `来源: [Wikipedia: Linear logic](https://en.wikipedia.org/wiki/Linear_logic)` |
| `来源: [Rust Reference; TRPL; Rust RFCs; Academic Papers](https://doc.rust-lang.org/reference/)` | `来源: [Rust Reference](...); [TRPL](...); [Rust RFCs](...); Academic Papers` |
| `来源: [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/)` | `来源: [POPL 2018 - RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)` |

## 遗留与下一步

- Mermaid 决策树节点中的来源标签保持纯文本，避免破坏图表渲染
- 继续按 `.kimi/EXECUTION_RUST_1_97_RELEASE_2026_07_09.md` 准备 Rust 1.97 发布内容
- 跟踪 Sea-ORM 2.0 stable 与 cargo-vet/cargo audit 上游修复
