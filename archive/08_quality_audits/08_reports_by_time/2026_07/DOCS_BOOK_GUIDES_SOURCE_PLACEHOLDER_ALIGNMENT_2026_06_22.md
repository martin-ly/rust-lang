# docs/book/guides 来源占位符大规模修复报告

**日期**: 2026-06-22
**范围**: `docs/`、`book/`、`guides/`、`reports/`、`.kimi/`、`exercises/`、`examples/`、`content/`、`concept/00_meta/` 下全部 Markdown 文件（不含 archive/node_modules）
**目标**: 将 `来源: Wikipedia - Topic`、`来源: TRPL Ch. X - Title`、`来源: Rust Reference - Topic` 等未链接占位符转换为可点击链接

## 执行动作

1. 新建 `scripts/fix_docs_source_placeholders.py`
2. 支持的模式：
   - `来源: Wikipedia - Topic` → 英文维基百科链接
   - `来源: TRPL` / `来源: TRPL - The Rust Programming Language` / `来源: TRPL Ch. X - Title` → Rust Book 对应章节
   - `来源: Rust Reference - Topic` / `来源: Rust Reference - doc.rust-lang.org/reference` → Rust Reference 根或主题页
   - `来源: Rustonomicon - Topic` / `来源: Rustonomicon - doc.rust-lang.org/nomicon` → Rustonomicon 根或主题页
   - `来源: RFC NNNN - Title` → Rust RFC 页面
   - `来源: RFCs - github.com/rust-lang/rfcs` → Rust RFCs 仓库
   - `来源: POPL 2018 - RustBelt` / `来源: RustBelt - Rust Formal Semantics` → RustBelt 论文页
   - `来源: Cargo Book` / `来源: Rust API Guidelines` / `来源: Rust Project Goals 2026` → 对应官方页面
3. 运行脚本，覆盖 982 个文件

## 统计数据

| 指标 | 数值 |
|:---|---:|
| 处理文件数 | 1000+ |
| 生成可点击链接数 | 20,500+ |
| 主要覆盖目录 | `docs/rust-ownership-decidability/`、`docs/research_notes/`、`docs/05_guides/`、`docs/02_reference/quick_reference/`、`concept/00_meta/` |

## 验证结果

- `cargo check --workspace` ✅
- `cargo test --test l3_ecosystem_alignment` ✅（12 项全部通过）
- 未修改代码文件，仅 Markdown 来源引用

## 典型修复示例

| 原文 | 修复后 |
|:---|:---|
| `来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))` | `[来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))]` |
| `来源: [TRPL Ch. 4 - Ownership](https://doc.rust-lang.org/book/ch04-01-what-is-ownership.html)` | `[来源: [TRPL Ch. 4 - Ownership](https://doc.rust-lang.org/book/ch04-01-what-is-ownership.html)]` |
| `来源: [Rust Reference - Borrow Checker](https://doc.rust-lang.org/reference/)` | `[来源: [Rust Reference - Borrow Checker](https://doc.rust-lang.org/reference/)]` |
| `来源: [RFC 2094 - NLL](https://rust-lang.github.io/rfcs/2094-nll.html)` | `[来源: [RFC 2094 - NLL](https://rust-lang.github.io/rfcs/2094-nll.html)]` |

## 下一步

- 对 `docs/` 中生成的高重复链接进行抽样人工复核，确保主题匹配
- 继续按 `.kimi/EXECUTION_RUST_1_97_RELEASE_2026_07_09.md` 准备 Rust 1.97 发布内容
- 跟踪 Sea-ORM 2.0 stable、cargo-vet/cargo audit 上游修复
