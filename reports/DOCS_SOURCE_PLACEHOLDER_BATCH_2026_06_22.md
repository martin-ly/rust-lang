# 全仓库 Markdown 来源占位符二次精修报告

> **执行日期**: 2026-06-22
> **状态**: ✅ 完成（脚本 + 抽样复核）
> **关联脚本**: `scripts/fix_docs_source_placeholders.py`

---

## 1. 修复内容

### 1.1 脚本关键 bug 修复

`scripts/fix_docs_source_placeholders.py` 的 `lookup()` 函数在维护过程中被误插入提前的 `return None`，导致：

- Wikipedia / RFC / TRPL / Rust Reference / Rustonomicon / Cargo Book 等核心模式全部失效
- 上一次运行实际只命中了 Tree/Stacked Borrows、Async Book 等极少数模式

本次已移除该 `return None`，并补充以下鲁棒性改进：

| 改进项 | 说明 |
|--------|------|
| 代码保护 | 通过 `FENCED_CODE_RE` / `INLINE_CODE_RE` 跳过 fenced block 与行内代码，避免 `#[kani::loop_invariant]` 等被误替换 |
| 引用链接保护 | `PATTERN` 增加 `(?!\(|\[)`，避免破坏已有 Markdown 链接与 reference-style 链接 |
| 嵌套括号归一化 | `lookup()` 自动剥离 `[The Rust Programming Language]` 这类一层括号包装 |
| 全匹配锚定 | 对 `Cargo`、`Clippy`、`crates.io` 等单术语改用 `re.fullmatch`，防止 `cargo-geiger` 被截断为 `Cargo` |

### 1.2 来源映射扩展

新增/补全的映射类别：

- **Rust 官方文档**: Rust Official Docs、Rust Standard Library、Rust Reference、TRPL、Rustonomicon、Rust By Example、Rust Cookbook、Rust CLI Book、Rust Design Patterns、The Rust Performance Book、The Embedded Rust Book、Rust Edition Guide、Rust Project Goals 等
- **学术会议**: ACM、IEEE、POPL、PLDI
- **形式化工具**: Kani、Verus、Prusti、Creusot、Aeneas、Miri、Coq、TLA+、Iris Project、Tree Borrows、RustBelt
- **生态 crate/工具**: serde、tokio、rayon、crossbeam、clap、axum、bevy、tauri、tokio-postgres、sqlx、diesel、sea-orm、tracing、anyhow、reqwest、ripgrep、bat、fd 等
- **发布跟踪**: releases.rs、Can I Use、cargo-vet、RustSec
- **其他权威来源**: LLVM Documentation、GitHub、crates.io、docs.rs、lib.rs、Inside Rust、This Week in Rust 等

---

## 2. 运行结果

```text
Pass 1: 1009 files, 11,379 replacements
Pass 2:  252 files,    449 replacements
----------------------------------------
Total:  1261 files, 11,828 replacements
```

覆盖目录：

- `docs/`
- `book/`
- `guides/`
- `reports/`
- `.kimi/`
- `exercises/`
- `examples/`
- `content/`
- `concept/`

> 注：`archive/` 与 `node_modules/` 仍按策略跳过。

---

## 3. 抽样复核

随机抽查以下文件，确认替换结果符合预期：

- `docs/04_research/04_cranelift_backend.md`：`[来源: Rust Official Docs]` → `来源: [Rust Official Docs](https://doc.rust-lang.org/)`
- `docs/04_research/04_cranelift_backend.md`：`[来源: ACM - Systems Programming]` → `来源: [ACM](https://dl.acm.org/)`
- `concept/06_ecosystem/03_core_crates.md`：`[serde]`、`[tokio.rs]`、`[crossbeam]` 等生态标签自动链接
- `concept/06_ecosystem/02_patterns.md`：`[Rust Design Patterns]` → 设计模式书直链
- `concept/07_future/rust_1_97_preview.md`：`[来源: releases.rs 2026-06-19]` → `来源: [Releases.rs](https://releases.rs/)`，行内代码 `#[kani::loop_invariant]` 未被误伤

---

## 4. 验证

```bash
cargo check --workspace
# Finished `dev` profile [unoptimized + debuginfo] target(s) in 0.47s
```

Markdown 变更未影响 Rust 构建。

---

## 5. 剩余工作

- 仍有少量内部标签（如 `💡 原创分析`、`Authority Source Sprint Batch N`）及年份/作者型学术引用（`van der Aalst 2003`、`Pierce 2002 - TAPL`）未自动链接，建议作为下一批人工/半自动精修对象。
- Mermaid 节点标签、目录中转义长来源字符串等复杂/转义场景仍需单独脚本或人工复核。
