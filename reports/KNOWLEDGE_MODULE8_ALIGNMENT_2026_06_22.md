# knowledge/ 模块 8 国际化对齐批量补充报告

> **执行日期**: 2026-06-22
> **脚本**: `scripts/bulk_add_knowledge_module8.py`
> **策略**: 仅向尚未包含 `## 📚 模块 8: 国际化对齐` 的文件追加模块 8；保留原有内容。

---

## 统计

- **扫描范围**: `knowledge/` 下所有 `*.md`（排除 `archive/`、`temp/`、`README.md`、`SUMMARY.md`）
- **已存在模块 8 的文件**: 30 个
- **本次补充文件数**: 89 个
- **主题分布**:

| 主题 | 文件数 |
|:---|---:|
| safety_critical | 44 |
| version_tracking | 8 |
| reference | 5 |
| start | 3 |
| roadmap | 3 |
| ownership | 2 |
| ffi | 2 |
| inline_asm | 2 |
| performance_optimization | 2 |
| default | 2 |
| formal | 2 |
| deployment | 2 |
| security | 2 |
| database | 2 |
| philosophy | 1 |
| borrowing | 1 |
| iterators | 1 |
| type_conversions | 1 |
| compiler_internals | 1 |
| type_driven_correctness | 1 |
| type_system | 1 |
| async | 1 |

---

## 主题推断规则

脚本按以下优先级确定每份文档的主题：

1. 文件名（不含扩展名）精确匹配关键词（如 `borrowing` → borrowing）。
2. 文件名中的最长关键词匹配（如 `performance_optimization` → performance_optimization）。
3. 目录默认主题（如 `04_expert/safety_critical/` → safety_critical）。
4. 内容前 800 字符中的最长关键词匹配。
5. 回退到 `default`。

---

## 来源结构

每个补充的模块 8 均包含三个子节：

- **8.1 官方来源**：TRPL、Rust Reference、Rustonomicon、Cargo Book、Async Book、std API 等官方文档。
- **8.2 学术来源**：RustBelt、Tree Borrows、RefinedRust、RFC 论文、形式化语义等。
- **8.3 社区权威**：This Week in Rust、Rustlings、Tokio/Axum/Diesel 官方文档、Rust Cookbook、Rust API Guidelines 等。

---

## 示例

### `knowledge/01_fundamentals/01_borrowing.md`

```markdown
## 📚 模块 8: 国际化对齐

> 本节按项目模板要求补充国际化权威来源：官方文档、学术论文/工业报告、社区权威资源。

### 8.1 官方来源

| 来源 | 类型 | 说明 |
|:---|:---|:---|
| [TRPL Ch04 — References and Borrowing](https://doc.rust-lang.org/book/ch04-02-references-and-borrowing.html) | 权威来源 | 借用与引用 |
| [Rust Reference — Lifetimes](https://doc.rust-lang.org/reference/lifetime-elision.html) | 权威来源 | 生命周期省略 |

### 8.2 学术来源

| 来源 | 类型 | 说明 |
|:---|:---|:---|
| [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) | 权威来源 | 借用语义 |
| [Tree Borrows — PLDI 2025](https://perso.crans.org/vanille/treebor/) | 权威来源 | 别名模型 |

### 8.3 社区权威

| 来源 | 类型 | 说明 |
|:---|:---|:---|
| [Brown University Interactive Rust Book](https://rust-book.cs.brown.edu/) | 权威来源 | 借用可视化 |
| [Rustlings](https://github.com/rust-lang/rustlings) | 权威来源 | 借用练习 |
```

---

## 后续工作

1. **人工复核**: 89 个文件中部分主题推断（如 `default`、`reference`）可能偏泛，建议由领域负责人复核并细化。
2. **缺失主题**: `knowledge/02_intermediate/` 中仍有部分核心文件已存在模块 8 但内容较泛，可进一步补充具体章节映射。
3. **概念页对齐**: `concept/` 下部分页面仍可补充「国际化对齐」或「来源」章节。
4. **自动化检查**: 可在 CI 中添加脚本，确保新增 knowledge 文档必须包含模块 8。

---

## 验证

- `cargo check --workspace` ✅
- `cargo test --test l3_ecosystem_alignment` ✅ 12 passed
- `cargo clippy -p c02_type_system -- -D warnings` ✅
- `cargo clippy -p exercises --tests -- -D warnings` ✅
