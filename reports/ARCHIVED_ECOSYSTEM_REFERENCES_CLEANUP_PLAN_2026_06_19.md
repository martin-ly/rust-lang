# 过时生态引用（async-std / wasm32-wasi）批量治理计划

> **状态**: 执行中
> **发起**: 2026-06-19
> **范围**: 全仓库 Markdown、Cargo 清单、代码注释中的 `async-std` 与旧版 `wasm32-wasi` 目标引用
> **目标**: 避免学习者被已归档/已弃用内容误导，同时为历史报告保留上下文

---

## 1. 背景与权威来源

### 1.1 `async-std` 已归档

- `async-std` 自 2024 年起进入维护模式，核心开发者建议新项目使用 **Tokio** 或 **smol**。
- 本仓库代码层已于 2026-06 完成清理：无实际 `async-std`/`backoff` 依赖，`c06_async` 与 `c10_networks` 均使用原生 `async fn`/AFIT 或 Tokio。
- 但文档层仍残留 191+ 处引用，分布在研究报告、归档笔记、学习路径中。

### 1.2 `wasm32-wasi` 目标已重命名

- 根据 Rust 官方博客：
  - 2024-04-09: [Changes to Rust's WASI targets](https://blog.rust-lang.org/2024/04/09/updates-to-wasi-targets.html)
  - 2026-04-04: [Changes to WebAssembly targets and handling undefined symbols](https://blog.rust-lang.org/2026/04/04/changes-to-webassembly-targets-and-handling-undefined-symbols.html)
- 旧目标 `wasm32-wasi` 已重命名为 **`wasm32-wasip1`**；WASI Preview 2 对应目标为 **`wasm32-wasip2`**（2024-11-26 已晋升 Tier 2）。
- 本仓库 `crates/c12_wasm` 代码已迁移至 `wasm32-wasip1/p2`，但文档中仍大量使用旧名称。

---

## 2. 治理策略

| 文件类型 | 处理原则 | 示例路径 |
|:---|:---|:---|
| **活跃学习文档** | 更新为当前推荐术语，并加历史说明 | `concept/`, `knowledge/`, `crates/*/docs/`, `content/`, `examples/` |
| **参考速查/术语表** | 保留旧名但标注「已弃用/已重命名」 | `docs/02_reference/`, `docs/10_terminology_standard.md` |
| **历史研究报告** | 不改写原文，顶部添加「历史文档」警告头 | `reports/`, `docs/archive/`, `concept/archive/`, `docs/rust-ownership-decidability/` |
| `.kimi/` 计划文件 | 仅追加说明，不破坏执行记录 | `.kimi/` |

---

## 3. 批量规则

### 3.1 `async-std`

- 若行中已含 `[已归档 2025-03]` 或「已停止维护」等字样：跳过。
- 否则在首次出现时追加：
  > `async-std` 项目已进入维护模式（2024 年后不再活跃开发），建议新项目使用 Tokio 或 smol。
- 表格/列表中的简短引用改为：
  > `async-std` `[已归档]`

### 3.2 `wasm32-wasi`

- 将独立的 `wasm32-wasi` 字符串替换为 `wasm32-wasip1`，并在附近添加注释：
  > `wasm32-wasi` 是旧目标名，现已被重命名为 `wasm32-wasip1`；WASI Preview 2 使用 `wasm32-wasip2`。
- 若上下文明确指向 WASI Preview 2（如组件模型、WIT），则使用 `wasm32-wasip2`。

---

## 4. 已知例外

- `archive/`、`reports/`、`docs/archive/` 中的历史记录保留原貌，仅加警告头。
- `crates/c12_wasm/src/wasi_migration.rs` 本身即为迁移示例，已正确，无需修改。
- 引用 `async-std` crate 作为研究对象的文档（如 `async-std-formal-analysis.md`）作为历史案例保留。

---

## 5. 质量检查

- 治理后运行：
  - `cargo check --workspace --all-features`
  - `cargo clippy --workspace --all-features`
  - `cargo test --workspace`
- 文档层不引入新的 Markdown 语法错误（脚本已校验表格分隔线）。

---

## 6. 执行结果（2026-06-19）

- [x] 治理计划与策略文档（本文件）
- [x] 活跃文档批量更新：77 个活跃 `.md` 文件顶部添加生态状态提示，正文 `wasm32-wasi` 统一替换为 `wasm32-wasip1`
- [x] 归档/报告/研究文档历史警告头：97 个文件（第一轮 54 + 第二轮 43）
- [x] 质量基线复核：`cargo check`、`cargo clippy`、`cargo test --workspace` 全绿

### 6.1 脚本与工具

- `scripts/maintenance/bulk_archive_warning.py`：为归档/报告/研究文档添加历史警告头
- `scripts/maintenance/bulk_active_ecosystem_update.py`：为活跃文档添加生态状态提示并替换旧 WASI 目标名

### 6.2 遗留问题

- 部分早期文档中存在 ``wasm32-wasip1` 或 `wasm32-wasip2`` 等Markdown 反引号嵌套格式异常，已在本次触及的文件中手工修复 2 处；其余文件待后续专项格式清理。
- 代码层 `Cargo.toml` 注释中的 `async-std`/`backoff` 残留不影响编译，保留作为历史说明。

### 6.3 统计

| 类别 | 数量 | 处理方式 |
|:---|---:|:---|
| 活跃文档更新 | 77 | 顶部提示 + `wasm32-wasi` → `wasm32-wasip1` |
| 归档/报告/研究文档警告头 | 97 | 顶部历史文档提示，保留原文 |
| 手工修复明显格式错误 | 2 | `24_wasm_target_evolution.md`、`05_rust_version_tracking.md` |
