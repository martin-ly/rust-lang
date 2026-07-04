# 全仓库命名规范 (Naming Convention)

> **EN**: Repository-wide naming convention for files, directories, and identifiers.
> **Scope**: 本规范适用于 `e:\_src\rust-lang` 及其所有子目录。当子目录存在更具体的命名约定时，子目录规则优先。

---

## 1. 总则

本知识库采用 **snake_case** 作为默认命名风格，目标是保证跨平台（尤其是 Windows/Linux/macOS 与 URL）的兼容性、可搜索性与一致性。

## 2. 文件与目录命名

### 2.1 默认规则

| 项目 | 规则 | 示例 |
|---|---|---|
| Markdown 文件 | `snake_case.md` 或 `number_prefix_snake_case.md` | `01_ownership.md`, `api_naming_conventions.md` |
| 目录 | `snake_case` 或 `number_prefix_snake_case` | `01_foundation`, `knowledge_topology` |
| Rust 源文件 | `snake_case.rs` | `main.rs`, `lib.rs`, `build.rs` |
| Python 脚本 | `snake_case.py` | `kb_auditor.py`, `detect_content_overlap.py` |
| 配置文件 | 按生态习惯，但优先小写 | `Cargo.toml`, `rust-toolchain.toml` |

### 2.2 禁止项

- 中文文件名
- 空格
- 混合大小写（如 `CamelCase.md`, `PascalCase.rs`）
- 特殊符号（除 `_`、`-`、`.` 外）

### 2.3 例外（过渡期保留）

以下位置的历史文件或日期风格文件可暂时保留原有命名，但新增文件应遵循本规范：

| 位置 | 说明 |
|---|---|
| `archive/` | 只读历史归档 |
| `.kimi/` | 日期风格的计划/检查清单文件 |
| `reports/` | 日期风格的审计报告 |
| `.github/ISSUE_TEMPLATE/` | GitHub 官方模板 |
| 标准生态文件名 | `README.md`, `Cargo.toml`, `CHANGELOG.md`, `LICENSE`, `Dockerfile`, `Makefile` 等 |

## 3. 概念文件层级编号

`concept/` 目录使用两位数字前缀表示 L0-L7 层级：

| 前缀 | 层级 | 示例 |
|---|---|---|
| `00_meta/` | L0 元层 | `00_meta/learning_guide.md` |
| `01_foundation/` | L1 基础 | `01_foundation/01_ownership.md` |
| `02_intermediate/` | L2 进阶 | `02_intermediate/01_traits.md` |
| `03_advanced/` | L3 高级 | `03_advanced/01_concurrency.md` |
| `04_formal/` | L4 形式化 | `04_formal/01_linear_logic.md` |
| `05_comparative/` | L5 比较 | `05_comparative/01_rust_vs_cpp.md` |
| `06_ecosystem/` | L6 生态 | `06_ecosystem/01_toolchain.md` |
| `07_future/` | L7 未来 | `07_future/01_ai_integration.md` |

## 4. crates 命名

Workspace crate 使用 `cXX_short_name` 格式：

- `c01_ownership_borrow_scope`
- `c02_type_system`
- `c06_async`

每个 crate 内部仍遵循 snake_case；`crates/*/reports/` 中的历史报告应逐步迁移到顶层 `archive/`。

## 5. 标识符命名

| 类型 | Rust | Python |
|---|---|---|
| 变量/函数 | `snake_case` | `snake_case` |
| 类型/结构体 | `PascalCase` | `PascalCase` |
| 常量 | `SCREAMING_SNAKE_CASE` | `SCREAMING_SNAKE_CASE` |
| 模块 | `snake_case` | `snake_case` |
| 宏 | `snake_case!` | — |

## 6. 检查命令

```bash
# 检查活跃目录中不符合 snake_case 的命名
python scripts/check_naming_convention.py
```

## 7. 违规处理流程

1. 新增文件必须通过命名检查。
2. 发现违规时，优先重命名文件并修复所有内部/外部引用。
3. 历史报告类文件优先迁移到 `archive/` 而非原地重命名。

---

**最后更新**: 2026-07-04
