# 贡献指南（CONTRIBUTING）

## 目标

- 统一文档与示例的结构、命名与链接规范，保证可导航与可演进。

## 命名规范

- 文件与目录：使用下划线分词（如 `02_programming_paradigms`）。
- 索引文件：目录入口统一为 `00_index.md`。
- README：目录根尽量包含 `README.md` 简介与导航。

## 结构规范

- 推荐文档结构：
  1) 目的
  2) 术语
  3) 核心概念/方法
  4) 实践与示例链接（仓库内相对路径）
  5) 设计建议/最佳实践
  6) 导航（返回上级、相关模块）

## 链接规范

- 使用相对路径链接本仓库内文档，例如：
  - `../../README.md`
  - `../01_synchronous/00_index.md`
- 在 crate 的 `README.md` 顶部添加统一导航：
  - 返回根：`../../rust-formal-engineering-system/README.md`
  - 相关主题索引（如同步/异步/质量/设计模式）。

## Lint 与格式

- Markdown：保证标题与列表前后空行，避免 MD022/MD032。
- 代码块：三反引号围栏并标注语言；不要在围栏前加缩进。
- Rust 代码：遵循 `rustfmt`，避免冗长的一行表达式。

## 提交信息（Conventional Commits）

- 类型建议：
  - `docs:` 文档/索引/导航
  - `feat:` 新示例或工具
  - `fix:` 修复链接或 lint 报告
  - `refactor:` 结构或命名调整（无行为改变）
- 示例：
  - `docs(fes): add async paradigm index and cross-links`
  - `docs(c05): add root navigation and examples map`

## 变更流程

1) 创建分支并编辑对应文件。
2) 本地运行 lint（或 IDE 内置规则），修正警告。
3) 提交 PR，并在描述中列出：变更范围、受影响链接、导航更新点。
4) 通过后合并并同步修改上级 `00_index.md` 的链接。

## 常见问题

- 新建目录忘记 `00_index.md`：请补充并更新上级索引导航。
- 链接跳转失败：优先使用相对路径，注意目录层级变化。
- 代码/文档不同步：在对应 crate 的 README 加示例清单与运行指引。
