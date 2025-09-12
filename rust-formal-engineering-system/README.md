# Rust 形式化工程系统（Rust Formal Engineering System）

本仓库旨在构建面向 Rust 的体系化「形式化工程系统」，贯通理论、范式、模式、领域、工具与质量保障，形成可演进的知识图谱与可执行示例。

## 项目目标

- 建立覆盖从理论到实践的结构化索引与导航。
- 以模块化文档与代码样例呈现核心概念与方法论。
- 提供跨模块的一致术语体系与交叉链接，支持持续演进。

## 项目结构（一级视图）

- 01_theoretical_foundations：理论基础（类型系统、代数、范畴、语义等）
- 02_programming_paradigms：编程范式（同步、异步、函数式、面向对象等）
- 03_design_patterns：设计模式（创建型、结构型、行为型，Rust 实践）
- 04_application_domains：应用领域（系统、网络、嵌入式、AI 等）
- 05_software_engineering：工程方法（需求、设计、测试、维护）
- 06_toolchain_ecosystem：工具链与生态（Cargo、Clippy、Miri、Fuzz 等）
- 07_cross_language_comparison：跨语言比较（C/C++、Go、Haskell、Zig 等）
- 08_practical_examples：实用示例（最佳实践与样板）
- 09_research_agenda：研究议程（前沿方向与问题列表）
- 10_quality_assurance：质量保障（形式化验证、测试、度量）

## 快速导航

- 编程范式总览：[`02_programming_paradigms/`](./02_programming_paradigms/)，同步范式索引见 [`01_synchronous/00_index.md`](./02_programming_paradigms/01_synchronous/00_index.md)
- 设计模式总览：[`03_design_patterns/`](./03_design_patterns/)
- 质量保障总览：[`10_quality_assurance/`](./10_quality_assurance/)

## 构建与使用

- 文档：直接浏览各目录下的 `*.md`。
- 代码：配套示例位于仓库 `crates/` 与 `formal_rust/`、`rust-formal-engineering-system` 相关子目录。
- 建议使用 `just` 或 `cargo` 脚本执行示例（根目录含 `justfile`）。

## 运行指南

- 构建：`cargo build -p <crate>`，示例如 `c06_async`、`c10_networks`
- 测试：`cargo test -p <crate>` 或工作区根运行 `cargo test`
- 基准：`cargo bench -p <crate>`（或 `--no-run` 先行）
- Windows PowerShell 示例请参考各 crate 的 README 顶部导航链接

## 常见问题（FAQ）

- 链接跳转失败？优先相对路径；确认目录层级；参考 [`CONTRIBUTING.md`](./CONTRIBUTING.md)
- 新建目录如何纳入导航？创建 `00_index.md` 并更新上级索引/根导航
- 如何选择同步/异步？参考 [`01_synchronous/00_index.md`](./02_programming_paradigms/01_synchronous/00_index.md) 与 [`02_async/00_index.md`](./02_programming_paradigms/02_async/00_index.md)

## 贡献指南（简要）

- 统一命名：文件与目录统一使用下划线分词；索引文件命名为 `00_index.md`。
- 统一结构：每个子模块建议包含 1) 目的、2) 术语、3) 核心概念、4) 实践、5) 参考。
- 统一链接：尽量使用相对路径链接同项目内文档；新增文档请更新相应上层 `00_index.md`。
- 完整贡献细则：参见 [`CONTRIBUTING.md`](./CONTRIBUTING.md)

## 里程碑

- v0.1：完成一级结构梳理与关键索引文件。
- v0.2：完成主要模块的交叉链接与最小实践样例。
- v1.0：覆盖核心主题并形成稳定导航体系。
