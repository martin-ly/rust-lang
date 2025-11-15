# Rust 形式化工程系统（Rust Formal Engineering System）

> **创建日期**: 2025-01-27
> **最后更新**: 2025-11-15
> **Rust 版本**: 1.91.1+ (Edition 2024) ✅
> **状态**: 持续维护中 🔄
> **更新内容**: Rust 1.91.1 特性更新完成 ✅

---

本仓库旨在构建面向 Rust 的体系化「形式化工程系统」，贯通理论、范式、模式、领域、工具与质量保障，形成可演进的知识图谱与可执行示例。

## 🎯 项目概述

Rust 形式化工程系统是一个全面的 Rust 学习和参考资源库，涵盖从理论基础到实践应用的所有方面。系统采用模块化设计，提供清晰的导航和交叉引用，支持持续演进和更新。

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

### 🗺️ 统一导航入口

- **[形式化理论与实践统一导航](../FORMAL_AND_PRACTICAL_NAVIGATION.md)** ⭐⭐⭐ - 推荐入口
  - 提供形式化系统与主项目代码之间的快速导航
  - 支持双向链接，无缝切换
  - 包含学习路径建议

### 核心模块

- 理论基础：[`01_theoretical_foundations/`](./01_theoretical_foundations/) - 类型系统、所有权、并发模型
- 编程范式：[`02_programming_paradigms/`](./02_programming_paradigms/) - 同步/异步、函数式、面向对象
- 设计模式：[`03_design_patterns/`](./03_design_patterns/) - 创建型、结构型、行为型模式
- 质量保障：[`10_quality_assurance/`](./10_quality_assurance/) - 测试、验证、度量

### 实践模块

- 应用领域：[`04_application_domains/`](./04_application_domains/) - 系统、网络、嵌入式、AI
- 软件工程：[`05_software_engineering/`](./05_software_engineering/) - 需求、设计、测试、运维
- 工具链生态：[`06_toolchain_ecosystem/`](./06_toolchain_ecosystem/) - Cargo、Clippy、Miri、Fuzz
- 实用示例：[`08_practical_examples/`](./08_practical_examples/) - 最佳实践与样板

### 扩展模块

- 跨语言比较：[`07_cross_language_comparison/`](./07_cross_language_comparison/) - C/C++、Go、Haskell、Zig
- 研究议程：[`09_research_agenda/`](./09_research_agenda/) - 前沿方向与问题列表

## 🔗 相关链接

- [统一导航页面](../FORMAL_AND_PRACTICAL_NAVIGATION.md) - 理论与实践导航
- [快速开始](./QUICK_START.md) - 5分钟快速上手指南 ⭐
- [维护指南](./MAINTENANCE_GUIDE.md) - 系统维护和更新指南 ⭐
- [版本更新日志](./RUST_1_91_CHANGELOG.md) - Rust 1.91 更新日志 ⭐
- [更新总结](./RUST_1_91_UPDATE_SUMMARY.md) - Rust 1.91 更新总结 ⭐
- [快速参考指南](./RUST_1_91_QUICK_REFERENCE.md) - Rust 1.91 快速参考 ⭐
- [最终状态报告](./RUST_1_91_FINAL_STATUS.md) - Rust 1.91 更新最终状态 ⭐
- [完成度报告](./COMPLETION_STATUS_REAL_2025_10_30.md) - 真实完成度评估

## 🛠️ 工具脚本

- `update_rust_version.sh` - 批量更新版本号
- `mark_placeholders.sh` - 自动标注占位符文件
- `check_links.sh` - 检查链接有效性
- `verify_cross_references.sh` - 验证和更新交叉引用
- `maintenance_check.sh` - 自动化维护检查（季度/月度/周度）

详细使用说明请参考 [维护指南](./MAINTENANCE_GUIDE.md) 和 [快速开始](./QUICK_START.md)。

- 文档：直接浏览各目录下的 `*.md`。
- 代码：配套示例位于仓库 `crates/` 与 `formal_rust/`、`rust-formal-engineering-system` 相关子目录。
- 建议统一使用 `cargo` 命令执行示例（本仓库不再依赖 `justfile`）。

## 运行指南

- 构建：`cargo build -p <crate>`，示例如 `c06_async`、`c10_networks`
- 测试：`cargo test -p <crate>` 或工作区根运行 `cargo test`
- 基准：`cargo bench -p <crate>`（或 `--no-run` 先行）
- Windows PowerShell 示例请参考各 crate 的 README 顶部导航链接

### 快速入口：基准与范式

- 最小基准指南：[`02_programming_paradigms/11_benchmark_minimal_guide.md`](./02_programming_paradigms/11_benchmark_minimal_guide.md)
- 异步范式：[`02_programming_paradigms/02_async/00_index.md`](./02_programming_paradigms/02_async/00_index.md)
- 同步范式：[`02_programming_paradigms/01_synchronous/00_index.md`](./02_programming_paradigms/01_synchronous/00_index.md)

## 常见问题（FAQ）

- 链接跳转失败？优先相对路径；确认目录层级；参考 [`CONTRIBUTING.md`](./CONTRIBUTING.md)
- 新建目录如何纳入导航？创建 `00_index.md` 并更新上级索引/根导航
- 如何选择同步/异步？参考 [`02_programming_paradigms/01_synchronous/00_index.md`](./02_programming_paradigms/01_synchronous/00_index.md) 与 [`02_programming_paradigms/02_async/00_index.md`](./02_programming_paradigms/02_async/00_index.md)
- 目录别名说明：异步范式主目录为 `02_async`；`02_asynchronous` 为兼容别名，仅含说明页与单一跳转；新增链接统一指向主目录。若历史链接指向 `02_asynchronous`，将通过该页跳转至主目录。
- 快速入口：[`异步范式主目录`](./02_programming_paradigms/02_async/00_index.md) ・ [`异步别名说明`](./02_programming_paradigms/02_asynchronous/00_index.md)

## 贡献指南（简要）

- 统一命名：文件与目录统一使用下划线分词；索引文件命名为 `00_index.md`。
- 统一结构：每个子模块建议包含 1) 目的、2) 术语、3) 核心概念、4) 实践、5) 参考。
- 统一链接：尽量使用相对路径链接同项目内文档；新增文档请更新相应上层 `00_index.md`。
- 完整贡献细则：参见 [`CONTRIBUTING.md`](./CONTRIBUTING.md)

## 新增主题最小步骤（Minimal Steps）

1) 在目标目录创建 `00_index.md`，包含：目的、术语、核心概念、仓库内示例链接、导航。
2) 在相邻上层 `00_index.md` 添加该目录的相对链接。
3) 在本 README 的“快速导航”或相关总览处补充入口（如适用）。
4) 若涉及代码示例，在对应 `crates/*` 的 README 顶部加入返回到本目录的导航。
5) 运行 Markdown Lint，确保标题/列表周围空行、代码块围栏规范。

## 📈 项目里程碑

- **v0.1** (2025-01-27): 完成一级结构梳理与关键索引文件 ✅
- **v0.2** (2025-10-30): 完成主要模块的交叉链接与最小实践样例 ✅
- **v1.0** (2025-11-10): 覆盖核心主题并形成稳定导航体系，同步到 Rust 1.91 ✅
- **v1.1** (2025-11-15): 同步到 Rust 1.91.1，完善所有模块内容 ✅
- **v1.2** (进行中): 持续完善内容，对标最新网络资源 🔄

## 🔄 当前状态

- ✅ Rust 1.91.1 版本更新已完成
- ✅ 核心文档已创建并更新
- ✅ 所有 crates 文档已统一标准化
- 🔄 占位符文件正在完善中
- 🔄 内容对标网络资源进行中

---

**最后更新**: 2025-11-15
**Rust 版本**: 1.91.1+
**维护者**: 项目维护者
**状态**: 持续维护中 🔄
