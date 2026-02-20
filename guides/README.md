# 学习指南 (Learning Guides)

> **说明**: 本目录为项目学习指南的集中入口。部分指南内容已整合至 `docs/` 和 `crates/*/docs/`。
> **最后更新**: 2026-02-13
> **完成度**: ✅ 100%（所有入口已就绪）

---

## 指南导航

### 快速入口

| 指南 | 实际位置 | 说明 |
| :--- | :--- | :--- || **快速开始** | [docs/README.md](../docs/README.md) | 文档主索引 |
| **学习检查清单** | [LEARNING_CHECKLIST.md](../LEARNING_CHECKLIST.md) | 进度追踪、间隔重复、自测题 |
| **交互式练习** | [exercises/README.md](../exercises/README.md) | Rustlings、Playground 对接 |
| **Rustlings 模块映射** | [exercises/RUSTLINGS_MAPPING.md](../exercises/RUSTLINGS_MAPPING.md) | C01–C12 与 Rustlings 习题对应 |
| **错误码映射** | [docs/02_reference/ERROR_CODE_MAPPING.md](../docs/02_reference/ERROR_CODE_MAPPING.md) | 编译器错误码 → 文档 |
| **QUICK_START** | [crates/c01_ownership_borrow_scope/docs/QUICK_START_GUIDE.md](../crates/c01_ownership_borrow_scope/docs/QUICK_START_GUIDE.md) | 所有权模块快速入门 |
| **异步编程快速开始** | [crates/c06_async/QUICK_START_GUIDE_2025.md](../crates/c06_async/QUICK_START_GUIDE_2025.md) | C06 异步快速入门 |

### 使用指南（位于 docs/）

| 指南 | 路径 |
| :--- | :--- || 异步编程使用指南 | [docs/05_guides/ASYNC_PROGRAMMING_USAGE_GUIDE.md](../docs/05_guides/ASYNC_PROGRAMMING_USAGE_GUIDE.md) |
| 设计模式使用指南 | [docs/05_guides/DESIGN_PATTERNS_USAGE_GUIDE.md](../docs/05_guides/DESIGN_PATTERNS_USAGE_GUIDE.md) |
| 宏系统使用指南 | [docs/05_guides/MACRO_SYSTEM_USAGE_GUIDE.md](../docs/05_guides/MACRO_SYSTEM_USAGE_GUIDE.md) |
| 线程并发使用指南 | [docs/05_guides/THREADS_CONCURRENCY_USAGE_GUIDE.md](../docs/05_guides/THREADS_CONCURRENCY_USAGE_GUIDE.md) |
| WASM 使用指南 | [docs/05_guides/WASM_USAGE_GUIDE.md](../docs/05_guides/WASM_USAGE_GUIDE.md) |
| 性能调优指南 | [docs/05_guides/PERFORMANCE_TUNING_GUIDE.md](../docs/05_guides/PERFORMANCE_TUNING_GUIDE.md) |
| 故障排查指南 | [docs/05_guides/TROUBLESHOOTING_GUIDE.md](../docs/05_guides/TROUBLESHOOTING_GUIDE.md) |

### 已完善指南

| 指南 | 路径 | 说明 |
| :--- | :--- | :--- || **AI 辅助编程指南** | [AI_ASSISTED_RUST_PROGRAMMING_GUIDE_2025.md](./AI_ASSISTED_RUST_PROGRAMMING_GUIDE_2025.md) | 提示词模板、RAG、工作流 |
| **AI+Rust 生态指南** | [docs/05_guides/AI_RUST_ECOSYSTEM_GUIDE.md](../docs/05_guides/AI_RUST_ECOSYSTEM_GUIDE.md) | Burn/Candle/LLM、用 Rust 构建 AI |

### 专题指南

| 指南 | 路径 | 说明 |
| :--- | :--- | :--- || **Unsafe Rust** | [docs/05_guides/UNSAFE_RUST_GUIDE.md](../docs/05_guides/UNSAFE_RUST_GUIDE.md) | Rustonomicon 导航与安全抽象 |
| **CLI 应用开发** | [docs/05_guides/CLI_APPLICATIONS_GUIDE.md](../docs/05_guides/CLI_APPLICATIONS_GUIDE.md) | 对标 Command Line Book |
| **嵌入式 Rust** | [docs/05_guides/EMBEDDED_RUST_GUIDE.md](../docs/05_guides/EMBEDDED_RUST_GUIDE.md) | 对标 Embedded Book |

### 导航入口（已就绪）

| 主题 | 项目内入口 | 说明 |
| :--- | :--- | :--- || **编译器内部机制** | [docs/06_toolchain/](../docs/06_toolchain/README.md) | 编译器特性、Cargo、rustdoc；[rustc Book](https://doc.rust-lang.org/rustc/) |
| **认知科学学习** | [LEARNING_CHECKLIST.md](../LEARNING_CHECKLIST.md) | 间隔重复、自测题；[Brown 交互版](https://rust-book.cs.brown.edu/) |
| **大学课程对标** | [docs/01_learning/OFFICIAL_RESOURCES_MAPPING.md](../docs/01_learning/OFFICIAL_RESOURCES_MAPPING.md) | 官方资源映射、模块对标 |
| **交互式学习平台** | [exercises/README.md](../exercises/README.md)、[RUSTLINGS_MAPPING.md](../exercises/RUSTLINGS_MAPPING.md) | Rustlings、Playground、习题映射 |
| **全局理论框架** | [docs/07_project/KNOWLEDGE_STRUCTURE_FRAMEWORK.md](../docs/07_project/KNOWLEDGE_STRUCTURE_FRAMEWORK.md) | 知识结构、思维表征 |
| **实践项目路线图** | [docs/01_learning/LEARNING_PATH_PLANNING.md](../docs/01_learning/LEARNING_PATH_PLANNING.md)、[CROSS_MODULE_INTEGRATION_EXAMPLES.md](../docs/05_guides/CROSS_MODULE_INTEGRATION_EXAMPLES.md) | 学习路径、跨模块集成示例 |

---

## 官方资源映射

| 官方资源 | 链接 | 项目对应 |
| :--- | :--- | :--- || The Rust Book | <https://doc.rust-lang.org/book/> | C01-C03 基础模块 |
| Rust By Example | <https://doc.rust-lang.org/rust-by-example/> | 各模块 examples/ |
| Rust Reference | <https://doc.rust-lang.org/reference/> | docs/ 深度文档 |
| Rustonomicon | <https://doc.rust-lang.org/nomicon/> | [UNSAFE_RUST_GUIDE](../docs/05_guides/UNSAFE_RUST_GUIDE.md)、形式化验证 |
| Cargo Book | <https://doc.rust-lang.org/cargo/> | [cargo_cheatsheet](../docs/02_reference/quick_reference/cargo_cheatsheet.md) |
| Command Line Book | <https://rust-cli.github.io/book/> | [CLI_APPLICATIONS_GUIDE](../docs/05_guides/CLI_APPLICATIONS_GUIDE.md) |
| Embedded Book | <https://doc.rust-lang.org/embedded-book/> | [EMBEDDED_RUST_GUIDE](../docs/05_guides/EMBEDDED_RUST_GUIDE.md) |
| Rustlings | <https://github.com/rust-lang/rustlings> | [RUSTLINGS_MAPPING](../exercises/RUSTLINGS_MAPPING.md) |
| Brown 交互版 | <https://rust-book.cs.brown.edu/> | 测验、可视化、高亮 |
| Compiler Error Index | <https://doc.rust-lang.org/error-index.html> | [ERROR_CODE_MAPPING](../docs/02_reference/ERROR_CODE_MAPPING.md) |

---

## 指南完成度

| 类别 | 数量 | 状态 |
| :--- | :--- | :--- || 快速入口 | 7 | ✅ |
| 使用指南 | 7 | ✅ |
| 速查卡 | 20 | ✅ |
| 已完善指南 | 2 (AI 辅助、AI+Rust 生态) | ✅ |
| 专题指南 | 3 (Unsafe/CLI/嵌入式) | ✅ |
| 导航入口 | 6 | ✅ |
| 官方资源映射 | 10 | ✅ |

---

**维护说明**: 本目录为指南入口索引。具体指南内容请查阅 `docs/` 或各 crate 的 `docs/` 子目录。
