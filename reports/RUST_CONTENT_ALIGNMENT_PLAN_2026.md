# Rust 项目全面内容对齐计划（2026）

> 生成日期：2026-05-11
> 基于：项目 v1.3.0 状态 + Rust 1.96.0+（stable）生态前沿 + 网络权威内容
> 制定原则：权威溯源、可运行验证、最小侵入、对称差跟踪

---

## 一、总体目标与原则

**目标**：将本项目从当前 v1.3.0 状态，全面对齐至 **Rust 1.96.0+（stable）** 及 **2025-2026 生态前沿**，覆盖语言特性、工具链、学术权威、生产实践四大维度，消除所有高优先级内容缺口。

**原则**：

- **权威溯源**：所有新增/更新内容必须标注权威来源（官方博客、RFC、PLDI/POPL 论文、RustConf 演讲、crates.io 官方文档）
- **可运行验证**：所有代码示例必须通过 `cargo check/clippy/test`， unsafe 代码需通过 Miri
- **最小侵入**：优先复用现有结构，通过新增模块/文件扩展，不破坏已有学习路径
- **对称差跟踪**：每完成一个主题，同步更新对称差分析报告

---

## 二、分阶段任务规划

### Phase 1：高优先级缺口紧急填补（预计 2-3 周）

| # | 任务 | 具体内容 | 权威来源 |
|---|------|---------|---------|
| 1.1 | **Unsafe Rust 练习模块实现** | 将 `exercises/src/unsafe_rust/mod.rs`（当前仅 11 行 TODO）实现为完整的 5 道练习题：原始指针操作、FFI 边界安全、MaybeUninit 模式、UnsafeCell 内部可变性、Miri 验证 | The Rustonomicon、Miri 官方文档、PLDI 2025 Tree Borrows |
| 1.2 | **AI/ML 生态实战 crate** | 新建 `examples/ai_ml_ecosystem_demo.rs` 或扩展 `c08_algorithms`，实际调用 `candle-core`/`candle-nn` 完成：文本分类推理、图像识别（ONNX）、简单神经网络训练 | Hugging Face Candle 官方示例、Burn Book、tch-rs 文档 |
| 1.3 | **数据库交互 Hands-On 示例** | 新建 `examples/database_ecosystem_demo.rs`，使用 `sqlx` + `sea-orm` + `redis` 完成：连接池管理、迁移、CRUD、事务、缓存模式 | SeaORM 官方文档、SQLx 文档 |
| 1.4 | **过程宏真实 crate 拆分** | 将 `c11_macro_system` 中的过程宏从 `pub mod` 模拟改为真正的独立 `proc-macro = true` crate，展示跨 crate 开发、TokenStream 调试、`syn` + `quote` + `darling` 组合 | The Little Book of Rust Macros、syn/quote 官方文档 |
| 1.5 | **Lock-free 数据结构补全** | 补全 `c05_threads/src/lockfree/` 下的 5 个空壳模块（queue、stack、hazard_pointers、memory_management、priority_queue），引用 Crossbeam 实现 | Crossbeam 源码、1024cores.net |

### Phase 2：Rust 1.95+ 特性全面跟踪与更新（预计 2-3 周）

| # | 任务 | 具体内容 | 权威来源 |
|---|------|---------|---------|
| 2.1 | **Rust 1.86-1.95 特性索引补全** | 为每个 crate 新增/更新 `rust_186_features.rs` 到 `rust_195_features.rs`，覆盖：Trait 对象 upcasting、裸函数、Let chains、`cfg_select!`、if let guards、match 中 let chains | blog.rust-lang.org 各版本发布说明 |
| 2.2 | **Rust 2024 Edition 深度迁移指南更新** | 更新 `knowledge/06_ecosystem/edition_2024.md`，补充 `cargo fix --edition` 实战案例、Resolver v3 详解、Workspace 级迁移策略 | Edition Guide、The Rust Programming Language (2024 Ed) |
| 2.3 | **异步闭包（Async Closures）深度文档** | 新建 `docs/03_guides/ASYNC_CLOSURES_DEEP_DIVE.md`，覆盖 `AsyncFn` trait 家族、`async \|x\| {}` 语法、与 `async move` 闭包的区别、在 Axum/Tokio 中的实战 | RFC 3668、Rust 1.85 发布说明 |
| 2.4 | **Let Chains 全面教程** | 新建/更新 `docs/03_guides/LET_CHAINS_GUIDE.md`，覆盖 `if`/`while`/`match` 中的 let chains、与早期返回模式对比、常见陷阱 | Rust 1.88 发布说明、RFC |
| 2.5 | **`use<..>` Precise Capturing 深度指南** | 在 `c02_type_system` 或 `c04_generic` 中新增模块，详解 `+ use<'lt>` 精确生命周期捕获、RPIT 捕获规则 2024 | RFC 3498 |

### Phase 3：生态系统前沿深度扩展（预计 3-4 周）

| # | 任务 | 具体内容 | 权威来源 |
|---|------|---------|---------|
| 3.1 | **Cargo Script / Frontmatter 指南** | 新建 `docs/03_guides/CARGO_SCRIPT_GUIDE.md`（如果尚无完整版），覆盖 `cargo +nightly -Zscript`、frontmatter 语法、单文件 Rust 脚本最佳实践 | Cargo 官方文档、Rust 1.96+ tracking |
| 3.2 | **WASM + AI 推理实战** | 在 `c12_wasm` 中新增 `wasm_ai_inference.rs`，使用 `tract-onnx` 或 `candle` 在浏览器中运行模型推理 | wasm-bindgen 文档、Candle WASM 示例 |
| 3.3 | **WASI Preview 2 / Component Model 更新** | 更新 `c12_wasm` 的 WASI 内容，补充 wit-bindgen 实战、jco 工具链、组件组合 | WASI 官方规范、Bytecode Alliance 博客 |
| 3.4 | **GUI 生态入门示例** | 新建 `examples/gui_ecosystem_demo.rs`，选择 `egui` 或 `iced` 实现一个跨平台桌面应用（计算器或 TODO） | egui/iced 官方示例 |
| 3.5 | **安全/密码学基础模块** | 新建 `examples/security_cryptography_demo.rs`，使用 `ring` + `rustls` 演示 TLS 握手、证书验证、AEAD 加密 | Rustls 文档、Ring 文档 |
| 3.6 | **Rust for Linux / eBPF 实战扩展** | 将 `c07_process/src/ebpf_aya.rs` 从占位扩展为可运行的 Aya 程序骨架；补充 Rust for Linux 内核模块开发流程 | Rust for Linux 官方文档、Aya Book |
| 3.7 | **Embassy 异步嵌入式框架深度指南** | 扩展 `c13_embedded` 的 Embassy 预研模块，增加：任务调度、HAL 抽象、Bluetooth 示例、与 Tokio 的架构对比 | Embassy 官方文档、Rust Embedded Book |

### Phase 4：学术权威与生产实践对齐（预计 2-3 周）

| # | 任务 | 具体内容 | 权威来源 |
|---|------|---------|---------|
| 4.1 | **Tree Borrows 2025 更新** | 更新 `content/academic/tree_borrows/` 系列，对齐 PLDI 2025 Distinguished Paper 最新成果，更新 Miri 验证示例 | PLDI 2025 论文、Tree Borrows 官方文档 |
| 4.2 | **Safety Tags / Unsafe Rust 前沿跟踪** | 新建 `content/emerging/safety_tags_preparation.md`，跟踪 2026 RFC 进展、Unsafe Rust 形式化验证新方向 | Inside Rust 博客、形式化验证社区 |
| 4.3 | **Rust 1.97+ / Edition 2026 前瞻** | 新建 `content/emerging/rust_197_edition_2026_preview.md`，跟踪：`build-std` 稳定化、异步 Drop、Polonius、Never Type 进展 | Rust Internals 论坛、Nightly 跟踪 |
| 4.4 | **性能优化与测试方法论升级** | 新建/更新 `docs/03_guides/PROPERTY_BASED_TESTING.md`（proptest）、`SNAPSHOT_TESTING_GUIDE.md`，扩展 `content/production/performance_tuning.md` | proptest 文档、insta 文档、RustConf 2025 性能演讲 |
| 4.5 | **AI 辅助 Rust 编程指南 2026 修订** | 更新 `guides/AI_ASSISTED_RUST_PROGRAMMING_GUIDE_2026.md`，纳入 Rust 1.95+ 特性提示词模板、LLM 辅助 Miri 调试 | 项目内现有指南、最新 LLM 研究 |

### Phase 5：工程质量与一致性保障（贯穿全程）

| # | 任务 | 具体内容 |
|---|------|---------|
| 5.1 | **Workspace `static mut` 全面清理** | 按 `STATIC_MUT_AUDIT_2026_05_07.md` 报告，将源码级 9 处 + 文档级 12 处 `static mut` 迁移至 `Atomic*`/`OnceLock`/`Cell` |
| 5.2 | **全 Workspace Miri 验证** | 对新增 unsafe 代码运行 `cargo miri test`，确保内存安全 |
| 5.3 | **Clippy 零警告保持** | 每次修改后执行 `cargo clippy --all-targets --all-features`，保持 0 errors, 0 warnings |
| 5.4 | **对称差分析报告更新** | 更新 `reports/RUST_195_EVOLUTION_SYMMETRIC_DIFFERENCE_ANALYSIS_*.md`，记录本次对齐后的差距变化 |
| 5.5 | **知识库 INDEX.md 更新** | 更新 `knowledge/INDEX.md`，将新增内容纳入 7 层知识体系 |

---

## 三、预期产出物清单

| 类别 | 数量 | 说明 |
|------|------|------|
| 新增/重写源文件 | ~25-30 个 | 分散在 c05, c07, c08, c11, c12, c13, exercises 等 |
| 新增指南文档 | ~8-10 篇 | docs/03_guides/ 和 content/emerging/ 下 |
| 新增示例文件 | ~4-6 个 | examples/ 目录下 |
| 更新现有文件 | ~15-20 个 | 版本特性跟踪、Edition 指南、WASI 内容等 |
| 新增测试 | ~100+ 个 | 覆盖所有新增代码模块 |
| 更新报告 | 3-5 份 | 对称差分析、静态审计、完成度报告 |

---

## 四、关键里程碑

- **M1（第 2 周末）**：Phase 1 完成，unsafe 练习、AI/ML demo、数据库 demo、proc-macro crate 可运行
- **M2（第 4 周末）**：Phase 2 完成，Rust 1.86-1.95 特性索引 100% 覆盖，Async Closures 深度指南发布
- **M3（第 7 周末）**：Phase 3 完成，WASM+AI、GUI、安全密码学、Rust for Linux/eBPF、Embassy 深度内容就绪
- **M4（第 9 周末）**：Phase 4 完成，学术权威对齐、2026 前瞻、测试方法论升级
- **M5（第 10 周末）**：Phase 5 收尾，全项目 Miri + Clippy 验证通过，所有报告更新完毕

---

## 五、需要确认的关键问题

在执行之前，请确认以下几点：

1. **计划范围确认**：上述 5 个 Phase、约 20+ 个任务是否符合预期？是否有需要**删减**或**追加**的主题？
2. **执行策略选择**：
   - **选项 A（推荐）**：按 Phase 顺序逐步执行，每完成一个 Phase 汇报进度，可随时调整优先级
   - **选项 B**：仅执行 Phase 1（高优先级缺口），其他 Phase 视后续需求决定
   - **选项 C**：一次性全面执行所有 Phase，最后统一汇报
3. **AI/ML 方向侧重**：项目中 AI/ML 当前几乎是空白。希望重点补充哪个方向？
   - Candle（Hugging Face，轻量推理）
   - Burn（Rust 原生深度学习）
   - Polars（数据处理/DataFrame）
   - 还是三者都覆盖？
4. **GUI 框架选择**：如果补充 GUI 示例，偏好：
   - egui（即时模式，游戏/工具类）
   - iced（Elm 架构，应用类）
   - Tauri（Web 技术栈桌面应用）
   - 还是多个都覆盖？
5. **嵌入式方向侧重**：Embassy vs RTIC，是否需要 hands-on 级别的代码（由于 Host 环境限制，可能以模拟/文档为主）？

---

*本计划保存于 `reports/RUST_CONTENT_ALIGNMENT_PLAN_2026.md`，可随时修改调整。*
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
