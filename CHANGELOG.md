# 更新日志 (Changelog)

> **最后更新**: 2026-05-07

---

## [1.3.0] - 2026-05-08

### 🚀 模块深度扩展（13 个 crate）

- **c13_embedded/rtic_framework.rs**: 新增 RTIC vs Embassy 决策矩阵、RTIC 2.x async 任务支持、工业温度控制器架构、中断延迟分析（100-200ns vs FreeRTOS 1-5μs）
- **c07_process/rust_for_linux_preview.rs**: 新增内核同步原语（SpinLock/Mutex/RwLock/RCU）、工作队列（Workqueue）、GFP 标志详解、Slab 分配器、GPIO LED 驱动骨架、Rust vs C 驱动对比
- **guides/**: 新建 `AI_ASSISTED_RUST_PROGRAMMING_GUIDE_2026.md`（7.4KB），新增 if let guards / cfg_select! / Atomic::update / use<..> / async closures 专项提示词模板；2025 版标记为归档
- **c12_wasm**: 新建 `component_model.rs`，覆盖 WASI Preview 2 组件模型、wit-bindgen、wasm-tools、wasmtime、jco；22 个新测试
- **c11_macro_system**: 新建 `compile_time_metaprogramming.rs`，覆盖 const fn 元编程、宏与 const 协同、tt muncher 递归宏模式；16 个新测试
- **c05_threads**: 新建 `thread_pool_patterns.rs`，覆盖线程池设计、工作窃取（Chase-Lev deque）、scoped threads 深入、无锁数据结构概念（Treiber 栈 / Michael-Scott 队列）；27 个新测试
- **c03_control_fn**: 新建 `if_let_guards_deep_dive.rs`，15 个测试，全部可运行代码示例
- **c04_generic**: 新建 `generic_advanced_patterns.rs`，覆盖 GAT 深入（LendingIterator）、HRTB 模式、类型族（Type Families）、泛型特化概念；21 个新测试
- **c09_design_pattern**: 新建 `rust_idioms.rs`，覆盖类型状态模式、新类型模式、访者模式（枚举 vs trait object）、RAII ScopeGuard、内部可变性决策树；15 个新测试
- **c01_ownership_borrow_scope**: 新建 `pin_and_self_referential.rs`，覆盖 Pin/Unpin/PhantomPinned、自引用结构安全 workaround、Pin Projection、所有权决策树（Cow/Rc/Arc）；22 个新测试
- **c02_type_system**: 新建 `type_system_frontier.rs`，覆盖 Never Type (!)、TAIT 概念、RPITIT/AFIT 实战、Auto Traits 深入、Coherence/Orphan Rules；28 个新测试
- **c08_algorithms**: 新建 `algorithm_decision_trees.rs`，覆盖排序/搜索/图/DP/并发算法选择决策树；22 个新测试
- **exercises**: 新建 `rust_195_feature_exercises.rs`，13 个 1.95 特性专项练习（if let guards、cfg_select!、Atomic::update、push_mut、cold_path）

### 📚 内容中心扩展

- **content/emerging/rust_1_95_preview.md**: 完全重写为 1.95 稳定特性全景（9.4KB），含语言特性、标准库 API、迁移指南、项目内示例索引
- **content/ecosystem/async_runtimes/tokio_deep_dive.md**: 新建 Tokio 运行时深度解析（8.1KB）
- **content/academic/tree_borrows_guide.md**: 新建 Tree Borrows 权威指南（6.2KB），含权限树、状态机、SB 对比、Miri 用法
- **content/production/kubernetes_deployment_guide.md**: 新建 K8s 部署指南（6.8KB），含 Dockerfile、Deployment、HPA、安全最佳实践
- **content/README.md**: 更新统计（11 文档 / 83+ 示例 / 65% 完成度）

### 🔧 工程修复

- 修复 c06_async `unused_features` 警告（移除 `async_fn_traits` feature 声明）
- 修复 c10_networks `items_after_test_module` clippy 警告（移动 `mod tests` 到文件末尾）
- 全 workspace `cargo clippy` 通过，0 errors 0 warnings

### 🏗️ Common Crate 扩展

- **arena 模块**: 新增 `Arena<T>` 类型安全分配器 + `Handle<T>` 索引句柄，支持嵌套数据结构，7 个测试
- **traits 模块**: 新增 `Comparable` trait（范围检查），`Serializable` trait（serde feature 下）
- **types 模块**: 新增 `Id<T>` 新类型（编译期 ID 类型安全）、`NonEmptyVec<T>`（保证非空的 Vec 包装）
- **工程修复**: `default-features` 加入 `error-trait` + `async`，解决单独编译 common 的依赖问题

### 📚 Content 中心扩充

- **content/ecosystem/database/sea_orm_deep_dive.md**: Sea-ORM 深度解析（7.2KB）
- **content/ecosystem/error_handling/anyhow_vs_thiserror.md**: anyhow/thiserror/miette 对比指南（5.3KB）
- **content/ecosystem/web_frameworks/actix_web_vs_axum.md**: Actix-web vs Axum 决策指南（4.0KB）
- **content/ecosystem/web_frameworks/grpc_microservices_guide.md**: gRPC + Tonic 微服务指南（6.7KB）
- **content/production/observability_guide.md**: 可观测性三大支柱实战指南（8.3KB）
- **content/production/security_best_practices.md**: Rust 生产安全最佳实践（6.0KB）
- **content/emerging/gen_blocks_guide.md**: `gen` blocks / `yield` 表达式前瞻指南（4.2KB）
- **content/emerging/wasm_advanced_topics.md**: WASM 高级主题（11KB）
- **content/academic/prusti_verification_tutorial.md**: Prusti 形式化验证教程（6.4KB）
- **content/production/serverless_deployment_guide.md**: Serverless 部署指南（10KB）
- **content/ecosystem/flutter_rust_bridge.md**: Flutter + Rust 跨平台指南（10KB）
- **content/ecosystem/serialization/serde_best_practices.md**: Serde 最佳实践（5.6KB）
- **content/README.md**: 统计更新至 23 文档 / 145+ 示例 / 82% 完成度
- **content/ecosystem/README.md**: 更新链接、日期、完成度标记

### 📚 Docs 文档更新

- `docs/01_learning/LEARNING_PATH_PLANNING.md`: 添加本轮新增模块学习路径指引
- `docs/05_guides/ASYNC_PROGRAMMING_USAGE_GUIDE.md`: 补充 async closures、`cfg_select!` 内容

### 🏗️ Crate 代码深化

- **c01**: 新增 `AsyncStateMachineConcept` — 解释 Pin 在 async/await 状态机中的核心作用
- **c02**: 新增 `TypeFamilyDemo` — 类型族（Type Families）实际代码演示，含 `ListFamily` / `TreeFamily`
- **c03**: 新增 `control_flow_patterns.rs` — match 高级模式、let chain、loop 标签（12 个测试）
- **c04**: 新增 `type_state_machine.rs` — HTTP 构建器和文件句柄的类型状态模式（8 个测试）
- **c08**: 新增 `AlgorithmSkeletons` — 二分查找、快速排序、BFS 的可运行骨架实现（3 个测试）
- **c09**: 新增 `functional_patterns.rs` — 高阶函数、迭代器管道、Monoid、组合子（11 个测试）

### 🏗️ Common Crate 扩展（续）

- **utils 模块**: 新增 `retry()` 同步重试函数、`Memoize<T, R>` 单值缓存结构
- **lib.rs re-export**: 更新所有新类型的公开导出

### ✅ 测试覆盖

- 全 workspace 测试通过: **2000+ tests**，0 failures

---

## [1.2.0] - 2026-05-07

### 🚀 Rust 1.95 特性补全

- **c12_wasm**: 完全重写 `rust_195_features.rs`，从纯文档升级为 760 行可执行代码，覆盖：
  - `cfg_select!` — 编译时 WASI p1/p2、浏览器或原生平台选择
  - `bool::TryFrom<{integer}>` — FFI 边界整数标志安全转布尔
  - `core::hint::cold_path` — WASM 错误路径分支预测优化
  - `if let` guards — `match` 表达式中的模式守卫
  - `core::range::RangeInclusive` — 端口范围与内存页范围验证
  - `ControlFlow::is_break` / `is_continue` (const) — 编译期评估的提前退出
- **c02_type_system**: 新增 Collection Mutable Methods 章节（`Vec::push_mut`、`VecDeque::*_mut`、`LinkedList::*_mut`）
- **c01_ownership_borrow_scope**: 新增 Layout Helpers 章节（`dangling_ptr`、`repeat`、`repeat_packed`、`extend_packed`）
- **assert_matches! 推广**: 在 5 个 crate 中替换 10 处 `assert!(matches!(...))` 为 `assert_matches!`

### 🌐 网络生态对齐

- **c10_networks/quic_advanced.rs**: 新增 Datagram（不可靠传输）、0-RTT、Connection Migration 三大高级特性模块，含配置结构体与 API 类型签名验证
- **c10_networks/libp2p_advanced.rs**: 新增 Relay v2、AutoNAT、DCUtR 三大 NAT 穿透模块；更新 libp2p feature flags
- **c06_async**: 新增 tokio `task::Builder` 演示（命名任务、tokio-console 可观测性）

### 🔮 Rust 1.96+ 特性跟踪

- **c13_embedded**: 新建 `rust_196_features.rs`，实现：
  - `core::pin::pin!` — 无 alloc 环境下的栈上固定
  - `const VecDeque::new` — 常量初始化环形缓冲区
  - `From<bool> for f32/f64` — 布尔传感器数据到浮点转换
  - `NonNull::new` const 支持 — 裸指针常量初始化
- **c07_process**: 新增 `pin!`、`const VecDeque`、`MAIN_SEPARATOR_STR`、`DerefMut for PathBuf` 演示

### 🔧 工程改进

- 修复 c08 模块 `std::range` → `core::range` 路径错误
- 移除 5 个未使用的依赖（c01 serde/serde_json、c03 serde_json、c04 array-init、c05 flume）
- 重构 c10_networks `build.rs`，使用 `protoc_executable()` API 替代 `unsafe` 块
- 修复 6 处 rustdoc HTML/链接警告
- 修复 c07_process `EnhancedConnection` 枚举 clippy 警告（`Box<NamedPipeConnection>`）
- Windows CI: `--all-features` 改为 `--features tls,quic,libp2p`，避免 pcap 链接失败

### ✅ 测试覆盖

- **quic_advanced.rs**: 新增 13 个测试
- **libp2p_advanced.rs**: 新增 14 个测试

---

## [1.1.0] - 2026-04-10

### 🚀 Rust 1.96 迁移完成

- ✅ Rust 版本升级: 1.94.0 → 1.96.0
- ✅ 支持 Rust 1.95/1.96 特性（含版本勘误修正）
- ✅ 工具链配置更新
- ✅ 所有 crates 兼容性验证通过

### 主要变更

- 更新 `rust-toolchain.toml` 到 1.96.0
- 更新 CI/CD 配置支持 Rust 1.96
- 文档版本号统一更新
- 迁移指南文档更新

---

## [1.0.0] - 2026-03-08

### 🎉 正式发布

- ✅ 项目达到 100% 完成度
- ✅ 全面支持 Rust 1.94.0
- ✅ 12 个学习模块全部完成
- ✅ 20+ 速查卡覆盖所有核心主题

### 新增内容

- 新增 Rust 1.94.0 特性支持
- 新增 AI/ML 相关速查卡
- 新增形式化方法文档
- 新增设计模式完整指南

### 修复

- 修复大量文档断链
- 优化代码示例
- 完善测试覆盖

---

## [0.9.0] - 2026-02-28

### 主要更新

- 研究笔记系统 100% 完成
- 文档完善度达到 100%
- 新增 17 个研究笔记
- 形式化方法文档完善

---

## [0.8.0] - 2025-12-11

### 主要更新

- 所有 crates 文档标准化
- 新增性能优化指南
- 新增异步编程完整指南
- 新增网络编程速查卡

---

## [0.7.0] - 2025-11-15

### 主要更新

- 文档体系全面标准化
- 建立文档标准规范
- 完成文档梳理报告

---

## [0.6.0] - 2025-10-30

### 主要更新

- mdBook 在线文档平台上线
- 新增项目完成状态报告
- 完善跨模块文档

---

## [0.5.0] - 2025-10-24

### 主要更新

- 项目完成度达到 93%
- 新增最终真实评估报告
- 新增学习路径指南
- C02 模块达到 100% 完成

---

## [0.4.0] - 2025-10-20

### 主要更新

- 全模块文档增强
- 新增 57 篇核心增强文档
- 新增知识图谱和思维导图
- 新增 255+ 技术对比矩阵

---

## [0.3.0] - 2025-01-26

### 主要更新

- 文档完善度达到 91%
- 研究笔记系统完成
- 新增交叉引用指南

---

## [0.2.0] - 2024-12-11

### 主要更新

- 新增多个实用指南
- 完善测试用例
- 优化项目结构

---

## [0.1.0] - 2024-10-01

### 初始版本

- 项目启动
- 基础模块搭建
- 核心文档创建

---

## 相关文档

- [README.md](./README.md)
- [ROADMAP.md](./ROADMAP.md)
- [CONTRIBUTING.md](./CONTRIBUTING.md)
