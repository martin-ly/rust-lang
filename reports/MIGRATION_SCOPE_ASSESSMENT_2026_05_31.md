> **⚠️ 历史文档提示**：
>
> 本文档包含 `async-std`、`wasm32-wasi` 等已归档或已重命名的生态引用。
> 其中技术观点反映了对应时间点的社区状态，可能与当前（Rust 1.96+）推荐实践不一致。
> 学习时请以 `concept/`、`knowledge/` 及官方文档为准。
>
> - `async-std` 已进入维护模式，新项目建议优先考虑 Tokio / smol。
> - `wasm32-wasi` 已重命名为 `wasm32-wasip1`；WASI Preview 2 目标为 `wasm32-wasip2`。

---

# 迁移范围评估报告

> **评估日期**: 2026-05-31
> **评估项**: async-std 移除 / wasm32-wasi 迁移 / async_trait (Axum 0.8) 清理
> **执行方式**: 自动化扫描 + 人工分类

---

## 任务 1: async-std 移除评估

### 关键发现

- **无真实代码依赖**: 全局搜索 `async_std::` 仅在归档对照表中有 6 处，没有任何 crate 真实依赖 async-std 运行时或调用其 API
- **工作区 Cargo.toml 中 async-std 已移除**（注释状态）

### 代码依赖（需改 Cargo.toml / .rs）

| 文件 | 当前内容摘要 | 修改建议 | 优先级 |
|---|---|---|---|
| `crates/c06_async/src/lib.rs:255` | `// async-std 运行时（已归档...）` + `mod async_std` 引用 | 更新注释，将 `async_std` mod 重命名为 `async_std_archive` 或彻底移除 | 中 |
| `crates/c06_async/src/async_std/mod.rs` | 完整的 async-std 归档对照表（6 处 `async-std`/`async_std`） | 保留归档性质，更新标题为 `async-std 历史归档（已移除）` | 低 |
| `crates/c06_async/examples/async_ecosystem_final_demo.rs` | `println!("...CLI工具 (推荐: async-std 或 smol)")` 等 | 改为推荐 tokio 或 smol | 中 |
| `crates/c06_async/examples/comprehensive_async_ecosystem_demo.rs` | 同上，两处 `推荐运行时: async-std 或 smol` | 改为推荐 tokio 或 smol | 中 |
| `crates/c06_async/examples/rust_async_ecosystem_comprehensive_demo.rs` | 模拟 `async-std` 性能数据、标准库风格 API 演示 | 标注为历史参考，改为 tokio 示例或保留归档说明 | 低 |
| `crates/c06_async/src/async_runtime_examples.rs` | `"easy_development" => "async-std"` 等模拟映射 | 更新映射为 tokio | 低 |
| `crates/c06_async/src/async_runtime_examples_fixed.rs` | 同上 | 更新映射为 tokio | 低 |
| `crates/c06_async/src/async_ecosystem_comprehensive.rs` | `async-std` 字符串用于运行时分析数据结构 | 标注为历史参考，无需改逻辑 | 低 |
| `crates/c06_async/src/async_integration_framework.rs` | `PerformanceProfile` 中 `async-std` 模拟数据 | 标注为历史参考 | 低 |
| `crates/c06_async/benches/async_ecosystem_performance_benchmarks.rs` | `("async-std", AsyncRuntimeType::AsyncStd)` 基准测试标签 | 移除 async-std 分支或标注为历史 | 低 |
| `crates/c06_async/src/actor_reactor_patterns.rs` | 表格注释 `tokio, async-std, smol` | 改为 `tokio, smol` 或标注历史 | 低 |

### 文档引用（需改 .md）

| 文件 | 当前内容摘要 | 修改类型 | 修改建议 | 优先级 |
|---|---|---|---|---|
| `content/ecosystem/async_runtimes/tokio_deep_dive.md` | 对比表 `Tokio \| async-std \| smol \| embassy` + 决策树分支 `async-std` | a) 介绍为可选 | 对比表增加"不推荐"标注；决策树分支改为指向 tokio | 中 |
| `concept/06_ecosystem/01_toolchain.md:494` | `tokio` vs `async-std` 后端 feature | a) 介绍为可选 | 改为 `tokio` 单一后端，标注 async-std 已移除 | 低 |
| `concept/06_ecosystem/04_application_domains.md:878` | 运行时选择 `Tokio vs async-std` | b) 推荐使用 | 改为推荐 tokio，标注 async-std 已归档 | 低 |
| `concept/03_advanced/18_network_programming.md:773` | `async_std::net::TcpStream` 作为异步网络示例 | c) 代码示例 | 改为 `tokio::net::TcpStream` | 中 |
| `concept/05_comparative/05_execution_model_isomorphism.md` | 多处 `tokio / async-std` 对比 | a) 介绍为可选 | 改为 `tokio / smol`，标注 async-std 历史 | 低 |
| `concept/05_comparative/11_rust_vs_kotlin.md` | `运行时可选（Tokio、async-std）` | b) 推荐使用 | 改为 `Tokio（推荐）、smol` | 低 |
| `concept/05_comparative/13_rust_vs_csharp.md` | `Tokio/async-std 选择` | b) 推荐使用 | 改为 tokio | 低 |
| `concept/05_comparative/15_rust_vs_typescript.md` | `显式（Tokio/async-std）` | b) 推荐使用 | 改为 tokio | 低 |
| `concept/06_ecosystem/README.md:40` | `异步运行时[Tokio / async-std]` | b) 推荐使用 | 改为 `Tokio` | 低 |
| `concept/00_meta/asp_marking_guide.md` 等元文档 | 多处已标注 `Tokio（async-std 已于 2025-03 停止维护）` | — | **无需修改**，已正确标注 | — |
| `concept/archive/03_advanced_02_async_original.md` | 归档原文，含 async-std 对比 | — | 归档文档，保留原样 | 低 |

### 汇总

- 高优先级文件数: 0（无真实代码依赖）
- 中优先级文件数: 7（示例推荐语、Axum 相关文档、网络编程文档）
- 低优先级文件数: 18（历史参考代码、归档文档、元数据注释）
- **预估总工时: 4-6 小时**

---

## 任务 2: wasm32-wasi 目标迁移评估

### 关键发现

- **项目已基本完成 wasm32-wasi → wasip1/wasip2 迁移**
- `grep "wasm32-wasi[^p]"` 在 `concept/`、`content/`、`.md` 文档中**零命中**
- 仅剩历史说明性引用（迁移指南中的对照表）

### 代码依赖

| 文件 | 当前内容摘要 | 修改建议 | 优先级 |
|---|---|---|---|
| `crates/c12_wasm/src/wasi_migration.rs` | 文件标题"从 wasm32-wasi 到 wasm32-wasip1/p2"，含历史对照表 | **无需修改**。专门的迁移指南，保留旧名称作为历史对照是正确做法 | — |
| `crates/c12_wasm/examples/component_model_demo.rs:196` | `println!("    wasm32-wasi      →  wasm32-wasip1  (旧目标重命名)");` | **无需修改**。历史映射说明 | — |
| `crates/c12_wasm/examples/component_model_demo.rs:244` | `wasm32-wasip1  - WASI Preview 1 (legacy, renamed from wasm32-wasi)` | **无需修改**。历史说明 | — |

### wasip1 vs wasip2 分类评估

| 文件/场景 | 当前目标 | 建议 | 原因 |
|---|---|---|---|
| `05_wasi_file_processor.rs` / `08_container_microservice.rs` / `10_ai_inference_wasinn.rs` / `11_crypto_operations.rs` | `wasm32-wasip1` | **保持 wasip1** | 文件处理、简单容器、AI 推理、加密操作——模块级 WASI 即可 |
| `09_wasi_02_component_example.rs` / `component_model_demo.rs` | `wasm32-wasip2` | **保持 wasip2** | 组件模型示例，需要 WIT 接口和跨语言组合 |
| `wasi_migration.rs` / `component_model.rs` | 同时提及 wasip1 + wasip2 | **保持双目标** | 迁移指南需要覆盖两种场景 |

### 汇总

- 高优先级文件数: 0
- 中优先级文件数: 0
- 低优先级文件数: 1（确认迁移指南时效性）
- **预估总工时: 0.5 小时**

---

## 任务 3: async_trait (Axum 0.8 迁移) 评估

### 关键发现

- **代码侧**: c06_async 的 13 处 `#[async_trait]` 均为教学演示代码中的**动态分发场景**（`Box<dyn Trait>`），不是 Axum handler
- **Rust AFIDT（async fn in dyn Trait）稳定前，这些必须保留**
- **文档侧**: axum_deep_dive.md 中的 `#[async_trait]` 可移除（Axum 0.8+ 原生支持）

### 区分原则

- `#[async_trait]` 或 `#[async_trait::async_trait]`（无 crate 前缀）→ 属于 `async-trait` crate，Axum 0.8+ 静态分发场景可移除
- `#[tonic::async_trait]` → tonic 内部宏，**不可移除**
- `#[rocket::async_trait]` → rocket 内部宏，**不可移除**
- 涉及 `Box<dyn Trait>` / `&dyn Trait` 的 trait → Rust 1.75+ 原生不支持，**必须保留**到 AFIDT 稳定

### 代码依赖

| 文件 | 当前内容摘要 | 修改建议 | 优先级 |
|---|---|---|---|
| `Cargo.toml:249` | `async-trait = "0.1.89"`（workspace） | 保留。因 c06_async 仍需此依赖 | 低 |
| `crates/c06_async/Cargo.toml:34` | `async-trait = { workspace = true }` | **暂时保留**。13 处 `#[async_trait]` 全部涉及 `dyn Trait` 动态分发 | 低 |
| `crates/c06_async/src/async_runtime_integration_framework.rs` | 7 处 `#[async_trait]`：`AsyncTask`、`RuntimeAdapter`、`AsyncComponent` | **不可移除**。`Box<dyn AsyncTask>` 等，需等 AFIDT | — |
| `crates/c06_async/src/async_runtime_integration_framework_simple.rs` | 6 处 `#[async_trait]`，同上 | **不可移除**。同上 | — |
| `crates/c06_async/src/afit_dyn_tracking.rs:42` | 文档注释中的 `/// #[async_trait]` | 保留，AFIDT 迁移 tracker | 低 |
| `crates/c10_networks/Cargo.toml:23` | `# async-trait 已迁移至原生 AFIT (1.75+)` | 已是完成状态，无需修改 | — |
| `crates/c10_networks/src/protocol/async_traits.rs` | 原生 `async fn` in trait 示例，无 `#[async_trait]` | 无需修改 | — |

### 文档引用（需改 .md）

| 文件 | 当前内容摘要 | 可否移除 | 修改建议 | 优先级 |
|---|---|---|---|---|
| `content/ecosystem/web_frameworks/axum_deep_dive.md:225` | `#[async_trait] impl FromRequestParts<S> for ApiKey` | ✅ 可移除 | Axum 0.8+ `FromRequestParts` 已支持原生 `async fn` | 高 |
| `content/ecosystem/README.md:489` | `#[async_trait] impl DatabaseTrait for Database` | ✅ 可移除 | 通用示例 trait，静态分发，改原生 `async fn` | 中 |
| `concept/06_ecosystem/35_architecture_patterns.md` | 多处 `// 注意：Axum 0.8+...` + `#[async_trait]` | ✅ 可移除 | 更新示例代码，移除 `#[async_trait]`，保留注释 | 中 |
| `concept/06_ecosystem/33_cqrs_event_sourcing.md` | 多处 `#[async_trait]` 在 Axum handler / service trait 上 | ✅ 可移除 | Axum 相关示例改原生；若含 `dyn Trait` 则保留并加注释 | 中 |
| `concept/06_ecosystem/32_event_driven_architecture.md:193,227` | `#[async_trait::async_trait]` 在 EventHandler trait 上 | ⚠️ 需确认 | 若仅为静态分发示例，可移除；若涉及 `dyn EventHandler` 则保留 | 中 |
| `concept/06_ecosystem/41_workflow_theory.md` | 两处 `#[async_trait]` | ⚠️ 需确认 | 检查是否涉及 dyn Trait | 中 |
| `concept/06_ecosystem/42_api_design_patterns.md:625` | `#[async_trait::async_trait]` | ⚠️ 需确认 | 检查上下文 | 中 |
| `concept/06_ecosystem/48_data_engineering.md:372,377,382` | `#[async_trait::async_trait]` on `DataSource`/`Transform`/`DataSink` | ✅ 可移除 | 从代码看是静态分发 trait（无 `dyn`），改原生 | 中 |
| `content/ecosystem/database/sea_orm_deep_dive.md:218` | `#[async_trait::async_trait] impl MigratorTrait` | ❌ 必须保留 | Sea-ORM 的 `MigratorTrait` 仍由 sea-orm 定义 | 低 |
| `concept/06_ecosystem/18_distributed_systems.md:186` | `#[tonic::async_trait]` | ❌ 必须保留 | tonic 内部宏 | — |
| `concept/06_ecosystem/42_api_design_patterns.md:747,795` | `#[tonic::async_trait]` | ❌ 必须保留 | tonic 宏 | — |
| `content/ecosystem/web_frameworks/grpc_microservices_guide.md` | `#[tonic::async_trait]` | ❌ 必须保留 | tonic 宏 | — |
| `content/ecosystem/web_frameworks/rocket_guide.md:96,126` | `#[rocket::async_trait]` | ❌ 必须保留 | rocket 内部宏 | — |
| `concept/03_advanced/02_async.md` | 已标注 `// 注意：Axum 0.8+ 使用原生 AFIT` | — | **无需修改** | — |
| `concept/03_advanced/02_async_patterns.md` | 同上，已有更新注释 | — | **无需修改** | — |
| `concept/07_future/rust_1_97_preview.md` | 讨论 AFIDT 消除 `#[async_trait]` 需求 | — | **无需修改** | — |

### 汇总

- 高优先级文件数: 1（`axum_deep_dive.md`）
- 中优先级文件数: 8（概念文档中 Axum/通用 trait 示例、README 示例、数据工程示例）
- 低优先级文件数: 7（sea-orm 需确认、AFIDT tracker、已标注注释文档）
- **预估总工时: 6-10 小时**
  - 代码侧: c06_async 的 `#[async_trait]` 因 dyn Trait 限制**暂不能动**，需等 Rust 1.97+ AFIDT
  - 文档侧: 约 8-10 个 .md 文件需更新示例代码并验证语法正确性

---

## 总体评估

| 迁移项 | 状态 | 预估工时 | 关键阻塞 |
|:---|:---|:---:|:---|
| async-std 移除 | 🟡 文档清理中 | 4-6h | 无（已确认无代码依赖） |
| wasm32-wasi 迁移 | 🟢 基本完成 | 0.5h | 无 |
| async_trait 清理 | 🟡 文档可推进，代码待 AFIDT | 6-10h | AFIDT 预计 1.97-1.98 稳定 |

**建议执行顺序**:

1. **立即**: wasm32-wasi 确认（0.5h）
2. **本周**: async-std 文档清理（4-6h）
3. **1.97 发布后**: async_trait 代码侧清理（配合 AFIDT 稳定）
4. **持续**: 文档侧 async_trait 清理可与 async-std 并行
