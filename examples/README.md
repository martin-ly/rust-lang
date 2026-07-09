# 根级综合示例

> **说明**: 本目录包含跨模块综合示例，**非 Cargo workspace 成员**。

## 用途

这些 `.rs` 文件展示多模块协同用法，可作为参考代码学习。由于不在 workspace 中，大部分文件可通过 `rustc` 直接编译，部分文件需要外部依赖。

## 使用方式

1. **直接编译** - 大部分文件支持 `rustc --edition 2024 --crate-type bin <file.rs>`
2. **复制到 Rust Playground** - 将代码复制到 [play.rust-lang.org](https://play.rust-lang.org/) 运行
3. **作为参考** - 阅读代码理解跨模块集成模式
4. **集成到项目** - 可将所需片段复制到你的 crate 中

## 文件说明

### 标准 Rust（直接编译）

| 文件 | 内容 |
| :--- | :--- |
| `advanced_usage_examples.rs` | 高级所有权、Arc/Rc、Barrier 并发示例 |
| `comprehensive_integration_example.rs` | 综合多模块集成示例（所有权+并发+算法+网络） |
| `concurrent_data_structures.rs` | 并发数据结构用法示例 |
| `module_complete_examples.rs` | 12 个核心模块完整用法速览 |
| `real_world_applications.rs` | 实际应用场景示例（Web、数据处理、配置管理） |
| `rust_194_array_windows_demo.rs` | Rust 1.94 `array_windows` 新特性演示 |
| `rust_194_control_flow_demo.rs` | Rust 1.94 `ControlFlow` 与 `Ordering` 新 API |
| `rust_194_lazy_lock_demo.rs` | Rust 1.94 `LazyLock::get()` 热路径优化 |
| `rust_194_lazylock_patterns.rs` | `LazyLock` 常见设计模式 |

### 需要外部依赖

| 文件 | 内容 | 依赖 |
| :--- | :--- | :--- |
| `comprehensive_web_server.rs` | 综合 Web 服务器示例 | `tokio` |
| `microservice_template.rs` | 微服务模板（Axum + Tower） | `tokio`, `axum` |
| `rust_194_controlflow_patterns.rs` | 控制流异步模式 | `tokio` |

> 运行方式：创建独立 Cargo 项目，添加对应依赖后执行。

### Cargo Script 格式

| 文件 | 内容 | 运行方式 |
| :--- | :--- | :--- |
| `cargo_script_demo.rs` | Cargo Script 单文件脚本演示 | `cargo +nightly -Zscript cargo_script_demo.rs` |

## 独立 Cargo 示例

| 目录 | 内容 | 运行方式 |
| :--- | :--- | :--- |
| `build_script_practice/` | build script 与外部 C 代码链接练习 | `cd build_script_practice && cargo build` |
| `incremental_practice/` | 观测 rustc 增量编译的 dep-graph 与 Red-Green 复用 | `cd incremental_practice && cargo test` |
| `resolver_v3_practice/` | resolver v3 与 MSRV 感知依赖解析实践 | `cd resolver_v3_practice && cargo tree` |

## 可运行示例

各模块的 `crates/*/examples/` 为 workspace 内可运行示例，使用以下命令运行：

```bash
cargo run -p c01_ownership_borrow_scope --example <example_name>
cargo run -p c06_async --example async_basic
# 等等
```

查看 [PROJECT_STRUCTURE.md](../PROJECT_STRUCTURE.md) 了解完整项目结构

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [Authority Source Sprint Batch 8](../concept/00_meta/02_sources/international_authority_index.md)

**文档版本**: 1.2
**对应 Rust 版本**: 1.97.0+ (Edition 2024)
**最后更新**: 2026-06-01
**状态**: ✅ 示例目录编译清理完成
