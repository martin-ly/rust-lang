# Cargo 指南实践（Cargo Guide Practices）

> **内容分级**: [参考级]
> **本节关键术语**: Dependencies · Features · CI · Build Performance · Cache · `CARGO_TARGET_DIR` — [完整对照表](../../00_meta/01_terminology/terminology_glossary.md)
>
> **EN**: Cargo Guide Practices
> **Summary**: Cargo 指南中的实践主题：依赖管理、features、测试组织、持续集成配置，以及构建性能优化策略。 Practical topics from the Cargo Guide: dependency management, features, test organization, CI configuration, and build performance.
> **受众**: [进阶]
> **Bloom 层级**: 理解 → 应用
> **A/S/P 标记**: **P** — Practice
> **双维定位**: E×Tool — 工具链与生态系统
> **定位**: 把 Cargo 官方指南中散落在多章的“怎么做”聚合为一份实践速查。
> **前置概念**: [Cargo Workflow](81_cargo_workflow.md) · [Cargo Dependency Resolution](60_cargo_dependency_resolution.md) · [Testing Strategies](../09_testing_and_quality/12_testing_strategies.md)
> **后置概念**: [Cargo Configuration](83_cargo_configuration.md) · [DevOps and CI/CD](../00_toolchain/28_devops_and_ci_cd.md) · [Performance Optimization](../10_performance/15_performance_optimization.md)

---

> **来源**: [Cargo Book — Dependencies](https://doc.rust-lang.org/cargo/guide/dependencies.html) · · [Rust Reference](https://doc.rust-lang.org/reference/introduction.html) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
> [Cargo Book — Tests](https://doc.rust-lang.org/cargo/guide/tests.html) ·
> [Cargo Book — Continuous Integration](https://doc.rust-lang.org/cargo/guide/continuous-integration.html) ·
> [Cargo Book — Build Performance](https://doc.rust-lang.org/cargo/guide/build-cache.html)

---

## 一、依赖管理实践

### 添加依赖

```bash
cargo add serde --features derive
cargo add tokio --features full
```

### 版本语义

`Cargo.toml` 中使用 SemVer 范围：

| 写法 | 含义 |
|:---|:---|
| `1.2.3` | `^1.2.3`，兼容 1.x.x 且 ≥1.2.3 |
| `~1.2.3` | ≥1.2.3 且 <1.3.0 |
| `=1.2.3` | 精确锁定 |

### Features

```toml
[dependencies]
serde = { version = "1.0", features = ["derive"] }
```

- Features 是 Cargo 的**条件编译**机制之一。
- 默认 features 会自动启用，可通过 `default-features = false` 关闭。

## 二、测试组织

Cargo 自动识别四类测试：

| 类型 | 位置 | 运行方式 |
|:---|:---|:---|
| 单元测试 | 内联于 `src/*.rs` 的 `#[cfg(test)]` 模块（Module） | `cargo test` |
| 集成测试 | `tests/*.rs` | `cargo test --test <name>` |
| 文档测试 | `///` 示例代码 | `cargo test --doc` |
| 基准测试 | `benches/*.rs` | `cargo bench` |

## 三、持续集成

典型 CI 步骤：

```yaml
- cargo check
- cargo test
- cargo clippy -- -D warnings
- cargo fmt --check
- cargo doc --no-deps
```

## 四、构建性能优化

| 策略 | 说明 |
|:---|:---|
| 共享构建缓存 | 设置 `CARGO_TARGET_DIR` 或 sccache |
| 增量编译 | 默认开启，`cargo check` 优先 |
| 并行编译 | `cargo build -j<N>` 控制并行度 |
| 减少依赖 | 审计并移除不必要依赖 |
| Profile 调优 | 见 [Cargo Profiles and Lints](65_cargo_profiles_and_lints.md) |

---

> **权威来源**: [Cargo Book — Guide](https://doc.rust-lang.org/cargo/guide/index.html)
> **内容分级**: [参考级]
