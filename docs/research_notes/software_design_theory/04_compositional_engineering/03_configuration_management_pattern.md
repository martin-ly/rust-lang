# 配置管理模式（Configuration Management Pattern） {#配置管理模式configuration-management-pattern}

> **概念族**: 软件设计 / 组合工程 / 配置管理
>
> **内容分级**: [核心级]
>
> **分级**: [A]
>
> **Bloom 层级**: L3-L5 (应用/分析/评价)
>
> **创建日期**: 2026-06-29
>
> **最后更新**: 2026-06-29
>
> **Rust 版本**: 1.96.0+ (Edition 2024)
>
> **状态**: ✅ 已完成
>
> **权威来源**:
>
> [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/) |
> [Cargo Book – Environment Variables](https://doc.rust-lang.org/cargo/reference/environment-variables.html) |
> [The Rust Programming Language](https://doc.rust-lang.org/book/) |
> [Rust Design Patterns](https://rust-unofficial.github.io/patterns/) |
> [config crate docs](https://docs.rs/config/latest/config/) |
> [clap docs](https://docs.rs/clap/latest/clap/) |
> [envy docs](https://docs.rs/envy/latest/envy/) |
> [figment docs](https://docs.rs/figment/latest/figment/)
>

---

## 📑 目录 {#目录}

- [配置管理模式（Configuration Management Pattern）](#配置管理模式configuration-management-pattern)
  - [📑 目录](#目录)
  - [概述](#概述)
  - [配置分层模型](#配置分层模型)
  - [Rust 配置 crate 选型](#rust-配置-crate-选型)
  - [Rust 实现方案](#rust-实现方案)
  - [完整代码示例](#完整代码示例)
  - [反例边界](#反例边界)
    - [1. 敏感信息泄露](#1-敏感信息泄露)
    - [2. 配置热加载竞态](#2-配置热加载竞态)
    - [3. 类型不匹配](#3-类型不匹配)
    - [4. 配置缺失未处理](#4-配置缺失未处理)
  - [权威来源索引](#权威来源索引)
  - [相关概念](#相关概念)

---

## 概述 {#概述}

> **来源**: [Rust Design Patterns](https://rust-unofficial.github.io/patterns/)

配置管理是组合工程在**运行期参数维度**的延伸：将应用程序的行为参数从代码中解耦，通过可组合、可覆盖的来源（CLI 参数、环境变量、配置文件、默认值）构建出最终生效配置。良好的配置管理需要满足：

1. **分层覆盖**：后加载来源覆盖先加载来源，形成稳定的优先级。
2. **类型安全**：配置值在编译期有类型，运行期通过 `serde` 反序列化。
3. **失败隔离**：配置缺失、格式错误、环境变量未设置等失败点必须显式处理。
4. **敏感信息保护**：密钥、令牌等不应写入版本控制或日志。

---

## 配置分层模型 {#配置分层模型}

> **来源**: [12-Factor App – Config](https://12factor.net/config)

典型配置来源按优先级从低到高排列：

| 层级 | 来源 | 典型用途 | 覆盖能力 |
|------|------|----------|----------|
| L1 | 硬编码默认值 | 保证程序在没有外部输入时仍可启动 | 最低 |
| L2 | 配置文件（TOML/JSON/YAML） | 环境相关配置（开发、测试、生产） | 中 |
| L3 | 环境变量 | 容器化部署、CI/CD、敏感参数注入 | 高 |
| L4 | CLI 参数 | 一次性调试、脚本调用 | 最高 |

> **原则**：代码只负责声明“需要什么配置”，而具体取值交给外部来源；同一键在高层出现时无条件覆盖低层。

---

## Rust 配置 crate 选型 {#rust-配置-crate-选型}

> **来源**: [crates.io](https://crates.io/)

| crate | 核心能力 | 适用场景 | 版本参考 |
|-------|----------|----------|----------|
| `config` | 多来源分层合并（文件、环境变量、字符串、默认值），支持热加载 | 通用服务端/工具配置 | `0.15` |
| `clap` | 声明式命令行参数解析，可派生 `Parser` | CLI 入口参数 | `4.x` |
| `envy` | 将环境变量直接反序列化到 `serde` 结构体 | 纯环境变量驱动的服务 | `0.4` |
| `figment` | 基于配置 Profile 的组合，支持 Provider 扩展 | 需要复杂配置组合（如 Rocket） | `0.10` |

- **`config`** 是“分层配置”的首选：默认 → 文件 → 环境变量 → 手动覆盖，代码简洁且优先级明确。
- **`clap`** 负责 CLI 层，常与 `config` 组合：先用 `clap` 解析命令行，再将解析结果作为最高优先级来源加入 `config`。
- **`envy`** 适合 12-Factor 应用，但缺乏文件/默认值分层，常与 `config` 互补。
- **`figment`** 在需要多 Profile（如 `default`、`debug`、`production`）组合时更灵活。

---

## Rust 实现方案 {#rust-实现方案}

> **来源**: [config crate docs](https://docs.rs/config/latest/config/)

推荐组合：

```rust
use config::{Config, Environment, File, FileFormat};
use serde::Deserialize;

#[derive(Debug, Clone, Deserialize)]
struct AppConfig {
    server: ServerConfig,
    log_level: String,
}

#[derive(Debug, Clone, Deserialize)]
struct ServerConfig {
    host: String,
    port: u16,
}

fn load_config() -> Result<AppConfig, config::ConfigError> {
    Config::builder()
        // 1. 硬编码默认值（TOML/JSON 字符串）
        .add_source(File::from_str(
            r#"
            [server]
            host = "127.0.0.1"
            port = 8080
            log_level = "info"
            "#,
            FileFormat::Toml,
        ))
        // 2. 可选配置文件
        .add_source(File::with_name("config/app").required(false))
        // 3. 环境变量，如 APP__SERVER__PORT=9000
        .add_source(
            Environment::with_prefix("APP")
                .separator("__")
                .try_parsing(true),
        )
        .build()?
        .try_deserialize()
}
```

设计要点：

- **`required(false)`**：配置文件可选，避免本地开发必须携带配置文件。
- **`try_parsing(true)`**：自动将环境变量字符串解析为数字、布尔值等类型。
- **分隔符 `__`**：将扁平环境变量映射到嵌套字段，如 `APP__SERVER__PORT` → `server.port`。
- **敏感字段**：使用独立结构体 `Secrets` 并通过环境变量单独注入，避免序列化到日志。

---

## 完整代码示例 {#完整代码示例}

> **来源**: [config crate docs](https://docs.rs/config/latest/config/)

完整可运行示例见：

- [crates/c07_process/examples/configuration_management_pattern.rs](../../../../crates/c07_process/examples/configuration_management_pattern.rs)

运行方式：

```bash
# 仅使用默认值 {#仅使用默认值}
cargo run -p c07_process --example configuration_management_pattern

# 使用环境变量覆盖 {#使用环境变量覆盖}
cd crates/c07_process
APP__SERVER__PORT=9000 APP__LOG_LEVEL=debug \
  cargo run --example configuration_management_pattern
```

示例要点：

1. 通过 `Config::builder()` 组合三种来源。
2. 使用 `serde` 派生实现类型化配置结构体。
3. 使用 `Environment` 实现 12-Factor 风格的环境变量覆盖。

---

## 反例边界 {#反例边界}

> **来源**: [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/) | [config crate docs](https://docs.rs/config/latest/config/)

### 1. 敏感信息泄露 {#1-敏感信息泄露}

**错误做法**：将数据库密码写入 `config/production.toml` 并提交到仓库。

```rust,ignore
// 反例：将密钥硬编码或写入配置文件
let cfg = AppConfig {
    database_url: "postgres://user:password@host/db".into(),
    ..Default::default()
};
```

**正确做法**：敏感字段仅通过环境变量或加密密钥管理服务注入，结构体实现 `Debug` 时遮蔽字段。

```rust
#[derive(Deserialize)]
struct Secrets {
    #[serde(rename = "database_url")]
    database_url: String,
}

impl std::fmt::Debug for Secrets {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Secrets").finish_non_exhaustive()
    }
}
```

### 2. 配置热加载竞态 {#2-配置热加载竞态}

**错误做法**：多线程共享可变 `Config` 并在收到文件变更通知时直接替换。

```rust,ignore
// 反例：无同步的热替换
static mut CONFIG: Option<AppConfig> = None;

fn reload() {
    unsafe { CONFIG = Some(load_config().unwrap()); }
}
```

**正确做法**：使用 `Arc<RwLock<AppConfig>>` 或 `Arc<AtomicPtr<...>>` 保证读取者看到完整一致的快照；必要时引入版本号，旧任务继续使用旧配置。

### 3. 类型不匹配 {#3-类型不匹配}

**错误做法**：环境变量值为 `"true"` 但目标字段为 `u16`，未启用 `try_parsing`。

```rust,ignore
// 反例：环境变量全为字符串，反序列化到数字字段会失败
#[derive(Deserialize)]
struct ServerConfig { port: u16 }
```

**正确做法**：启用 `Environment::try_parsing(true)`，或对字段使用自定义反序列化器处理空值/缺省值。

### 4. 配置缺失未处理 {#4-配置缺失未处理}

**错误做法**：使用 `unwrap()` 直接崩溃，用户无法得知缺少哪个键。

```rust,ignore
let cfg: AppConfig = load_config().unwrap();
```

**正确做法**：使用 `thiserror`/`anyhow` 将 `config::ConfigError` 转换为可读错误，并在入口统一报告。

---

## 权威来源索引 {#权威来源索引}

> **来源**: [权威来源对齐文档](../../10_authoritative_source_alignment_network.md)

| 优先级 | 来源 | 说明 |
|--------|------|------|
| P0 | [Rust Reference](https://doc.rust-lang.org/reference/) | `static`、`const`、模块与可见性规则 |
| P0 | [Cargo Book – Environment Variables](https://doc.rust-lang.org/cargo/reference/environment-variables.html) | Cargo 运行期环境变量约定 |
| P0 | [The Rust Programming Language](https://doc.rust-lang.org/book/) | 错误处理、 trait、生命周期基础 |
| P1 | [config crate docs](https://docs.rs/config/latest/config/) | 分层配置 API、环境变量解析 |
| P1 | [clap docs](https://docs.rs/clap/latest/clap/) | 命令行参数解析与派生宏 |
| P1 | [envy docs](https://docs.rs/envy/latest/envy/) | 环境变量到结构体反序列化 |
| P1 | [figment docs](https://docs.rs/figment/latest/figment/) | Profile 化配置组合 |
| P2 | [Rust Design Patterns](https://rust-unofficial.github.io/patterns/) | Builder、Strategy、依赖注入等设计模式 |
| P2 | [12-Factor App – Config](https://12factor.net/config) | 环境变量优先的配置哲学 |

---

## 相关概念 {#相关概念}

> **来源**: [Rust Design Patterns](https://rust-unofficial.github.io/patterns/)

- [服务组合](README.md)：配置管理是服务组合的参数化延伸。
- [01_formal_composition](01_formal_composition.md)：组合工程的形式化定义。
- [02_effectiveness_proofs](02_effectiveness_proofs.md)：组合有效性定理。
- [Builder / 类型状态](../01_design_patterns_formal/README.md)：复杂配置对象常使用 Builder 构造。
- [错误处理](../../10_error_handling_cheatsheet.md)：配置解析失败必须显式处理。
- [Crate 架构](../07_crate_architectures/00_crate_architecture_master_index.md)：Feature flag 与配置分层共同决定 crate 运行期行为。
