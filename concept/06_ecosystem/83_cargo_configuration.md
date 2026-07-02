# Cargo 配置与环境变量（Cargo Configuration）

> **内容分级**: [参考级]
> **本节关键术语**: Configuration · Environment Variables · `.cargo/config.toml` · Credential Provider · `CARGO_*` — [完整对照表](../00_meta/terminology_glossary.md)
>
> **EN**: Cargo Configuration
> **Summary**: Cargo 完整配置机制：`.cargo/config.toml` 层级、常用配置项、环境变量映射、凭证提供者与 registry 认证配置。
> **受众**: [进阶]
> **Bloom 层级**: 理解 → 应用
> **A/S/P 标记**: **P** — Practice
> **双维定位**: E×Tool — 工具链与生态系统
> **定位**: 把 Cargo 的“配置”与“环境变量”两大参考章节集中为一份可查阅权威页。
> **前置概念**: [Cargo Workflow](81_cargo_workflow.md) · [Cargo Registries and Publishing](62_cargo_registries_and_publishing.md) · [Cargo Authentication and Cache](63_cargo_authentication_and_cache.md)
> **后置概念**: [Cargo Commands Reference](84_cargo_commands_reference.md) · [Cross Compilation](17_cross_compilation.md)

---

> **来源**: [Cargo Book — Configuration](https://doc.rust-lang.org/cargo/reference/config.html) · · [Rust Reference](https://doc.rust-lang.org/reference/) · [TRPL](https://doc.rust-lang.org/book/title-page.html)
> [Cargo Book — Environment Variables](https://doc.rust-lang.org/cargo/reference/environment-variables.html) ·
> [Cargo Book — Registry Authentication](https://doc.rust-lang.org/cargo/reference/registry-authentication.html)

---

## 一、配置层级

Cargo 按以下顺序读取配置，后读取的覆盖先读取的：

1. `CARGO_HOME/config.toml`（默认 `~/.cargo/config.toml`）
2. 当前目录及所有父目录中的 `.cargo/config.toml`
3. 命令行参数 `--config <path>`
4. 环境变量 `CARGO_*`

## 二、常用配置项

### 替换 registry 源

```toml
[registries]
my-registry = { index = "https://my-registry.example.com/index" }

[source.crates-io]
replace-with = "my-registry"
```

### 设置默认 target

```toml
[build]
target = "x86_64-unknown-linux-gnu"
rustflags = ["-C", "target-cpu=sandybridge"]
```

### 别名

```toml
[alias]
br = "build --release"
t = "test"
```

## 三、环境变量

| 变量 | 作用 |
|:---|:---|
| `CARGO_HOME` | Cargo 缓存与配置主目录 |
| `CARGO_TARGET_DIR` | 统一构建输出目录 |
| `CARGO_NET_OFFLINE` | 离线模式 |
| `CARGO_HTTP_TIMEOUT` | HTTP 超时 |
| `RUSTFLAGS` | 传递给 `rustc` 的 flag |
| `CARGO_BUILD_JOBS` | 并行编译任务数 |

Cargo 还会向构建脚本和测试暴露大量以 `CARGO_*` 开头的环境变量。

## 四、Registry 认证

Cargo 支持多种凭证提供机制：

| 方式 | 说明 |
|:---|:---|
| `cargo login` | 将 token 写入 `~/.cargo/credentials.toml` |
| 凭证提供程序 | 通过 `credential-provider` 配置集成外部 secret 管理器 |
| `net.git-fetch-with-cli` | 使用系统 git 进行 fetch，便于 SSH 认证 |

详见 [Cargo Authentication and Cache](63_cargo_authentication_and_cache.md)。

---

> **权威来源**: [Cargo Book — Configuration](https://doc.rust-lang.org/cargo/reference/config.html)
> **内容分级**: [参考级]
