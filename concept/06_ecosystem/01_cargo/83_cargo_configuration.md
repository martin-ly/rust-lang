# Cargo 配置与环境变量（Cargo Configuration）

> **内容分级**: [参考级]
> **本节关键术语**: Configuration · Environment Variables · `.cargo/config.toml` · Credential Provider · `CARGO_*` — [完整对照表](../../00_meta/01_terminology/terminology_glossary.md)
>
> **EN**: Cargo Configuration
> **Summary**: Cargo configuration for Rust 1.97.0+: `.cargo/config.toml` hierarchy, common settings, environment variable mapping, credential providers, registry authentication, resolver options, and cross-compilation setup.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **受众**: [进阶]
> **Bloom 层级**: L2-L3
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **A** — Application
> **双维定位**: E×Tool — 工具链与生态系统
> **定位**: 把 Cargo 的“配置”与“环境变量”两大参考章节集中为一份可查阅权威页。
> **前置概念**: [Cargo Workflow](81_cargo_workflow.md) · [Cargo Registries and Publishing](62_cargo_registries_and_publishing.md) · [Cargo Authentication and Cache](63_cargo_authentication_and_cache.md)
> **后置概念**: [Cargo Commands Reference](84_cargo_commands_reference.md) · [Cross Compilation](../05_systems_and_embedded/17_cross_compilation.md)

---

> **来源**: [Cargo Book — Configuration](https://doc.rust-lang.org/cargo/reference/config.html) · [Cargo Book — Environment Variables](https://doc.rust-lang.org/cargo/reference/environment-variables.html) · [Cargo Book — Registry Authentication](https://doc.rust-lang.org/cargo/reference/registry-authentication.html)

---

## 一、配置层级

Cargo 按以下顺序读取配置，后读取的覆盖先读取的：

1. `CARGO_HOME/config.toml`（默认 `~/.cargo/config.toml`）
2. 当前目录及所有父目录中的 `.cargo/config.toml`
3. 命令行参数 `--config <path>`
4. 环境变量 `CARGO_*`

## 二、常用配置项

「常用配置项」涉及替换 registry 源、设置默认 target与别名，本节逐一说明其要点。

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
target-dir = "target"
build-dir = "target/build"
```

### 别名

```toml
[alias]
br = "build --release"
t = "test"
lint = "clippy --workspace -- -D warnings"
```

## 三、环境变量映射

| 环境变量 | 对应配置键 | 作用 |
|:---|:---|:---|
| `CARGO_HOME` | — | Cargo 缓存与配置主目录 |
| `CARGO_TARGET_DIR` | `build.target-dir` | 统一构建输出目录 |
| `CARGO_BUILD_JOBS` | `build.jobs` | 并行编译任务数 |
| `CARGO_NET_OFFLINE` | `net.offline` | 离线模式 |
| `CARGO_HTTP_TIMEOUT` | `http.timeout` | HTTP 超时 |
| `RUSTFLAGS` | `build.rustflags` | 传递给 `rustc` 的 flag |
| `CARGO_RESOLVER_INCOMPATIBLE_RUST_VERSIONS` | `resolver.incompatible-rust-versions` | resolver v3 MSRV 策略 |

Cargo 还会向构建脚本和测试暴露大量以 `CARGO_*` 开头的环境变量。

## 四、Resolver v3 配置

```toml
[resolver]
incompatible-rust-versions = "fallback"  # v3 默认值
```

可选值：

| 值 | 行为 |
|:---|:---|
| `fallback` | 优先选择 `rust-version` 兼容的版本；没有时才回退到不兼容版本（v3 默认） |
| `allow` | 把 `rust-version` 不兼容的版本与普通版本同等对待（v1/v2 默认行为） |

环境变量也可覆盖：

```bash
CARGO_RESOLVER_INCOMPATIBLE_RUST_VERSIONS=allow cargo update
```

## 五、Registry 认证

Cargo 支持多种凭证提供机制：

| 方式 | 说明 |
|:---|:---|
| `cargo login` | 将 token 写入当前 credential provider |
| 凭证提供程序 | 通过 `credential-provider` 配置集成外部 secret 管理器 |
| `net.git-fetch-with-cli` | 使用系统 git 进行 fetch，便于 SSH 认证 |

推荐全局配置：

```toml
[registry]
global-credential-providers = [
    "cargo:token",
    "cargo:libsecret",
    "cargo:macos-keychain",
    "cargo:wincred",
]
```

详见 [Cargo Authentication and Cache](63_cargo_authentication_and_cache.md)。

## 六、跨编译配置示例

```toml
[build]
target = "x86_64-unknown-linux-musl"

[target.x86_64-unknown-linux-musl]
linker = "x86_64-linux-musl-gcc"
```

更多内容见 [Cross Compilation](../05_systems_and_embedded/17_cross_compilation.md)。

## 七、配置层级选择决策表

| 场景 | 推荐位置 | 原因 |
|:---|:---|:---|
| 个人机器上的镜像/别名 | `~/.cargo/config.toml` | 不影响仓库他人 |
| 项目统一的 rustflags/target | `.cargo/config.toml` | 与代码一起版本化 |
| CI 临时覆盖 | 环境变量 | 不修改仓库文件 |
| 单次命令实验 | `--config <path>` | 最小侵入 |

## 八、常用项目级配置模板

一个典型的 Rust 1.97.0+ 项目 `.cargo/config.toml`：

```toml
[build]
rustflags = ["-W", "clippy::pedantic"]

[alias]
t = "test --workspace"
c = "check --workspace"

[registries.crates-io]
protocol = "sparse"

[resolver]
incompatible-rust-versions = "fallback"
```

## 九、网络与缓存配置

| 配置键 | 示例 | 用途 |
|:---|:---|:---|
| `net.retry` | `3` | 下载失败重试次数 |
| `net.timeout` | `30` | 网络请求超时（秒） |
| `http.timeout` | `60` | HTTP 超时 |
| `http.check-revoke` | `false` | Windows 证书吊销检查 |
| `registries.crates-io.protocol` | `"sparse"` | 使用 sparse index |

## 十、与 Source Replacement 的关系

`[source]` 与 `[registries]` 配置可让企业将 crates.io 替换为内部 registry，同时保留原始 package 的 identity。详见 [Cargo Source Replacement](61_cargo_source_replacement.md)。

> **L5 对比**: [Rust vs C++](../../05_comparative/01_systems_languages/01_rust_vs_cpp.md) · [Rust vs Go](../../05_comparative/01_systems_languages/02_rust_vs_go.md)

---

> **权威来源**: [Cargo Book — Configuration](https://doc.rust-lang.org/cargo/reference/config.html)

---

## 国际权威参考 / International Authority References（P0 官方 · P1 学术 · P2 生态）

> 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。

- **P1 学术/形式化**: [Rudra: Finding Memory Safety Bugs in Rust at the Ecosystem Scale (SOSP 2021)](https://dl.acm.org/doi/10.1145/3477132.3483570)
