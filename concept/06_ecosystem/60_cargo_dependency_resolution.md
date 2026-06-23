> **内容分级**: [综述级]

> **本节关键术语**: Dependency Resolution · SemVer · Lockfile · Features Unification · Resolver Version · `rust-version` · `cargo tree` · Yanked — [完整对照表](../00_meta/terminology_glossary.md)
>
# Cargo 依赖解析

> **EN**: Cargo Dependency Resolution
> **Summary**: Explains how Cargo resolves crate dependency versions, selects compatible SemVer ranges, unifies features, handles lockfiles, resolver versions, and `rust-version` requirements.
> **受众**: [中级 → 高级]
> **Bloom 层级**: 理解 → 应用
> **A/S/P 标记**: **P** — Practice
> **双维定位**: E×Tool — 工具链与生态系统
> **定位**: 把“`cargo build` 时到底选了哪个版本、为什么选这个版本、特性如何合并”讲清楚。
> **前置概念**: [Cargo Toolchain](./01_toolchain.md) · [Semantic Versioning](https://semver.org/lang/zh-CN/) · [Traits](../02_intermediate/01_traits.md)
> **后置概念**: [Cargo Build Scripts](./59_cargo_build_scripts.md) · [Cargo Registries and Publishing](./62_cargo_registries_and_publishing.md)

---

> **来源**: [Cargo — Dependency Resolution](https://doc.rust-lang.org/cargo/reference/resolver.html)
> [Cargo Book — SemVer Compatibility](https://doc.rust-lang.org/cargo/reference/semver.html) ·
> [Cargo Book — Features](https://doc.rust-lang.org/cargo/reference/features.html) ·
> [Cargo Book — Resolver (Specifying Dependencies)](https://doc.rust-lang.org/cargo/reference/specifying-dependencies.html) ·
> [Cargo Book — Resolver versions](https://doc.rust-lang.org/cargo/reference/resolver.html#resolver-versions) ·
> [RFC 3537 — MSRV-aware resolver](https://rust-lang.github.io/rfcs/3537-msrv-resolver.html)

## 📑 目录

- [Cargo 依赖解析](#cargo-依赖解析)
  - [📑 目录](#-目录)
  - [一、解析的目标与输入](#一解析的目标与输入)
  - [二、SemVer 兼容性与版本要求](#二semver-兼容性与版本要求)
  - [三、解析算法：贪心 + 回溯](#三解析算法贪心--回溯)
  - [四、特性合并（Feature Unification）](#四特性合并feature-unification)
    - [4.1 同一个 crate 在一个主版本内只编译一次](#41-同一个-crate-在一个主版本内只编译一次)
    - [4.2 Feature unification 的副作用](#42-feature-unification-的副作用)
  - [五、Lockfile 的作用](#五lockfile-的作用)
  - [六、Resolver 版本差异](#六resolver-版本差异)
  - [七、`rust-version` 与 MSRV 感知](#七rust-version-与-msrv-感知)
    - [7.1 MSRV-aware resolver 行为](#71-msrv-aware-resolver-行为)
    - [7.2 控制解析策略](#72-控制解析策略)
    - [7.3 工作空间与混合 MSRV](#73-工作空间与混合-msrv)
  - [八、Yanked 版本与冲突诊断](#八yanked-版本与冲突诊断)
    - [8.1 Yanked 版本](#81-yanked-版本)
    - [8.2 诊断工具](#82-诊断工具)
  - [嵌入式测验](#嵌入式测验)
    - [测验 1：`serde = "1.2.3"` 与 `serde = "=1.2.3"` 的区别是什么？](#测验-1serde--123-与-serde--123-的区别是什么)
    - [测验 2：为什么同一 crate 的 `^1` 和 `^2` 可以共存，而两个 `^1.x` 只能出现一次？](#测验-2为什么同一-crate-的-1-和-2-可以共存而两个-1x-只能出现一次)
    - [测验 3：什么是 feature unification？它可能带来什么副作用？](#测验-3什么是-feature-unification它可能带来什么副作用)
    - [测验 4：二进制 crate 和库 crate 对 `Cargo.lock` 的态度为何不同？](#测验-4二进制-crate-和库-crate-对-cargolock-的态度为何不同)
  - [权威来源索引](#权威来源索引)

---

## 一、解析的目标与输入

`cargo build` 执行前，Cargo 需要把 `Cargo.toml` 中的依赖声明转换成具体版本。解析的输入包括：

- 工作区所有 `Cargo.toml` 中的依赖项与版本要求；
- `Cargo.lock` 中已有的锁定版本；
- Registry 索引中的可用版本；
- 每个 crate 的依赖与 features 声明。

输出：一棵依赖树（Dependency Tree），每个节点对应一个具体版本。

```text
my-app 0.1.0
├── serde 1.0.217
│   └── serde_derive 1.0.217 (proc-macro)
├── tokio 1.42.0
│   └── ...
└── local-crate (path dependency)
```

---

## 二、SemVer 兼容性与版本要求

Cargo 默认使用 **SemVer**（语义化版本）。版本要求写法与含义：

| 写法 | 含义 |
|:---|:---|
| `1.2.3` | `^1.2.3`，兼容 1.x.x 且 ≥ 1.2.3 |
| `^1.2.3` | 与上相同 |
| `~1.2.3` | 兼容 1.2.x |
| `>=1.2, <2.0` | 显式范围 |
| `=1.2.3` | 精确锁定 |
| `*` | 任何版本 |

> **关键洞察**: Cargo 只会在同一个 crate 的兼容主版本内选择一个版本；如果两个依赖分别要求 `^1` 和 `^2`，则 `foo` 会同时出现 `foo 1.x` 和 `foo 2.x`。
>
> [来源: Cargo Book — SemVer Compatibility](https://doc.rust-lang.org/cargo/reference/semver.html)

---

## 三、解析算法：贪心 + 回溯

Cargo 的解析器本质上是一个 SAT-like 约束求解器：

1. **贪心选择**: 对每个 crate，优先选择满足版本要求的最新兼容版本；
2. **特性统一**: 同一 crate 在一个兼容主版本内只保留一份，所有使用该 crate 的地方统一启用 features；
3. **冲突回溯**: 如果后续依赖的版本要求与当前选择冲突，回退并尝试其他版本；
4. **无全局最优**: 目标是“找到一个合法解”，而非理论最优解；因此不同 Cargo 版本可能得到略有不同的结果。

> **定理**: 依赖解析问题在 NP 困难意义上与 SAT 类似，但 Cargo 使用启发式 + 回溯在实际 registry 规模下足够快。
>
> [来源: Cargo Book — How Cargo resolves dependencies](https://doc.rust-lang.org/cargo/reference/resolver.html#how-cargo-resolves-dependencies)

---

## 四、特性合并（Feature Unification）

### 4.1 同一个 crate 在一个主版本内只编译一次

```toml
# crate A
[dependencies]
serde = { version = "1", features = ["derive"] }

# crate B
[dependencies]
serde = { version = "1", default-features = false, features = ["std"] }
```

如果 `my-app` 同时依赖 A 和 B，那么 `serde 1.x` 只会被编译一次，并且 **启用 `derive` + `std`**。

### 4.2 Feature unification 的副作用

合并后特性可能比任何单独使用者需要的都多，导致编译时间变长或引入不必要的依赖。可以通过 `resolver = "2"` 或 `"3"` 在不同 target/构建配置间做更细粒度的统一。

```toml
[workspace]
resolver = "2"
```

---

## 五、Lockfile 的作用

`Cargo.lock` 把解析结果持久化：

- 保证团队成员、CI、部署使用完全相同的依赖版本；
- 二进制 crate 应提交 `Cargo.lock`；
- 库 crate 通常不提交 `Cargo.lock`（由依赖方解析）。

```bash
# 更新某个依赖到最新兼容版本
cargo update -p serde

# 查看当前依赖树
cargo tree
```

---

## 六、Resolver 版本差异

| Resolver | 主要行为变化 | 默认启用场景 |
|:---|:---|:---|
| v1 | 默认统一所有 target 和 dev/build 依赖的 features | Edition 2015/2018 |
| v2 | 区分 `dev-dependencies`、`target-specific` 依赖的 features | Edition 2021+ |
| v3 | 在 v2 基础上引入 **MSRV-aware resolution**：优先选择满足 `rust-version` 的版本 | Rust 1.84+ 显式声明；Edition 2024 默认 |

推荐在 workspace 根显式声明：

```toml
[workspace]
members = ["crates/*"]
resolver = "3"
```

或在单包中声明：

```toml
[package]
name = "my-crate"
version = "0.1.0"
resolver = "3"
```

> **关键事实**
>
> - Resolver v3 随 **Rust 1.84.0** 稳定。
> - **Edition 2024** 的项目默认使用 resolver v3。
> - v3 与 v2 的 feature unification 行为相同；v3 的核心新增能力是 MSRV-aware version selection。
>
> [来源: Cargo Book — Resolver versions](https://doc.rust-lang.org/cargo/reference/resolver.html#resolver-versions) · [Rust 1.84.0 Release Notes](https://releases.rs/docs/1.84.0/)

---

## 七、`rust-version` 与 MSRV 感知

`Cargo.toml` 中的 `rust-version` 字段声明包的 MSRV（Minimum Supported Rust Version）：

```toml
[package]
name = "my-crate"
version = "0.1.0"
rust-version = "1.70"
```

### 7.1 MSRV-aware resolver 行为

从 **Rust 1.84.0 / resolver v3** 开始，Cargo 在解析依赖时会考虑 `rust-version`：

- 若包的 `rust-version` 为 `1.70`，Cargo 会优先选择 `rust-version <= 1.70` 的依赖版本；
- 若依赖未声明 `rust-version`，则按现有行为处理（通常仍选择最新兼容版本）；
- 若不存在满足 MSRV 的版本，Cargo 会回退到最新版本并给出诊断信息，而不是直接失败；
- 使用 `--ignore-rust-version` 可临时忽略 MSRV 约束（例如 CI 验证最新依赖时）。

### 7.2 控制解析策略

通过 `.cargo/config.toml` 的 `resolver.precedence` 可以调整版本选择优先级：

```toml
[build]
resolver.precedence = "rust-version"  # v3 默认值：优先 MSRV 兼容版本
```

可选值：

| 值 | 行为 |
|:---|:---|
| `rust-version` | 优先选择与 `package.rust-version` / 当前工具链兼容的版本（v3 默认） |
| `maximum` | 优先选择满足 SemVer 约束的最新版本（v1/v2 默认行为） |
| `minimum` | 优先选择最低版本（对应 `-Zminimal-versions` 实验） |

环境变量也可覆盖：

```bash
# CI 中验证最新依赖
CARGO_BUILD_RESOLVER_PRECEDENCE=maximum cargo update
```

### 7.3 工作空间与混合 MSRV

工作空间没有独立的 `workspace.rust-version`；resolver 会取工作空间成员中**最低**的 `rust-version` 作为约束。如果工作空间内存在不同 MSRV 的成员，低 MSRV 成员会约束高 MSRV 成员的独特依赖。可通过显式版本要求或 `cargo update --precise` 微调。

> **提示**: `rust-version` 是 Cargo 元数据，不是编译器强制的语法约束；真正失败通常发生在编译时遇到新语法或 API。MSRV-aware resolver 的目标是把失败从"编译时"提前到"解析时"，减少手动 `cargo update --precise` 的负担。
>
> [来源: Cargo Book — The rust-version field](https://doc.rust-lang.org/cargo/reference/manifest.html#the-rust-version-field) · [RFC 3537 — MSRV-aware resolver](https://rust-lang.github.io/rfcs/3537-msrv-resolver.html) · [Cargo issue #9930](https://github.com/rust-lang/cargo/issues/9930)

---

## 八、Yanked 版本与冲突诊断

### 8.1 Yanked 版本

- crate 作者可以从 registry 撤回（yank）某个版本；
- 已有 `Cargo.lock` 的项目仍可继续构建；
- 新项目执行 `cargo update` 或首次解析时，yanked 版本不会被选择。

### 8.2 诊断工具

```bash
# 查看依赖树
cargo tree

# 查看某个依赖为何被引入
cargo tree -i some_crate

# 解释 resolver 选择某个版本的原因
cargo tree --duplicates
```

---

## 嵌入式测验

### 测验 1：`serde = "1.2.3"` 与 `serde = "=1.2.3"` 的区别是什么？

<details>
<summary>✅ 答案与解析</summary>

`"1.2.3"` 等价于 `^1.2.3`，允许兼容的更高版本如 `1.2.4`、`1.3.0`；`"=1.2.3"` 精确锁定，只使用 `1.2.3`。

</details>

---

### 测验 2：为什么同一 crate 的 `^1` 和 `^2` 可以共存，而两个 `^1.x` 只能出现一次？

<details>
<summary>✅ 答案与解析</summary>

Cargo 在主版本内保证兼容性，因此 `^1.x` 和 `^1.y` 可以统一为同一个版本；`^1` 和 `^2` 属于不同主版本，可能破坏兼容性，所以各自保留一份。

</details>

---

### 测验 3：什么是 feature unification？它可能带来什么副作用？

<details>
<summary>✅ 答案与解析</summary>

Feature unification 指同一 crate 在一个主版本内只编译一次，并集所有使用者要求的 features。副作用是可能启用比单个使用者更多的 features，增加编译时间和依赖。

</details>

---

### 测验 4：二进制 crate 和库 crate 对 `Cargo.lock` 的态度为何不同？

<details>
<summary>✅ 答案与解析</summary>

二进制需要可复现构建，所以应提交 `Cargo.lock`；库会被嵌入到不同项目中解析，因此通常不提交 `Cargo.lock`，让最终应用决定版本。

</details>

---

## 权威来源索引

| 来源 | 可信度 | 说明 |
|:---|:---:|:---|
| [Cargo Book — Dependency Resolution](https://doc.rust-lang.org/cargo/reference/resolver.html) | ✅ 一级 | 依赖解析官方文档 |
| [Cargo Book — SemVer Compatibility](https://doc.rust-lang.org/cargo/reference/semver.html) | ✅ 一级 | 语义化版本官方文档 |
| [Cargo Book — Features](https://doc.rust-lang.org/cargo/reference/features.html) | ✅ 一级 | Features 官方文档 |
| [Cargo Book — Specifying Dependencies](https://doc.rust-lang.org/cargo/reference/specifying-dependencies.html) | ✅ 一级 | 版本要求语法 |
| [RFC 3537 — MSRV-aware resolver](https://rust-lang.github.io/rfcs/3537-msrv-resolver.html) | ✅ 一级 | MSRV-aware 解析器设计 |
| [Rust 1.84.0 Release Notes](https://releases.rs/docs/1.84.0/) | ✅ 一级 | resolver v3 / MSRV resolver 稳定公告 |

---

> **权威来源**: [Cargo Book](https://doc.rust-lang.org/cargo/), [SemVer](https://semver.org/lang/zh-CN/), [Rust Reference](https://doc.rust-lang.org/reference/)
> **权威来源对齐变更日志**: 2026-06-23 更新，对齐 Rust 1.84.0+ / RFC 3537 / Cargo resolver v3 & MSRV-aware resolver

**文档版本**: 1.0
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-06-21
**状态**: ✅ 已对齐 Cargo Book resolver 文档
