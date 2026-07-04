> **内容分级**: [综述级]
> [综述级]
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
> **前置概念**: [Rust vs C++](../05_comparative/01_rust_vs_cpp.md)
> **后置概念**: [Cargo Build Scripts](59_cargo_build_scripts.md) · [Cargo Registries and Publishing](62_cargo_registries_and_publishing.md)

---

> **来源**:
>
> [Cargo — Dependency Resolution](https://doc.rust-lang.org/cargo/reference/resolver.html) ·
> [TRPL](https://doc.rust-lang.org/book/title-page.html) ·
> [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) ·
> [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) ·
> [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
>
> [Cargo Book — SemVer Compatibility](https://doc.rust-lang.org/cargo/reference/semver.html) ·
> [Cargo Book — Features](https://doc.rust-lang.org/cargo/reference/features.html) ·
> [Cargo Book — Resolver (Specifying Dependencies)](https://doc.rust-lang.org/cargo/reference/specifying-dependencies.html) ·
> [Cargo Book — Resolver versions](https://doc.rust-lang.org/cargo/reference/resolver.html#resolver-versions) ·
> [Cargo Book — rust-version](https://doc.rust-lang.org/cargo/reference/manifest.html#the-rust-version-field) ·
> [RFC 3537 — MSRV-aware resolver](https://rust-lang.github.io/rfcs/3537-msrv-resolver.html)


---

> **过渡**: 从 Cargo 依赖解析 的直观描述转向其形式化定义，需要先把日常经验中的模糊直觉转化为可验证的术语。

> **过渡**: 在建立 Cargo 依赖解析 的核心命题之后，下一步是审视这些命题在边界条件下的稳定性——这正是反命题与反例的价值所在。

> **过渡**: 最后，将 Cargo 依赖解析 与相邻概念连接，形成从 L1 到 L7 的纵向认知路径，避免孤立记忆。


---

> **定理 1** [Tier 2]: Cargo 依赖解析 的核心约束 ⟹ 编译器可以在编译期排除一整类运行时（Runtime）错误。
>
> **定理 2** [Tier 2]: 正确理解 Cargo 依赖解析 的语义 ⟹ 开发者能够写出既安全又零成本抽象（Zero-Cost Abstraction）的代码。
>
> **定理 3** [Tier 3]: 将 Cargo 依赖解析 与 Rust 的所有权（Ownership）/生命周期（Lifetimes）模型结合 ⟹ 可以在更大系统中进行可扩展的推理。


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
  - [九、可运行实践：resolver v3 与混合 MSRV workspace](#九可运行实践resolver-v3-与混合-msrv-workspace)
    - [9.1 示例结构](#91-示例结构)
    - [9.2 运行与观察](#92-运行与观察)
    - [9.3 切换解析策略](#93-切换解析策略)
    - [9.4 诊断重复依赖](#94-诊断重复依赖)
    - [9.5 验证](#95-验证)
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

通过 `.cargo/config.toml` 的 `[resolver]` 表可以调整 MSRV 不兼容版本的处理方式（Rust 1.84+）：

```toml
[resolver]
incompatible-rust-versions = "fallback"  # v3 默认值：优先 MSRV 兼容版本
```

可选值：

| 值 | 行为 |
|:---|:---|
| `fallback` | 优先选择 `rust-version` 兼容的版本；没有时才回退到不兼容版本（v3 默认） |
| `allow` | 把 `rust-version` 不兼容的版本与普通版本同等对待（v1/v2 默认行为） |

环境变量也可覆盖：

```bash
# CI 中验证最新依赖
CARGO_RESOLVER_INCOMPATIBLE_RUST_VERSIONS=allow cargo update
```

> **注**：早期 RFC 草案使用 `build.resolver.precedence` / `CARGO_BUILD_RESOLVER_PRECEDENCE` 命名，但最终稳定实现采用 `[resolver] incompatible-rust-versions` / `CARGO_RESOLVER_INCOMPATIBLE_RUST_VERSIONS`。`--ignore-rust-version` 命令行选项等价于临时将策略设为 `allow`。

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

## 九、可运行实践：resolver v3 与混合 MSRV workspace

本节提供一个最小可运行的 workspace 示例，演示 resolver v3 的 MSRV 感知解析、混合 MSRV workspace 的约束行为以及 `cargo tree` 诊断重复依赖。

> 示例代码位于 `examples/resolver_v3_practice/`，是一个独立 workspace（子目录自带 `[workspace]` 表），可直接 `cd` 进去运行，不会与根 workspace 冲突。

### 9.1 示例结构

```text
examples/resolver_v3_practice/
├── Cargo.toml          # workspace 根：resolver = "3"
├── .cargo/config.toml  # 显式启用 incompatible-rust-versions = "fallback"
├── legacy-lib/         # rust-version = "1.70"
├── modern-app/         # rust-version = "1.84"
└── edge-bin/           # rust-version = "1.96"
```

三个 member 都依赖 `clap = "4"`，因此 workspace 的等效 MSRV 约束取成员中最低值 **1.70**。`legacy-lib` 还依赖 `indexmap = "1"`，`modern-app` 依赖 `indexmap = "2"`，用于演示主版本重复。

workspace 根的关键配置：

```toml
# examples/resolver_v3_practice/Cargo.toml
[workspace]
resolver = "3"
members = ["legacy-lib", "modern-app", "edge-bin"]
```

局部 resolver 配置（覆盖根 workspace 的 `incompatible-rust-versions = "allow"`）：

```toml
# examples/resolver_v3_practice/.cargo/config.toml
[resolver]
incompatible-rust-versions = "fallback"
```

`legacy-lib/Cargo.toml`：

```toml
[package]
name = "legacy-lib"
version = "0.1.0"
edition = "2021"
rust-version = "1.70"

[dependencies]
clap = { version = "4", features = ["derive"] }
indexmap = "1"
```

### 9.2 运行与观察

进入目录并执行默认解析：

```bash
cd examples/resolver_v3_practice
cargo update
cargo tree
```

预期输出（节选）：

```text
     Locking 36 packages to latest Rust 1.70 compatible versions
      Adding clap v4.4.18 (available: v4.6.1, requires Rust 1.85)
...
edge-bin v0.1.0 (examples/resolver_v3_practice/edge-bin)
├── clap v4.4.18
│   ├── clap_builder v4.4.18
│   └── clap_derive v4.4.7 (proc-macro)
├── legacy-lib v0.1.0 (...)
│   ├── clap v4.4.18 (*)
│   └── indexmap v1.9.3
│       └── hashbrown v0.12.3
└── modern-app v0.1.0 (...)
    ├── clap v4.4.18 (*)
    └── indexmap v2.11.4
        └── hashbrown v0.16.1
```

观察点：

1. `clap 4.6.1` 可用，但 resolver 选择了 `clap 4.4.18`，因为 4.6.1 要求 Rust 1.85，高于 workspace 最低 MSRV 1.70。
2. `indexmap` 同时存在 `1.9.3` 与 `2.11.4` 两个主版本，因为它们分别被不同成员以不兼容的主版本要求引入。

### 9.3 切换解析策略

默认 `fallback` 策略优先 MSRV 兼容版本。若要在 CI 中验证最新依赖，可临时覆盖为 `allow`：

```bash
# 优先选择最新版本，忽略 MSRV（等价于旧 RFC 草案中的 maximum 策略）
CARGO_RESOLVER_INCOMPATIBLE_RUST_VERSIONS=allow cargo update
cargo tree
```

预期 `clap` 会升级到 `4.6.1`：

```text
     Locking 27 packages to latest compatible versions
edge-bin v0.1.0 (...)
├── clap v4.6.1
│   ├── clap_builder v4.6.0
...
```

也可使用命令行选项：

```bash
cargo update --ignore-rust-version
```

> **关于 `minimum` 策略**：当前稳定版 Cargo（1.84+）未提供与 RFC 草案中 `minimum` 对应的独立环境变量。如需测试最低依赖版本，可使用 nightly 的 `cargo update -Zminimal-versions`，或手动把依赖版本下界设高后执行 `cargo update --precise`。

### 9.4 诊断重复依赖

```bash
cargo tree --duplicates
```

预期输出：

```text
hashbrown v0.12.3
└── indexmap v1.9.3
    └── legacy-lib v0.1.0 (...)
        ├── edge-bin v0.1.0 (...)
        └── modern-app v0.1.0 (...)
            └── edge-bin v0.1.0 (...)

hashbrown v0.16.1
└── indexmap v2.11.4
    └── modern-app v0.1.0 (...) (*)

indexmap v1.9.3 (*)
indexmap v2.11.4 (*)
```

这清晰地展示了 `indexmap` 两个主版本为何同时出现：legacy-lib 需要 1.x，modern-app 需要 2.x。

### 9.5 验证

确保示例可编译：

```bash
cd examples/resolver_v3_practice
cargo check --workspace
```

应成功完成。

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
| [Cargo Book — rust-version](https://doc.rust-lang.org/cargo/reference/manifest.html#the-rust-version-field) | ✅ 一级 | `rust-version` / MSRV 字段官方文档 |
| [RFC 3537 — MSRV-aware resolver](https://rust-lang.github.io/rfcs/3537-msrv-resolver.html) | ✅ 一级 | MSRV-aware 解析器设计 |
| [Rust 1.84.0 Release Notes](https://releases.rs/docs/1.84.0/) | ✅ 一级 | resolver v3 / MSRV resolver 稳定公告 |

---

> **权威来源**: [Cargo Book](https://doc.rust-lang.org/cargo/), [SemVer](https://semver.org/lang/zh-CN/), [Rust Reference](https://doc.rust-lang.org/reference/)
> **权威来源对齐变更日志**: 2026-06-23 更新，对齐 Rust 1.84.0+ / RFC 3537 / Cargo resolver v3 & MSRV-aware resolver；2026-06-26 新增第九章可运行实践 `examples/resolver_v3_practice/` [来源: P2 Deep Content Sprint]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.1+ (Edition 2024)
**最后更新**: 2026-06-26
**状态**: ✅ 已对齐 Cargo Book resolver 文档
