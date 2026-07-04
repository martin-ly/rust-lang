> **内容分级**: [综述级]
> **本节关键术语**: Registry · crates.io · Cargo Index · Sparse Protocol · Git Protocol · `cargo publish` · `cargo yank` · `cargo owner` · Authentication Token — [完整对照表](../../00_meta/01_terminology/terminology_glossary.md)
>
# Cargo Registry 与包发布

> **EN**: Cargo Registries and Publishing
> **Summary**: Explains how Cargo registries work, the sparse vs git index protocols, publishing workflow, yank/owner commands, authentication, and private registry setup.
> **受众**: [中级 → 高级]
> **Bloom 层级**: 理解 → 应用
> **A/S/P 标记**: **P** — Practice
> **双维定位**: E×Tool — 工具链与生态系统
> **定位**: 把“怎么把 crate 发布到 crates.io / 私有 registry、registry 内部如何索引、认证如何工作”系统化。
> **前置概念**: [Rust vs C++](../../05_comparative/01_systems_languages/01_rust_vs_cpp.md)
> **后置概念**: [Supply Chain Security](72_cargo_security_cves.md) · [Cargo Toolchain](../00_toolchain/01_toolchain.md)

---

> **来源**: [Cargo — Registries](https://doc.rust-lang.org/cargo/reference/registries.html) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
> [Cargo Book — Cargo Registries](https://doc.rust-lang.org/cargo/reference/registries.html) ·
> [Cargo Book — Alternative Registries](https://doc.rust-lang.org/cargo/reference/registries.html#using-an-alternate-registry) ·
> [Cargo Book — config.toml — Registries](https://doc.rust-lang.org/cargo/reference/config.html#registries)

---

> **过渡**: 从 Cargo Registry 与包发布 的直观描述转向其形式化定义，需要先把日常经验中的模糊直觉转化为可验证的术语。

> **过渡**: 在建立 Cargo Registry 与包发布 的核心命题之后，下一步是审视这些命题在边界条件下的稳定性——这正是反命题与反例的价值所在。

> **过渡**: 最后，将 Cargo Registry 与包发布 与相邻概念连接，形成从 L1 到 L7 的纵向认知路径，避免孤立记忆。

---

> **定理 1** [Tier 2]: Cargo Registry 与包发布 的核心约束 ⟹ 编译器可以在编译期排除一整类运行时（Runtime）错误。
>
> **定理 2** [Tier 2]: 正确理解 Cargo Registry 与包发布 的语义 ⟹ 开发者能够写出既安全又零成本抽象（Zero-Cost Abstraction）的代码。
>
> **定理 3** [Tier 3]: 将 Cargo Registry 与包发布 与 Rust 的所有权（Ownership）/生命周期（Lifetimes）模型结合 ⟹ 可以在更大系统中进行可扩展的推理。

## 📑 目录

- [Cargo Registry 与包发布](#cargo-registry-与包发布)
  - [📑 目录](#-目录)
  - [一、Registry 是什么](#一registry-是什么)
  - [二、Registry 索引协议](#二registry-索引协议)
  - [三、发布流程：cargo publish](#三发布流程cargo-publish)
    - [3.1 准备工作](#31-准备工作)
    - [3.2 Cargo.toml 必填字段](#32-cargotoml-必填字段)
  - [四、Yank 与 Owner 管理](#四yank-与-owner-管理)
    - [4.1 Yank（撤回）](#41-yank撤回)
    - [4.2 Owner 管理](#42-owner-管理)
  - [五、认证与 Token](#五认证与-token)
  - [六、私有 Registry 与 Source Replacement](#六私有-registry-与-source-replacement)
    - [6.1 配置私有 Registry](#61-配置私有-registry)
    - [6.2 Source Replacement（源替换）](#62-source-replacement源替换)
  - [七、发布前的检查清单](#七发布前的检查清单)
  - [嵌入式测验](#嵌入式测验)
    - [测验 1：sparse 协议相比 git 协议的主要优势是什么？](#测验-1sparse-协议相比-git-协议的主要优势是什么)
    - [测验 2：`cargo yank` 会删除已经发布的 crate 源码吗？](#测验-2cargo-yank-会删除已经发布的-crate-源码吗)
    - [测验 3：发布 crate 到 crates.io 时，`license` 字段是必须的吗？](#测验-3发布-crate-到-cratesio-时license-字段是必须的吗)
    - [测验 4：Source replacement 会改变 crate 名称或版本要求吗？](#测验-4source-replacement-会改变-crate-名称或版本要求吗)
  - [权威来源索引](#权威来源索引)

---

## 一、Registry 是什么

Registry 是托管 Rust crate 包与元数据的服务。最权威、最常用的 registry 是 **crates.io**。

一个 registry 至少提供：

- **Index（索引）**: 包含所有 crate 的版本、依赖、features 等元数据；
- **Crate Storage**: 实际的 `.crate` 文件（tar.gz 格式）。

Cargo 通过索引找到可用版本，通过 crate 存储下载源码。

---

## 二、Registry 索引协议

从 Cargo 1.70 开始，默认使用 **sparse 协议**，替代了旧的 git 协议：

| 协议 | 机制 | 优点 |
|:---|:---|:---|
| **Sparse (HTTP)** | 按需下载 `index.crates.io/...` 下的单个索引文件 | 更快、无需完整 git clone |
| **Git** | 克隆整个 git 仓库作为索引 | 完整历史、离线可用 |

```toml
# ~/.cargo/config.toml 中切换回 git 协议（通常不需要）
[registries.crates-io]
protocol = "git"
```

> **状态**: Rust 1.96 默认使用 sparse 协议。
>
> [Cargo Book — Registry Protocols](https://doc.rust-lang.org/cargo/reference/registry-index.html)(<https://doc.rust-lang.org/cargo/reference/registries.html#registry-protocols>)

---

## 三、发布流程：cargo publish

### 3.1 准备工作

```bash
# 1. 登录 crates.io（浏览器打开获取 API token）
cargo login <your-api-token>

# 2. 检查包内容
cargo package --list

# 3. 本地预发布检查
cargo publish --dry-run

# 4. 正式发布
cargo publish
```

### 3.2 Cargo.toml 必填字段

```toml
[package]
name = "my-crate"
version = "0.1.0"
edition = "2024"
license = "MIT OR Apache-2.0"
description = "A short description"
authors = ["Your Name <you@example.com>"]
repository = "https://github.com/you/my-crate"
rust-version = "1.96.1"
```

> **注意**: crates.io 要求 `license` 或 `license-file` 至少一个。
>
> [Cargo Book — Publishing on crates.io](https://doc.rust-lang.org/cargo/reference/publishing.html)(<https://doc.rust-lang.org/cargo/reference/publishing.html>)

---

## 四、Yank 与 Owner 管理

### 4.1 Yank（撤回）

```bash
# 撤回某个版本
cargo yank --vers 0.1.0

# 撤销撤回（24 小时内可恢复）
cargo yank --vers 0.1.0 --undo
```

- Yank 不会删除源码或已下载的 crate；
- 已有 `Cargo.lock` 的项目仍可继续构建；
- 新项目执行解析时不会再选择 yanked 版本。

### 4.2 Owner 管理

```bash
# 添加 owner（用户或团队）
cargo owner --add github:rust-lang:libs

# 移除 owner
cargo owner --remove github:rust-lang:libs

# 列出 owner
cargo owner --list
```

---

## 五、认证与 Token

Cargo 支持多种 token 存储方式：

| 方式 | 命令/配置 |
|:---|:---|
| 明文存储在 `~/.cargo/credentials.toml` | `cargo login <token>` |
| 使用凭据提供者 | `[registry.global-credential-providers]` |
| 通过 `CARGO_REGISTRY_TOKEN` 环境变量 |  CI/CD 常用 |

> **安全建议**: 在 CI 中使用环境变量或凭据提供者，避免把 token 提交到仓库。
>
> [Cargo Book — Authentication](https://doc.rust-lang.org/cargo/reference/authentication.html)(<https://doc.rust-lang.org/cargo/reference/config.html#credentials>)

---

## 六、私有 Registry 与 Source Replacement

### 6.1 配置私有 Registry

```toml
# ~/.cargo/config.toml
[registries.my-company]
index = "sparse+https://crates.my-company.com/git/index/"
```

在 `Cargo.toml` 中引用（Reference）：

```toml
[dependencies]
internal-utils = { version = "1.0", registry = "my-company" }
```

### 6.2 Source Replacement（源替换）

可以把 crates.io 替换为镜像或本地路径：

```toml
# ~/.cargo/config.toml
[source.crates-io]
replace-with = 'my-mirror'

[source.my-mirror]
registry = "sparse+https://mirrors.my-company.com/crates.io-index/"
```

> **注意**: Source replacement 只影响索引和下载位置，不改变 crate 名称或版本要求。
>
> [Cargo Book — Source Replacement](https://doc.rust-lang.org/cargo/reference/source-replacement.html)(<https://doc.rust-lang.org/cargo/reference/source-replacement.html>)

---

## 七、发布前的检查清单

```markdown
- [ ] `Cargo.toml` 包含 `name`、`version`、`edition`、`license`、`description`
- [ ] `README.md` 和 CHANGELOG 已更新
- [ ] 已运行 `cargo test` 并通过
- [ ] 已运行 `cargo clippy` 无警告
- [ ] 已运行 `cargo publish --dry-run` 成功
- [ ] API 文档 `cargo doc` 无 broken intra-doc links
- [ ] 版本号符合 SemVer 规范
- [ ] 若存在破坏性变更，已升级主版本号
```

---

## 嵌入式测验

### 测验 1：sparse 协议相比 git 协议的主要优势是什么？

<details>
<summary>✅ 答案与解析</summary>

Sparse 协议按需下载单个索引文件，无需克隆整个 git 仓库，速度更快、占用空间更少。

</details>

---

### 测验 2：`cargo yank` 会删除已经发布的 crate 源码吗？

<details>
<summary>✅ 答案与解析</summary>

不会。Yank 只是标记该版本不再用于新的依赖解析，已有 `Cargo.lock` 的项目仍可继续下载和构建。

</details>

---

### 测验 3：发布 crate 到 crates.io 时，`license` 字段是必须的吗？

<details>
<summary>✅ 答案与解析</summary>

是的，必须提供 `license` 或 `license-file` 之一，否则 `cargo publish` 会被拒绝。

</details>

---

### 测验 4：Source replacement 会改变 crate 名称或版本要求吗？

<details>
<summary>✅ 答案与解析</summary>

不会。Source replacement 只改变索引和下载源的位置，crate 名称、版本要求和依赖解析逻辑保持不变。

</details>

---

## 权威来源索引

| 来源 | 可信度 | 说明 |
|:---|:---:|:---|
| [Cargo Book — Publishing on crates.io](https://doc.rust-lang.org/cargo/reference/publishing.html) | ✅ 一级 | 发布流程官方文档 |
| [Cargo Book — Cargo Registries](https://doc.rust-lang.org/cargo/reference/registries.html) | ✅ 一级 | Registry 官方文档 |
| [Cargo Book — Source Replacement](https://doc.rust-lang.org/cargo/reference/source-replacement.html) | ✅ 一级 | 源替换官方文档 |
| [Cargo Book — Authentication](https://doc.rust-lang.org/cargo/reference/config.html#credentials) | ✅ 一级 | 认证官方文档 |

---

> **权威来源**: [Cargo Book](https://doc.rust-lang.org/cargo/index.html), [crates.io policies](https://crates.io/policies), [The Rust Reference](https://doc.rust-lang.org/reference/introduction.html)
> **权威来源对齐变更日志**: 2026-06-21 创建，对齐 Rust 1.96.1 / sparse registry 默认

**文档版本**: 1.0
**对应 Rust 版本**: 1.96.1+ (Edition 2024)
**最后更新**: 2026-06-21
**状态**: ✅ 已对齐 Cargo Book registry/publishing 文档
