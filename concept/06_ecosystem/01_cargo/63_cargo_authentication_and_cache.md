> **内容分级**: [综述级]
> **本节关键术语**: Credential Provider · `cargo:token` · `CARGO_HOME` · Build Cache · Target Dir · Build Dir · Dep-info · `sccache` · Registry Token — [完整对照表](../../00_meta/01_terminology/terminology_glossary.md)
>
# Cargo 认证与构建缓存

> **EN**: Cargo Authentication and Build Cache
> **Summary**: Explains Cargo's credential provider system, token storage options, registry authentication, and the layout of `CARGO_HOME`, target/build directories, dep-info files, and shared caches like sccache.
> **受众**: [中级 → 高级]
> **Bloom 层级**: 理解 → 应用
> **A/S/P 标记**: **P** — Practice
> **双维定位**: E×Tool — 工具链与生态系统
> **定位**: 把“Cargo 如何安全地存 token、如何组织缓存、如何加速构建”系统化，补齐 registry 之后的工程实践闭环。
> **前置概念**: [Rust vs C++](../../05_comparative/01_systems_languages/01_rust_vs_cpp.md)
> **后置概念**: [Cargo Security CVEs](72_cargo_security_cves.md) · [DevOps and CI/CD](../00_toolchain/28_devops_and_ci_cd.md)

---

> **来源**: [Cargo — Registry Authentication](https://doc.rust-lang.org/cargo/reference/registry-authentication.html) · [Cargo — Configuration](https://doc.rust-lang.org/cargo/reference/config.html) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
> [Cargo Book — Cargo Home](https://doc.rust-lang.org/cargo/guide/cargo-home.html) ·
> [Cargo Book — Build Cache](https://doc.rust-lang.org/cargo/reference/build-cache.html) ·
> [Cargo Book — Config — Credentials](https://doc.rust-lang.org/cargo/reference/config.html#credentials)

---

> **过渡**: 从 Cargo 认证与构建缓存 的直观描述转向其形式化定义，需要先把日常经验中的模糊直觉转化为可验证的术语。

> **过渡**: 在建立 Cargo 认证与构建缓存 的核心命题之后，下一步是审视这些命题在边界条件下的稳定性——这正是反命题与反例的价值所在。

> **过渡**: 最后，将 Cargo 认证与构建缓存 与相邻概念连接，形成从 L1 到 L7 的纵向认知路径，避免孤立记忆。

---

> **定理 1** [Tier 2]: Cargo 认证与构建缓存 的核心约束 ⟹ 编译器可以在编译期排除一整类运行时（Runtime）错误。
>
> **定理 2** [Tier 2]: 正确理解 Cargo 认证与构建缓存 的语义 ⟹ 开发者能够写出既安全又零成本抽象（Zero-Cost Abstraction）的代码。
>
> **定理 3** [Tier 3]: 将 Cargo 认证与构建缓存 与 Rust 的所有权（Ownership）/生命周期（Lifetimes）模型结合 ⟹ 可以在更大系统中进行可扩展的推理。

## 📑 目录

- [Cargo 认证与构建缓存](#cargo-认证与构建缓存)
  - [📑 目录](#-目录)
  - [一、Registry 认证概述](#一registry-认证概述)
  - [二、Credential Providers](#二credential-providers)
    - [2.1 内置 Providers](#21-内置-providers)
    - [2.2 推荐全局配置](#22-推荐全局配置)
  - [三、Token 的存储与使用](#三token-的存储与使用)
    - [3.1 `cargo login`](#31-cargo-login)
    - [3.2 环境变量](#32-环境变量)
    - [3.3 自定义 Provider](#33-自定义-provider)
  - [四、`CARGO_HOME` 目录结构](#四cargo_home-目录结构)
  - [五、Target Dir 与 Build Dir](#五target-dir-与-build-dir)
    - [5.1 `target/` 目录](#51-target-目录)
    - [5.2 目录布局](#52-目录布局)
    - [5.3 Build Dir（中间产物）](#53-build-dir中间产物)
  - [六、Dep-info 文件](#六dep-info-文件)
  - [七、共享缓存：`sccache`](#七共享缓存sccache)
  - [嵌入式测验](#嵌入式测验)
    - [测验 1：为什么认证 registry 必须配置 credential provider？](#测验-1为什么认证-registry-必须配置-credential-provider)
    - [测验 2：`cargo:token` provider 有什么安全注意事项？](#测验-2cargotoken-provider-有什么安全注意事项)
    - [测验 3：`CARGO_REGISTRIES_<NAME>_TOKEN` 环境变量什么时候生效？](#测验-3cargo_registries_name_token-环境变量什么时候生效)
    - [测验 4：`sccache` 与普通 Cargo 缓存有什么区别？](#测验-4sccache-与普通-cargo-缓存有什么区别)
  - [权威来源索引](#权威来源索引)

---

## 一、Registry 认证概述

访问需要认证的 registry（如私有 registry 或 crates.io 发布）时，Cargo 需要 token。Cargo 通过 **credential providers** 来存取 token：

- 每个 provider 是一个可执行程序或内置 provider；
- provider 负责安全地存储和检索 token；
- 使用认证 registry **必须**配置 credential provider（公共 registry 除外）。

> [Cargo Book — Registry Authentication](https://doc.rust-lang.org/cargo/reference/authentication.html)(<https://doc.rust-lang.org/cargo/reference/registry-authentication.html>)

---

## 二、Credential Providers

### 2.1 内置 Providers

| Provider | 平台 | 说明 |
|:---|:---|:---|
| `cargo:token` | 全平台 | 明文存储在 `credentials.toml`，环境变量也走它 |
| `cargo:wincred` | Windows | Windows Credential Manager |
| `cargo:macos-keychain` | macOS | macOS Keychain |
| `cargo:libsecret` | Linux | GNOME Keyring / KDE Wallet / KeePassXC 等 |
| `cargo:token-from-stdout <cmd>` | 全平台 | 从子进程 stdout 读取 token |

### 2.2 推荐全局配置

```toml
# ~/.cargo/config.toml
[registry]
global-credential-providers = [
    "cargo:token",
    "cargo:libsecret",
    "cargo:macos-keychain",
    "cargo:wincred",
]
```

> **注意**: 列表中越靠后的 provider 优先级越高。
>
> [Cargo Book — Recommended configuration](https://doc.rust-lang.org/cargo/reference/config.html)(<https://doc.rust-lang.org/cargo/reference/registry-authentication.html#recommended-configuration>)

---

## 三、Token 的存储与使用

### 3.1 `cargo login`

```bash
# 登录 crates.io，token 会写入当前 credential provider
cargo login <token>

# 登出
cargo logout
```

### 3.2 环境变量

```bash
export CARGO_REGISTRIES_MYREGISTRY_TOKEN="my-token"
```

> **重要**: 只有 `cargo:token` provider 被配置时，环境变量才会生效。

### 3.3 自定义 Provider

```toml
[registry]
global-credential-providers = ["cargo-credential-1password --account my.1password.com"]
```

自定义 provider 必须实现 [Credential Provider Protocol](https://doc.rust-lang.org/cargo/reference/credential-provider-protocol.html)。

---

## 四、`CARGO_HOME` 目录结构

`CARGO_HOME` 默认是 `~/.cargo`（Windows: `%USERPROFILE%\.cargo`）：

```text
~/.cargo/
├── bin/              # cargo install 安装的二进制
├── config.toml       # 全局配置
├── credentials.toml  # cargo:token 明文凭证（如使用）
├── registry/
│   ├── cache/        # 下载的 .crate 文件
│   ├── index/        # registry 索引（sparse 或 git）
│   └── src/          # 解压后的 crate 源码
└── git/
    ├── checkouts/    # git 依赖的检出目录
    └── db/           # git 依赖的 bare 仓库
```

> [Cargo Book — Cargo Home](https://doc.rust-lang.org/cargo/reference/config.html#credentialstransport)(<https://doc.rust-lang.org/cargo/guide/cargo-home.html>)

---

## 五、Target Dir 与 Build Dir

### 5.1 `target/` 目录

默认位于工作区根目录，可通过以下方式修改：

- `CARGO_TARGET_DIR` 环境变量
- `build.target-dir` 配置
- `--target-dir` 命令行参数

### 5.2 目录布局

```text
target/
├── debug/            # dev / test profile
├── release/          # release / bench profile
├── doc/              # cargo doc 输出
├── package/          # cargo package 输出
└── <triple>/         # 指定 --target 时
    ├── debug/
    └── release/
```

### 5.3 Build Dir（中间产物）

Rust 1.96+ 把中间产物（如 `deps/`、`incremental/`、`build/`）放到独立的 build dir，默认与 target dir 相同。可通过 `CARGO_BUILD_BUILD_DIR` 或 `build.build-dir` 单独配置。

> [Cargo Book — Build Cache](https://doc.rust-lang.org/cargo/reference/build-cache.html)(<https://doc.rust-lang.org/cargo/reference/build-cache.html>)

---

## 六、Dep-info 文件

每个编译产物旁边都有一个 `.d` 文件，记录该产物的所有源文件依赖：

```makefile
# target/debug/foo.d
/path/to/myproj/target/debug/foo: /path/to/myproj/src/lib.rs /path/to/myproj/src/main.rs
```

用途：

- 外部构建系统判断是否需要重新调用 Cargo；
- 可通过 `build.dep-info-basedir` 改成相对路径。

---

## 七、共享缓存：`sccache`

`sccache` 是 Mozilla 提供的编译缓存，可跨工作区共享构建结果：

```bash
# 安装
cargo install sccache

# 启用（bash 可放入 .bashrc）
export RUSTC_WRAPPER=sccache

# 或通过 Cargo 配置
[build]
rustc-wrapper = "sccache"
```

> **收益**: 在 CI 或多项目开发中显著减少重复编译时间。

---

## 嵌入式测验

### 测验 1：为什么认证 registry 必须配置 credential provider？

<details>
<summary>✅ 答案与解析</summary>

为了避免 token 被无意中以明文形式存储在磁盘上。Credential provider 负责安全地存取 token。

</details>

---

### 测验 2：`cargo:token` provider 有什么安全注意事项？

<details>
<summary>✅ 答案与解析</summary>

`cargo:token` 把 token 以明文形式存储在 `credentials.toml` 中，不如 OS keychain/libsecret 安全，但兼容性最好，也支持环境变量。

</details>

---

### 测验 3：`CARGO_REGISTRIES_<NAME>_TOKEN` 环境变量什么时候生效？

<details>
<summary>✅ 答案与解析</summary>

只有 `cargo:token` provider 被配置在 `global-credential-providers` 中时，对应的环境变量才会被读取。

</details>

---

### 测验 4：`sccache` 与普通 Cargo 缓存有什么区别？

<details>
<summary>✅ 答案与解析</summary>

普通 Cargo 缓存只在一个工作区内共享；`sccache` 作为 `RUSTC_WRAPPER` 可跨多个工作区甚至 CI 环境共享编译结果。

</details>

---

## 权威来源索引

| 来源 | 可信度 | 说明 |
|:---|:---:|:---|
| [Cargo Book — Registry Authentication](https://doc.rust-lang.org/cargo/reference/registry-authentication.html) | ✅ 一级 | Registry 认证官方文档 |
| [Cargo Book — Cargo Home](https://doc.rust-lang.org/cargo/guide/cargo-home.html) | ✅ 一级 | CARGO_HOME 官方文档 |
| [Cargo Book — Build Cache](https://doc.rust-lang.org/cargo/reference/build-cache.html) | ✅ 一级 | 构建缓存官方文档 |
| [Cargo Book — Config — Credentials](https://doc.rust-lang.org/cargo/reference/config.html#credentials) | ✅ 一级 | 凭证配置官方文档 |

---

> **权威来源**: [Cargo Book](https://doc.rust-lang.org/cargo/index.html), [The Rust Reference](https://doc.rust-lang.org/reference/introduction.html)
> **权威来源对齐变更日志**: 2026-06-21 创建，对齐 Rust 1.96.1 / Cargo 认证与缓存文档

**文档版本**: 1.0
**对应 Rust 版本**: 1.96.1+ (Edition 2024)
**最后更新**: 2026-06-21
**状态**: ✅ 已对齐 Cargo Book authentication/cache 文档
