# Cargo Registry 内部机制（Cargo Registry Internals）

> **内容分级**: [参考级]
> **本节关键术语**: Registry Index · Registry Web API · Credential Provider · crates.io · Sparse Index — [完整对照表](../00_meta/01_terminology/terminology_glossary.md)
>
> **EN**: Cargo Registry Internals
> **Summary**: Cargo registry 的运行机制：索引格式、Web API、凭证提供程序协议，以及企业自建 registry 所需的核心概念。
> **受众**: [专家]
> **Bloom 层级**: 理解 → 分析
> **A/S/P 标记**: **P** — Practice
> **双维定位**: E×Tool — 工具链与生态系统
> **定位**: 为需要自建 registry、审计依赖来源或集成内部凭证系统的团队提供权威参考。
> **前置概念**: [Cargo Registries and Publishing](62_cargo_registries_and_publishing.md) · [Cargo Authentication and Cache](63_cargo_authentication_and_cache.md) · [Cargo Configuration](83_cargo_configuration.md)
> **后置概念**: [Cargo Commands Reference](84_cargo_commands_reference.md) · [Security Practices](19_security_practices.md)

---

> **来源**: [Cargo Book — Registries](https://doc.rust-lang.org/cargo/reference/registries.html) · · [Rust Reference](https://doc.rust-lang.org/reference/) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
> [Cargo Book — Running a Registry](https://doc.rust-lang.org/cargo/reference/running-a-registry.html) ·
> [Cargo Book — Registry Authentication](https://doc.rust-lang.org/cargo/reference/registry-authentication.html) ·
> [Cargo Book — Registry Index Format](https://doc.rust-lang.org/cargo/reference/registry-index.html)

---

## 一、Registry Index

Registry index 是一个 git 仓库，按 crate 名分片存储元数据：

```text
3/
  /a/
    serde
```

每个文件包含该 crate 所有版本的 JSON 记录：

```json
{
  "name": "serde",
  "vers": "1.0.200",
  "deps": [...],
  "cksum": "sha256-hash",
  "features": {...},
  "yanked": false
}
```

现代 Cargo 支持 **sparse index**（HTTP 增量拉取），减少 git clone 开销。

## 二、Registry Web API

crates.io 提供 REST API 支持：

- 上传 crate (`/api/v1/crates/new`)
- yank/unyank
- 管理 owners
- 搜索 crate

自建 registry 可实现兼容子集。

## 三、Credential Provider 协议

Cargo 通过外部凭证提供程序安全获取 registry token：

```toml
[registry]
global-credential-providers = ["cargo:token", "my-provider"]
```

提供程序通过标准输入输出与 Cargo 交互，避免将 token 明文写入磁盘。

## 四、自建 Registry 要点

| 组件 | 说明 |
|:---|:---|
| Index 仓库 | 存储 crate 元数据 |
| 存储后端 | 存放 `.crate` 文件 |
| Web API | 处理 publish/yank/owner |
| 认证层 | 验证用户身份与权限 |

常用开源方案：

- **crates.io** 本身（开源但针对官方场景）
- **Kellnr**
- **Cloudsmith / Artifactory** 商业方案

## 五、与 Source Replacement 的关系

`[source]` 与 `[registries]` 配置可让企业将 crates.io 替换为内部 registry，同时保留原始 package 的 identity。

详见 [Cargo Source Replacement](61_cargo_source_replacement.md)。

---

> **权威来源**: [Cargo Book — Running a Registry](https://doc.rust-lang.org/cargo/reference/running-a-registry.html)
> **内容分级**: [参考级]
