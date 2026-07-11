# Cargo Registry 内部机制（Cargo Registry Internals）

> **内容分级**: [参考级]
> **本节关键术语**: Registry Index · Registry Web API · Credential Provider · crates.io · Sparse Index — [完整对照表](../../00_meta/01_terminology/terminology_glossary.md)
>
> **EN**: Cargo Registry Internals
> **Summary**: How Cargo registries work internally for Rust 1.97.0+: sparse vs git index, index entry format, Web API, credential provider protocol, publishing pipeline, and self-hosted registry design.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **受众**: [专家]
> **Bloom 层级**: L2-L4
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **P** — Practice
> **双维定位**: E×Tool — 工具链与生态系统
> **定位**: 为需要自建 registry、审计依赖来源或集成内部凭证系统的团队提供权威参考。
> **前置概念**: [Cargo Registries and Publishing](62_cargo_registries_and_publishing.md) · [Cargo Authentication and Cache](63_cargo_authentication_and_cache.md) · [Cargo Configuration](83_cargo_configuration.md)
> **后置概念**: [Cargo Commands Reference](84_cargo_commands_reference.md) · [Security Practices](../07_security_and_cryptography/19_security_practices.md)

---

> **来源**: [Cargo Book — Registries](https://doc.rust-lang.org/cargo/reference/registries.html) · [Cargo Book — Running a Registry](https://doc.rust-lang.org/cargo/reference/running-a-registry.html) · [Cargo Book — Registry Authentication](https://doc.rust-lang.org/cargo/reference/registry-authentication.html) · [Cargo Book — Registry Index Format](https://doc.rust-lang.org/cargo/reference/registry-index.html)

---

## 一、Registry 组件

一个 Cargo registry 至少包含：

| 组件 | 说明 |
|:---|:---|
| Index | 按 crate 名分片的元数据仓库 |
| Crate Storage | 实际的 `.crate` 文件（tar.gz） |
| Web API | 处理 publish、yank、owner、搜索 |
| Authentication | 验证发布者身份与权限 |

## 二、Registry Index

Registry index 是一个 git 仓库或 HTTP 索引，按 crate 名分片存储元数据：

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
  "yanked": false,
  "rust_version": "1.56",
  "pubtime": "2024-05-01T12:00:00Z"
}
```

从 Rust 1.70 起，Cargo 默认使用 **sparse index**（HTTP 增量拉取），减少 git clone 开销。

## 三、Sparse vs Git Index

| 维度 | Sparse Index | Git Index |
|:---|:---|:---|
| 协议 | HTTP 按需下载 | Git 完整克隆 |
| 启动延迟 | 低 | 高（首次 clone） |
| 磁盘占用 | 小 | 大（完整历史） |
| 离线能力 | 依赖本地缓存 | 完整仓库可离线浏览 |
| 默认状态 | Rust 1.70+ 默认 | 可手动切换 |

切换回 git 协议：

```toml
[registries.crates-io]
protocol = "git"
```

## 四、Registry Web API

crates.io 提供 REST API 支持：

| 端点 | 作用 |
|:---|:---|
| `PUT /api/v1/crates/new` | 上传 crate |
| `DELETE /api/v1/crates/{name}/{version}/yank` | yank 版本 |
| `PUT /api/v1/crates/{name}/{version}/unyank` | 撤销 yank |
| `GET /api/v1/crates/{name}` | 查询 crate 信息 |
| `GET /api/v1/crates/{name}/owners` | 查询所有者 |

自建 registry 可实现兼容子集。

## 五、Credential Provider 协议

Cargo 通过外部凭证提供程序安全获取 registry token：

```toml
[registry]
global-credential-providers = ["cargo:token", "my-provider"]
```

提供程序通过标准输入输出与 Cargo 交互，避免将 token 明文写入磁盘。自定义 provider 需实现 [Credential Provider Protocol](https://doc.rust-lang.org/cargo/reference/credential-provider-protocol.html)。

## 六、自建 Registry 要点

| 组件 | 说明 |
|:---|:---|
| Index 仓库 | 存储 crate 元数据 |
| 存储后端 | 存放 `.crate` 文件 |
| Web API | 处理 publish/yank/owner |
| 认证层 | 验证用户身份与权限 |

常用开源/商业方案：

- **crates.io** 本身（开源但针对官方场景）
- **Kellnr**
- **Cloudsmith / Artifactory** 商业方案

## 七、发布流程与校验

```bash
# 1. 本地打包
cargo package --list

# 2. 预发布检查
cargo publish --dry-run

# 3. 正式发布
cargo publish
```

发布时 Cargo 会：

1. 读取 `Cargo.toml` 元数据；
2. 打包符合 `include`/`exclude` 的文件；
3. 计算 tarball 的 SHA-256 校验和；
4. 上传 `.crate` 文件与元数据到 registry；
5. Registry 更新 index。

## 八、与 Source Replacement 的关系

`[source]` 与 `[registries]` 配置可让企业将 crates.io 替换为内部 registry，同时保留原始 package 的 identity。详见 [Cargo Source Replacement](61_cargo_source_replacement.md)。

## 九、Registry 部署模式决策表

| 场景 | 推荐方案 |
|:---|:---|
| 公共开源 crate | crates.io |
| 企业内部私有 crate | 私有 registry（Kellnr / Artifactory） |
| 离线/审计 | `cargo vendor` + directory source |
| 仅加速下载 | Source replacement / 镜像 |
| 完整控制依赖来源 | 自建 registry + source replacement |

想要体验 resolver v3 与 `public = true` 的 workspace 示例，可查看 [`crates/c17_resolver_v3_public_demo`](../../../crates/c17_resolver_v3_public_demo/)。

> **L5 对比**: [Rust vs C++](../../05_comparative/01_systems_languages/01_rust_vs_cpp.md) · [Rust vs Go](../../05_comparative/01_systems_languages/02_rust_vs_go.md)

---

> **权威来源**: [Cargo Book — Running a Registry](https://doc.rust-lang.org/cargo/reference/running-a-registry.html)

---

## 国际权威参考 / International Authority References（P0 官方 · P1 学术 · P2 生态）

> 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。

- **P1 学术/形式化**: [Rudra: Finding Memory Safety Bugs in Rust at the Ecosystem Scale (SOSP 2021)](https://dl.acm.org/doi/10.1145/3477132.3483570)
