# Cargo Workspaces（工作区）

> **内容分级**: [综述级]
> **本节关键术语**: Workspace · Root Package · Virtual Workspace · Workspace Inheritance · `workspace.package` · `workspace.dependencies` · `workspace.lints` · `default-members` · `resolver` — [完整对照表](../../00_meta/01_terminology/01_terminology_glossary.md)
>
> **EN**: Cargo Workspaces
> **Summary**: Cargo workspace 的组成方式：root package 与 virtual workspace、`members`/`exclude`/`default-members`、`workspace.package`/`workspace.dependencies`/`workspace.lints` 继承机制，以及 resolver 设置。
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **受众**: [中级 → 高级]
> **Bloom 层级**: L2-L3
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **A** — Application
> **双维定位**: E×Tool — 工具链与生态系统
> **定位**: 把“何时该用 workspace、如何组织多 crate 项目、如何统一依赖与 lint 配置”讲清楚。
> **前置概念**: [Cargo Dependency Resolution](06_cargo_dependency_resolution.md) · [Cargo Manifest Reference](10_cargo_manifest_reference.md) · [Terminology Glossary](../../00_meta/01_terminology/01_terminology_glossary.md)
> **后置概念**: [Cargo Profiles and Lints](11_cargo_profiles_and_lints.md) · [Cargo Registries and Publishing](08_cargo_registries_and_publishing.md) · [Rust vs C++](../../05_comparative/01_systems_languages/01_rust_vs_cpp.md)

---

> **来源**: [Cargo Book — Workspaces](https://doc.rust-lang.org/cargo/reference/workspaces.html) · · [Rust Reference](https://doc.rust-lang.org/reference/introduction.html) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
> [Cargo Book — The Manifest Format](https://doc.rust-lang.org/cargo/reference/manifest.html) ·
> [Cargo Book — Resolver versions](https://doc.rust-lang.org/cargo/reference/resolver.html#resolver-versions)

---

## 一、什么是 Workspace

**Workspace（工作区）** 是一组被一起管理的 package，称为 **workspace members**。使用 workspace 的核心收益：

- 一条命令作用于所有成员，例如 `cargo check --workspace`、`cargo test --workspace`。
- 所有成员共享 workspace root 下的 **同一个 `Cargo.lock`**。
- 所有成员共享 workspace root 下的 **同一个 `target` 输出目录**。
- 通过 `workspace.package`、`workspace.dependencies`、`workspace.lints` 在成员间共享元数据和配置。
- `[patch]`、`[replace]`、`[profile.*]` 只在 **root manifest** 中生效，成员 crate 中的这些段被忽略。

---

## 二、Root Package vs Virtual Workspace

本节围绕「Root Package vs Virtual Works…」展开，覆盖 Root package 与  Virtual workspace 两个方面。

### Root package

如果 `Cargo.toml` 中同时存在 `[workspace]` 和 `[package]`，则该 package 是 workspace 的 **root package**。

```toml
[workspace]
members = ["crates/*"]

[package]
name = "my_app"
version = "0.1.0"
edition = "2024"
```

### Virtual workspace

`Cargo.toml` 中只有 `[workspace]` 而没有 `[package]`，称为 **virtual manifest**。适用于没有“主 package”、所有 package 平级组织的场景。

```toml
[workspace]
members = ["crates/*"]
resolver = "3"
```

> **注意**：virtual workspace 必须显式设置 `resolver`，因为没有 `package.edition` 可供推断 resolver 版本。

---

## 三、`members` 与 `exclude`

```toml
[workspace]
members = ["member1", "path/to/member2", "crates/*"]
exclude = ["crates/foo", "path/to/other"]
```

- `members`：显式列出 workspace 成员路径，支持 glob（`*`、`?`）。
- `exclude`：排除不想纳入 workspace 的路径。
- 位于 workspace 目录内的 `path` 依赖会自动成为成员。
- Cargo 会从当前目录向上搜索包含 `[workspace]` 的 `Cargo.toml`；成员 crate 可通过 `package.workspace` 手动指向 workspace root。

---

## 四、`default-members`

当在 workspace root 运行 `cargo build` 等命令且未使用 `-p`/`--package`/`--workspace` 时，Cargo 使用 `default-members`。

```toml
[workspace]
members = ["path/to/member1", "path/to/member2", "path/to/member3/*"]
default-members = ["path/to/member2", "path/to/member3/foo"]
```

- 如果存在 root package，默认使用 root package（可用 `--package` 或 `--workspace` 覆盖）。
- 如果是 virtual workspace 且未指定 `default-members`，则默认作用于所有成员（等效 `--workspace`）。

---

## 五、`workspace.package` 继承

在 workspace root 定义通用 package 元数据，成员通过 `{key}.workspace = true` 继承。

```toml
# [PROJECT_DIR]/Cargo.toml
[workspace]
members = ["bar"]

[workspace.package]
version = "1.2.3"
authors = ["Nice Folks"]
description = "A short description"
documentation = "https://example.com/bar"
edition = "2024"
rust-version = "1.78"
```

```toml
# [PROJECT_DIR]/bar/Cargo.toml
[package]
name = "bar"
version.workspace = true
authors.workspace = true
description.workspace = true
documentation.workspace = true
edition.workspace = true
```

支持的 key：

`authors`, `categories`, `description`, `documentation`, `edition`, `exclude`, `homepage`, `include`, `keywords`, `license`, `license-file`, `publish`, `readme`, `repository`, `rust-version`, `version`。

> **MSRV**: Requires 1.64+

---

## 六、`workspace.dependencies` 继承

在 workspace root 统一声明依赖版本，成员通过 `workspace = true` 继承。

```toml
# [PROJECT_DIR]/Cargo.toml
[workspace]
members = ["bar"]

[workspace.dependencies]
serde = { version = "1.0", features = ["derive"] }
tokio = { version = "1.40", default-features = false }
```

```toml
# [PROJECT_DIR]/bar/Cargo.toml
[package]
name = "bar"

[dependencies]
serde = { workspace = true, features = ["std"] }
tokio = { workspace = true, features = ["rt-multi-thread"] }
```

> **注意**：
>
> - `workspace.dependencies` 中的依赖不能声明为 `optional`。
> - 此处声明的 `features` 会与成员 `[dependencies]` 中声明的 `features` **叠加**。

> **MSRV**: Requires 1.64+

---

## 七、`workspace.lints` 继承

在 workspace root 统一配置 lint，成员通过 `[lints] workspace = true` 继承。

```toml
# [PROJECT_DIR]/Cargo.toml
[workspace]
members = ["crates/*"]

[workspace.lints.rust]
unsafe_code = "forbid"
unreachable_pub = "warn"

[workspace.lints.clippy]
needless_return = "warn"
```

```toml
# [PROJECT_DIR]/crates/bar/Cargo.toml
[package]
name = "bar"

[lints]
workspace = true
```

> **MSRV**: Respected as of 1.74

---

## 八、Resolver 设置

Workspace root 的 `resolver` 字段决定整个 workspace 使用的依赖解析器版本。

```toml
[workspace]
members = ["crates/*"]
resolver = "3"
```

| 场景 | 推断/要求 |
|:---|:---|
| Root package 未指定 `resolver` | 根据 `package.edition` 推断：`2021` → resolver 2，`2024` → resolver 3 |
| Virtual workspace 未指定 `resolver` | 必须显式设置，否则 Cargo 会报错 |
| 显式指定 `resolver = "3"` | 覆盖 edition 推断 |

> 详见 [Cargo Dependency Resolution](06_cargo_dependency_resolution.md) 中“Resolver 版本差异”一节。

---

## 九、`workspace.metadata`

`workspace.metadata` 被 Cargo 忽略，供外部工具存储 workspace 级配置。

```toml
[workspace]
members = ["member1", "member2"]

[workspace.metadata.webcontents]
root = "path/to/webproject"
tool = ["npm", "run", "build"]
```

> 对应还有 `package.metadata`，外部工具通常可约定：若 `package.metadata` 缺失，回退到 `workspace.metadata`。

---

## 十、实践建议

1. **多 crate 项目优先使用 workspace**：避免重复依赖、统一 lockfile、加速增量编译。
2. **Virtual workspace 适合“平台型”仓库**：没有单一主 crate，多个 crate 平行发展。
3. **Root package 适合“应用 + 库”仓库**：顶层是最终可执行程序，子目录是内部库。
4. **统一依赖版本**：将常用依赖放在 `workspace.dependencies`，成员只声明 `workspace = true`。
5. **显式设置 `resolver = "3"`**：在 virtual workspace 或跨 edition 混合时避免意外回退到旧解析器。
6. **善用 `default-members`**：在大型 monorepo 中减少默认构建范围，提升日常反馈速度。

---

## 十一、相关概念

| 概念 | 关系 |
|:---|:---|
| [Cargo Dependency Resolution](06_cargo_dependency_resolution.md) | workspace 共享一个 `Cargo.lock` 和 resolver |
| [Cargo Manifest Reference](10_cargo_manifest_reference.md) | workspace 成员仍遵循 manifest 格式 |
| [Cargo Profiles and Lints](11_cargo_profiles_and_lints.md) | `[profile]` 和 `[workspace.lints]` 在 workspace root 生效 |
| [Cargo Source Replacement](07_cargo_source_replacement.md) | `[patch]`/`[replace]` 只在 workspace root 生效 |

---

## 国际权威参考 / International Authority References（P1 学术 · P2 生态）

> 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。

- **P2 生态/社区**: [docs.rs/toml — 生态权威 API 文档](https://docs.rs/toml) · [docs.rs/cargo_metadata — 生态权威 API 文档](https://docs.rs/cargo_metadata)
