> **内容分级**: [实践级]

# Resolver v3 与 `public = true` 的 feature unification 演示

> **EN**: Resolver v3 and `public = true` Feature-Unification Demo
> **Summary**: A runnable workspace example showing how Cargo resolver v3 and `public = true` interact with feature unification: crate A depends on B and C; B and C publicly depend on D with different features; A also depends on D directly. The resulting `crate-d` is built with the union of all requested features.
> **Rust 版本**: 1.97.0 (stable)
> **受众**: [进阶]
> **Bloom 层级**: L3-L4
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **P** — Practice
> **双维定位**: E×Tool — Cargo 工具链与生态系统
> **定位**: 把“resolver v3 + public dependency”从概念落到可运行的 Cargo workspace，观察 `cargo tree -e features` 的实际输出。
> **前置概念**: [Cargo Dependency Resolution](06_cargo_dependency_resolution.md) · [Cargo `public = true` 与 Resolver v3](02_public_private_deps.md) · [Cargo Workspaces](14_cargo_workspaces.md)
> **后置概念**: [Cargo 1.96 新特性](04_cargo_196_features.md)

---

> **来源**: [Cargo Book — Dependency Resolution](https://doc.rust-lang.org/cargo/reference/resolver.html) · [Cargo Book — Features](https://doc.rust-lang.org/cargo/reference/features.html) · [RFC 3516 — Public & Private Dependencies](https://github.com/rust-lang/rfcs/pull/3516) · [Rust 1.84.0 Release Notes](https://releases.rs/docs/1.84.0/)

---

## 一、示例结构

完整代码位于 [`crates/c17_resolver_v3_public_demo`](../../../crates/c17_resolver_v3_public_demo/)。

```text
crates/c17_resolver_v3_public_demo/
├── Cargo.toml          # Crate A：依赖 B、C 与 D(serde)
├── src/main.rs
├── crate-b/Cargo.toml  # Crate B：public = true，依赖 D(std)
├── crate-c/Cargo.toml  # Crate C：public = true，依赖 D(alloc)
└── crate-d/Cargo.toml  # Crate D：提供 std / alloc / serde feature
```

依赖关系：

```text
A ──► B ──public──► D(std)
│
└──► C ──public──► D(alloc)
│
└──────────────► D(serde)
```

- `crate-b` 将 `crate-d` 声明为 `public = true`，并启用 `std`。
- `crate-c` 将 `crate-d` 声明为 `public = true`，并启用 `alloc`。
- `c17_resolver_v3_public_demo`（Crate A）直接依赖 `crate-d`，并启用 `serde`。

## 二、关键清单片段

resolver v3 的行为差异通过三个 crate 的清单片段展示：Crate B 声明依赖的默认 feature、Crate C 以 `default-features = false` 引用同一依赖、Crate A 同时依赖 B 和 C。v2 解析器会把 B 的默认 feature 统一进 C 的构建（feature 泄漏），v3 则按构建目标隔离 feature 集。阅读顺序：先看 B/C 的声明差异，再看 A 的解析结果对比表——feature 统一的语义变化全部体现在这三段 TOML 的组合效果中。

### Crate B

```toml
[dependencies]
crate-d = { path = "../crate-d", features = ["std"], public = true }
```

### Crate C

```toml
[dependencies]
crate-d = { path = "../crate-d", features = ["alloc"], public = true }
```

### Crate A

```toml
[dependencies]
crate-b = { path = "crate-b" }
crate-c = { path = "crate-c" }
crate-d = { path = "crate-d", features = ["serde"] }
```

## 三、`cargo tree -e features` 输出

在仓库根目录执行：

```bash
cargo tree -p c17_resolver_v3_public_demo -e features
```

得到：

```text
c17_resolver_v3_public_demo v0.1.0 (E:\_src\rust-lang\crates\c17_resolver_v3_public_demo)
├── crate-b feature "default"
│   └── crate-b v0.1.0 (...)
│       ├── crate-d feature "default"
│       │   └── crate-d v0.1.0 (...)
│       └── crate-d feature "std"
│           └── crate-d v0.1.0 (...)
├── crate-d feature "default" (*)
├── crate-d feature "serde"
│   └── crate-d v0.1.0 (...)
└── crate-c feature "default"
    └── crate-c v0.1.0 (...)
        ├── crate-d feature "alloc"
        │   └── crate-d v0.1.0 (...)
        └── crate-d feature "default" (*)
```

观察点：

1. `crate-d` 只出现一次实例（路径相同、版本相同）。
2. B 请求 `std`，C 请求 `alloc`，A 请求 `serde`，三者合并为 `std + alloc + serde`。
3. `(*)` 表示该节点已在树中其他位置出现，Cargo 复用同一编译单元。

## 四、Resolver v3 与 v2 的差异

| 维度 | Resolver v2 | Resolver v3 |
|:---|:---|:---|
| 默认场景 | Edition 2021 | Edition 2024 / 显式 `resolver = "3"` |
| Feature unification | 区分 dev / target / build / proc-macro | 与 v2 一致 |
| MSRV-aware 解析 | 默认 `allow`（忽略 `rust-version`） | 默认 `fallback`（优先满足 `rust-version`） |
| `public = true` | 语法上被忽略 | 语法上被忽略；nightly 启用完整语义检查 |

> **核心事实**: resolver v3 并不是 feature unification 算法的重写，而是在 v2 基础上默认开启 MSRV-aware version selection。`public = true` 属于独立的 public-dependency 实验特性，其完整 lint  enforcement 需要 nightly `-Zpublic-dependency`。

## 五、稳定版行为说明

当前稳定版 Cargo（1.97.0）对本示例会发出两条警告：

```text
warning: ...crate-b\Cargo.toml: ignoring `public` on dependency crate-d,
        pass `-Zpublic-dependency` to enable support for it
warning: ...crate-c\Cargo.toml: ignoring `public` on dependency crate-d,
        pass `-Zpublic-dependency` to enable support for it
```

这表示：

- `public = true` 的**语法**已被稳定 Cargo 接受，不会导致解析失败。
- 其**语义**（exported-private-dependencies lint、公共/私有依赖的 SemVer 约束）在稳定版上尚未启用。
- 因此本示例在稳定 Rust 上 `cargo check --workspace` 可以通过，只是带有上述警告。

如需体验完整语义，可在 nightly 上运行：

```bash
cargo +nightly check -p c17_resolver_v3_public_demo -Zpublic-dependency
```

## 六、验证命令

```bash
# 1. 检查整个 workspace
cargo check --workspace

# 2. 观察 feature unification
cargo tree -p c17_resolver_v3_public_demo -e features

# 3. 运行示例
cargo run -p c17_resolver_v3_public_demo
```

预期输出：

```text
B: Hello from crate-d / std feature
C: Hello from crate-d / alloc feature
D (serde): Hello from crate-d / serde feature
```

## 七、延伸阅读

- [Cargo Book — Dependency Resolution](https://doc.rust-lang.org/cargo/reference/resolver.html)
- [Cargo Book — Features](https://doc.rust-lang.org/cargo/reference/features.html)
- [RFC 3516 — Public & Private Dependencies](https://github.com/rust-lang/rfcs/pull/3516)
- [Cargo `public = true` 与 Resolver v3](02_public_private_deps.md)
- [Cargo Dependency Resolution](06_cargo_dependency_resolution.md)
- [Rust vs Go：包管理与模块（Module）系统对比](../../05_comparative/01_systems_languages/03_rust_vs_go.md)
- [TOML v1.1 与 Cargo 清单指南](../../../docs/09_toolchain/16_toml_v11_cargo_guide.md)

---

**文档版本**: 1.0
**最后更新**: 2026-07-09
**状态**: ✅ 可运行示例已落地

---

## ⚠️ 反例与陷阱

**反例：feature 统一（unification）意外启用功能。**

```toml
# 旧 resolver（v1）下：dev-dependencies 的 feature 会污染正常构建
[dependencies]
serde = "1.0"

[dev-dependencies]
serde = { version = "1.0", features = ["rc"] }  # cargo build 也会启用 rc！
```

resolver v1 下 `cargo build` 与 `cargo test` 的 feature 集合被统一，`#[cfg(feature = "rc")]` 在正常构建中意外开启，造成「本地构建过、CI 交叉编译挂」类幽灵失败。

**修正对照**：

```toml
# Cargo.toml（workspace root 或包）
resolver = "3"   # edition 2024 默认；旧 edition 需显式声明
```

**陷阱要点**：resolver v3 按目标/用途隔离 feature 统一域；升级 resolver 属行为变更，需在 MSRV 与依赖树评估后进行——本页所述 public feature unification 规则是判定兼容性的检查清单。

---

## 国际权威参考 / International Authority References（P1 学术 · P2 生态）

> 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。

- **P2 生态/社区**: [docs.rs/toml — 生态权威 API 文档](https://docs.rs/toml) · [docs.rs/cargo_metadata — 生态权威 API 文档](https://docs.rs/cargo_metadata)
- **P1 学术/形式化**: [Rudra: Finding Memory Safety Bugs in Rust at the Ecosystem Scale (SOSP 2021)](https://dl.acm.org/doi/10.1145/3477132.3483570)
