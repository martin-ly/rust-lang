# Cargo resolver v3 / `public = true` 演示

> **EN**: Cargo resolver v3 and `public = true` feature-unification demo workspace.

本目录包含一个可在稳定 Rust 上 `cargo check` 通过的最小 workspace 示例，用于演示：

- Crate A 同时依赖 Crate B 与 Crate C。
- Crate B 与 Crate C 都依赖 Crate D，但启用不同 feature。
- Crate B/C 的 `Cargo.toml` 中以注释形式保留了 `public = true` 写法：`public` 依赖目前仍是 nightly-only 特性（需 `-Zpublic-dependency`），稳定版 cargo 会忽略并告警；稳定版构建中普通依赖已足以演示 feature unification。
- Crate A 直接依赖 Crate D 并启用第三个 feature，观察 Cargo 的 feature unification 行为。

## 目录结构

```text
crates/c17_resolver_v3_public_demo/
├── Cargo.toml          # Crate A（workspace member）
├── src/main.rs
├── crate-b/Cargo.toml  # Crate B：public = true（nightly-only，稳定版以注释保留），启用 crate-d/std
├── crate-b/src/lib.rs
├── crate-c/Cargo.toml  # Crate C：public = true（nightly-only，稳定版以注释保留），启用 crate-d/alloc
├── crate-c/src/lib.rs
├── crate-d/Cargo.toml  # Crate D：提供 std / alloc / serde 三个 additive feature
└── crate-d/src/lib.rs
```

## 运行验证

```bash
# 从仓库根目录检查整个 workspace
cargo check --workspace

# 仅检查本示例
cargo check -p c17_resolver_v3_public_demo

# 查看 feature unification 结果
cargo tree -p c17_resolver_v3_public_demo -e features

# 运行示例二进制
cargo run -p c17_resolver_v3_public_demo
```

## 关键输出

`cargo tree -e features` 会显示 B、C、A 对 Crate D 的 feature 请求汇聚到同一个 `crate-d` 实例上：

```text
c17_resolver_v3_public_demo v0.1.0 (...)
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

最终 `crate-d` 被构建为 `std + alloc + serde` 的并集。

## 稳定版与 nightly 说明

- 当前稳定版 Cargo 会**解析** `public = true` 字段并给出警告：
  `ignoring`public`on dependency crate-d, pass -Zpublic-dependency to enable support for it`。
- 因此本示例在稳定 Rust 上 `cargo check --workspace` 可通过（仅产生上述警告）。
- `public = true` 的完整语义检查（例如 `exported_private_dependencies` lint）需要 nightly 的 `-Zpublic-dependency`。

## 配套文档

详细概念解释见：

- [`concept/06_ecosystem/01_cargo/03_resolver_v3_public_feature_unification.md`](../../concept/06_ecosystem/01_cargo/03_resolver_v3_public_feature_unification.md)
- [`concept/06_ecosystem/01_cargo/02_public_private_deps.md`](../../concept/06_ecosystem/01_cargo/02_public_private_deps.md)
