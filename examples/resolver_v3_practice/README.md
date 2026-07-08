# Resolver v3 / `public = true` 实践

> **定位**: 可运行的 Cargo Resolver v3 与 `public = true` 依赖可见性示例 workspace。

---

## 内容

本 workspace 用 3 个 crate 演示 resolver v3 与公共/私有依赖声明：

| Crate | MSRV | 角色 | 公共依赖 | 私有依赖 |
|---|---|---|---|---|
| `legacy-lib` | 1.70 | 底层库，公开 `LegacyFlags` | `bitflags` | `serde`, `indexmap` |
| `modern-app` | 1.84 | 中间库，复用并扩展公共 API | `legacy-lib`, `bitflags`, `serde` | `indexmap` |
| `edge-bin` | 1.96.1 | 顶层二进制 | （二进制无下游，默认私有） | `legacy-lib`, `modern-app`, `serde`, `serde_json` |

### 演示要点

1. **Resolver v3 的 MSRV-aware 解析**
   workspace 根显式声明 `resolver = "3"`，并在 `.cargo/config.toml` 中设置 `incompatible-rust-versions = "fallback"`。由于 `legacy-lib` 的 `rust-version = "1.70"`，resolver 会优先选择满足该 MSRV 的最新兼容版本（如 `serde_json v1.0.149` 而非需要 Rust 1.71+ 的更新版）。

2. **`public = true` 的语义**
   - `legacy-lib` 将 `bitflags` 标为 `public = true`，因为它在 `pub struct LegacyFlags` 中暴露 `bitflags` 宏生成的类型。
   - `legacy-lib` 将 `serde` 标为 `public = false`，因为 `InternalConfig` 是私有类型。
   - `modern-app` 将 `legacy-lib`、`bitflags`、`serde` 均标为 `public = true`，因为其公共 API 中使用了这些依赖的类型。

3. **传递依赖可见性**
   `modern-app` 可以在公共 API 中返回 `legacy_lib::LegacyFlags`，因为 `legacy-lib` 被声明为公共依赖；下游因此知道 `LegacyFlags` 来自 `legacy-lib` 的公共 API。

4. **feature 统一**
   通过 `cargo tree -e features -p edge-bin` 可观察到 `serde` 的 `derive`、`std`、`rc` 等 feature 被统一为并集。在 `public-dependency` 完全启用后，公共依赖的 feature 将在整个公共依赖链中统一，而私有依赖的 feature 仅在各自子树中统一。

---

## 运行

```bash
cd examples/resolver_v3_practice

# 稳定版检查（public 字段会被接受但忽略，并给出警告）
cargo check --workspace

# 查看 feature 统一结果
cargo tree -e features -p edge-bin

# 查看是否有重复依赖
cargo tree --duplicates

# 运行二进制
cargo run -p edge-bin
cargo run -p modern-app
```

### 使用 nightly 启用完整 `public-dependency` 检查

截至 Rust 1.96.1，`public = true/false` 的**语法**已被 Cargo 接受，但编译器对 `exported_private_dependencies` 的强制执行仍需 nightly 与 `-Zpublic-dependency`：

```bash
rustup run nightly cargo check -Zpublic-dependency --workspace
```

若将某个私有依赖的类型错误地暴露到公共 API，nightly 会发出类似下方的警告：

```text
warning: trait `Flags` from private dependency 'bitflags' in public interface
```

---

## 延伸阅读

- 权威概念页: [`concept/06_ecosystem/01_cargo/10_public_private_deps.md`](../../concept/06_ecosystem/01_cargo/10_public_private_deps.md)
- Cargo Book — [Dependency Resolution](https://doc.rust-lang.org/cargo/reference/resolver.html)
- RFC 3516 — [Public & Private Dependencies](https://github.com/rust-lang/rfcs/pull/3516)
