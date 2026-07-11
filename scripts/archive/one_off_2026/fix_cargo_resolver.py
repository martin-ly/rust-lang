#!/usr/bin/env python3
"""Align Cargo resolver v3 / MSRV-aware resolver content with official docs."""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
FILE = ROOT / "concept" / "06_ecosystem" / "60_cargo_dependency_resolution.md"

text = FILE.read_text(encoding="utf-8")

# 1. Update source block to add RFC 3537 and Cargo resolver docs
old_source = """> **来源**: [Cargo — Dependency Resolution](https://doc.rust-lang.org/cargo/reference/resolver.html)
> [Cargo Book — SemVer Compatibility](https://doc.rust-lang.org/cargo/reference/semver.html) ·
> [Cargo Book — Features](https://doc.rust-lang.org/cargo/reference/features.html) ·
> [Cargo Book — Resolver (Specifying Dependencies)](https://doc.rust-lang.org/cargo/reference/specifying-dependencies.html)"""

new_source = """> **来源**: [Cargo — Dependency Resolution](https://doc.rust-lang.org/cargo/reference/resolver.html)
> [Cargo Book — SemVer Compatibility](https://doc.rust-lang.org/cargo/reference/semver.html) ·
> [Cargo Book — Features](https://doc.rust-lang.org/cargo/reference/features.html) ·
> [Cargo Book — Resolver (Specifying Dependencies)](https://doc.rust-lang.org/cargo/reference/specifying-dependencies.html) ·
> [Cargo Book — Resolver versions](https://doc.rust-lang.org/cargo/reference/resolver.html#resolver-versions) ·
> [RFC 3537 — MSRV-aware resolver](https://rust-lang.github.io/rfcs/3537-msrv-resolver.html)"""

if old_source in text:
    text = text.replace(old_source, new_source)
else:
    print("Warning: source block not found")

# 2. Replace section 6
old_sec6 = """## 六、Resolver 版本差异

| Resolver | 主要行为变化 |
|:---|:---|
| v1 | 默认统一所有 target 和 dev/build 依赖的 features |
| v2 | 区分 `dev-dependencies`、`target-specific` 依赖的 features；默认 Edition 2021+ |
| v3 | 进一步细粒度控制，避免某些 feature 泄漏；Rust 1.96+ 默认 |

推荐在 workspace 根显式声明：

```toml
[workspace]
members = ["crates/*"]
resolver = "3"
```

> **状态**: Rust 1.96 默认 resolver 为 v3，但显式声明仍然是最佳实践。
>
> [来源: Cargo Book — Resolver](https://doc.rust-lang.org/cargo/reference/resolver.html#resolver-versions)"""

new_sec6 = """## 六、Resolver 版本差异

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
> - Resolver v3 随 **Rust 1.84.0** 稳定。
> - **Edition 2024** 的项目默认使用 resolver v3。
> - v3 与 v2 的 feature unification 行为相同；v3 的核心新增能力是 MSRV-aware version selection。
>
> [来源: Cargo Book — Resolver versions](https://doc.rust-lang.org/cargo/reference/resolver.html#resolver-versions) · [Rust 1.84.0 Release Notes](https://releases.rs/docs/1.84.0/)"""

if old_sec6 in text:
    text = text.replace(old_sec6, new_sec6)
else:
    print("Warning: section 6 not found")

# 3. Replace section 7
old_sec7 = """## 七、`rust-version` 与 MSRV 感知

`Cargo.toml` 中的 `rust-version` 字段声明包的 MSRV（Minimum Supported Rust Version）：

```toml
[package]
name = "my-crate"
version = "0.1.0"
rust-version = "1.70"
```

解析器会优先选择满足当前工具链和 MSRV 约束的版本。如果某个依赖的新版本需要更新的 Rust，Cargo 会尽量选择旧版本，除非无法解析。

> **提示**: `rust-version` 是 Cargo 元数据，不是编译器强制的语法约束；真正失败通常发生在编译时遇到新语法或 API。
>
> [来源: Cargo Book — The rust-version field](https://doc.rust-lang.org/cargo/reference/manifest.html#the-rust-version-field)"""

new_sec7 = """## 七、`rust-version` 与 MSRV 感知

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
> [来源: Cargo Book — The rust-version field](https://doc.rust-lang.org/cargo/reference/manifest.html#the-rust-version-field) · [RFC 3537 — MSRV-aware resolver](https://rust-lang.github.io/rfcs/3537-msrv-resolver.html) · [Cargo issue #9930](https://github.com/rust-lang/cargo/issues/9930)"""

if old_sec7 in text:
    text = text.replace(old_sec7, new_sec7)
else:
    print("Warning: section 7 not found")

# 4. Update authority source table
old_table = """| [Cargo Book — Specifying Dependencies](https://doc.rust-lang.org/cargo/reference/specifying-dependencies.html) | ✅ 一级 | 版本要求语法 |

---"""

new_table = """| [Cargo Book — Specifying Dependencies](https://doc.rust-lang.org/cargo/reference/specifying-dependencies.html) | ✅ 一级 | 版本要求语法 |
| [RFC 3537 — MSRV-aware resolver](https://rust-lang.github.io/rfcs/3537-msrv-resolver.html) | ✅ 一级 | MSRV-aware 解析器设计 |
| [Rust 1.84.0 Release Notes](https://releases.rs/docs/1.84.0/) | ✅ 一级 | resolver v3 / MSRV resolver 稳定公告 |

---"""

if old_table in text:
    text = text.replace(old_table, new_table)
else:
    print("Warning: authority table not found")

# 5. Update changelog line at bottom
old_changelog = "> **权威来源对齐变更日志**: 2026-06-21 创建，对齐 Rust 1.96.0 / Cargo resolver v3"
new_changelog = "> **权威来源对齐变更日志**: 2026-06-23 更新，对齐 Rust 1.84.0+ / RFC 3537 / Cargo resolver v3 & MSRV-aware resolver"

if old_changelog in text:
    text = text.replace(old_changelog, new_changelog)
else:
    print("Warning: changelog line not found")

FILE.write_text(text, encoding="utf-8")
print(f"Updated {FILE.relative_to(ROOT)}")
