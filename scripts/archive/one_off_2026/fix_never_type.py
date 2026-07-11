#!/usr/bin/env python3
"""Precise never type stabilization status in concept/01_foundation/05_never_type.md."""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
FILE = ROOT / "concept" / "01_foundation" / "05_never_type.md"

text = FILE.read_text(encoding="utf-8")

# 1. Fix RFC 1216 URL double slash
old_url = "[RFC 1216](https://rust-lang.github.io/rfcs//1216-bang-type.html)"
new_url = "[RFC 1216](https://rust-lang.github.io/rfcs/1216-bang-type.html)"
text = text.replace(old_url, new_url)

# 2. Add stabilization status note after the source block
old_source = """> **来源**:
>
> [Rust Reference — Never Type](https://doc.rust-lang.org/reference/types/never.html) ·
> [The Rust Programming Language](https://doc.rust-lang.org/book/) ·
> [Rustonomicon](https://doc.rust-lang.org/nomicon/) ·
> [RFC 1216](https://rust-lang.github.io/rfcs/1216-bang-type.html)

## 目录"""

new_source = """> **来源**:
>
> [Rust Reference — Never Type](https://doc.rust-lang.org/reference/types/never.html) ·
> [The Rust Programming Language](https://doc.rust-lang.org/book/) ·
> [Rustonomicon](https://doc.rust-lang.org/nomicon/) ·
> [RFC 1216](https://rust-lang.github.io/rfcs/1216-bang-type.html) ·
> [Rust Release Notes — 1.92.0](https://doc.rust-lang.org/beta/releases.html) ·
> [Rust Release Notes — 1.96.0](https://github.com/rust-lang/rust/issues/156512)
>
> **稳定化状态**: `!` 已在大量上下文中可用（如发散函数、`Result<T, !>`、`Option<!>`），但**完整类型地位（full never type stabilization）仍在进行中**。Rust 1.92 将 `never_type_fallback_flowing_into_unsafe` 与 `dependency_on_unit_never_type_fallback` 两个 future-compatibility lint 提升为 deny-by-default；Rust 1.96 进一步统一了 `!` 在 tuple 表达式中的 coercion 行为。

## 目录"""

if old_source in text:
    text = text.replace(old_source, new_source)
else:
    print("Warning: source block not found")

# 3. Update TOC chapter title
old_toc = "  - [四、Rust 1.96 改进：Tuple Coercion](#四rust-196-改进tuple-coercion)"
new_toc = "  - [四、Never Type 稳定化进展](#四never-type-稳定化进展)"
text = text.replace(old_toc, new_toc)

# 4. Update section heading and content
old_section = """## 四、Rust 1.96 改进：Tuple Coercion

> **[来源: [Rust 1.96 Release Notes](https://blog.rust-lang.org/releases/latest/)]**

Rust 1.96 稳定了 never type 在 **tuple 表达式**中的 coercion 行为：

```rust,ignore
/// Rust 1.96+：! 在 tuple 中自动 coercion
fn tuple_coercion_demo() -> (i32, String) {
    if false {
        (panic!("never"), "test".to_string())
        // panic!() 返回 !，在 tuple 中被 coercion 为 i32
    } else {
        (42, "hello".to_string())
    }
}

/// 实际应用场景：配置加载
fn load_critical_config() -> (String, u16) {
    match Config::try_load() {
        Ok(cfg) => (cfg.host, cfg.port),
        Err(_) => (fatal_error("config missing"), 0),
        // fatal_error() 返回 !，在 tuple 中被 coercion
    }
}

struct Config {
    host: String,
    port: u16,
}

impl Config {
    fn try_load() -> Result<Self, ()> {
        Ok(Config { host: "localhost".to_string(), port: 8080 })
    }
}
```

> **关键洞察**: 1.96 之前，某些边缘情况下 `!` 在 tuple 中不会被自动 coercion，导致需要显式处理。1.96 统一了这一行为，使 `!` 的语义更加一致。"""

new_section = """## 四、Never Type 稳定化进展

### 4.1 完整稳定化仍在进行中

> **[来源: [Rust Project Goals 2026 — Stabilize never type](https://rust-lang.github.io/rust-project-goals/2026/stabilize-never-type.html)]**

`!` 作为 Rust 类型系统的底类型，其完整稳定化是一个多阶段过程：

| 阶段 | 版本 | 内容 | 状态 |
|:---|:---|:---|:---:|
| 底类型语义可用 | 1.0+ | `panic!`、`loop {}`、`return` 等发散表达式类型为 `!` | ✅ 已稳定 |
| `Result<T, !>` / `Option<!>` 模式 | 1.x+ | 用 `!` 表达"不可能的错误/值" | ✅ 已稳定 |
| Never type fallback lint | 1.92 | `never_type_fallback_flowing_into_unsafe`、`dependency_on_unit_never_type_fallback` 设为 deny-by-default | ✅ 已稳定 |
| Tuple coercion 统一 | 1.96 | `!` 在 tuple 表达式中总是 coercion | ✅ 已稳定 |
| 完整类型地位 | 待定 | 消除剩余不稳定边界，可能需要下一代 trait solver 配合 | 🧪 进行中 |

### 4.2 Rust 1.92：deny-by-default 的 future-compatibility lint

Rust 1.92 将以下两个 lint 提升为 deny-by-default：

- `never_type_fallback_flowing_into_unsafe`：检测 `!` fallback 流入 `unsafe` 上下文、可能导致 soundness 问题的代码。
- `dependency_on_unit_never_type_fallback`：检测依赖 "`!` 在某些位置回退为 `()`" 这一旧行为的代码。

这些 lint 不会破坏正常代码，但会迫使开发者修复那些将在完整 never type 稳定化后失效的边缘模式。

[来源: [Rust 1.92 Release Notes](https://doc.rust-lang.org/beta/releases.html)]

### 4.3 Rust 1.96：Tuple Coercion

> **[来源: [Rust 1.96 Release Notes](https://github.com/rust-lang/rust/issues/156512)]**

Rust 1.96 稳定了 never type 在 **tuple 表达式**中的 coercion 行为：

```rust,ignore
/// Rust 1.96+：! 在 tuple 中自动 coercion
fn tuple_coercion_demo() -> (i32, String) {
    if false {
        (panic!("never"), "test".to_string())
        // panic!() 返回 !，在 tuple 中被 coercion 为 i32
    } else {
        (42, "hello".to_string())
    }
}

/// 实际应用场景：配置加载
fn load_critical_config() -> (String, u16) {
    match Config::try_load() {
        Ok(cfg) => (cfg.host, cfg.port),
        Err(_) => (fatal_error("config missing"), 0),
        // fatal_error() 返回 !，在 tuple 中被 coercion
    }
}

struct Config {
    host: String,
    port: u16,
}

impl Config {
    fn try_load() -> Result<Self, ()> {
        Ok(Config { host: "localhost".to_string(), port: 8080 })
    }
}
```

> **关键洞察**: 1.96 之前，某些边缘情况下 `!` 在 tuple 中不会被自动 coercion，导致需要显式处理。1.96 统一了这一行为，使 `!` 的语义更加一致。"""

if old_section in text:
    text = text.replace(old_section, new_section)
else:
    print("Warning: section 4 not found")

FILE.write_text(text, encoding="utf-8")
print(f"Updated {FILE.relative_to(ROOT)}")
