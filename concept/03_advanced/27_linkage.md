> **内容分级**: [专家级]
>
# Linkage（链接）

> **EN**: Linkage
> **Summary**: Rust 编译器支持的 crate 链接方式：bin、lib、dylib、staticlib、cdylib、rlib、proc-macro，以及 C 运行时静态/动态链接和混合代码库的注意事项。
>
> **受众**: [进阶] / [专家]
> **Bloom 层级**: 理解 → 应用
> **A/S/P 标记**: **P** — Process / Platform
> **双维定位**: P×Sys — 编译器输出与平台链接行为
> **前置依赖**: [FFI Advanced](09_ffi_advanced.md) · [Attributes and Macros](../01_foundation/12_attributes_and_macros.md) · [Smart Pointers](../02_intermediate/12_smart_pointers.md) · [Terminology Glossary](../00_meta/terminology_glossary.md)
> **后置概念**: [Unsafe Rust](03_unsafe.md) · [Preludes](../01_foundation/35_preludes.md) · [Rust vs C++](../05_comparative/01_rust_vs_cpp.md)
> **定理链**: N/A — 编译器行为/平台相关文档
> **主要来源**: [Rust Reference — Linkage](https://doc.rust-lang.org/reference/linkage.html) · [Kohlbecker et al. — Hygienic Macro Expansion](https://doi.org/10.1145/41625.41632) · [Flatt — Binding as Sets of Scopes](https://doi.org/10.1145/2814304.2814305) · [Rust Reference — External Blocks](https://doc.rust-lang.org/reference/items/external-blocks.html) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)

>
> **来源**: [Rust Reference — Linkage](https://doc.rust-lang.org/reference/linkage.html) · [Rust Reference — crate_type](https://doc.rust-lang.org/reference/linkage.html)

---

## 一、概述

本节主要从**编译器**而非语言语义的角度，介绍 Rust 支持的 crate 链接方式。Rust 编译器可以通过命令行标志或 `#![crate_type = "..."]` 属性生成多种输出产物。

> **核心原则**：编译器会尽量避免同一个库在最终产物中出现多次。

---

## 二、Crate 类型

### `bin` — 可执行文件

```rust
#![crate_type = "bin"]

fn main() {
    println!("hello");
}
```

- 生成可运行的可执行文件。
- 要求 crate 中存在 `main` 函数。
- 默认 crate 类型。

### `lib` — 编译器推荐的库

```rust
#![crate_type = "lib"]
```

- 生成“编译器推荐”的库格式。
- 具体生成哪种底层格式由编译器决定，但对 `rustc` 始终可用。
- 可视为 `rlib`/`dylib` 的别名之一。

### `dylib` — 动态 Rust 库

```rust
#![crate_type = "dylib"]
```

- 强制生成动态库。
- 可被其他 Rust 库或可执行文件依赖。
- 输出：Linux `.so`、macOS `.dylib`、Windows `.dll`。

### `staticlib` — 静态系统库

```rust
#![crate_type = "staticlib"]
```

- 生成包含本 crate 及其所有上游依赖代码的静态系统库。
- **编译器不会尝试链接 `staticlib`**，主要用于将 Rust 代码嵌入非 Rust 应用。
- 输出：Linux/macOS/Windows(MinGW) `.a`，Windows(MSVC) `.lib`。

> **注意**：`staticlib` 包含依赖代码并导出所有公共符号。将其链接到共享库时，通常需要通过 linker script、symbol list 或 module definition 文件限制导出符号。

### `cdylib` — 动态系统库（C ABI）

```rust
#![crate_type = "cdylib"]
```

- 生成供其他语言加载的动态系统库。
- 输出：Linux `.so`、macOS `.dylib`、Windows `.dll`。

### `rlib` — Rust 静态库

```rust
#![crate_type = "rlib"]
```

- 编译中间产物，可视为“静态 Rust 库”。
- 与 `staticlib` 不同，`rlib` 会被 `rustc` 在后续链接中读取元数据。
- 用于生成静态链接的可执行文件和 `staticlib`。

### `proc-macro` — 过程宏 crate

```rust
#![crate_type = "proc-macro"]
```

- 只导出过程宏。
- 编译器自动设置 `proc_macro` cfg。
- 始终使用编译器自身的目标（例如 `x86_64-unknown-linux-gnu`），即使它是为其他目标构建的 crate 的依赖。

---

## 三、命令行 vs 属性

- 通过 `--crate-type=...` 命令行标志指定时，`#![crate_type]` 属性会被忽略。
- 同一方法（全命令行或全属性）指定的多个输出类型可以**叠加**，一次编译生成多个产物。
- 混合使用命令行和属性时，仅生成命令行指定的产物。

```bash
# 同时生成 rlib 和 dylib
rustc --crate-type=rlib,dylib src/lib.rs
```

---

## 四、依赖格式选择规则

当 crate A 依赖 crate B 时，编译器可能同时找到 `rlib` 和 `dylib` 两种形式的 B。选择规则如下：

1. **生成 `staticlib` 时**：所有上游依赖必须是 `rlib` 格式。无法将动态库转换为静态格式。
2. **生成 `rlib` 时**：上游依赖格式无限制，只需能读取元数据即可。
3. **生成可执行文件且未使用 `-C prefer-dynamic`**：优先尝试 `rlib`；若某些依赖无 `rlib`，则尝试动态链接。
4. **生成 `dylib` 或动态链接的可执行文件**：编译器会协调 `rlib` 和 `dylib` 依赖，尽量最大化动态依赖。

---

## 五、C 运行时的静态与动态链接

标准库支持为不同目标选择静态或动态 C 运行时。默认行为由目标决定：

- 大多数目标默认**动态**链接 C 运行时。
- 以下目标默认**静态**链接：
  - `arm-unknown-linux-musleabi`
  - `arm-unknown-linux-musleabihf`
  - `armv7-unknown-linux-musleabihf`
  - `i686-unknown-linux-musl`
  - `x86_64-unknown-linux-musl`

### `crt-static` target feature

通过 `-C target-feature=+crt-static` 或 `-crt-static` 控制：

```bash
# 静态 C 运行时
rustc -C target-feature=+crt-static foo.rs

# 动态 C 运行时
rustc -C target-feature=-crt-static foo.rs
```

在代码中可通过 `cfg(target_feature = "crt-static")` 检测：

```rust
#[cfg(target_feature = "crt-static")]
fn foo() { println!("static C runtime"); }

#[cfg(not(target_feature = "crt-static"))]
fn foo() { println!("dynamic C runtime"); }
```

在 Cargo build script 中可通过 `CARGO_CFG_TARGET_FEATURE` 检测：

```rust
use std::env;

fn main() {
    let features = env::var("CARGO_CFG_TARGET_FEATURE").unwrap_or_default();
    if features.contains("crt-static") {
        println!("cargo:rustc-link-arg=-static");
    }
}
```

---

## 六、混合 Rust 与外部代码

将 Rust 与 C/C++ 混合链接为单一二进制文件有两种方式：

### 方式 1：使用 `rustc` 链接

```bash
rustc --crate-type=bin src/main.rs -L native=/path/to/libs -l myclib
```

或在 Rust 代码中使用 `#[link]`：

```rust
#[link(name = "myclib", kind = "static")]
extern "C" {}
```

### 方式 2：使用外部链接器

1. 生成 Rust `staticlib`。
2. 将 `staticlib` 传入外部链接器。

> **限制**：多个 Rust `staticlib` 一起链接可能冲突。若需组合多个 Rust 子系统，应生成**单个** `staticlib`（例如通过大量 `extern crate` 将多个 `rlib` 聚合）。
> **不支持**：直接将 `rlib` 传入外部链接器。

---

## 七、Panic 展开与链接一致性

如果 Rust 产物是 **potentially unwinding** 的，则所有 crate 必须使用 `unwind` panic 策略，否则可能导致未定义行为。

潜在展开的条件：

- 使用 `unwind` panic handler。
- 包含一个使用 `unwind` panic 策略的 crate，且该 crate 调用了 `-unwind` ABI 函数。
- 向拥有独立 Rust runtime 副本的另一个 Rust 产物发起 `"Rust" ABI` 调用，且该产物是 potentially unwinding 的。

> 使用 `rustc` 链接时，这些规则会自动强制执行。使用 `dlopen` 等不由 `rustc` 控制的链接方式时，需要手动保证一致性。

---

## 八、快速选择指南

| 场景 | 推荐 crate type |
|:---|:---|
| 普通可执行程序 | `bin` |
| 普通 Rust 库（给 Rust 用） | `lib` 或 `rlib` |
| 需要动态链接的 Rust 插件 | `dylib` |
| 嵌入非 Rust 应用的静态库 | `staticlib` |
| 供其他语言调用的动态库 | `cdylib` |
| 过程宏 | `proc-macro` |

---

## 九、关联概念

| 概念 | 关系 |
|:---|:---|
| [FFI Advanced](09_ffi_advanced.md) | `cdylib`/`staticlib` 常用于 FFI 场景 |
| [Preludes](../01_foundation/35_preludes.md) | `extern crate` 影响 extern prelude 和链接 |
| [Unsafe Rust](03_unsafe.md) | FFI 和混合代码库通常涉及 unsafe |