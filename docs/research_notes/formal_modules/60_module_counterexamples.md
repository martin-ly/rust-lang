# 模块系统反例与边界案例 {#模块系统反例与边界案例}

> **EN**: Module Counterexamples
> **Summary**: 模块系统反例与边界案例 Module Counterexamples.
> **内容分级**: [核心级]
> **层级**: L6 (反例边界)
> **Bloom 层级**: L5-L6 (分析/评价)
> **概念族**: 形式化模块（Module） / 反例边界
> **Rust 版本**: 1.96.1+ (Edition 2024)
> **状态**: ✅ 已完成
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29

---

## 目录 {#目录}

- [模块系统反例与边界案例 {#模块系统反例与边界案例}](#模块系统反例与边界案例-模块系统反例与边界案例)
  - [目录 {#目录}](#目录-目录)
  - [1. 循环模块依赖 {#1-循环模块依赖}](#1-循环模块依赖-1-循环模块依赖)
    - [现象 {#现象-7}](#现象-现象-7)
    - [编译器错误 {#编译器错误-2}](#编译器错误-编译器错误-2)
    - [根因 {#根因-6}](#根因-根因-6)
    - [修复方案 {#修复方案-5}](#修复方案-修复方案-5)
  - [2. `mod` 重复声明 {#2-mod-重复声明}](#2-mod-重复声明-2-mod-重复声明)
    - [现象 {#现象-7}](#现象-现象-7-1)
    - [编译器错误 {#编译器错误-2}](#编译器错误-编译器错误-2-1)
    - [根因 {#根因-6}](#根因-根因-6-1)
    - [修复方案 {#修复方案-5}](#修复方案-修复方案-5-1)
  - [3. `pub(in path)` 指向不可见模块 {#3-pubin-path-指向不可见模块}](#3-pubin-path-指向不可见模块-3-pubin-path-指向不可见模块)
    - [现象 {#现象-7}](#现象-现象-7-2)
    - [编译器错误 {#编译器错误-2}](#编译器错误-编译器错误-2-2)
    - [根因 {#根因-6}](#根因-根因-6-2)
    - [修复方案 {#修复方案-5}](#修复方案-修复方案-5-2)
  - [4. `use` 路径的相对/绝对混淆 {#4-use-路径的相对绝对混淆}](#4-use-路径的相对绝对混淆-4-use-路径的相对绝对混淆)
    - [现象 {#现象-7}](#现象-现象-7-3)
    - [边界情况 {#边界情况}](#边界情况-边界情况)
    - [根因 {#根因-6}](#根因-根因-6-3)
  - [5. Edition 2018+ 中多余的 `extern crate` {#5-edition-2018-中多余的-extern-crate}](#5-edition-2018-中多余的-extern-crate-5-edition-2018-中多余的-extern-crate)
    - [现象 {#现象-7}](#现象-现象-7-4)
    - [边界与例外 {#边界与例外}](#边界与例外-边界与例外)
    - [根因 {#根因-6}](#根因-根因-6-4)
  - [6. `crate-type` 与链接目标不匹配 {#6-crate-type-与链接目标不匹配}](#6-crate-type-与链接目标不匹配-6-crate-type-与链接目标不匹配)
    - [现象 {#现象-7}](#现象-现象-7-5)
    - [典型错误 {#典型错误}](#典型错误-典型错误)
    - [修复方案 {#修复方案-5}](#修复方案-修复方案-5-3)
  - [7. 可见性突破安全抽象边界 {#7-可见性突破安全抽象边界}](#7-可见性突破安全抽象边界-7-可见性突破安全抽象边界)
    - [现象 {#现象-7}](#现象-现象-7-6)
    - [根因 {#根因-6}](#根因-根因-6-5)
    - [修复方案 {#修复方案-5}](#修复方案-修复方案-5-4)
  - [8. `#[no_mangle]` 符号冲突 {#8-no\_mangle-符号冲突}](#8-no_mangle-符号冲突-8-no_mangle-符号冲突)
    - [现象 {#现象-7}](#现象-现象-7-7)
    - [链接器错误 {#链接器错误}](#链接器错误-链接器错误)
    - [根因 {#根因-6}](#根因-根因-6-6)
    - [修复方案 {#修复方案-5}](#修复方案-修复方案-5-5)
  - [总结 {#总结}](#总结-总结)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [RFC 参考 {#rfc-参考}](#rfc-参考-rfc-参考)
  - [权威来源参考 {#权威来源参考}](#权威来源参考-权威来源参考)
  - [学术权威参考 {#学术权威参考}](#学术权威参考-学术权威参考)
  - [社区权威参考 {#社区权威参考}](#社区权威参考-社区权威参考)

---

## 1. 循环模块依赖 {#1-循环模块依赖}

### 现象 {#现象-7}

Rust 模块系统禁止 **模块定义之间的循环依赖**（circular module dependencies）。以下代码试图让 `a` 依赖 `b`，同时 `b` 依赖 `a`：

```rust
// src/a.rs
pub mod b;

// src/b.rs
pub mod a;
```

### 编译器错误 {#编译器错误-2}

```text
error[E0585]: found a documentation comment that doesn't document anything
  --> src/a.rs:1:1
   |
1  | /// doc
   | ^^^^^^^
   |
   = help: doc comments must come before what they document, maybe a comment was intended with `//`?
```

实际更典型的错误形式为：

```text
error[E0433]: failed to resolve: use of undeclared crate or module `b`
```

或当通过 `use` 引用（Reference）自身时产生循环引用错误。

### 根因 {#根因-6}

Rust 名称解析器在解析模块树时要求 DAG（有向无环图）。`mod` 声明会在当前模块内引入子模块；如果两个文件互相 `mod` 对方，则形成定义循环。

### 修复方案 {#修复方案-5}

- **提取公共依赖**：将共享类型/函数抽到第三个模块。
- **使用 trait 解耦**：一个模块定义 trait，另一个模块实现它。
- **重新划分职责**：按依赖方向重新组织模块边界。

> **对应规则**: Rust Reference – [Items and Modules](https://doc.rust-lang.org/reference/items.html)

---

## 2. `mod` 重复声明 {#2-mod-重复声明}

### 现象 {#现象-7}

同一个模块文件不能被两个父模块同时 `mod` 声明：

```rust
// src/lib.rs
pub mod foo;
pub mod bar;

// src/foo.rs
pub mod shared;

// src/bar.rs
pub mod shared; // ❌ shared 已被 foo 引入
```

### 编译器错误 {#编译器错误-2}

```text
error[E0583]: file not found for module `shared`
  --> src/bar.rs:1:1
   |
1  | pub mod shared;
   | ^^^^^^^^^^^^^^^
   |
   = help: to create what the `shared` module refers to, use file src/bar/shared.rs or src/bar/shared/mod.rs
```

即使文件存在，也会在 crate 命名空间中出现重复定义：

```text
error[E0428]: the name `shared` is defined multiple times
```

### 根因 {#根因-6}

`mod` 是 **声明式** 的：它把文件挂载到当前模块命名空间下。每个模块在 crate 根命名空间中必须有唯一路径。

### 修复方案 {#修复方案-5}

- 只在 crate 的单一入口 `mod` 共享模块。
- 需要跨模块访问时，使用 `use crate::foo::shared::...` 而不是再次 `mod`。

---

## 3. `pub(in path)` 指向不可见模块 {#3-pubin-path-指向不可见模块}

### 现象 {#现象-7}

`pub(in some::path)` 指定的路径必须是一个 **当前项可见的祖先模块**。

```rust
mod outer {
    mod inner {
        pub(in crate::outer::inner::deep) fn secret() {}
        //            ^^^^^^^^^^^^^^^^^^^ deep 不存在
    }
}
```

### 编译器错误 {#编译器错误-2}

```text
error[E0433]: failed to resolve: could not find `deep` in `inner`
```

### 根因 {#根因-6}

`pub(in path)` 的限制路径必须是当前 crate 中真实存在的模块，并且该路径必须能够从当前项访问到。

### 修复方案 {#修复方案-5}

- 使用实际存在的祖先路径，例如 `pub(in crate::outer::inner)`。
- 或改用 `pub(crate)` / `pub(super)`。

> **对应规则**: Rust Reference – [Visibility and Privacy](https://doc.rust-lang.org/reference/visibility-and-privacy.html)

---

## 4. `use` 路径的相对/绝对混淆 {#4-use-路径的相对绝对混淆}

### 现象 {#现象-7}

Edition 2018 之前 `use` 路径默认从 crate 根开始；Edition 2018+ 中 `use` 路径默认也是绝对路径（从 crate 根开始），但在 2024 Edition 中 `use` 仍然解析为绝对路径。

```rust
// Edition 2024
mod foo {
    pub fn bar() {}
}

fn main() {
    use foo::bar; // ✅ 绝对路径：crate::foo::bar
}
```

反例：试图用相对路径 `self::` / `super::` 时不写前缀：

```rust
mod foo {
    pub fn bar() {}
}

mod baz {
    // 想要引用同级的 foo::bar，但 use 默认是绝对路径
    use foo::bar; // ❌ 实际查找 crate::foo，而 foo 在 crate 根存在，可能意外成功
}
```

### 边界情况 {#边界情况}

在子模块内部引用父模块的兄弟模块时，必须使用 `super::` 或 `crate::`：

```rust
mod foo {
    pub fn bar() {}
}

mod baz {
    use super::foo::bar; // ✅ 正确
}
```

### 根因 {#根因-6}

`use` 路径总是绝对解析，除非显式使用 `self::`、`super::` 或 `crate::` 限定。

---

## 5. Edition 2018+ 中多余的 `extern crate` {#5-edition-2018-中多余的-extern-crate}

### 现象 {#现象-7}

在 Edition 2018 / 2021 / 2024 中，对于正常依赖，`extern crate` 已无需显式书写：

```rust
// Cargo.toml 已声明 serde = "1"
extern crate serde; // ⚠️ 冗余，Edition 2018+ 通常不需要
```

### 边界与例外 {#边界与例外}

仍需 `extern crate` 的场景：

- 宏（Macro） crate：`#[macro_use] extern crate lazy_static;`（除非使用 2018+ 的 `use lazy_static::lazy_static;`）。
- 内建 crate：`extern crate core;` 在某些 `#![no_std]` 边缘场景需要。
- 重命名：`extern crate foo as bar;`。

### 根因 {#根因-6}

Edition 2018 把 crate 作为名称空间中的顶级模块，自动注入。

---

## 6. `crate-type` 与链接目标不匹配 {#6-crate-type-与链接目标不匹配}

### 现象 {#现象-7}

在 `Cargo.toml` 中设置错误的 `crate-type` 会导致链接阶段失败：

```toml
[lib]
crate-type = ["cdylib"]
```

然后尝试 `cargo test` 运行单元测试，可能因为无法生成测试二进制而失败；或尝试把 cdylib 当 rlib 链接：

```text
error: cannot satisfy dependencies so `serde` only shows up once
```

### 典型错误 {#典型错误}

把 `bin` crate 的 `crate-type` 设为 `lib`：

```toml
[[bin]]
name = "app"
crate-type = ["cdylib"] # ❌ bin 不能有 crate-type
```

### 修复方案 {#修复方案-5}

- `lib` 默认是 `rlib`；需要 C ABI 时再加 `cdylib`/`staticlib`。
- 一个 package 最多一个 `lib`，可以有多个 `bin`。

---

## 7. 可见性突破安全抽象边界 {#7-可见性突破安全抽象边界}

### 现象 {#现象-7}

模块可见性不仅是封装，还是 unsafe 抽象的安全边界。错误放宽可见性会破坏不变量：

```rust
pub mod safe_wrapper {
    // 内部 unsafe 实现细节，本应私有
    pub mod internal {
        pub unsafe fn raw_pointer_op(ptr: *mut u8) {
            // ...
        }
    }

    pub fn public_api() {
        // 正确封装 unsafe
    }
}
```

将 `internal` 设为 `pub` 后，外部代码可以直接调用 `safe_wrapper::internal::raw_pointer_op`，绕过安全封装。

### 根因 {#根因-6}

Rust 的安全性依赖于模块边界维护的不变量。可见性是 **逻辑封装** 与 **安全契约** 的共同基础。

### 修复方案 {#修复方案-5}

- unsafe 实现细节应设为 `pub(crate)` 或私有。
- 使用 `pub` 暴露的 API 必须保证调用时不需要额外 unsafe 前提，或明确标注 `unsafe fn` 并文档化契约。

---

## 8. `#[no_mangle]` 符号冲突 {#8-no_mangle-符号冲突}

### 现象 {#现象-7}

`#[no_mangle]` 关闭 Rust 名称修饰，使函数具有固定的 C 链接名。若两个 crate 都导出同名符号，链接时冲突：

```rust
// crate-a/src/lib.rs
#[no_mangle]
pub extern "C" fn init() {}

// crate-b/src/lib.rs
#[no_mangle]
pub extern "C" fn init() {}
```

### 链接器错误 {#链接器错误}

```text
error: linking with `cc` failed: exit code: 1
  = note: ld: duplicate symbol '_init' in .../libcrate_a.a and .../libcrate_b.a
```

### 根因 {#根因-6}

链接器全局符号表要求每个符号唯一。`#[no_mangle]` 使 Rust 函数进入全局符号表。

### 修复方案 {#修复方案-5}

- 使用唯一前缀命名：`mylib_init`。
- 或使用 `#[export_name = "mylib_init"]`。
- 静态链接时注意符号隐藏与版本脚本。

---

## 总结 {#总结}

| 反例 | 涉及概念 | 关键规则 |
| :--- | :--- | :--- |
| 循环模块依赖 | 模块树、名称解析 | 模块树必须是 DAG |
| `mod` 重复声明 | 命名空间、挂载点 | 每个模块路径唯一 |
| `pub(in path)` 错误 | 受限可见性 | 路径必须存在且可达 |
| `use` 相对/绝对混淆 | 路径解析 | `use` 默认绝对路径 |
| 多余 `extern crate` | Edition 语义 | 2018+ 自动注入依赖 crate |
| `crate-type` 不匹配 | 链接、crate 类型 | lib/bin/proc-macro 限制 |
| 可见性突破安全边界 | 安全抽象、封装 | unsafe 细节不应过度暴露 |
| `#[no_mangle]` 符号冲突 | 链接、符号可见性 | 全局符号必须唯一 |

> **权威来源**: [Rust Reference – Items and Modules](https://doc.rust-lang.org/reference/items.html) | [Rust Reference – Visibility and Privacy](https://doc.rust-lang.org/reference/visibility-and-privacy.html) | [Rust Reference – Linkage](https://doc.rust-lang.org/reference/linkage.html) | [The Rust Programming Language – Ch 7](https://doc.rust-lang.org/book/ch07-00-managing-growing-projects-with-packages-crates-and-modules.html) | [Rust By Example – Crates](https://doc.rust-lang.org/rust-by-example/mod.html) | [rustc-dev-guide – Name Resolution](https://rustc-dev-guide.rust-lang.org/name-resolution.html)

## 相关概念 {#相关概念}

- [模块系统规范](10_module_system_specification.md)
- [Linkage 与符号](20_linkage_and_symbols.md)
- [模块系统与安全抽象](40_module_safety_abstraction.md)
- [形式化工具中的模块映射](50_formal_tools_module_mapping.md)
- [知识图谱索引](../10_knowledge_graph_index.md)

---

## RFC 参考 {#rfc-参考}

> **来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)**

- [RFC 到反例自动化映射索引](../10_rfc_to_counterexample_mapping.md)
- [Rust RFCs 官方索引](https://rust-lang.github.io/rfcs/)
- [RFC 2126: Path clarity](https://rust-lang.github.io/rfcs/2126-path-clarity.html)

## 权威来源参考 {#权威来源参考}

本反例汇编参考以下 P1/P1.5/P2 权威来源：

- [RFC 2126: Path clarity](https://rust-lang.github.io/rfcs/2126-path-clarity.html)
- [Rust Reference Modules](https://doc.rust-lang.org/reference/items/modules.html)

## 学术权威参考 {#学术权威参考}

- [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)
- [Aeneas](https://aeneas-verification.github.io/)
- [RustSEM](https://link.springer.com/article/10.1007/s10703-024-00460-3)

## 社区权威参考 {#社区权威参考}

- [Inside Rust Blog](https://blog.rust-lang.org/inside-rust/)
- [This Week in Rust](https://this-week-in-rust.org/)
