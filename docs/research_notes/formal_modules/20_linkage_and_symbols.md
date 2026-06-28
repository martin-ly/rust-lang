# Linkage 与符号机制

> **内容分级**: [归档级]
>
> **分级**: [B]
> **Bloom 层级**: L5-L6 (分析/评价/创造)
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29
> **Rust 版本**: 1.96.0+
> **状态**: ✅ 新建完成 / 权威国际化来源对齐完成

---

## 目录

- [Linkage 与符号机制](#linkage-与符号机制)
  - [目录](#目录)
  - [研究目标](#研究目标)
  - [概念定义](#概念定义)
  - [属性关系](#属性关系)
  - [解释与论证](#解释与论证)
    - [为什么 Rust 默认要 name mangling](#为什么-rust-默认要-name-mangling)
    - [`extern crate` 的演进](#extern-crate-的演进)
    - [`#[linkage = "internal"]` 与 `static`](#linkage--internal-与-static)
  - [Rust 示例](#rust-示例)
    - [1. 基本 FFI 导出](#1-基本-ffi-导出)
    - [2. `extern crate` 别名（Rust 2018+ 场景）](#2-extern-crate-别名rust-2018-场景)
    - [3. 显式符号名](#3-显式符号名)
  - [反例与边界](#反例与边界)
  - [权威来源对照表](#权威来源对照表)

---

## 研究目标

明确 Rust crate 在编译、链接阶段的符号可见性与 linkage 规则，区分语言级可见性（visibility）与链接器级符号可见性（symbol visibility / linkage），为 unsafe FFI、动态库、嵌入式等场景提供形式化参考。

---

## 概念定义

| 术语 | 定义 |
| :--- | :--- |
| **Linkage** | 决定符号在链接阶段的作用范围。Rust 中 `static`（内部链接）、`external`（外部链接）以及通过 `#[linkage = "..."]` 指定的 LLVM linkage 类型。 |
| **`extern crate`** | 在 Rust 2015/2018 中显式声明外部 crate 依赖；在 Rust 2021+ 中，除特殊场景（如宏/重命名）外基本由 Cargo 隐式处理。 |
| **`crate-type`** | 编译目标类型：`bin`、`lib`、`rlib`、`dylib`、`staticlib`、`cdylib`、`proc-macro` 等，决定输出产物与链接约定。 |
| **`#[no_mangle]`** | 禁用 Rust 的符号混淆（mangling），使函数在目标文件中使用原始名称，便于 FFI 与动态符号查找。 |
| **符号可见性（Symbol Visibility）** | 目标文件/动态库中符号是否对外导出。Rust 默认仅导出 `pub` 且被标记为 `#[no_mangle]` 或 `extern "C"` 的函数；语言级 `pub` 不保证链接器级导出。 |

> **来源:** [Rust Reference – Linkage](https://doc.rust-lang.org/reference/items/external-blocks.html#linkage)
>
> **来源:** [Rustonomicon – FFI](https://doc.rust-lang.org/nomicon/ffi.html)
>
> **来源:** [Ferrocene Language Specification – Crates and Linkage](https://spec.ferrocene.dev/)

---

## 属性关系

```text
Source Crate
├── crate-type
│   ├── bin          → 可执行文件，符号由 linker 决定最终导出
│   ├── lib / rlib   → Rust 原生静态库，metadata + object code
│   ├── dylib        → Rust 动态库（含 metadata，可被其他 Rust crate 链接）
│   ├── cdylib       → C-compatible 动态库（无 Rust metadata）
│   └── staticlib    → C-compatible 静态库
├── Language Visibility
│   ├── pub          → 在 Rust 类型系统中可见
│   └── 默认/private → 语言级不可见
└── Symbol Visibility
    ├── #[no_mangle] / extern "C" → 指定导出名称与 ABI
    ├── #[export_name = "..."]    → 显式设置符号名
    └── 默认 mangled 名称         → 不便于外部链接
```

**关键关系：**

1. **语言可见性 ≠ 链接器符号可见性**：`pub fn foo()` 在 Rust 源程序中对其他 crate 可见，但在生成的目标文件中其符号名被 mangled，外部 C 代码无法直接链接。
2. **`#[no_mangle]` 打开链接器级接口**：它保留原始标识符，常用于 FFI 边界；同时要求标识符在全局唯一，否则触发链接错误。
3. **`crate-type` 决定 ABI 边界**：`dylib` 保留 Rust ABI 与 metadata，适合 Rust-to-Rust 动态链接；`cdylib` 只暴露 C ABI，适合跨语言边界。

> **来源:** [Rust Reference – crate-type](https://doc.rust-lang.org/reference/linkage.html)

---

## 解释与论证

### 为什么 Rust 默认要 name mangling

Name mangling 把模块路径、泛型参数、crate 哈希等信息编码到符号名中，以支持重载（函数名相同但签名不同）、泛型单态化和 crate 内唯一性。`#[no_mangle]` 关闭这一机制，代价是失去重载与泛型信息，因此通常只用于无泛型的 `extern "C"` 函数。

### `extern crate` 的演进

- Rust 2015：必须通过 `extern crate foo;` 引入依赖。
- Rust 2018：Cargo 自动注入 `extern crate`；显式声明仅用于别名或宏导出。
- Rust 2021+：更少见，依赖管理基本由 Cargo.toml 与 `use` 完成。

形式化地看，`extern crate` 在 name resolution 阶段向 crate root 注入一个外部 crate 名称空间，而 `use` 是在该名称空间内创建局部别名。

### `#[linkage = "internal"]` 与 `static`

LLVM 的 `internal` linkage 表示符号仅在当前编译单元内可见。Rust 中的 `const` 与 `static` 若未被 `pub` 或 `#[no_mangle]` 暴露，通常会被优化为内部链接，但这不是语言级保证。`#[linkage]` 属性属于 unstable feature，需要 nightly。

> **来源:** [Rustonomicon – Other reprs](https://doc.rust-lang.org/nomicon/other-reprs.html)

---

## Rust 示例

### 1. 基本 FFI 导出

```rust
// src/lib.rs
#[no_mangle]
pub extern "C" fn add(a: i32, b: i32) -> i32 {
    a + b
}
```

编译为 `cdylib` 后，C 代码可直接链接 `add` 符号：

```toml
[lib]
crate-type = ["cdylib"]
```

### 2. `extern crate` 别名（Rust 2018+ 场景）

```rust
// Cargo.toml 依赖名为 old_name，但在代码中希望使用 new_name
extern crate old_name as new_name;

pub use new_name::SomeType;
```

### 3. 显式符号名

```rust
#[export_name = "my_custom_add"]
pub extern "C" fn add(a: i32, b: i32) -> i32 {
    a + b
}
```

---

## 反例与边界

| 场景 | 代码 | 结果 |
| :--- | :--- | :--- |
| `#[no_mangle]` 泛型函数 | `#[no_mangle] pub extern "C" fn f<T>(x: T) {}` | 编译错误：mangling 是泛型单态化的基础 |
| 同名 `#[no_mangle]` | 两个 crate 都定义 `#[no_mangle] pub extern "C" fn add` | 链接错误：重复符号 |
| 语言级 `pub` 默认导出到 C | `pub fn foo() {}` | C 端看不到原始名称，符号已被 mangled |
| `dylib` 当 `cdylib` 用 | `crate-type = ["dylib"]` | C 端链接困难，且包含 Rust metadata；应使用 `cdylib` |

> **来源:** [Rust Reference – External Blocks](https://doc.rust-lang.org/reference/items/external-blocks.html)

---

## 权威来源对照表

| 概念 | Rust Reference | Rustonomicon | Ferrocene FLS | 备注 |
| :--- | :--- | :--- | :--- | :--- |
| Linkage / crate-type | [Linkage](https://doc.rust-lang.org/reference/linkage.html) | — | 对应章节 | Reference 列出全部 crate-type |
| FFI / `#[no_mangle]` | [External Blocks](https://doc.rust-lang.org/reference/items/external-blocks.html) | [FFI](https://doc.rust-lang.org/nomicon/ffi.html) | 对应章节 | Rustonomicon 侧重 unsafe 与 ABI |
| `extern crate` | [extern crate](https://doc.rust-lang.org/reference/items/extern-crates.html) | — | 对应章节 | 2018/2021 edition 已弱化 |
| Symbol Visibility | — | [FFI](https://doc.rust-lang.org/nomicon/ffi.html) | 对应章节 | 与 linker 行为相关，语言规范未完全覆盖 |

---

> **权威来源**: [Rust Reference – Linkage](https://doc.rust-lang.org/reference/linkage.html) | [Rust Reference – External Blocks](https://doc.rust-lang.org/reference/items/external-blocks.html) | [Rustonomicon – FFI](https://doc.rust-lang.org/nomicon/ffi.html) | [Ferrocene Language Specification](https://spec.ferrocene.dev/)
