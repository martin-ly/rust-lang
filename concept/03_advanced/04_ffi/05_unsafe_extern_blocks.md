> **内容分级**: [专家级]
>
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **本节关键术语**: unsafe extern blocks · safe extern · FFI · unsafe boundary · unsafe-op-in-unsafe-fn · edition migration — [完整对照表](../../00_meta/01_terminology/01_terminology_glossary.md)

# `unsafe extern blocks`：Edition 2024 的 FFI 安全边界

> **EN**: `unsafe extern blocks` in Rust Edition 2024
> **Summary**: Rust Edition 2024 makes `extern` blocks syntactically `unsafe`, introduces `safe` FFI declarations, and provides a migration lint to close the implicit-trust hole in pre-2024 FFI bindings.
> **受众**: [专家]
> **Bloom 层级**: L3-L4
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **S+P** — Structure + Procedure
> **双维定位**: S×Eva — 评判 extern 块的安全边界声明是否充分
> **定位**: 系统分析 Rust Edition 2024 对 `extern` 块的安全语义调整：从旧式块本身为 safe item 的隐患，到 `unsafe extern {}` 的显式 unsafe 契约，再到块内 `safe fn` 的审计机制，以及 `rust_2024_compatibility` lint 的迁移路径。
> **前置概念**:
> [Rust FFI](01_rust_ffi.md) ·
> [Unsafe Rust](../02_unsafe/01_unsafe.md) ·
> [Unsafe 边界全景](../02_unsafe/02_unsafe_boundary_panorama.md) ·
> [Linkage](03_linkage.md) ·
> [Type System](../../01_foundation/02_type_system/01_type_system.md) ·
> [Memory Management](../../02_intermediate/02_memory_management/01_memory_management.md)
> **后置概念**:
> [Async FFI 边界](04_async_ffi_boundary.md) ·
> [FFI 高级主题](02_ffi_advanced.md) ·
> [Rust 内存模型](../02_unsafe/06_memory_model.md)

---

> **来源**:
> [Rust Reference — External Blocks](https://doc.rust-lang.org/reference/items/external-blocks.html) ·
> [Rust Edition Guide 2024 — unsafe extern blocks](https://doc.rust-lang.org/edition-guide/rust-2024/unsafe-extern.html) ·
> [RFC 3484 — unsafe extern blocks](https://rust-lang.github.io/rfcs/3484-unsafe-extern-blocks.html) ·
> [The Rustonomicon — FFI](https://doc.rust-lang.org/nomicon/ffi.html)

---

## 🧠 知识结构图

```mermaid
mindmap
  root((unsafe extern blocks))
    旧式问题
      extern {} 块为 safe item
      隐式信任外部代码
    Edition 2024 变化
      unsafe extern {}
      块内函数自动 unsafe fn
      safe fn 显式审计
    safe FFI
      块内 safe fn 声明
      extern "C" fn 安全定义
      unsafe extern "C" fn 契约定义
      安全契约文档化
    迁移路径
      rust_2024_compatibility lint
      cargo fix 自动迁移
    判定规则
      何时 unsafe extern
      何时 safe fn
      跨 Edition 差异
    边界测试
      忘记 unsafe 调用
      错误 safe 声明致 UB
      跨 Edition 混用
```

## 📑 目录

- [`unsafe extern blocks`：Edition 2024 的 FFI 安全边界](#unsafe-extern-blocksedition-2024-的-ffi-安全边界)
  - [🧠 知识结构图](#-知识结构图)
  - [📑 目录](#-目录)
  - [一、核心概念](#一核心概念)
    - [1.1 旧式 `extern {}` 的语义漏洞](#11-旧式-extern--的语义漏洞)
    - [1.2 Edition 2024：`unsafe extern {}`](#12-edition-2024unsafe-extern-)
    - [1.3 `safe` FFI：显式声明已审计边界](#13-safe-ffi显式声明已审计边界)
      - [位置 A：`unsafe extern` 块内的 `safe fn` 声明](#位置-aunsafe-extern-块内的-safe-fn-声明)
      - [位置 B：函数定义的语义对称](#位置-b函数定义的语义对称)
    - [1.4 迁移路径：`rust_2024_compatibility` lint](#14-迁移路径rust_2024_compatibility-lint)
  - [二、判定规则](#二判定规则)
    - [2.1 何时使用 `unsafe extern {}`](#21-何时使用-unsafe-extern-)
    - [2.2 何时使用 `safe fn`](#22-何时使用-safe-fn)
      - [块内 `safe fn` 声明](#块内-safe-fn-声明)
      - [函数定义：`extern "C" fn` 与 `unsafe extern "C" fn`](#函数定义extern-c-fn-与-unsafe-extern-c-fn)
    - [2.3 2021 Edition 与 2024 Edition 的行为差异](#23-2021-edition-与-2024-edition-的行为差异)
  - [三、边界测试 / 反例](#三边界测试--反例)
    - [3.1 反例：2024 Edition 下忘记 `unsafe` 调用 extern 函数](#31-反例2024-edition-下忘记-unsafe-调用-extern-函数)
    - [3.2 反例：错误声明 `safe` 但实际会触发 UB 的外部函数](#32-反例错误声明-safe-但实际会触发-ub-的外部函数)
    - [3.3 反例：跨 Edition 混用导致的兼容性错误](#33-反例跨-edition-混用导致的兼容性错误)
  - [四、与 `unsafe_op_in_unsafe_fn` 及 unsafe 契约的关系](#四与-unsafe_op_in_unsafe_fn-及-unsafe-契约的关系)
    - [`unsafe_op_in_unsafe_fn` 的协同作用](#unsafe_op_in_unsafe_fn-的协同作用)
    - [unsafe 契约的三层结构](#unsafe-契约的三层结构)
  - [五、最佳实践与检查清单](#五最佳实践与检查清单)
    - [编写 Edition 2024 FFI 绑定的检查清单](#编写-edition-2024-ffi-绑定的检查清单)
    - [常见误区](#常见误区)
  - [六、相关概念](#六相关概念)
  - [🧭 思维导图（Mindmap）](#-思维导图mindmap)

---

## 一、核心概念

### 1.1 旧式 `extern {}` 的语义漏洞

在 Rust Edition 2021 及之前，`extern "ABI" { ... }` 块本身是一个**safe item**：声明它不需要 `unsafe` 上下文，可以出现在模块（Module）级别。然而，块内声明的函数**默认仍是 `unsafe fn`**，调用者仍需在调用点写 `unsafe` 块：

```rust,edition2021
// Edition 2021：块本身是 safe item，但调用仍需 unsafe
extern "C" {
    fn abs(x: i32) -> i32;
}

fn main() {
    // 调用仍需 unsafe 块
    unsafe {
        println!("{}", abs(-3));
    }
}
```

> **问题本质**：`extern` 块声明的是**编译器无法验证的外部符号**。外部函数的签名是否正确、是否遵守 Rust 的内存安全（Memory Safety）与别名规则，完全依赖 `extern` 块作者的人工审计。但旧式语法把这份「对外部代码的信任断言」隐藏在一个 safe item 中——块本身不要求 `unsafe`，读者难以直观判断谁应为签名错误导致的 UB 负责。
>
> 这造成责任边界模糊：如果 `extern` 块中的签名写错，运行时（Runtime） UB 应归咎于**写块的人**还是**调用者**？Rust 2024 的答案是前者，因此要求 `extern` 块本身显式标注 `unsafe`。

---

### 1.2 Edition 2024：`unsafe extern {}`

Rust Edition 2024 通过 [RFC 3484](https://rust-lang.github.io/rfcs/3484-unsafe-extern-blocks.html) 修改了 `extern` 块的语法：

- `extern "ABI" { ... }`（不带 `unsafe`）在 Edition 2024 下是**编译错误**。
- 必须写为 `unsafe extern "ABI" { ... }`。
- 块内所有函数声明**自动视为 `unsafe fn`**，调用时必须使用 `unsafe` 块或处于 `unsafe` 函数中。

```rust
// Edition 2024：正确的声明方式
unsafe extern "C" {
    fn abs(x: i32) -> i32;
}

fn main() {
    unsafe {
        println!("{}", abs(-3));
    }
}
```

> **语义变化**：`unsafe` 从「允许写 unsafe 代码的上下文」转变为对 `extern` 块本身的**修饰**，明确表示「该块内所有外部符号都是不可验证的，调用它们需要 unsafe」。
>
> 这一改动不影响 `extern "C" fn` 的定义式：在 Rust 中实现的 `extern "C" fn` 仍然是 safe 函数（其内部若使用 unsafe，已在定义处隔离）。

---

### 1.3 `safe` FFI：显式声明已审计边界

Edition 2024 在 `unsafe extern {}` 块内引入 `safe` 安全限定符，用于**显式声明某个外部符号已被审计为安全**，从而撤销调用处的 `unsafe` 块要求：

#### 位置 A：`unsafe extern` 块内的 `safe fn` 声明

```rust
unsafe extern "C" {
    safe fn abs(x: i32) -> i32; // 已审计：调用时无需 unsafe 块
}

fn main() {
    println!("{}", abs(-3)); // ✅ 不需要 unsafe
}
```

> **契约**：写 `safe fn` 等于承诺「该外部函数的行为满足 Rust 安全契约」——不会破坏内存安全、不会引入数据竞争、不会违反其签名对应的生命周期（Lifetimes）与别名规则。这个承诺是**人工审计结论**，编译器不验证。

#### 位置 B：函数定义的语义对称

Edition 2024 的 `safe` 限定符**不用于顶层函数定义**。暴露给 C 的 Rust 函数仍用普通 `extern "C" fn` 定义，它本身就是 safe 函数：

```rust,ignore
// 将 Rust 函数暴露给 C，这是一个 safe 函数
#[unsafe(no_mangle)]
pub extern "C" fn rust_add(a: i32, b: i32) -> i32 {
    a + b
}
```

> **注意**：`safe` 作为安全限定符目前**仅在 `unsafe extern {}` 块内**用于声明外部符号。顶层 `extern "C" fn` 定义式本身就是 safe 的，无需也不支持额外加 `safe`。`unsafe extern "C" fn` 则用于定义「对 C 暴露但调用者需满足额外契约」的 unsafe 函数。

---

### 1.4 迁移路径：`rust_2024_compatibility` lint

对于仍在 Edition 2021 编写的 crate，可以通过启用 `rust_2024_compatibility` lint 提前发现需要迁移的位置：

```toml
# Cargo.toml
[package]
edition = "2021"

[lints.rust]
rust_2024_compatibility = "warn"
```

启用后，编译器会对以下情况发出警告：

- `extern "C" { ... }` 块未标注 `unsafe`；
- 块内需要显式标注 `safe` 或接受默认 unsafe；
- `extern fn` 裸写（RFC 3722 同时推动 ABI 字符串显式化）。

运行 `cargo fix --edition` 可以自动将大多数旧式 `extern` 块改写为 `unsafe extern` 块，并保留原有语义（块内函数默认 unsafe）。随后人工审计哪些函数可以加上 `safe`。

> **迁移原则**：
>
> 1. 先机械迁移：`extern "C" { ... }` → `unsafe extern "C" { ... }`；
> 2. 再人工审计：对确认安全的外部函数加上 `safe fn`；
> 3. 不要批量加 `safe`——每个 `safe` 都是一份不可由编译器验证的契约。

---

## 二、判定规则

### 2.1 何时使用 `unsafe extern {}`

默认情况下，所有 Edition 2024 的 extern 块都应使用 `unsafe extern {}`：

```rust,ignore
unsafe extern "C" {
    fn some_external_api(x: *const u8, len: usize) -> i32;
}
```

**适用场景**：

| 场景 | 说明 |
|:---|:---|
| 调用 C/C++ 等外部库 | 外部实现不在 Rust 控制范围内 |
| 外部函数签名由头文件/文档给出 | 任何签名错配都是 ABI 级 UB |
| 外部函数可能读写全局状态 | 违反 Rust 的别名/线程安全假设 |
| 尚未完成人工安全审计 | 保持默认 unsafe，避免过早 `safe` |

---

### 2.2 何时使用 `safe fn`

#### 块内 `safe fn` 声明

仅当满足以下全部条件时，才在 `unsafe extern` 块内写 `safe fn`：

1. **签名正确**：参数类型、返回类型、ABI 字符串与外部实现完全一致；
2. **行为可验证**：外部函数不会触发未定义行为（UB），只要传入合法参数；
3. **不破坏 Rust 不变量**：不会绕过借用（Borrowing）检查、不会制造数据竞争、不会返回悬垂指针；
4. **文档化**：在代码注释或安全封装层中说明审计依据。

典型例子是 C 标准库中已知纯函数：

```rust,ignore
unsafe extern "C" {
    safe fn abs(x: i32) -> i32;
    safe fn strlen(s: *const std::ffi::c_char) -> usize; // 需保证传入有效 NUL 结尾字符串
}
```

> **注意**：即使 `strlen` 是 C 标准库函数，标注 `safe` 仍然要求调用者保证指针有效。`safe` 不消除前置条件，只是把「调用处写 `unsafe` 块」的要求移除。前置条件必须在类型系统（Type System）或文档中表达。

#### 函数定义：`extern "C" fn` 与 `unsafe extern "C" fn`

把 Rust 函数暴露给 C 时，使用 `extern "C" fn` 定义 safe 函数：

```rust,ignore
#[unsafe(no_mangle)]
pub extern "C" fn compute_sum(a: i32, b: i32) -> i32 {
    a.checked_add(b).unwrap_or(i32::MAX)
}
```

如果该函数对调用者有额外前置条件（例如要求传入的指针有效），则定义为 `unsafe extern "C" fn`，在 Rust 文档和语义上明确其为 unsafe：

```rust,ignore
#[unsafe(no_mangle)]
pub unsafe extern "C" fn compute_with_ptr(ptr: *const i32) -> i32 {
    // 函数体仍需为每个 unsafe 操作写 unsafe 块（受 unsafe_op_in_unsafe_fn 约束）
    unsafe { ptr.read() }
}
```

> **与块内 `safe fn` 的区别**：块内 `safe fn` 改变的是**外部声明**的调用语义；顶层 `extern "C" fn` / `unsafe extern "C" fn` 改变的是**Rust 函数对外暴露**的语义。两者应用场景不同，不要混淆。

---

### 2.3 2021 Edition 与 2024 Edition 的行为差异

| 特性 | Edition 2021 | Edition 2024 |
|:---|:---|:---|
| `extern "C" { fn f(); }` | ✅ 合法，块本身是 safe item | ❌ 编译错误：`extern blocks must be unsafe` |
| `unsafe extern "C" { fn f(); }` | ❌ 不支持该语法 | ✅ 合法，块内函数默认 unsafe fn |
| 调用 extern 函数是否需要 `unsafe` | 需要（块内函数默认 unsafe fn） | 需要（除非声明为 `safe fn`） |
| `safe fn` 声明 | 不支持 | ✅ 支持，调用处无需 `unsafe` |
| `safe` 安全限定符 | 不支持 | ✅ 仅支持在 `unsafe extern {}` 块内使用 |
| 迁移 lint | 无 | `rust_2024_compatibility` |

> **关键洞察**：Edition 2024 并没有改变 FFI 的**运行时语义**——外部代码仍然不可验证。它改变的是**语法层面如何表达信任**：把隐式的「extern 块本身是 safe item」改为显式的「extern 块必须标注 unsafe，块内 safe 符号需要单独标注」。

---

## 三、边界测试 / 反例

### 3.1 反例：2024 Edition 下忘记 `unsafe` 调用 extern 函数

在 Edition 2024 中，`unsafe extern` 块内的函数默认是 `unsafe fn`，safe Rust 代码中直接调用会导致编译错误。

```rust,compile_fail
unsafe extern "C" {
    fn c_compute(x: i32) -> i32;
}

fn main() {
    // ❌ 编译错误：调用 `unsafe fn` 需要 `unsafe` 块或 `unsafe` 函数
    let result = c_compute(42);
    println!("{}", result);
}
```

**错误信息示例**：

```text
error[E0133]: call to unsafe function is unsafe and requires unsafe function or block
  --> src/main.rs:7:18
   |
7  |     let result = c_compute(42);
   |                  ^^^^^^^^^^^^^ call to unsafe function
```

**修正**：

```rust,ignore
unsafe extern "C" {
    fn c_compute(x: i32) -> i32;
}

fn main() {
    let result = unsafe { c_compute(42) };
    println!("{}", result);
}
```

> **教学要点**：这个编译错误是 Edition 2024 刻意引入的。它强迫调用者在每次调用点思考「我正在跨越 Rust 安全边界」。

---

### 3.2 反例：错误声明 `safe` 但实际会触发 UB 的外部函数

`safe fn` 是人工审计承诺，错误标注会制造**看似 safe 实则 UB** 的陷阱。

```rust,ignore
unsafe extern "C" {
    // ❌ 错误：此函数并非对所有输入都安全
    safe fn c_deref(ptr: *const i32) -> i32;
}

fn main() {
    // 看似 safe，实则如果传入空指针即 UB
    let ptr: *const i32 = std::ptr::null();
    let _ = c_deref(ptr); // 运行时 UB，编译器无法捕获
}
```

**正确做法**：

```rust,ignore
unsafe extern "C" {
    // 保持 unsafe，让调用者负责前置条件
    fn c_deref(ptr: *const i32) -> i32;
}

fn safe_deref(ptr: *const i32) -> Option<i32> {
    if ptr.is_null() {
        None
    } else {
        Some(unsafe { c_deref(ptr) })
    }
}
```

> **核心原则**：`safe` 标注不能替代**类型系统层面的前置条件检查**。如果外部函数对输入有要求（非空、有效生命周期、特定线程上下文等），要么在 safe 封装层中检查，要么不要标注 `safe`。

---

### 3.3 反例：跨 Edition 混用导致的兼容性错误

当一个 workspace 中同时存在 Edition 2021 和 Edition 2024 的 crate 时，extern 块的语法差异可能导致 macro、inline 或共享绑定代码编译失败。

```rust,edition2021,ignore
// 在 Edition 2021 crate 中编写的绑定宏展开结果
extern "C" {
    fn legacy_api(x: i32) -> i32;
}

fn main() {
    unsafe { legacy_api(1); }
}
```

如果上述代码通过 `include!`、宏（Macro）展开或复制粘贴进入 Edition 2024 crate，会产生：

```text
error: extern blocks must be unsafe
  --> src/generated.rs:1:1
   |
1  | / extern "C" {
2  | |     fn legacy_api(x: i32) -> i32;
3  | | }
   | |_^
```

**修正策略**：

1. 在代码生成工具（如 `bindgen`）中指定目标 Edition，让它生成 `unsafe extern "C" { ... }`；
2. 对跨 Edition 共享的 FFI 绑定，统一升级到 Edition 2024 语法；
3. 如果必须保留旧语法，使用 `cfg(edition = "2021")` 等条件编译隔离（实际项目极少需要）。

> **工程建议**：大型项目迁移到 Edition 2024 时，应优先统一 FFI 绑定生成流程，而不是让不同 crate 的 extern 块语法长期分叉。

---

## 四、与 `unsafe_op_in_unsafe_fn` 及 unsafe 契约的关系

### `unsafe_op_in_unsafe_fn` 的协同作用

`unsafe_op_in_unsafe_fn` 是一个 lint（已在 Edition 2024 默认 `deny`），它要求**在 `unsafe fn` 内部，每一次 unsafe 操作仍需显式使用 `unsafe` 块**。这与 `unsafe extern` 块形成互补：

```rust,ignore
unsafe extern "C" {
    fn c_alloc(size: usize) -> *mut u8;
}

// unsafe fn 内部仍需为每个 unsafe 操作写 unsafe 块
unsafe fn use_c_alloc(size: usize) -> *mut u8 {
    let ptr = unsafe { c_alloc(size) }; // ✅ 显式
    ptr
}

fn main() {
    let _ = unsafe { use_c_alloc(16) };
}
```

如果没有 `unsafe_op_in_unsafe_fn`（或显式 `#![allow(unsafe_op_in_unsafe_fn)]`），旧式写法允许在 `unsafe fn` 内直接调用 unsafe 函数而不加 `unsafe` 块。Edition 2024 默认收紧这一行为，使得 unsafe 契约的层级更加清晰：

```text
unsafe extern "C" { fn f(); }   // 声明层：外部符号不可验证
        ↓
unsafe fn wrapper() {            // 函数层：封装者承担安全责任
    unsafe { f(); }              // 操作层：每次 unsafe 调用仍需显式
}
        ↓
pub fn safe_api() {              // 公开层：对外暴露 safe 接口
    unsafe { wrapper(); }
}
```

### unsafe 契约的三层结构

| 层级 | 关键字/语法 | 责任方 | 是否可机械迁移 |
|:---|:---|:---|:---:|
| 声明外部符号 | `unsafe extern "C" { ... }` | 声明者：承认外部代码不可验证 | ✅ |
| 标注已审计符号 | `safe fn`（块内） | 审计者：人工确认满足安全契约 | ❌（需人工） |
| 隔离 unsafe 操作 | `unsafe { ... }` | 调用者：满足前置条件 | ✅（lint 辅助） |

> **关键洞察**：`unsafe extern` 块解决的是「声明处隐式 safe」的问题；`unsafe_op_in_unsafe_fn` 解决的是「`unsafe fn` 内部隐式 unsafe」的问题。两者共同把 FFI 的安全边界从「一处声明、到处安全」改为「层层显式、处处负责」。

---

## 五、最佳实践与检查清单

### 编写 Edition 2024 FFI 绑定的检查清单

```text
□ extern 块必须带 unsafe：unsafe extern "ABI" { ... }
□ ABI 字符串显式化：优先写 extern "C"，不写裸 extern
□ 默认将块内函数视为 unsafe fn，调用处加 unsafe 块
□ 仅对完成人工审计的函数标注 safe fn
□ safe 标注需伴随文档：说明审计依据与前置条件
□ 对外暴露的 FFI 封装应是 safe 函数，内部 unsafe 块尽可能小
□ 启用 rust_2024_compatibility lint 提前迁移旧代码
□ 代码生成工具（bindgen）配置为生成 2024 风格语法
```

### 常见误区

| 误区 | 正确理解 |
|:---|:---|
| `unsafe extern` 让外部代码变安全了 | ❌ 没有。它只是显式标记了不可验证性 |
| `safe fn` 可以随便加 | ❌ 每个 `safe` 都是一份人工审计契约 |
| `safe` 可用于顶层 `extern "C" fn` | ❌ 错误。`safe` 限定符仅在 `unsafe extern {}` 块内有效 |
| 迁移时只需 `cargo fix` 即可 | ⚠️ 机械迁移后必须人工审计 safe 标注 |

---

## 六、相关概念

- [Rust FFI](01_rust_ffi.md) — FFI 安全边界、ABI 与类型映射
- [FFI 高级主题](02_ffi_advanced.md) — 不透明类型、回调、panic 边界
- [Linkage](03_linkage.md) — 链接属性、`#[link]`、RFC 3722 ABI 显式化
- [Async FFI 边界](04_async_ffi_boundary.md) — async 上下文中的 FFI 调用
- [Unsafe Rust](../02_unsafe/01_unsafe.md) — unsafe Rust 基础语义
- [Unsafe 边界全景](../02_unsafe/02_unsafe_boundary_panorama.md) — unsafe 边界的系统视角
- [Rust 内存模型](../02_unsafe/06_memory_model.md) — unsafe 代码的内存模型基础
- [Type System](../../01_foundation/02_type_system/01_type_system.md) — Rust 类型系统基础
- [Memory Management](../../02_intermediate/02_memory_management/01_memory_management.md) — 内存管理模型

---

> **权威来源**: [Rust Reference — External Blocks](https://doc.rust-lang.org/reference/items/external-blocks.html) · [Rust Edition Guide 2024 — unsafe extern blocks](https://doc.rust-lang.org/edition-guide/rust-2024/unsafe-extern.html) · [RFC 3484](https://rust-lang.github.io/rfcs/3484-unsafe-extern-blocks.html) · [The Rustonomicon — FFI](https://doc.rust-lang.org/nomicon/ffi.html)
> **权威来源对齐变更日志**: 2026-07-15 创建，对齐 Rust 1.97.0+ (Edition 2024)

**文档版本**: 1.0
**最后更新**: 2026-07-15
**状态**: ✅ 概念文件创建完成

---

## 🧭 思维导图（Mindmap）

```mermaid
mindmap
  root((unsafe extern blocks))
    旧式 extern 块问题
      块本身为 safe item
      信任断言被隐藏
      责任边界模糊
    Edition 2024 语法
      unsafe extern "C" {}
      块内函数自动 unsafe fn
      调用需 unsafe 块
    safe FFI 机制
      块内 safe fn 声明
      extern "C" fn 安全定义
      unsafe extern "C" fn 契约定义
      人工审计契约
    迁移与兼容性
      rust_2024_compatibility lint
      cargo fix 机械迁移
      人工审计 safe 标注
    判定规则
      默认 unsafe extern
      safe 仅用于已审计函数
      跨 Edition 需统一语法
    反例与边界
      忘记 unsafe 调用
      错误 safe 声明导致 UB
      跨 Edition 混用错误
    与 unsafe 契约的关系
      unsafe_op_in_unsafe_fn
      三层责任结构
      显式化安全边界
```
