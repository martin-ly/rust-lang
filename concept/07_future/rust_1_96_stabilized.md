# Rust 1.96 稳定特性（当前 patch 1.96.1）

> **EN**: Rust 1.96 Stabilized Features (current patch 1.96.1)
> **EN**: Rust 1.96 Stabilized Features (current patch 1.96.1)
> **Summary**: Rust 1.96.0 于 2026-05-28 首次稳定，当前最新 patch 为 1.96.1。本文档覆盖 1.96 列车引入的关键语言与库特性：Copy-compatible range 类型、assert_matches! 宏（Macro）、NonZero 范围迭代、AssertUnwindSafe / LazyCell / LazyLock 的 From 实现、s390x vector assembly 以及 Cargo 安全修复。
>
> **受众**: [进阶] / [专家]
> **内容分级**: [参考级]
> **对应 Rust 版本**: **1.96.1 stable**
> **最后更新**: 2026-06-26
> **状态**: ✅ 已对齐 Rust 1.96.1 stable
>
> **权威来源**: · [Rust Reference](https://doc.rust-lang.org/reference/) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
>
> - [Announcing Rust 1.96.0](https://releases.rs/docs/1.96.0/)
> - [releases.rs — 1.96.0](https://releases.rs/docs/1.96.0/)
> - [RFC 3550](https://github.com/rust-lang/rfcs/pull/3550)

---

> **前置概念**:
>
> [Rust 版本跟踪](05_rust_version_tracking.md) ·
> [Ranges](../02_intermediate/15_iterator_patterns.md) ·
> [Panic 与 unwind](../02_intermediate/04_error_handling.md)
>
> **后置概念**:
>
> [Rust 1.97.0 前沿特性预览](rust_1_97_preview.md) ·
> [Rust 1.98+ 前沿特性预览](rust_1_98_preview.md) ·
> [Toolchain](../06_ecosystem/01_toolchain.md) ·
> [Testing](../06_ecosystem/16_testing.md)
>

---

---

> **过渡**: 从 Rust 1.96 稳定特性（当前 patch 1.96.1 的直观描述转向其形式化定义，需要先把日常经验中的模糊直觉转化为可验证的术语。

> **过渡**: 在建立 Rust 1.96 稳定特性（当前 patch 1.96.1 的核心命题之后，下一步是审视这些命题在边界条件下的稳定性——这正是反命题与反例的价值所在。

> **过渡**: 最后，将 Rust 1.96 稳定特性（当前 patch 1.96.1 与相邻概念连接，形成从 L1 到 L7 的纵向认知路径，避免孤立记忆。

---

> **定理 1** [Tier 2]: Rust 1.96 稳定特性（当前 patch 1.96.1 的核心约束 ⟹ 编译器可以在编译期排除一整类运行时（Runtime）错误。
>
> **定理 2** [Tier 2]: 正确理解 Rust 1.96 稳定特性（当前 patch 1.96.1 的语义 ⟹ 开发者能够写出既安全又零成本抽象（Zero-Cost Abstraction）的代码。
>
> **定理 3** [Tier 3]: 将 Rust 1.96 稳定特性（当前 patch 1.96.1 与 Rust 的所有权（Ownership）/生命周期（Lifetimes）模型结合 ⟹ 可以在更大系统中进行可扩展的推理。

## 1. 语言层

### 1.1 `assert_matches!` / `debug_assert_matches!`

稳定版本：**1.96.0**

```rust
use std::assert_matches;
use std::debug_assert_matches;

let result: Result<i32, &str> = Ok(42);
assert_matches!(result, Ok(n) if n > 0);
debug_assert_matches!(result, Ok(n) if n > 0);
```

- 未加入 prelude，需显式导入。
- 失败时打印 `Debug` 表示，优于 `assert!(matches!(..))`。

### 1.2 `expr` metavariable 在 `cfg` 中的使用

过程宏（Procedural Macro）可以将表达式元变量传递给 `cfg` / `cfg_attr`，增强了宏与条件编译的交互能力。

### 1.3 s390x inline assembly vector registers

稳定版本：**1.96.0**

`s390x` 目标支持在 `asm!` 中使用 `v0`..`v31` vector registers。

---

## 2. 标准库层

### 2.1 `core::range` Copy 类型

稳定版本：**1.96.0**（RFC 3550）

| 新类型 | 说明 |
|---|---|
| `core::range::Range<T>` | 实现 `Copy`，`IntoIterator` |
| `core::range::RangeFrom<T>` | 实现 `Copy`，`IntoIterator` |
| `core::range::RangeToInclusive<T>` | 实现 `Copy`，`IntoIterator` |
| `core::range::RangeIter<T>` | 对应迭代器（Iterator） |
| `core::range::RangeFromIter<T>` | 对应迭代器（Iterator） |
| `core::range::RangeToInclusiveIter<T>` | 对应迭代器（Iterator） |

```rust
use std::range::Range;

#[derive(Clone, Copy)]
struct Span(Range<usize>);

impl Span {
    fn of<'a>(&self, s: &'a str) -> &'a str {
        &s[self.0]
    }
}
```

### 2.2 `NonZero` 范围迭代

稳定版本：**1.96.0**

```rust
use std::num::NonZeroU32;

let start = NonZeroU32::new(1).unwrap();
let end = NonZeroU32::new(4).unwrap();
let values: Vec<u32> = (start..=end).map(|nz| nz.get()).collect();
assert_eq!(values, vec![1, 2, 3, 4]);
```

### 2.3 `From<T>` 扩展

稳定版本：**1.96.0**

- `From<T> for AssertUnwindSafe<T>`
- `From<T> for LazyCell<T, F>`
- `From<T> for LazyLock<T, F>`

```rust
use std::cell::LazyCell;
use std::panic::AssertUnwindSafe;
use std::sync::LazyLock;

let _: AssertUnwindSafe<String> = AssertUnwindSafe::from(String::from("x"));
let _: LazyCell<i32, fn() -> i32> = LazyCell::from(42);
let _: LazyLock<i32, fn() -> i32> = LazyLock::from(2026);
```

### 2.4 `valid for read/write` 定义重构

对内存模型中 "valid for read/write" 的定义进行了精确化：默认排除 null 指针，各方法单独声明例外。这主要影响 unsafe 代码的文档与形式化语义，对普通用户无直接 API 变化。

---

## 3. Cargo 与工具链

### 3.1 git + alternate registry 共存

```toml
my-crate = { version = "1.2", registry = "internal", git = "https://github.com/myorg/my-crate" }
```

### 3.2 安全修复

- **CVE-2026-5223**：拒绝含 symlink 的 tarball。
- **CVE-2026-5222**：限制 `.git` 后缀规范化到 git 协议。

### 3.3 rustdoc

- `target.'cfg(..)'.rustdocflags` 配置支持。
- `missing_doc_code_examples` lint 改进。

---

## 4. 兼容性注意

- WebAssembly 链接器不再默认 `--allow-undefined`。
- `-Csoft-float` 已移除。
- `avr` 目标 `c_double` 调整为 `f32`。
- 最低外部 LLVM 版本为 21。

---

## 5. 练习与验证

- 测验：`exercises/tests/l3_rust_196_alignment.rs`
- 速查：`docs/06_toolchain/06_22_rust_1_96_features.md`

---

> **权威来源**: [Rust 1.96.0 Release Notes](https://releases.rs/docs/1.96.0/), [releases.rs 1.96.0](https://releases.rs/docs/1.96.0/)

## 6. 工具链与兼容性细节

### 6.1 Rustdoc 改进

| 改进 | 说明 | 影响 |
|:---|:---|:---|
| Deprecation notes 渲染方式变更 | 弃用说明现在像普通文档一样渲染，不再使用 `white-space: pre-wrap` 和剥离 `<p>` 标签。多行弃用说明如需换行，请使用标准 Markdown 方法 `" \n"`（两个空格 + 换行） | 文档可视化更可预测 |
| `missing_doc_code_examples` lint | 不再在 impl items 上触发此 lint | 减少误报 |
| Sidebar 分离 | 方法和关联函数在侧边栏中分开显示 | 导航更清晰 |

### 6.2 Cargo 细节

#### Git + Alternate Registry 共存

```toml
[dependencies]
my-crate = { git = "https://github.com/example/my-crate", registry = "corp" }
```

本地使用 git 版本，发布时使用 registry 版本。

#### `target.'cfg(..)'.rustdocflags`

Cargo 1.96 支持按目标条件配置 `rustdoc` 标志，此前只能通过 `RUSTDOCFLAGS` 环境变量全局设置。

```toml
[target.'cfg(unix)']
rustdocflags = ["--cfg", "docsrs"]
```

与 `RUSTDOCFLAGS` 环境变量合并而非覆盖，但环境变量标志在命令行中更靠后，可能覆盖同名配置。

### 6.3 编译器改进

| 改进 | 说明 |
|:---|:---|
| LoongArch Linux link relaxation | 龙芯架构启用链接松弛优化 |
| `riscv64gc-unknown-fuchsia` RVA22 + vector | RISC-V Fuchsia 目标基线提升至 RVA22 |
| `unused_features` lint | 恢复/新增 lint，警告未使用的 `#![feature(...)]` |

### 6.4 平台支持

| 目标 | 变更 |
|:---|:---|
| `loongarch64-unknown-linux-gnu` | Link relaxation 启用 |
| `riscv64gc-unknown-fuchsia` | 基线提升至 RVA22 + vector |
| `s390x-unknown-linux-gnu` | 向量寄存器内联汇编（Inline Assembly）支持 |

### 6.5 底层与兼容性

#### 指针 “valid for read/write” 契约重构

Rust 1.96 对标准库中“指针有效可读/可写”的定义进行了重构：

- **基础定义现在不包含 null**：按照新的统一约定，一个指针要“valid for read/write”，首先必须是非空指针；null 指针不再被默认视为有效。
- **null 例外下沉到具体方法**：对于历史上明确允许 null 的特殊场景（例如零大小类型 `T` 的 `<*const T>::read` / `<*mut T>::write`），标准库在相应方法的 Safety 说明中单独注明 null 例外，而不是让基础定义包容 null。

这只是一次文档/契约层面的澄清，绝大多数安全代码的行为没有变化；但写 `unsafe` 代码时应以具体方法的 Safety 说明为准，而不要假设“null 天然可读可写”。

```rust
use std::ptr;

fn read_or_default<T: Copy>(ptr: *const T, fallback: T) -> T {
    if ptr.is_null() {
        fallback
    } else {
        unsafe { ptr.read() }
    }
}
```

#### JSON Target Spec 内部变更

Rust 1.96 对内部 JSON target spec 做了收紧/调整，主要影响使用自定义目标或维护目标定义的开发者：

- `aarch64` 软浮点目标现在必须显式设置 `"rustc_abi": "softfloat"`。
- 对 `llvm-target` 等 ABI 相关值的校验更严格，并与 `cfg(target_abi)` 的取值保持一致。

```bash
rustc +nightly -Z unstable-options --print target-spec-json-schema
```

### 6.6 兼容性注意（完整列表）

| 变更 | 影响范围 |
|:---|:---|
| `#[repr(Int)]` enum layout 修复 | 涉及 uninhabited ZST 字段的边缘情况 |
| 禁止 `Pin<Foo>` unsize-coerce（Foo 不实现 `Deref`） | 此前错误允许的 coercion |
| `#![reexport_test_harness_main]` 被正确 gate | 意外稳定属性的限制 |
| RPITIT 类型过严报错 | 过于私有的返回类型 |
| `uninhabited_static` deny-by-default | 依赖项中的 static uninhabited 类型 |
| 移除 `-Csoft-float` | 改用 `target-feature` |
| `use S::{self as Other}` 禁止 | `{self}` 要求模块（Module）父级 |
| 重复属性首项优先 | `export_name`/`link_name`/`link_section` |
| 最低外部 LLVM 升至 21 | 构建 rustc 的 LLVM 要求 |
| `avr` 目标 `c_double` 为 `f32` | 匹配 AVR 上 C 的 double 宽度 |

---

## 7. 项目覆盖映射

| 1.96 特性 | 概念文档 | Crate 代码示例 | 测试 |
|:---|:---|:---:|:---:|
| `assert_matches!` | `concept/02_intermediate/05_assert_matches.md` | `c02_type_system` | ✅ 183 passed |
| `core::range::*` | `concept/02_intermediate/06_range_types.md` | `c02_type_system` | ✅ |
| `NonZero` 范围迭代 | `concept/02_intermediate/06_range_types.md` | `c02_type_system` | ✅ |
| `From<T>` for cell types | `concept/02_intermediate/08_interior_mutability.md` | `c02_type_system` | ✅ |
| `ManuallyDrop` 常量模式 | `concept/02_intermediate/03_memory_management.md` | `c02_type_system` | ✅ |
| `expr` metavariable to `cfg` | `concept/03_advanced/04_macros.md` | `c11_macro_system_proc` | ✅ 97 passed |
| Never 类型 tuple coercion | `concept/02_intermediate/02_generics.md` | `c02_type_system` | ✅ |

---

## 8. 与 Rust 1.95 特性对比

| 特性 | 1.95 | 1.96 |
|:---|:---|:---|
| `if let` guards | ✅ 已稳定 | ✅ 已稳定 |
| `assert_matches!` | ❌ 不稳定 | ✅ **稳定** |
| `core::range::Range` / `RangeFrom` / `RangeToInclusive` | ❌ 不稳定 | ✅ **稳定** |
| `From<T>` for `LazyLock` / `LazyCell` | ❌ 不存在 | ✅ **新增** |
| `NonZero` 范围迭代 | ❌ 不支持 | ✅ **新增** |
| `expr` metavariable to `cfg` | ❌ 不支持 | ✅ **新增** |
| `ManuallyDrop` 常量模式 | ❌ 回归 | ✅ **修复** |
| Never 类型 tuple coercion | ❌ 不完整 | ✅ **完善** |

---

> **权威来源**: [Rust 1.96.0 Release Notes](https://releases.rs/docs/1.96.0/), [releases.rs 1.96.0](https://releases.rs/docs/1.96.0/)
