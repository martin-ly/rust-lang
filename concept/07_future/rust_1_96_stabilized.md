# Rust 1.96.0 稳定特性

> **内容重叠提示**: 本文与 [`docs/06_toolchain/06_22_rust_1_96_features.md`](../../docs/06_toolchain/06_22_rust_1_96_features.md) 内容高度重叠。`docs/` 版本提供工具链参考；`concept/` 版本为项目权威主轨。
> **内容重叠提示**: 本文与 [`docs/06_toolchain/06_21_rust_1_97_features.md`](../../docs/06_toolchain/06_21_rust_1_97_features.md) 内容高度重叠。`docs/` 版本提供工具链参考；`concept/` 版本为项目权威主轨。
> **内容重叠提示**: 本文与 [`knowledge/06_ecosystem/emerging/05_rust_1_96.md`](../../knowledge/06_ecosystem/emerging/05_rust_1_96.md) 内容高度重叠。`knowledge/` 版本提供专项深入；`concept/` 版本为项目权威主轨。
> **EN**: Rust 1.96.0 Stabilized Features
> **Summary**: Rust 1.96.0（2026-05-28 stable）引入的关键语言与库特性：Copy-compatible range 类型、assert_matches! 宏（Macro）、NonZero 范围迭代、AssertUnwindSafe / LazyCell / LazyLock 的 From 实现、s390x vector assembly 以及 Cargo 安全修复。
>
> **受众**: [进阶] / [专家]
> **内容分级**: [参考级]
> **对应 Rust 版本**: **1.96.0 stable**
> **最后更新**: 2026-06-26
> **状态**: ✅ 已对齐 Rust 1.96.0 stable
>
> **权威来源**:
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
> [Rust 1.97 前沿特性预览](rust_1_97_preview.md) ·
> [Rust 1.98+ 前沿特性预览](rust_1_98_preview.md)
>

---

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
| `core::range::RangeToInclusiveIter<T>` | 对应迭代器 |

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
