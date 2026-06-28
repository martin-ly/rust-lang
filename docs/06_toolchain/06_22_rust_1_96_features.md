# Rust 1.96.0 稳定特性综述

> **代码状态**: [实现级 — 可运行示例已补充]
> **分级**: [A]
> **Bloom 层级**: L2-L3
> **对应 Rust 版本**: **1.96.0 stable**（2026-05-28）
> **最后更新**: 2026-06-26
> **状态**: ✅ 权威来源对齐完成
>
> **权威来源**:
>
> - [Announcing Rust 1.96.0](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0.html)
> - [releases.rs — 1.96.0](https://releases.rs/docs/1.96.0/)
> - [RFC 3550 — Copy-compatible Range types](https://rust-lang.github.io/rfcs/3550-new-range.html)

---

## 一、语言特性

### 1.1 `assert_matches!` / `debug_assert_matches!`

Rust 1.96.0 稳定了 `assert_matches!` 和 `debug_assert_matches!` 宏。它们等价于 `assert!(matches!(..))`，但在失败时会打印被匹配值的 `Debug` 输出，便于诊断。

**注意**：这两个宏**没有加入 prelude**，需要显式导入：

```rust
use std::assert_matches;
use std::debug_assert_matches;

let result: Result<i32, &str> = Ok(42);
assert_matches!(result, Ok(n) if n > 0);
debug_assert_matches!(result, Ok(n) if n > 0);
```

> 权威来源: [Rust 1.96.0 Release Notes — Assert matching patterns](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0.html)

### 1.2 支持 s390x vector registers 的 inline assembly

`s390x-unknown-linux-gnu` 等目标现在可以在 inline assembly 中使用 `v0`..`v31` 等 vector registers。

```rust,ignore
#[cfg(target_arch = "s390x")]
unsafe fn read_vr0() -> u128 {
    let out: u128;
    std::arch::asm!(
        "vlr {}, v0",
        out(reg) out,
    );
    out
}
```

### 1.3 `expr` metavariable 可用于 `cfg`

过程宏中现在允许将 `expr` 元变量传递给 `cfg` / `cfg_attr`，提升了宏的表达能力。

---

## 二、标准库新稳定 API

### 2.1 `core::range` Copy 类型

RFC 3550 落地：`core::range` 模块新增了 `Range`、`RangeFrom`、`RangeToInclusive` 等类型。它们实现 `IntoIterator` 而非 `Iterator`，因此可以实现 `Copy`，解决了长期以来 range 不能放在 `#[derive(Copy)]` 结构体中的问题。

```rust
use std::range::Range;

#[derive(Clone, Copy)]
struct Span(Range<usize>);

impl Span {
    fn of<'a>(&self, s: &'a str) -> &'a str {
        &s[self.0]
    }
}

let span = Span(Range { start: 1, end: 4 });
assert_eq!(span.of("hello"), "ell");
// span 实现 Copy，可再次消费
assert_eq!(span.of("world"), "orl");
```

> 注意：当前 `0..1` 语法仍产生旧的 `std::ops::Range` 类型。语言级迁移预计随 Rust 2027 Edition 完成。

### 2.2 `NonZero` 整数范围迭代

`NonZeroI8`..`NonZeroU128` 现在支持 `Range` / `RangeInclusive` 迭代。

```rust
use std::num::NonZeroU32;

let start = NonZeroU32::new(1).unwrap();
let end = NonZeroU32::new(4).unwrap();
let values: Vec<u32> = (start..=end).map(|nz| nz.get()).collect();
assert_eq!(values, vec![1, 2, 3, 4]);
```

### 2.3 `From<T> for AssertUnwindSafe<T>`

任何类型 `T` 现在可以直接通过 `AssertUnwindSafe::from(value)` 包装，简化了 catch_unwind 的边界标注。

```rust
use std::panic::AssertUnwindSafe;

let value = String::from("panic safe");
let wrapped: AssertUnwindSafe<String> = AssertUnwindSafe::from(value);
```

### 2.4 `From<T> for LazyCell<T, F>` / `LazyLock<T, F>`

1.96.0 为 `LazyCell` 和 `LazyLock` 增加了 `From<T>` 实现，允许从值直接构造（当闭包类型 `F` 兼容时）。

```rust
use std::cell::LazyCell;
use std::sync::LazyLock;

let cell: LazyCell<i32, fn() -> i32> = LazyCell::from(42);
let lock: LazyLock<i32, fn() -> i32> = LazyLock::from(2026);

assert_eq!(*cell, 42);
assert_eq!(*lock, 2026);
```

---

## 三、Cargo 与安全修复

### 3.1 同时指定 git 仓库与 alternate registry

依赖项现在可以同时声明 `git` 和 `registry`：

```toml
[dependencies]
my-crate = { version = "1.2", registry = "internal", git = "https://github.com/myorg/my-crate" }
```

本地构建使用 git 版本，`cargo publish` 使用 registry 版本。

### 3.2 修复 CVE-2026-5222 / CVE-2026-5223

| CVE | 严重度 | 影响范围 | 修复内容 |
|---|---|---|---|
| CVE-2026-5223 | Medium | 第三方 registry 用户 | 拒绝包含 symlink 的 crate tarball |
| CVE-2026-5222 | Low | 第三方 registry 用户 | 仅对 git 协议进行 `.git` 后缀规范化，避免凭证泄漏 |

仅使用 crates.io 的用户不受上述漏洞影响。

---

## 四、Rustdoc 改进

- `missing_doc_code_examples` lint 行为改进。
- 支持 `target.'cfg(..)'.rustdocflags` 配置。

---

## 五、兼容性注意事项

- WebAssembly 目标不再向 linker 传递 `--allow-undefined`；未定义符号现在是 linker error。
- 移除 `-Csoft-float` 选项。
- `avr` 目标下 `c_double` 改为 `f32` 以匹配 C 的 `double`。
- 最小外部 LLVM 版本升级到 21。

---

## 六、练习入口

- `exercises/tests/l3_rust_196_alignment.rs` — 10 个可运行测验覆盖上述特性。

---

> **权威来源**: [Rust 1.96.0 Release Notes](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0.html), [releases.rs 1.96.0](https://releases.rs/docs/1.96.0/)
