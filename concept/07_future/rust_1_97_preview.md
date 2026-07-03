# Rust 1.97.0 前沿特性预览（Beta）

> **内容重叠提示**: 本文与 [`docs/02_reference/quick_reference/02_rust_197_features_cheatsheet.md`](../../docs/02_reference/quick_reference/02_rust_197_features_cheatsheet.md) 内容高度重叠。`concept/` 版本为项目权威主轨；`docs/` 版本提供快速参考。
> **代码状态**: [实现级 — 代码已补充]
>
> **EN**: Rust 1.97.0 Preview Features (Beta)
> **Summary**: Comprehensive coverage of features targeted for stabilization in Rust 1.97.0 (beta/nightly candidate, expected stable 2026-07-09), including language, standard library, toolchain, and target changes.
>
> **受众**: [进阶]
> **内容分级**: [参考级]
> **状态**: Rust 1.97.0 尚未 stable（beta/nightly 候选，预计 2026-07-09 进入 stable）
> **跟踪版本**: Rust 1.97.0 beta / nightly candidate (预计 2026-07-09 stable)
> **Rust 属性标记**: `#[stable(feature = "...", since = "1.97.0")]`
>
> **前置依赖**: [Rust 1.96 稳定特性](rust_1_96_stabilized.md) · [Toolchain](../06_ecosystem/01_toolchain.md) · [NonZero](../02_intermediate/03_memory_management.md)
> **后置概念**: [Rust 1.98 前沿特性预览](rust_1_98_preview.md)

---

> **来源**: [Rust 1.97.0 Release Notes](https://releases.rs/docs/1.97.0/) · · [Rust Reference](https://doc.rust-lang.org/reference/) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
> [Rust Project Goals 2026](https://rust-lang.github.io/rust-project-goals/2026/) ·
> [releases.rs — 1.97.0](https://releases.rs/docs/1.97.0/)
> **Nightly 探测结果（2026-07-01）**: 在最新 nightly 上运行 [`scripts/probe_rust_197_apis.rs`](../../scripts/probe_rust_197_apis.rs)，12 项候选 API 中 **9 项已可用**：`NonZero` 位操作、`char::is_control() const`、`NonZeroU32::midpoint`/`isqrt`、`ptr::fn_addr_eq`、`const size_of_val`/`align_of_val`、`BuildHasherDefault::new const`、`Box::as_ptr`、`int::format_into`。
> 尚未可用/仍需 feature gate 的 3 项：`VecDeque::truncate_front`、`VecDeque::retain_back`、`Vec::into_non_null`，大概率推迟至 **Rust 1.98.0**。发布日前请再次运行探测程序确认。

## 📑 目录

- [Rust 1.97.0 前沿特性预览（Beta）](#rust-1970-前沿特性预览beta)
  - [📑 目录](#-目录)
  - [一、语言与编译器](#一语言与编译器)
    - [1.1 `must_use` lint 扩展](#11-must_use-lint-扩展)
    - [1.2 空 `export_name` 报错](#12-空-export_name-报错)
    - [1.3 `linker-messages` 默认 warn](#13-linker-messages-默认-warn)
    - [1.4 元组索引简写修复](#14-元组索引简写修复)
    - [1.5 `pin!` 阻止隐式解引用强制](#15-pin-阻止隐式解引用强制)
  - [二、标准库 API](#二标准库-api)
    - [2.1 `NonZero` 位操作](#21-nonzero-位操作)
    - [2.2 `char::is_control()` const 稳定](#22-charis_control-const-稳定)
    - [2.3 `Option<NonZero*>` niche 编码偏好 `-1`](#23-optionnonzero-niche-编码偏好--1)
    - [2.4 `NonZeroU32::midpoint` / `isqrt`](#24-nonzerou32midpoint--isqrt)
    - [2.5 `ptr::fn_addr_eq`](#25-ptrfn_addr_eq)
    - [2.6 `const size_of_val` / `align_of_val`](#26-const-size_of_val--align_of_val)
    - [2.7 `BuildHasherDefault::new` const](#27-buildhasherdefaultnew-const)
    - [2.8 `Box::as_ptr`](#28-boxas_ptr)
    - [2.9 `Option::as_slice` / `as_mut_slice`](#29-optionas_slice--as_mut_slice)
  - [三、目标平台与工具链](#三目标平台与工具链)
    - [3.1 `cfg_target_has_atomic_equal_alignment`](#31-cfg_target_has_atomic_equal_alignment)
    - [3.2 `WSAESHUTDOWN` 映射](#32-wsaeshutdown-映射)
    - [3.3 NVIDIA GPU 目标基线提升](#33-nvidia-gpu-目标基线提升)
  - [四、推迟到 1.98 的候选特性](#四推迟到-198-的候选特性)
  - [五、迁移建议](#五迁移建议)

---

## 一、语言与编译器

### 1.1 `must_use` lint 扩展

`#[must_use]` 的lint诊断现在将 `Result<T, E>` / `ControlFlow<B, C>` 视为与其内部类型 `T`/`C` 等效。这意味着如果一个内部类型已标记 `must_use`，则包含它的 `Result` 或 `ControlFlow` 也会触发未使用警告。

```rust
#[must_use]
struct ImportantToken;

fn give_token() -> Result<ImportantToken, std::io::Error> {
    Ok(ImportantToken)
}

fn main() {
    // ⚠️ Rust 1.97+ 会警告：Result<ImportantToken, _> 的 must_use 被忽略
    give_token();
}
```

### 1.2 空 `export_name` 报错

`#[export_name = ""]` 现在被明确拒绝，避免链接器因空符号名产生歧义。

```rust,ignore
// ❌ 编译错误
#[export_name = ""]
pub fn foo() {}
```

### 1.3 `linker-messages` 默认 warn

链接器输出消息从默认 `allow` 恢复为 `warn-by-default`，帮助开发者更快发现链接阶段问题。

```bash
# 如需保持静默
RUSTFLAGS="-A linker-messages" cargo build
```

### 1.4 元组索引简写修复

在 struct 模式中，语法上拒绝元组索引简写，修复一个正确性回归，避免与字段名的意外冲突。

### 1.5 `pin!` 阻止隐式解引用强制

`pin!` 宏现在阻止隐式 deref coercions，避免 `Pin<&mut T>` 在宏内部意外转换为其他类型，减少与 self-referential 类型相关的 bug。

---

## 二、标准库 API

### 2.1 `NonZero` 位操作

`NonZeroU*` / `NonZeroI*` 新增位模式查询方法，便于在 unsafe 或性能敏感代码中直接操作非零整数的位表示。

```rust
use std::num::NonZeroU32;

let n = NonZeroU32::new(0b00010100).unwrap();
assert_eq!(n.highest_one(), 4);  // 1 << 4 = 16
assert_eq!(n.lowest_one(), 2);   // 1 << 2 = 4
assert_eq!(n.bit_width(), 5);    // 需要 5 bit 表示 20
```

### 2.2 `char::is_control()` const 稳定

`char::is_control` 现在可在 `const` 上下文调用，扩展编译期字符分类能力。

```rust
const SPACE: char = ' ';
const IS_CONTROL: bool = SPACE.is_control(); // false
```

### 2.3 `Option<NonZero*>` niche 编码偏好 `-1`

`Option<NonZero*>` 的 niche 编码现在优先使用 `-1` 表示 `None`，优化 FFI 和序列化互操作场景。

> **注意**: 这是编译器内部表示变更，不影响 Safe Rust 语义；unsafe 代码若依赖具体 niche 值需重新验证。

### 2.4 `NonZeroU32::midpoint` / `isqrt`

与整数类型的 `midpoint` 和 `isqrt` 对应，`NonZero` 变体保证结果仍为非零（在定义域内）。

```rust
use std::num::NonZeroU32;

let a = NonZeroU32::new(10).unwrap();
let b = NonZeroU32::new(20).unwrap();
assert_eq!(a.midpoint(b).get(), 15);

let n = NonZeroU32::new(25).unwrap();
assert_eq!(n.isqrt().get(), 5);
```

### 2.5 `ptr::fn_addr_eq`

提供一种可移植的函数指针地址比较方式，处理 `fn` 指针在比较时可能涉及的 provenance 问题。

```rust
fn a() {}
fn b() {}

assert!(std::ptr::fn_addr_eq(a, a));
assert!(!std::ptr::fn_addr_eq(a, b));
```

### 2.6 `const size_of_val` / `align_of_val`

`std::mem::size_of_val` 和 `std::mem::align_of_val` 现在可在 `const` 上下文调用。

```rust
const BUF: [u8; 10] = [0; 10];
const SIZE: usize = std::mem::size_of_val(&BUF);   // 10
const ALIGN: usize = std::mem::align_of_val(&BUF); // 1
```

### 2.7 `BuildHasherDefault::new` const

`BuildHasherDefault::new` 成为 `const fn`，允许在编译期构造默认哈希器。

```rust
use std::hash::BuildHasherDefault;
use std::collections::hash_map::DefaultHasher;

const HASHER: BuildHasherDefault<DefaultHasher> = BuildHasherDefault::new();
```

### 2.8 `Box::as_ptr`

`Box<T>` 新增 `as_ptr` 方法，无需先解引用即可获取堆分配对象的裸指针。

```rust
let b = Box::new(42);
let p = Box::as_ptr(&b);
assert_eq!(unsafe { *p }, 42);
```

### 2.9 `Option::as_slice` / `as_mut_slice`

`Option<T>` 可直接转换为切片视图，`Some(x)` → `[x]`，`None` → `[]`。

```rust
let opt = Some(42);
assert_eq!(opt.as_slice(), &[42]);

let none: Option<i32> = None;
assert_eq!(none.as_slice(), &[]);
```

---

## 三、目标平台与工具链

### 3.1 `cfg_target_has_atomic_equal_alignment`

新增 cfg 条件，用于检测目标平台上所有原子类型的对齐是否等于其对应整数类型的对齐。

```rust
#[cfg(target_has_atomic_equal_alignment = "ptr")]
fn optimized_ptr_atomic() {
    // 可依赖指针大小原子与 usize 对齐相同的平台
}
```

### 3.2 `WSAESHUTDOWN` 映射

Windows 套接字错误 `WSAESHUTDOWN` 现在正确映射为 `io::ErrorKind::BrokenPipe`，统一跨平台错误语义。

### 3.3 NVIDIA GPU 目标基线提升

`nvptx64-nvidia-cuda` 目标在 Rust 1.97 提升硬件基线：

| 维度 | 旧基线 | 新基线（1.97+） |
|:---|:---|:---|
| PTX ISA | 6.0 | 7.0 |
| 最低 SM | sm_50 (Maxwell) / sm_52 (Pascal) | sm_70 (Volta) |

影响：pre-Volta GPU 不再被默认支持；未指定 `-C target-cpu` 时默认变为 `sm_70`。

---

## 四、推迟到 1.98 的候选特性

以下特性原被讨论为 1.97 候选，但因 beta cutoff 错过 1.97，将进入 **Rust 1.98.0**（预计 2026-08-20 稳定）：

| 特性 | 说明 |
|:---|:---|
| `core::range::{legacy, RangeFull, RangeTo}` | RFC 3550 range 类型补全 |
| `NonZero<T>::from_str_radix` | 非零整数按进制解析 |
| `float_algebraic` | 浮点代数运算 intrinsics |
| `int_format_into` | 整数零分配格式化到缓冲区 |
| `PathBuf::into_string` | `PathBuf` 零成本转 `String` |
| `Result::map_or_default` / `Option::map_or_default` | 便捷默认值映射 |
| `VecDeque::truncate_front` / `retain_back` | 双端队列对称 API |

---

## 五、迁移建议

1. **升级工具链**

   ```bash
   rustup update stable
   cargo update
   ```

2. **审查 `must_use` 扩展带来的新警告**
   - 搜索项目中 `Result<#[must_use] T, E>` 的未使用处。
   - 使用 `let _ = ...;` 显式忽略，或改用 `?`/`if let` 处理。

3. **利用 `NonZero` 位操作优化性能代码**
   - 替换手动 `trailing_zeros`/`leading_zeros` 的边界检查。

4. **NVIDIA GPU 项目**
   - 确认目标硬件是否为 Volta+；如需支持旧 GPU，显式指定 `-C target-cpu=sm_52` 等。

5. **不要提前依赖 1.98 特性**
   - `float_algebraic`、`RandomSource`、`VecDeque::truncate_front` 等仍不稳定或属于 1.98。

---

> **对应练习**: [`exercises/src/rust_197/`](../../exercises/src/rust_197)
