# Rust 1.93 稳定特性
>
> **EN**: Rust 1.93 Stabilized Features
> **Summary**: Rust 1.93 stabilized features across MaybeUninit APIs, String/Vec raw parts, VecDeque conditional pop, slice array conversion, Duration nanoseconds, and formatting helpers.
>
> **受众**: [进阶] / [专家]
> **层级**: L7 未来概念
> **Bloom 层级**: 理解 → 应用
> **Rust 版本**: 1.93.0+ (历史版本)
> **状态**: 从 `crates/c12_wasm/docs/rust_193_wasm_improvements.md` 迁移整理
>
> **主要来源**: [The Rust Reference](https://doc.rust-lang.org/reference/introduction.html) · [The Rust Programming Language](https://doc.rust-lang.org/book/title-page.html) · [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **前置概念**: [Ownership](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md) · [Type System](../../01_foundation/02_type_system/04_type_system.md) · [Unsafe Rust](../../03_advanced/02_unsafe/03_unsafe.md)
> **后置概念**: [Rust 1.92 稳定特性](rust_1_92_stabilized.md) · [Rust 版本跟踪](05_rust_version_tracking.md) · [WebAssembly 生态](../../06_ecosystem/11_domain_applications/11_webassembly.md)

---

## 一、概述

Rust 1.93.0 在标准库中稳定了一批与内存管理、容器操作和格式化相关的新 API。这些特性对 WebAssembly、嵌入式和系统编程场景尤为实用。

---

## 二、主要稳定特性

### 2.1 `MaybeUninit` 增强 API

新增 `assume_init_ref`、`assume_init_mut`、`assume_init_drop`、`write_copy_of_slice`、`write_clone_of_slice` 等方法，使未初始化内存的批量写入与安全读取更加便利。

```rust
use std::mem::MaybeUninit;

let mut buf: [MaybeUninit<u8>; 16] = [MaybeUninit::uninit(); 16];
MaybeUninit::write_copy_of_slice(&mut buf, b"hello");
let init = MaybeUninit::assume_init_ref(&buf[..5]);
```

### 2.2 `String` / `Vec` 原始部分拆分

`into_raw_parts` 将 `String` 或 `Vec` 拆分为原始指针、长度与容量三元组，便于与 FFI 或 Wasm 线性内存进行零拷贝交互。

```rust
let v = vec![1, 2, 3];
let (ptr, len, cap) = v.into_raw_parts();
// 使用 ptr/len/cap 与外部运行时交互
```

### 2.3 `VecDeque` 条件弹出

`pop_front_if` 与 `pop_back_if` 允许在满足谓词时从双端队列两端条件弹出元素，简化数据流处理。

```rust
use std::collections::VecDeque;

let mut deque: VecDeque<i32> = [1, 2, 3, 4].into_iter().collect();
let maybe_two = deque.pop_front_if(|x| *x == 1);
```

### 2.4 切片安全转固定长度数组

`<[T]>::as_array` 与 `as_mut_array` 将切片安全转换为固定长度数组引用，失败时返回 `None`。

```rust
let bytes = b"abcd";
let arr: Option<&[u8; 4]> = bytes.as_array();
```

### 2.5 `Duration::from_nanos_u128`

高精度纳秒转换为 `Duration`，适用于测量粒度低于 64 位纳秒上限的场景。

```rust
use std::time::Duration;

let d = Duration::from_nanos_u128(3_000_000_000_u128);
```

### 2.6 `char::MAX_LEN_UTF8` / `MAX_LEN_UTF16`

提供字符编码最大长度常量，用于缓冲区预分配。

```rust
let mut buf = [0u8; char::MAX_LEN_UTF8];
let len = '世'.encode_utf8(&mut buf).len();
```

### 2.7 `fmt::from_fn`

通过闭包快速构造自定义 `Display`/`Debug` 格式化器，减少样板代码。

```rust
use std::fmt;

let f = fmt::from_fn(|f, _| write!(f, "custom"));
println!("{}", f);
```

---

## 三、迁移提示

- 使用 `MaybeUninit::write_copy_of_slice` 替代手动循环写入，可减少 unsafe 代码量。
- `String`/`Vec::into_raw_parts` 与 `from_raw_parts` 配对使用，注意所有权与容量一致性。
- `as_array` 返回 `Option`，避免手动长度检查与 `try_into` 转换。

---

> **来源**: [The Rust Reference](https://doc.rust-lang.org/reference/introduction.html) · [The Rust Programming Language](https://doc.rust-lang.org/book/title-page.html) · [Rust Standard Library](https://doc.rust-lang.org/std/)
