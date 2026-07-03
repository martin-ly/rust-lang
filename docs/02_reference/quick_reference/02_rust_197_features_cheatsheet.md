# Rust 1.97 特性速查表（beta / nightly 候选） {#rust-197-特性速查表}

> **EN**: Rust 197 Features Cheatsheet (Beta / Nightly Candidate)
> **Summary**: Rust 1.97 特性速查表（beta / nightly 候选）。当前最新稳定版为 1.96.1，1.97 尚未 stable。
> **权威来源**: 本文对应权威来源为 [`concept/07_future/rust_1_97_preview.md`](../../../../concept/07_future/rust_1_97_preview.md)。
> 本文与权威来源内容高度重叠；`concept/` 版本为项目权威主轨，本文保留作为快速参考。
> **分级**: [A]
> **Bloom 层级**: L2 (理解)
> **版本**: Rust 1.97
> **更新日期**: 2026-06-09
> **适用版本**: stable (预计 2026-07-XX 发布)
> **MSRV 注意**: 本项目当前 MSRV 为 1.96.1。1.97 API 使用 `#![allow(clippy::incompatible_msrv)]` 标注，
> 当前需要 nightly 1.98.0 编译器才能实际使用；待 1.97 进入 stable 后可改用 stable 编译器。
>
> **受众**: [初学者] / [进阶]
> **内容分级**: [实验级]

---

## 目录 {#目录}

- [Rust 1.97 特性速查表 {#rust-197-特性速查表}](#rust-197-特性速查表-rust-197-特性速查表)
  - [目录 {#目录}](#目录-目录)
  - [语言特性 {#语言特性}](#语言特性-语言特性)
    - [AsyncFn\* trait family 加入 prelude {#asyncfn-trait-family-加入-prelude}](#asyncfn-trait-family-加入-prelude-asyncfn-trait-family-加入-prelude)
  - [核心标准库 API {#核心标准库-api}](#核心标准库-api-核心标准库-api)
    - [数值计算 {#数值计算}](#数值计算-数值计算)
    - [指针与 Strict Provenance {#指针与-strict-provenance}](#指针与-strict-provenance-指针与-strict-provenance)
    - [网络/IP 地址 {#网络ip-地址}](#网络ip-地址-网络ip-地址)
    - [文件系统 {#文件系统}](#文件系统-文件系统)
    - [错误处理 {#错误处理}](#错误处理-错误处理)
    - [集合与迭代器 {#集合与迭代器}](#集合与迭代器-集合与迭代器)
    - [异步 {#异步}](#异步-异步)
    - [其他 {#其他}](#其他-其他)
  - [Const 上下文稳定 {#const-上下文稳定}](#const-上下文稳定-const-上下文稳定)
  - [Cargo 改进 {#cargo-改进}](#cargo-改进-cargo-改进)
  - [快速参考示例 {#快速参考示例}](#快速参考示例-快速参考示例)
    - [二分搜索中点（无溢出） {#二分搜索中点无溢出}](#二分搜索中点无溢出-二分搜索中点无溢出)
    - [异步闭包 trait 约束 {#异步闭包-trait-约束}](#异步闭包-trait-约束-异步闭包-trait-约束)
    - [严格 provenance 模式 {#严格-provenance-模式}](#严格-provenance-模式-严格-provenance-模式)
  - [迁移检查清单 {#迁移检查清单}](#迁移检查清单-迁移检查清单)
  - [相关链接 {#相关链接}](#相关链接-相关链接)

---

## 语言特性 {#语言特性}

> **[来源: Rust 1.97 Release Notes](https://github.com/rust-lang/rust/releases/tag/1.97.0)**

### AsyncFn* trait family 加入 prelude {#asyncfn-trait-family-加入-prelude}

Rust 1.85.0 将 `AsyncFn`, `AsyncFnMut`, `AsyncFnOnce` 三个 trait 加入标准 prelude（所有 Edition），
允许像使用普通闭包一样使用异步闭包，无需显式导入。

```rust
async fn call_async<F>(f: F, arg: i32) -> i32
where
    F: AsyncFn(i32) -> i32,
{
    f(arg).await
}

// 使用
let result = call_async(async |x| x * 2, 21).await;
```

---

## 核心标准库 API {#核心标准库-api}

> **[来源: Rust Standard Library](https://doc.rust-lang.org/std/)**

### 数值计算 {#数值计算}

| API | 签名 | 说明 |
|-----|------|------|
| `midpoint` | `{float, integer}::midpoint(other)` | 计算中点，无溢出 |
| `NonZero*::midpoint` | `NonZeroU32::midpoint(other)` | 非零整数中点 |
| `isqrt` | `u32::isqrt()` | 整数平方根 floor(sqrt(n)) |
| `checked_isqrt` | `i32::checked_isqrt()` | 安全整数平方根（负数返回 None） |
| `NonZero::isqrt` | `NonZeroU32::isqrt()` | 非零整数平方根 |

```rust
// midpoint 避免溢出
let a = u32::MAX;
let b = u32::MAX;
assert_eq!(a.midpoint(b), u32::MAX); // 不会溢出

// isqrt
assert_eq!(16u32.isqrt(), 4);
assert_eq!((-1i32).checked_isqrt(), None);
```

### 指针与 Strict Provenance {#指针与-strict-provenance}

| API | 签名 | 说明 |
|-----|------|------|
| `without_provenance` | `ptr::without_provenance(addr)` | 创建无 provenance 指针 |
| `dangling` | `ptr::dangling<T>()` | 创建对齐的悬空指针 |
| `addr` | `ptr.addr()` | 获取地址（usize） |
| `with_addr` | `ptr.with_addr(new_addr)` | 保留 provenance，替换地址 |
| `map_addr` | `ptr.map_addr(f)` | 通过闭包映射地址 |
| `byte_add` | `ptr.byte_add(offset)` | 按字节偏移（unsafe） |
| `wrapping_byte_add` | `ptr.wrapping_byte_add(offset)` | 环绕字节偏移（safe） |

```rust
let ptr = &42u32 as *const u32;
let addr = ptr.addr();                  // 剥离 provenance
let shifted = ptr.with_addr(addr + 4);  // 保留 provenance，新地址
let byte_off = unsafe { ptr.byte_add(4) }; // 按字节偏移
```

### 网络/IP 地址 {#网络ip-地址}

| API | 签名 | 说明 |
|-----|------|------|
| `is_unique_local` | `Ipv6Addr::is_unique_local()` | ULA (fc00::/7) |
| `is_unicast_link_local` | `Ipv6Addr::is_unicast_link_local()` | fe80::/10 |
| `to_canonical` | `IpAddr::to_canonical()` | IPv4-mapped → IPv4 |
| `BitAnd/BitOr/Not` | `Ipv4Addr & Ipv4Addr` | 位运算 |

```rust
let ula = Ipv6Addr::new(0xfc00, 0, 0, 0, 0, 0, 0, 1);
assert!(ula.is_unique_local());

let a = Ipv4Addr::new(192, 168, 0, 0);
let b = Ipv4Addr::new(0, 0, 255, 255);
let masked = a & b; // 192.168.0.0
```

### 文件系统 {#文件系统}

| API | 签名 | 说明 |
|-----|------|------|
| `FileTimes` | `FileTimes::new()` | 构建文件时间修改请求 |
| `File::set_times` | `file.set_times(times)` | 原子设置时间戳 |
| `File::set_modified` | `file.set_modified(time)` | 快捷设置修改时间 |

```rust
let mut times = FileTimes::new();
times.set_modified(SystemTime::now());
file.set_times(times)?;
```

### 错误处理 {#错误处理}

| API | 说明 |
|-----|------|
| `io::ErrorKind::QuotaExceeded` | 磁盘配额耗尽 |
| `io::ErrorKind::CrossesDevices` | 跨设备操作（如跨 FS rename） |

```rust
match err.kind() {
    io::ErrorKind::QuotaExceeded => "清理磁盘空间",
    io::ErrorKind::CrossesDevices => "使用 copy+delete",
    _ => "其他错误",
}
```

### 集合与迭代器 {#集合与迭代器}

| API | 说明 |
|-----|------|
| `Extend` for tuples (1-12) | 并行扩展多个集合 |
| `FromIterator<(A, B, ...)>` for tuples | 一次 collect，多个容器 |
| `VecDeque::truncate_front` | 截断前部，保留后部 `n` 个元素 |
| `BufRead` for `VecDeque<u8>` | 无锁缓冲读取 |
| `Option::as_slice` / `as_mut_slice` | Option → 切片视图 |
| `From<&mut [T]>` for `Box/Rc/Arc<[T]>` | 可变切片转换 |

```rust
// 元组 Extend
let mut result: (Vec<i32>, Vec<String>) = (Vec::new(), Vec::new());
result.extend([(1, "a".to_string()), (2, "b".to_string())]);

// VecDeque::truncate_front
let mut buf = VecDeque::from([1, 2, 3, 4, 5]);
buf.truncate_front(2);  // 保留后部 2 个
assert_eq!(buf.make_contiguous(), &[4, 5]);

// Option as_slice
let opt = Some(42);
assert_eq!(opt.as_slice(), &[42]);
let none: Option<i32> = None;
assert!(none.as_slice().is_empty());
```

### 异步 {#异步}

| API | 说明 |
|-----|------|
| `Waker::noop()` | 无操作 Waker，用于同步轮询 |

```rust
let waker = Waker::noop();
let mut cx = Context::from_waker(&waker);
let poll_result = future.poll(&mut cx);
```

### 其他 {#其他}

| API | 说明 |
|-----|------|
| `ptr::fn_addr_eq(a, b)` | 函数指针地址比较 |
| `FromStr` for `CString` | 从字符串解析 C 字符串 |
| `LowerExp` / `UpperExp` for `NonZero` | 科学计数法格式化 |
| `NonZero::{highest_one, lowest_one, bit_width}` | 非零整数的位索引与位宽查询 |

---

## Const 上下文稳定 {#const-上下文稳定}

> **[来源: Rust Reference — Const Evaluation](https://doc.rust-lang.org/reference/const_eval.html)**

以下 API 在 Rust 1.97 中可在 `const fn` / `const` 上下文中使用：

| API | 说明 |
|-----|------|
| `mem::size_of_val` / `align_of_val` | 值的大小/对齐 |
| `Layout::for_value` / `align_to` / `pad_to_align` / `extend` / `array` | 内存布局 |
| `mem::swap` / `ptr::swap` | 交换值 |
| `NonNull::new` | 创建 NonNull |
| `HashMap::with_hasher` / `HashSet::with_hasher` | 构造带自定义 hasher 的集合 |
| `Atomic*::from_ptr` | 从指针创建原子引用（unsafe） |
| `<ptr>::is_null` / `as_ref` / `as_mut` | 指针检查与转换 |
| `Pin::new` / `new_unchecked` / `get_ref` / `get_mut` / `static_ref` / `static_mut` | Pin 操作 |
| float methods (`recip`, `to_degrees`, `clamp`, `abs`, etc.) | 浮点数运算 |
| `MaybeUninit::write` | 写入 MaybeUninit |
| `char::is_control` | 字符是否为控制字符 |

---

## Cargo 改进 {#cargo-改进}

> **[来源: Cargo Documentation](https://doc.rust-lang.org/cargo/)**

| 特性 | 说明 |
|------|------|
| `CARGO_CFG_FEATURE` | build script 环境变量，传递当前启用的 features |
| cfg 关键字 future-incompatibility warning | 对 cfg 条件中的关键字引入警告 |
| higher precedence trailing flags | 尾部标志更高优先级解析 |

```rust
// In build.rs:
use std::env;
fn main() {
    if let Ok(features) = env::var("CARGO_CFG_FEATURE") {
        println!("cargo:rustc-cfg=features={}", features);
    }
}
```

---

## 快速参考示例 {#快速参考示例}

> **[来源: Rust Standard Library](https://doc.rust-lang.org/std/)**

### 二分搜索中点（无溢出） {#二分搜索中点无溢出}

```rust
fn binary_search_mid(low: usize, high: usize) -> usize {
    low.midpoint(high)  // 避免 (low + high) / 2 溢出
}
```

### 异步闭包 trait 约束 {#异步闭包-trait-约束}

```rust
async fn process_items<F>(processor: F, items: Vec<i32>) -> Vec<i32>
where
    F: AsyncFnMut(i32) -> i32,
{
    let mut results = Vec::new();
    for item in items {
        results.push(processor(item).await);
    }
    results
}
```

### 严格 provenance 模式 {#严格-provenance-模式}

```rust
let ptr = &value as *const T;
let addr = ptr.addr();                    // 仅获取数值地址
let tagged = ptr.map_addr(|a| a | 1);     // 设置低位标记
let original = tagged.with_addr(addr);    // 恢复原始地址，保留 provenance
```

---

## 迁移检查清单 {#迁移检查清单}

> **[来源: Rust Edition Guide](https://doc.rust-lang.org/edition-guide/)**

- [ ] 确认项目编译器升级到 Rust 1.97+
- [ ] 检查新的 `io::ErrorKind` 变体是否需要处理
- [ ] 评估 `AsyncFn*` trait 是否可以简化异步闭包代码
- [ ] 考虑使用 `midpoint` / `isqrt` 替换自定义实现
- [ ] 评估 Strict Provenance API 对 unsafe 代码的改进机会
- [ ] 更新 CI/CD 中的 Rust 版本

---

## 相关链接 {#相关链接}

- [Rust 1.97 Release Notes](https://blog.rust-lang.org/)
- [Rust Standard Library](https://doc.rust-lang.org/std/)
- [The Rust Reference](https://doc.rust-lang.org/reference/)
- [Rust 1.96 特性速查表](02_rust_196_features_cheatsheet.md)
- [Rust 1.98 Nightly 前瞻速查表](02_rust_198_nightly_preview_cheatsheet.md)
- [Rust 版本跟踪](../../../concept/07_future/05_rust_version_tracking.md)

---

> **权威来源**: [Rust Standard Library](https://doc.rust-lang.org/std/), [Rust Reference](https://doc.rust-lang.org/reference/)
>
> **文档版本**: 1.0
> **对应 Rust 版本**: 1.97.0+ (Edition 2024)
> **最后更新**: 2026-05-29
> **状态**: 🔄 预览版（基于 nightly 1.98.0 提前准备）
