# Rust 边界条件与特例示例

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-12
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **用途**: 集合、算法、并发等模块的边界/特例示例

---

## 目录

- [Rust 边界条件与特例示例](#rust-边界条件与特例示例)
  - [目录](#目录)
  - [集合边界](#集合边界)
    - [空 Vec 与零长度](#空-vec-与零长度)
    - [空 HashMap / BTreeMap](#空-hashmap--btreemap)
    - [空切片](#空切片)
  - [算法特例](#算法特例)
    - [空输入的排序与搜索](#空输入的排序与搜索)
    - [单元素与双元素](#单元素与双元素)
  - [并发特例](#并发特例)
    - [零个线程 / 空任务列表](#零个线程--空任务列表)
    - [通道已关闭](#通道已关闭)
    - [Mutex poison](#mutex-poison)
  - [数值溢出](#数值溢出)
    - [整数溢出（debug 下 panic）](#整数溢出debug-下-panic)
    - [除零](#除零)
  - [字符串与切片](#字符串与切片)
    - [空字符串](#空字符串)
    - [字节边界上的字符切分](#字节边界上的字符切分)
    - [零长度范围](#零长度范围)
  - [unsafe 与 FFI](#unsafe-与-ffi)
    - [空指针解引用](#空指针解引用)
    - [FFI 边界：C 传入空指针](#ffi-边界c-传入空指针)
    - [悬垂引用典型反例](#悬垂引用典型反例)
  - [WASM 特例](#wasm-特例)
    - [无 std 环境](#无-std-环境)
    - [阻塞 API 在 WASM](#阻塞-api-在-wasm)
  - [panic 边界](#panic-边界)
    - [panic 与 unwrap](#panic-与-unwrap)
    - [断言边界](#断言边界)
  - [空 Future 与异步](#空-future-与异步)
    - [空 select](#空-select)
    - [已完成 Future](#已完成-future)
  - [Rust 1.93 行为变更特例](#rust-193-行为变更特例)
    - [BTreeMap::append 行为变更](#btreemapappend-行为变更)
    - [Copy specialization 移除](#copy-specialization-移除)
    - [vec::IntoIter 与 RefUnwindSafe](#vecintoiter-与-refunwindsafe)
  - [相关文档](#相关文档)

---

## 集合边界

### 空 Vec 与零长度

```rust
let empty: Vec<i32> = vec![];
assert!(empty.is_empty());
assert_eq!(empty.len(), 0);
// empty[0];  // ❌ panic: index out of bounds
empty.first();  // ✅ 返回 None
empty.get(0);   // ✅ 返回 None
```

### 空 HashMap / BTreeMap

```rust
use std::collections::HashMap;

let map: HashMap<i32, &str> = HashMap::new();
map.get(&1);  // ✅ 返回 None，不 panic
map.insert(1, "a");  // 插入后非空
```

### 空切片

```rust
let slice: &[i32] = &[];
assert!(slice.is_empty());
slice.iter().next();  // ✅ 返回 None
```

---

## 算法特例

### 空输入的排序与搜索

```rust
let empty: Vec<i32> = vec![];
empty.sort();  // ✅ 无操作，不 panic
empty.binary_search(&0);  // ✅ Err(0)，表示应插入位置

let one = vec![1];
one.binary_search(&1);  // ✅ Ok(0)
one.binary_search(&0);  // ✅ Err(0)
```

### 单元素与双元素

```rust
let single = vec![42];
single.windows(2).next();  // None，窗口大小 > len
single.chunks(1).count();  // 1
```

---

## 并发特例

### 零个线程 / 空任务列表

```rust
let handles: Vec<_> = vec![];
for h in handles {
    h.join().unwrap();
}
// ✅ 正常，无任务
```

### 通道已关闭

```rust
use std::sync::mpsc;

let (tx, rx) = mpsc::channel();
drop(tx);
rx.recv();  // ✅ Err，表明通道已关闭
```

### Mutex poison

```rust
// 当持有 MutexGuard 的线程 panic 时，Mutex 被标记为 poisoned
let mutex = std::sync::Mutex::new(1);
match mutex.lock() {
    Ok(guard) => {},
    Err(poisoned) => {
        let guard = poisoned.into_inner();  // 可恢复
    }
}
```

---

## 数值溢出

### 整数溢出（debug 下 panic）

```rust
let x: u8 = 255;
// let y = x + 1;  // debug: panic, release: wrapping
let y = x.wrapping_add(1);  // ✅ 明确 wrapping，y = 0
let z = x.saturating_add(1);  // ✅ 饱和，z = 255
```

### 除零

```rust
let x: i32 = 1;
// let y = x / 0;  // ❌ 编译错误或运行时 panic
let zero = 0;
let y = x.checked_div(zero);  // ✅ None
```

---

## 字符串与切片

### 空字符串

```rust
let s = "";
assert!(s.is_empty());
s.chars().next();  // None
s.as_bytes();      // &[]
```

### 字节边界上的字符切分

```rust
let s = "hello";
// 必须在字符边界切分
let ok = &s[0..1];   // "h"
// let bad = &s[0..2];  // 若 "he" 是字符边界则 OK
// 使用 chars() 安全迭代
for c in s.chars() {
    // 按字符处理
}
```

### 零长度范围

```rust
let s = "hello";
let sub = &s[2..2];  // ✅ ""
```

---

## unsafe 与 FFI

### 空指针解引用

```rust
let ptr: *const i32 = std::ptr::null();
// let _ = unsafe { *ptr };  // ❌ UB，Rust 1.93 deref_nullptr 默认 deny
if !ptr.is_null() {
    let _ = unsafe { *ptr };
}
```

### FFI 边界：C 传入空指针

```rust
#[repr(C)]
struct Foo { x: i32 }

extern "C" {
    fn c_get_foo() -> *const Foo;
}

fn safe_wrapper() -> Option<&'static Foo> {
    let ptr = unsafe { c_get_foo() };
    if ptr.is_null() { None } else { Some(unsafe { &*ptr }) }
}
```

### 悬垂引用典型反例

```rust
// ❌ 返回局部变量的引用
fn bad() -> &i32 {
    let x = 42;
    &x  // 编译错误：x 的生命周期不足
}

// ✅ 返回传入的引用或拥有所有权
fn good(x: &i32) -> &i32 { x }
```

---

## WASM 特例

### 无 std 环境

```rust
#![no_std]
// 无 std::thread、std::sync::Mutex 等
// 使用 core / alloc
```

### 阻塞 API 在 WASM

```rust
// ❌ wasm32 下 std::thread::sleep 可能不可用或行为不同
// std::thread::sleep(Duration::from_secs(1));

// ✅ 使用 wasm_bindgen 的 setTimeout 或 async/await
#[cfg(target_arch = "wasm32")]
// 使用 web_sys 或 js_sys 的异步 API
```

---

## panic 边界

### panic 与 unwrap

```rust
let opt: Option<i32> = None;
// opt.unwrap();  // ❌ panic
opt.unwrap_or(0);  // ✅ 提供默认值

let res: Result<i32, &str> = Err("error");
// res.unwrap();  // ❌ panic
res.unwrap_or_default();  // ✅ 或 map_err 处理
```

### 断言边界

```rust
let v = vec![1, 2, 3];
// v[10];  // ❌ panic: index out of bounds
v.get(10);  // ✅ 返回 None
```

---

## 空 Future 与异步

### 空 select

```rust
use tokio::select;

// 无分支的 select! 会永久挂起
// select! { }  // ❌ 编译错误或永远阻塞

// ✅ 至少一个分支
tokio::select! {
    _ = async { } => {}
}
```

### 已完成 Future

```rust
use std::future::ready;

let f = std::future::ready(42);
// f 立即完成，poll 一次即返回 Ready(42)
```

---

## Rust 1.93 行为变更特例

### BTreeMap::append 行为变更

**Rust 1.93** 起，`BTreeMap::append` 当追加的条目已存在时，**不再覆盖**目标中的现有键，而是保留目标中的值。

```rust
use std::collections::BTreeMap;

let mut a = BTreeMap::new();
a.insert(1, "a");
let mut b = BTreeMap::new();
b.insert(1, "b");  // 相同 key

a.append(&mut b);
// 1.93 之前：a[1] 可能为 "b"
// 1.93 起：a[1] 保留为 "a"，b 中 (1,"b") 被丢弃
assert_eq!(a.get(&1), Some(&"a"));
```

### Copy specialization 移除

**Rust 1.93** 在 Copy trait 上停止内部使用 specialization。部分标准库 API 可能改为调用 `Clone::clone` 而非按位复制，**可能导致性能回归**。

```rust
// 若依赖 Copy 类型的按位复制优化，1.93 后可能略有性能差异
let v: Vec<i32> = vec![1, 2, 3];
let v2 = v.clone();  // 可能受影响
```

### vec::IntoIter 与 RefUnwindSafe

**Rust 1.93** 放宽 `vec::IntoIter<T>: UnwindSafe` 约束，不再要求 `T: RefUnwindSafe`。

```rust
// 1.93 起：即使 T 不实现 RefUnwindSafe，vec::IntoIter<T> 仍为 UnwindSafe
use std::panic::UnwindSafe;
use std::vec::IntoIter;

fn assert_unwind_safe<T: UnwindSafe>() {}
assert_unwind_safe::<IntoIter<*mut i32>>();  // 1.93 可行
```

---

## 相关文档

- [集合与迭代器速查卡](./quick_reference/collections_iterators_cheatsheet.md)
- [算法速查卡](./quick_reference/algorithms_cheatsheet.md)
- [线程与并发速查卡](./quick_reference/threads_concurrency_cheatsheet.md)
