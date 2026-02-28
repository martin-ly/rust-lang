# Rust 边界条件与特例示例

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-12
> **Rust 版本**: 1.93.1+ (Edition 2024)
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
  - [更多边界情况代码示例](#更多边界情况代码示例)
    - [所有权边界](#所有权边界)
      - [部分移动后使用](#部分移动后使用)
      - [Copy 类型的隐式复制](#copy-类型的隐式复制)
    - [生命周期边界](#生命周期边界)
      - [生命周期省略规则边界](#生命周期省略规则边界)
      - [NLL (Non-Lexical Lifetimes) 边界](#nll-non-lexical-lifetimes-边界)
    - [泛型边界](#泛型边界)
      - [递归类型大小边界](#递归类型大小边界)
      - [零大小类型 (ZST)](#零大小类型-zst)
    - [模式匹配边界](#模式匹配边界)
      - [穷尽性检查边界](#穷尽性检查边界)
    - [并发边界](#并发边界)
      - [死锁边界](#死锁边界)
      - [Send/Sync 自动派生边界](#sendsync-自动派生边界)
    - [unsafe 边界](#unsafe-边界)
      - [裸指针解引用边界](#裸指针解引用边界)
      - [未对齐指针边界](#未对齐指针边界)
    - [迭代器边界](#迭代器边界)
      - [迭代器失效边界](#迭代器失效边界)
  - [🔗 形式化边界分析 {#-形式化边界分析}](#-形式化边界分析--形式化边界分析)
    - [所有权与借用边界](#所有权与借用边界)
    - [类型系统边界](#类型系统边界)
    - [并发边界 {#并发边界-1}](#并发边界-并发边界-1)
    - [unsafe 边界 {#unsafe-边界-1}](#unsafe-边界-unsafe-边界-1)
  - [相关文档](#相关文档)
    - [速查卡](#速查卡)
    - [形式化文档](#形式化文档)

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

## 更多边界情况代码示例

### 所有权边界

#### 部分移动后使用

```rust
struct Person {
    name: String,
    age: u32,
}

fn partial_move() {
    let person = Person {
        name: String::from("Alice"),
        age: 30,
    };

    // 部分移动
    let name = person.name;

    // ❌ 编译错误：person 部分移动，不能整体使用
    // println!("{:?}", person);

    // ✅ 可以使用未移动的字段
    println!("年龄: {}", person.age);

    // ✅ 但不能再次移动已移动的字段
    // let name2 = person.name;  // 错误
}
```

#### Copy 类型的隐式复制

```rust
fn copy_behavior() {
    let x = 42i32;
    let y = x;  // 复制，不是移动
    let z = x;  // 仍然可用

    // 所有变量都有效
    println!("{} {} {}", x, y, z);
}
```

### 生命周期边界

#### 生命周期省略规则边界

```rust
// 省略规则适用的情况
fn first_word(s: &str) -> &str {  // 输入生命周期 = 输出生命周期
    &s[0..1]
}

// 省略规则不适用的情况（需要显式标注）
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}

// 不同的生命周期参数
fn mix_lifetimes<'a, 'b>(x: &'a str, y: &'b str) -> &'a str {
    x  // 只能返回 x，因为 y 的生命周期可能更短
}
```

#### NLL (Non-Lexical Lifetimes) 边界

```rust
fn nll_example() {
    let mut x = String::from("hello");
    let y = &x;  // 不可变借用开始
    println!("{}", y);  // 最后一次使用 y
    // y 的借用在这里结束（NLL），不是作用域结束

    let z = &mut x;  // ✅ 现在可以可变借用
    z.push_str(" world");
}
```

### 泛型边界

#### 递归类型大小边界

```rust
// ❌ 编译错误：递归类型大小无限
// enum List {
//     Cons(i32, List),
//     Nil,
// }

// ✅ 使用 Box 解决
enum List {
    Cons(i32, Box<List>),
    Nil,
}

fn recursive_type() {
    let list = List::Cons(1, Box::new(List::Cons(2, Box::new(List::Nil))));
}
```

#### 零大小类型 (ZST)

```rust
use std::mem::size_of;

struct ZeroSized;
enum Void {}

fn zero_sized_types() {
    assert_eq!(size_of::<ZeroSized>(), 0);
    assert_eq!(size_of::<()>(), 0);  // 单元类型
    assert_eq!(size_of::<[(); 1000]>(), 0);  // 1000 个 ZST 数组仍是 ZST
}
```

### 模式匹配边界

#### 穷尽性检查边界

```rust
enum Option<T> {
    Some(T),
    None,
}

fn exhaustive_match(x: Option<i32>) -> i32 {
    match x {
        Some(v) => v,
        None => 0,
    }  // ✅ 穷尽
}

// 使用 _ 通配符
fn wildcard_match(x: Option<i32>) -> i32 {
    match x {
        Some(v) => v,
        _ => 0,  // 匹配所有其他情况
    }
}

// @ 绑定
fn at_binding(x: Option<i32>) -> i32 {
    match x {
        v @ Some(_) => {
            println!("有值: {:?}", v);
            v.unwrap()
        }
        None => 0,
    }
}
```

### 并发边界

#### 死锁边界

```rust
use std::sync::{Mutex, MutexGuard};

fn deadlock_risk() {
    let m1 = Mutex::new(0);
    let m2 = Mutex::new(0);

    // 线程 1
    let _guard1 = m1.lock().unwrap();
    // ... 某些操作
    // let _guard2 = m2.lock().unwrap();  // 潜在死锁风险

    // 线程 2 如果以相反顺序获取锁，会导致死锁
}

// ✅ 解决方案：一致的加锁顺序或使用 std::sync::LockGuard
```

#### Send/Sync 自动派生边界

```rust
use std::rc::Rc;
use std::sync::Arc;

fn auto_trait_bounds() {
    // Rc 不是 Send
    let rc = Rc::new(42);
    // std::thread::spawn(move || {
    //     println!("{}", rc);  // 编译错误：Rc 不是 Send
    // });

    // Arc 是 Send
    let arc = Arc::new(42);
    std::thread::spawn(move || {
        println!("{}", arc);  // ✅ 正确
    });
}
```

### unsafe 边界

#### 裸指针解引用边界

```rust
fn raw_pointer_edges() {
    let mut x = 42;
    let r = &mut x as *mut i32;

    // ✅ 安全的裸指针创建
    unsafe {
        *r = 100;  // 解引用
    }

    // 空指针检查（Rust 1.93 deref_nullptr lint）
    let null_ptr: *const i32 = std::ptr::null();
    unsafe {
        // *null_ptr;  // ❌ UB！Rust 1.93 默认 deny
    }
}
```

#### 未对齐指针边界

```rust
fn unaligned_pointer() {
    let bytes: [u8; 8] = [0; 8];

    // ❌ 可能未对齐
    // let ptr = bytes.as_ptr() as *const u64;
    // unsafe { *ptr; }  // UB 如果未对齐

    // ✅ 使用 read_unaligned
    let ptr = bytes.as_ptr() as *const u64;
    unsafe {
        let val = ptr.read_unaligned();  // 安全地读取未对齐数据
    }
}
```

### 迭代器边界

#### 迭代器失效边界

```rust
fn iterator_invalidation() {
    let mut v = vec![1, 2, 3];

    // ❌ 编译错误：不能在使用迭代器时修改集合
    // for x in &v {
    //     v.push(*x);  // 错误！
    // }

    // ✅ 解决方案：收集后再修改
    let to_add: Vec<_> = v.iter().copied().collect();
    v.extend(to_add);
}
```

---

## 🔗 形式化边界分析 {#-形式化边界分析}

### 所有权与借用边界

| 边界情况 | 形式化规则 | 相关文档 |
| :--- | :--- | :--- |
| 部分移动 | $\Omega(\text{field}) = \text{Moved}$，结构体不能整体使用 | [ownership_model](../research_notes/formal_methods/ownership_model.md#示例-8-复杂所有权场景---结构体字段移动) |
| 复制语义 | $\Gamma(y) = \text{copy}(\Gamma(x))$，原变量仍有效 | [ownership_model](../research_notes/formal_methods/ownership_model.md#规则-4-复制语义) |
| NLL | $\text{Scope}(r) = [t_1, t_{\text{last\_use}}]$ | [lifetime_formalization](../research_notes/formal_methods/lifetime_formalization.md) |

### 类型系统边界

| 边界情况 | 形式化规则 | 相关文档 |
| :--- | :--- | :--- |
| 递归类型 | 需满足 $\text{size\_of}(T) < \infty$ | [type_system_foundations](../research_notes/type_theory/type_system_foundations.md) |
| ZST | $\text{size\_of}(T) = 0$ | [Rust Reference](https://doc.rust-lang.org/reference/dynamically-sized-types.html) |
| 生命周期子类型 | $\ell_2 <: \ell_1 \leftrightarrow \ell_1 \supseteq \ell_2$ | [lifetime_formalization](../research_notes/formal_methods/lifetime_formalization.md#定义-14-生命周期子类型) |

### 并发边界 {#并发边界-1}

| 边界情况 | 形式化规则 | 相关文档 |
| :--- | :--- | :--- |
| Send 边界 | $T: \text{Send} \rightarrow \text{可以跨线程转移}$ | [send_sync_formalization](../research_notes/formal_methods/send_sync_formalization.md#defs-send1send-sync1sendsync-形式化) |
| Sync 边界 | $T: \text{Sync} \leftrightarrow \&T: \text{Send}$ | [send_sync_formalization](../research_notes/formal_methods/send_sync_formalization.md#sendsync-关系) |
| 数据竞争 | $\text{DataRaceFree}(P)$ 编译期保证 | [borrow_checker_proof](../research_notes/formal_methods/borrow_checker_proof.md#定理-1-数据竞争自由) |

### unsafe 边界 {#unsafe-边界-1}

| 边界情况 | 形式化规则 | 相关文档 |
| :--- | :--- | :--- |
| 裸指针 | $\text{deref}(p)$ 合法仅当 $\text{nonnull}(p)$ | [borrow_checker_proof](../research_notes/formal_methods/borrow_checker_proof.md#def-raw1-裸指针与-deref_nullptr) |
| 未对齐访问 | 需使用 `read_unaligned` | [Rust Reference](https://doc.rust-lang.org/reference/behavior-considered-undefined.html) |
| FFI 边界 | `extern` 函数类型布局一致 | [borrow_checker_proof](../research_notes/formal_methods/borrow_checker_proof.md#def-extern1-extern-abi-边界) |

---

## 相关文档

### 速查卡

- [集合与迭代器速查卡](./quick_reference/collections_iterators_cheatsheet.md)
- [算法速查卡](./quick_reference/algorithms_cheatsheet.md)
- [线程与并发速查卡](./quick_reference/threads_concurrency_cheatsheet.md)
- [所有权速查卡](./quick_reference/ownership_cheatsheet.md)

### 形式化文档

- [所有权模型形式化](../research_notes/formal_methods/ownership_model.md)
- [借用检查器证明](../research_notes/formal_methods/borrow_checker_proof.md)
- [生命周期形式化](../research_notes/formal_methods/lifetime_formalization.md)
- [Send/Sync 形式化](../research_notes/formal_methods/send_sync_formalization.md)
