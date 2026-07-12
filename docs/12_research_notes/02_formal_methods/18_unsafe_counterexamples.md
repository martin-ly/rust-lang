# Unsafe 与 FFI 反例边界 {#unsafe-与-ffi-反例边界}

<!-- canonical-normalized 2026-07-11 -->
> **权威来源（Canonical）**: 本文件为unsafe 反例集（反例，独特内容）；通用 Rust 概念解释请以 concept 权威页为准：[`concept L3 unsafe`](../../../concept/03_advanced/02_unsafe/01_unsafe.md)
>
> 根据 AGENTS.md §2 Canonical 规则：本文仅保留本文独特内容（unsafe 反例与边界（反例集，非概念正文）），不重复 concept/ 中的概念定义、规则与定理推导。

> **EN**: Unsafe Counterexamples
> **Summary**: Unsafe 与 FFI 反例边界 Unsafe Counterexamples.
> **内容分级**: [核心级]
> **层级**: L6 (反例边界)
> **Bloom 层级**: L5-L6
> **概念族**: unsafe / FFI / 内存安全（Memory Safety） / 反例边界
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29

---

## 目录 {#目录}

- [Unsafe 与 FFI 反例边界 {#unsafe-与-ffi-反例边界}](#unsafe-与-ffi-反例边界-unsafe-与-ffi-反例边界)
  - [目录 {#目录}](#目录-目录)
  - [1. 解引用悬空裸指针 {#1-解引用悬空裸指针}](#1-解引用悬空裸指针-1-解引用悬空裸指针)
    - [现象 {#现象-6}](#现象-现象-6)
    - [后果 {#后果-6}](#后果-后果-6)
    - [修复方案 {#修复方案-6}](#修复方案-修复方案-6)
  - [2. 越界访问裸指针 {#2-越界访问裸指针}](#2-越界访问裸指针-2-越界访问裸指针)
    - [现象 {#现象-6}](#现象-现象-6-1)
    - [后果 {#后果-6}](#后果-后果-6-1)
    - [修复方案 {#修复方案-6}](#修复方案-修复方案-6-1)
  - [3. 数据竞争：裸指针并发写 {#3-数据竞争裸指针并发写}](#3-数据竞争裸指针并发写-3-数据竞争裸指针并发写)
    - [现象 {#现象-6}](#现象-现象-6-2)
    - [后果 {#后果-6}](#后果-后果-6-2)
    - [修复方案 {#修复方案-6}](#修复方案-修复方案-6-2)
  - [4. 类型双关（Type Pun）导致错位 {#4-类型双关type-pun导致错位}](#4-类型双关type-pun导致错位-4-类型双关type-pun导致错位)
    - [现象 {#现象-6}](#现象-现象-6-3)
    - [后果 {#后果-6}](#后果-后果-6-3)
    - [修复方案 {#修复方案-6}](#修复方案-修复方案-6-3)
  - [5. `unsafe impl` 虚假 Send/Sync {#5-unsafe-impl-虚假-sendsync}](#5-unsafe-impl-虚假-sendsync-5-unsafe-impl-虚假-sendsync)
    - [现象 {#现象-6}](#现象-现象-6-4)
    - [后果 {#后果-6}](#后果-后果-6-4)
    - [修复方案 {#修复方案-6}](#修复方案-修复方案-6-4)
  - [6. FFI 调用后使用已释放内存 {#6-ffi-调用后使用已释放内存}](#6-ffi-调用后使用已释放内存-6-ffi-调用后使用已释放内存)
    - [现象 {#现象-6}](#现象-现象-6-5)
    - [后果 {#后果-6}](#后果-后果-6-5)
    - [修复方案 {#修复方案-6}](#修复方案-修复方案-6-5)
  - [7. `transmute` 误用 {#7-transmute-误用}](#7-transmute-误用-7-transmute-误用)
    - [现象 {#现象-6}](#现象-现象-6-6)
    - [后果 {#后果-6}](#后果-后果-6-6)
    - [修复方案 {#修复方案-6}](#修复方案-修复方案-6-6)
  - [总结 {#总结}](#总结-总结)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [RFC 参考 {#rfc-参考}](#rfc-参考-rfc-参考)
  - [权威来源参考 {#权威来源参考}](#权威来源参考-权威来源参考)
  - [社区权威参考 {#社区权威参考}](#社区权威参考-社区权威参考)

---

## 1. 解引用悬空裸指针 {#1-解引用悬空裸指针}

### 现象 {#现象-6}

```rust
let ptr: *const i32 = {
    let x = 42;
    &x as *const i32
}; // x 在这里 drop
unsafe {
    println!("{}", *ptr); // ❌ 悬空解引用
}
```

### 后果 {#后果-6}

运行时（Runtime）未定义行为（UB），可能读取垃圾数据或触发段错误。

### 修复方案 {#修复方案-6}

- 保证裸指针指向的内存在整个使用期间有效。
- 使用引用或智能指针（Smart Pointer）管理生命周期（Lifetimes）。

---

## 2. 越界访问裸指针 {#2-越界访问裸指针}

### 现象 {#现象-6}

```rust
let arr = [1, 2, 3];
let ptr = arr.as_ptr();
unsafe {
    println!("{}", *ptr.add(100)); // ❌ 越界
}
```

### 后果 {#后果-6}

UB，可能破坏堆元数据或被安全机制检测为越界。

### 修复方案 {#修复方案-6}

- 始终校验偏移量是否在分配大小内。
- 使用 `slice::get_unchecked` 仅在已验证索引后使用。

---

## 3. 数据竞争：裸指针并发写 {#3-数据竞争裸指针并发写}

### 现象 {#现象-6}

```rust
use std::thread;

static mut COUNTER: i32 = 0;

fn main() {
    let mut handles = vec![];
    for _ in 0..10 {
        handles.push(thread::spawn(|| unsafe {
            COUNTER += 1; // ❌ 数据竞争
        }));
    }
    // ...
}
```

### 后果 {#后果-6}

UB，结果不可预期。

### 修复方案 {#修复方案-6}

- 使用 `AtomicI32`。
- 或使用 `Mutex<i32>` / `RwLock<i32>`。

---

## 4. 类型双关（Type Pun）导致错位 {#4-类型双关type-pun导致错位}

### 现象 {#现象-6}

```rust
let bytes: [u8; 4] = [0x01, 0x00, 0x00, 0x00];
let ptr = bytes.as_ptr() as *const u32;
unsafe {
    println!("{}", *ptr); // ⚠️ 未对齐或 endian 问题
}
```

### 后果 {#后果-6}

- 未对齐访问导致 UB。
- endian 不一致导致逻辑错误。

### 修复方案 {#修复方案-6}

- 使用 `u32::from_le_bytes` / `from_be_bytes`。
- 使用 `std::ptr::read_unaligned` 时仍需谨慎。

---

## 5. `unsafe impl` 虚假 Send/Sync {#5-unsafe-impl-虚假-sendsync}

### 现象 {#现象-6}

```rust
use std::cell::Cell;

struct Bad(Cell<i32>);

unsafe impl Send for Bad {}
unsafe impl Sync for Bad {}

// 现在可以跨线程共享 Cell，造成数据竞争
```

### 后果 {#后果-6}

绕过借用（Borrowing）检查器，运行时数据竞争 UB。

### 修复方案 {#修复方案-6}

- 不手动实现 Send/Sync，让编译器自动推导。
- 若必须实现，确保所有字段本身满足 Send/Sync 且内部不变量成立。

---

## 6. FFI 调用后使用已释放内存 {#6-ffi-调用后使用已释放内存}

### 现象 {#现象-6}

```rust
extern "C" {
    fn get_string() -> *const c_char;
    fn free_string(p: *const c_char);
}

unsafe {
    let s = get_string();
    let _rust_str = CStr::from_ptr(s).to_str().unwrap();
    free_string(s);
    // ❌ 后续使用 _rust_str 指向已释放内存
}
```

### 后果 {#后果-6}

use-after-free，UB。

### 修复方案 {#修复方案-6}

- 在释放前复制数据到 Rust 拥有所有权（Ownership）的类型（`String`、`Vec<u8>`）。
- 明确 FFI 端内存管理协议。

---

## 7. `transmute` 误用 {#7-transmute-误用}

### 现象 {#现象-6}

```rust
let f: f32 = 1.0;
let i: i32 = unsafe { std::mem::transmute(f) }; // ✅ 合法：大小相同

let x: u64 = 1;
let p: *const u8 = unsafe { std::mem::transmute(x) }; // ❌ 大小相同但语义错误
```

### 后果 {#后果-6}

产生无效值、未对齐指针、破坏类型不变量。

### 修复方案 {#修复方案-6}

- 优先使用类型安全转换：`as`、`.into()`、`from_le_bytes`。
- `transmute` 前验证：`size_of::<A>() == size_of::<B>()`、对齐、合法值。

---

## 总结 {#总结}

| 反例 | 涉及概念 | 后果 | 修复方向 |
|------|----------|------|----------|
| 悬空裸指针 | 生命周期、裸指针 | UB / 段错误 | 保证内存有效 |
| 越界访问 | 指针运算 | UB | 边界检查 |
| 裸指针并发写 | 数据竞争 | UB | Atomic / Mutex |
| 类型双关 | 对齐、endian | UB / 逻辑错误 | 安全转换 API |
| 虚假 Send/Sync | 并发不变量 | 数据竞争 | 不手动实现 |
| FFI use-after-free | FFI 内存协议 | UB | 复制所有权 |
| `transmute` 误用 | 类型擦除 | UB | 安全转换 |

> **权威来源**: [Rust Reference – Unsafe Blocks](https://doc.rust-lang.org/reference/unsafe-blocks.html) | [Rust Reference – Extern Functions](https://doc.rust-lang.org/reference/items/external-blocks.html) | [Rustonomicon](https://doc.rust-lang.org/nomicon/) | [The Rust Programming Language – Ch 19.1](https://doc.rust-lang.org/book/ch19-01-unsafe-rust.html) | [Rust Reference – Behavior Considered Undefined](https://doc.rust-lang.org/reference/behavior-considered-undefined.html)

## 相关概念 {#相关概念}

- [安全与非安全全面论证](../03_formal_proofs/28_safe_unsafe_comprehensive_analysis.md)
- [模块（Module）系统与安全抽象](../04_formal_module_system/05_module_safety_abstraction.md)
- [所有权与借用反例](17_ownership_counterexamples.md)
- [并发与异步（Async）反例](16_concurrency_async_counterexamples.md)
- [通用反例汇编](../03_formal_proofs/08_counter_examples_compendium.md)
- [知识图谱索引](../06_concept_models/13_knowledge_graph_index.md)

---

## RFC 参考 {#rfc-参考}

> **来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)**

- [RFC 到反例自动化映射索引](../01_alignment_matrices/30_rfc_to_counterexample_mapping.md)
- [Rust RFCs 官方索引](https://rust-lang.github.io/rfcs/)
- [RFC 2580: Pointer metadata](https://rust-lang.github.io/rfcs/2580-ptr-meta.html)
- [RFC 2585: Unsafe blocks in unsafe fn](https://rust-lang.github.io/rfcs/2585-unsafe-block-in-unsafe-fn.html)

## 权威来源参考 {#权威来源参考}

本反例汇编参考以下 P1/P1.5/P2 权威来源：

- [Unsafe Code Guidelines](https://rust-lang.github.io/unsafe-code-guidelines/)
- [Rustonomicon](https://doc.rust-lang.org/nomicon/)
- [RustSEM](https://link.springer.com/article/10.1007/s10703-024-00460-3)

## 社区权威参考 {#社区权威参考}

- [Inside Rust Blog](https://blog.rust-lang.org/inside-rust/)
- [This Week in Rust](https://this-week-in-rust.org/)
