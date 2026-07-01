# 所有权与借用反例边界 {#所有权与借用反例边界}

> **内容分级**: [核心级]
> **层级**: L6 (反例边界)
> **Bloom 层级**: L5-L6 (分析/评价)
> **概念族**: 所有权 / 借用 / 反例边界
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29

---

## 目录 {#目录}

- [所有权与借用反例边界 {#所有权与借用反例边界}](#所有权与借用反例边界-所有权与借用反例边界)
  - [目录 {#目录}](#目录-目录)
  - [1. 使用已移动的值 {#1-使用已移动的值}](#1-使用已移动的值-1-使用已移动的值)
    - [现象 {#现象-6}](#现象-现象-6)
    - [编译器错误 {#编译器错误-5}](#编译器错误-编译器错误-5)
    - [修复方案 {#修复方案-6}](#修复方案-修复方案-6)
  - [2. 同一作用域内多次可变借用 {#2-同一作用域内多次可变借用}](#2-同一作用域内多次可变借用-2-同一作用域内多次可变借用)
    - [现象 {#现象-6}](#现象-现象-6-1)
    - [编译器错误 {#编译器错误-5}](#编译器错误-编译器错误-5-1)
    - [修复方案 {#修复方案-6}](#修复方案-修复方案-6-1)
  - [3. 可变与不可变借用重叠 {#3-可变与不可变借用重叠}](#3-可变与不可变借用重叠-3-可变与不可变借用重叠)
    - [现象 {#现象-6}](#现象-现象-6-2)
    - [编译器错误 {#编译器错误-5}](#编译器错误-编译器错误-5-2)
    - [修复方案 {#修复方案-6}](#修复方案-修复方案-6-2)
  - [4. 返回悬垂引用 {#4-返回悬垂引用}](#4-返回悬垂引用-4-返回悬垂引用)
    - [现象 {#现象-6}](#现象-现象-6-3)
    - [编译器错误 {#编译器错误-5}](#编译器错误-编译器错误-5-3)
    - [修复方案 {#修复方案-6}](#修复方案-修复方案-6-3)
  - [5. 自引用结构体被移动 {#5-自引用结构体被移动}](#5-自引用结构体被移动-5-自引用结构体被移动)
    - [现象 {#现象-6}](#现象-现象-6-4)
    - [编译器错误 {#编译器错误-5}](#编译器错误-编译器错误-5-4)
    - [修复方案 {#修复方案-6}](#修复方案-修复方案-6-4)
  - [6. 错误实现 Send / Sync {#6-错误实现-send-sync}](#6-错误实现-send--sync-6-错误实现-send-sync)
    - [现象 {#现象-6}](#现象-现象-6-5)
    - [后果 {#后果}](#后果-后果)
    - [修复方案 {#修复方案-6}](#修复方案-修复方案-6-5)
  - [7. 生命周期参数不足 {#7-生命周期参数不足}](#7-生命周期参数不足-7-生命周期参数不足)
    - [现象 {#现象-6}](#现象-现象-6-6)
    - [编译器错误 {#编译器错误-5}](#编译器错误-编译器错误-5-5)
    - [修复方案 {#修复方案-6}](#修复方案-修复方案-6-6)
  - [总结 {#总结}](#总结-总结)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [RFC 参考 {#rfc-参考}](#rfc-参考-rfc-参考)
  - [权威来源参考 {#权威来源参考}](#权威来源参考-权威来源参考)
  - [社区权威参考 {#社区权威参考}](#社区权威参考-社区权威参考)

---

## 1. 使用已移动的值 {#1-使用已移动的值}

### 现象 {#现象-6}

```rust
let s = String::from("hello");
let t = s;
println!("{}", s); // ❌ s 已移动
```

### 编译器错误 {#编译器错误-5}

```text
error[E0382]: borrow of moved value: `s`
```

### 修复方案 {#修复方案-6}

- 使用 `clone()` 显式复制堆数据。
- 使用引用 `&s` 避免移动。
- 重新设计函数签名以借用而非获取所有权。

---

## 2. 同一作用域内多次可变借用 {#2-同一作用域内多次可变借用}

### 现象 {#现象-6}

```rust
let mut v = vec![1, 2, 3];
let a = &mut v;
let b = &mut v; // ❌ 第二个可变借用
a.push(4);
```

### 编译器错误 {#编译器错误-5}

```text
error[E0499]: cannot borrow `v` as mutable more than once at a time
```

### 修复方案 {#修复方案-6}

- 缩小借用作用域，使两次借用不重叠。
- 按索引或 split 分割集合，如 `split_first_mut()`。

---

## 3. 可变与不可变借用重叠 {#3-可变与不可变借用重叠}

### 现象 {#现象-6}

```rust
let mut v = vec![1, 2, 3];
let first = &v[0];
v.push(4); // ❌ 不可变借用 first 仍有效
println!("{}", first);
```

### 编译器错误 {#编译器错误-5}

```text
error[E0502]: cannot borrow `v` as mutable because it is also borrowed as immutable
```

### 修复方案 {#修复方案-6}

- 将读取操作提前到修改之前完成。
- 使用临时作用域隔离不可变借用。

---

## 4. 返回悬垂引用 {#4-返回悬垂引用}

### 现象 {#现象-6}

```rust
fn dangling() -> &String {
    let s = String::from("hello");
    &s // ❌ 返回局部变量的引用
}
```

### 编译器错误 {#编译器错误-5}

```text
error[E0106]: missing lifetime specifier
error[E0515]: cannot return reference to local variable `s`
```

### 修复方案 {#修复方案-6}

- 返回拥有所有权的值 `String`。
- 使用生命周期参数将输入引用与输出引用关联。
- 使用 `Rc<str>` / `Arc<str>` 等共享所有权类型。

---

## 5. 自引用结构体被移动 {#5-自引用结构体被移动}

### 现象 {#现象-6}

```rust
struct Parser {
    text: String,
    current: &str, // 指向 text 内部
}
```

`Parser` 被移动后，`current` 仍指向旧地址，导致悬垂。

### 编译器错误 {#编译器错误-5}

```text
error[E0106]: missing lifetime specifier
```

（因为无法表达自引用生命周期）

### 修复方案 {#修复方案-6}

- 使用索引 `usize` 代替引用。
- 使用 `Pin<Box<Self>>` 配合 unsafe 保证不再移动。
- 重新设计数据结构，避免自引用。

> **相关文档**: [10_pin_self_referential.md](10_pin_self_referential.md)

---

## 6. 错误实现 Send / Sync {#6-错误实现-send-sync}

### 现象 {#现象-6}

```rust
use std::sync::Arc;
use std::thread;

struct NotThreadSafe(*mut u8);

unsafe impl Send for NotThreadSafe {}
unsafe impl Sync for NotThreadSafe {}

fn main() {
    let v = Arc::new(NotThreadSafe(std::ptr::null_mut()));
    for _ in 0..4 {
        let v = Arc::clone(&v);
        thread::spawn(move || unsafe { *v.0 = 1 }); // ❌ 数据竞争
    }
}
```

### 后果 {#后果}

运行时数据竞争、未定义行为（UB）。编译器不会报错，因为 `unsafe impl` 是用户承诺。

### 修复方案 {#修复方案-6}

- 除非完全理解不变量，否则不要手动实现 `Send` / `Sync`。
- 使用 `std::sync::Mutex`、`RwLock`、`Atomic*` 等线程安全原语包装非线程安全状态。

---

## 7. 生命周期参数不足 {#7-生命周期参数不足}

### 现象 {#现象-6}

```rust
fn longest(x: &str, y: &str) -> &str {
    if x.len() > y.len() { x } else { y }
}
```

### 编译器错误 {#编译器错误-5}

```text
error[E0106]: missing lifetime specifier
```

### 修复方案 {#修复方案-6}

```rust
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}
```

必要时使用 `Cow<'a, str>` 或返回拥有所有权的 `String` 以解除生命周期耦合。

---

## 总结 {#总结}

| 反例 | 违反规则 | 典型错误码 | 修复方向 |
|------|----------|------------|----------|
| 使用已移动的值 | 所有权唯一性 | E0382 | clone / 借用 / 改签名 |
| 多次可变借用 | 借用唯一性 | E0499 | 缩小作用域 / split |
| 可变+不可变借用重叠 | 借用排斥性 | E0502 | 重排操作 / 临时作用域 |
| 返回悬垂引用 | 引用有效性 | E0106 / E0515 | 返回所有权 / 生命周期参数 |
| 自引用结构体被移动 | 移动语义 | E0106 | 索引 / Pin / 重新设计 |
| 错误实现 Send/Sync | 并发不变量 | — (运行时 UB) | 不手动实现 / 使用同步原语 |
| 生命周期参数不足 | 生命周期推断 | E0106 | 显式标注 / 返回 owned 类型 |

> **权威来源**: [Rust Reference – Ownership](https://doc.rust-lang.org/reference/ownership.html) | [Rust Reference – Lifetimes](https://doc.rust-lang.org/reference/lifetime-elision.html) | [The Rust Programming Language – Ch 4](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html) | [The Rust Programming Language – Ch 10](https://doc.rust-lang.org/book/ch10-00-generics.html) | [Rustonomicon – Send and Sync](https://doc.rust-lang.org/nomicon/send-and-sync.html) | [Pin and Suffering](https://blog.yoshuawuyts.com/pin-streams/)

## 相关概念 {#相关概念}

- [所有权模型](10_ownership_model.md)
- [借用检查器证明](10_borrow_checker_proof.md)
- [生命周期形式化](../type_theory/10_lifetime_formalization.md)
- [Pin 与自引用](10_pin_self_referential.md)
- [Send/Sync 形式化](10_send_sync_formalization.md)
- [通用反例汇编](../10_counter_examples_compendium.md)
- [知识图谱索引](../10_knowledge_graph_index.md)

---

## RFC 参考 {#rfc-参考}

> **来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)**

- [RFC 到反例自动化映射索引](../10_rfc_to_counterexample_mapping.md)
- [Rust RFCs 官方索引](https://rust-lang.github.io/rfcs/)
- [RFC 2094: Non-lexical lifetimes](https://rust-lang.github.io/rfcs/2094-nll.html)
- [RFC 1858: Immovable types](https://github.com/rust-lang/rfcs/pull/1858)

## 权威来源参考 {#权威来源参考}

本反例汇编参考以下 P1/P1.5/P2 权威来源：

- [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)
- [Stacked Borrows](https://plv.mpi-sws.org/rustbos/)
- [Tree Borrows](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html)

## 社区权威参考 {#社区权威参考}

- [Inside Rust Blog](https://blog.rust-lang.org/inside-rust/)
- [This Week in Rust](https://this-week-in-rust.org/)
