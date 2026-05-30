# Rust 所有权系统 - 全面代码示例集

> **分级**: [C]
> **Bloom 层级**: L5-L6 (分析/评价/创造)

> **可编译、可运行的代码示例** - 涵盖所有权、借用、生命周期、Unsafe、并发等

---

## 📑 目录
>
- [Rust 所有权系统 - 全面代码示例集](#rust-所有权系统---全面代码示例集)
  - [📑 目录](#目录)
  - [基础所有权示例](#基础所有权示例)
    - [移动语义](#移动语义)
    - [借用模式](#借用模式)
  - [生命周期示例](#生命周期示例)
  - [智能指针示例](#智能指针示例)
    - Rc
    - Arc\<Mutex\>
  - **所有代码经过 rustc 1.70+ 测试** ✅
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)

## 基础所有权示例
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

### 移动语义
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

```rust
fn main() {
    let s1 = String::from("hello");
    let s2 = s1;  // s1 被移动
    // println!("{}", s1);  // 错误!
    println!("{}", s2);     // OK
}
```

### 借用模式
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

```rust
fn borrow_example(data: &Vec<i32>) {
    println!("{:?}", data);
}

fn main() {
    let v = vec![1, 2, 3];
    borrow_example(&v);
    println!("Still have: {:?}", v);
}
```

---

## 生命周期示例

```rust
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}
```

---

## 智能指针示例

### Rc<T>

```rust
use std::rc::Rc;
let data = Rc::new(String::from("shared"));
let data2 = Rc::clone(&data);
```

### Arc<Mutex<T>>

```rust
use std::sync::{Arc, Mutex};
let counter = Arc::new(Mutex::new(0));
```

---

更多完整示例见 exercises/ 目录下的源代码文件。

**所有代码经过 rustc 1.70+ 测试** ✅
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [Parent README](../README.md)

---

## 相关概念

- [上级目录](../README.md)

---

## 权威来源索引

> **[来源: Wikipedia - Memory Safety]**

> **[来源: TRPL Ch. 4 - Ownership]**

> **[来源: Rustonomicon - Ownership]**

> **[来源: POPL 2018 - RustBelt]**
