# 12.10 内存泄漏检测（Memory Leak Detection）

---


## 📊 目录

- [理论简述](#理论简述)
- [核心代码示例](#核心代码示例)
- [详细注释](#详细注释)
- [理论映射](#理论映射)
- [边界情况与常见错误](#边界情况与常见错误)
- [FAQ](#faq)


## 理论简述

内存泄漏是指已分配的内存未被及时释放，导致资源浪费。Rust通过所有权、Drop特质和智能指针自动管理内存，但循环借用等场景仍可能导致泄漏。可借助工具如`valgrind`、`cargo-geiger`等检测泄漏。相关理论详见[内存管理机制](../../11_memory_management/01_memory_management_theory.md)与[内存安全理论](../../11_memory_management/02_memory_safety.md)。

---

## 核心代码示例

```rust
use std::rc::Rc;

fn main() {
    // 循环借用导致内存泄漏
    struct Node {
        next: Option<Rc<Node>>,
    }
    let a = Rc::new(Node { next: None });
    let b = Rc::new(Node { next: Some(a.clone()) });
    // a.next = Some(b.clone()); // 编译错误：a为不可变
    // 实际项目中可用RefCell+Rc实现可变循环借用
    println!("a借用计数: {}", Rc::strong_count(&a));
    println!("b借用计数: {}", Rc::strong_count(&b));
}
```

---

## 详细注释

- Rc循环借用会导致内存无法释放，形成泄漏。
- Rust自动管理大部分内存，但需注意借用计数型结构的循环借用。
- 可用Weak指针打破循环，或用工具检测泄漏。

---

## 理论映射

- 对应[内存管理机制](../../11_memory_management/01_memory_management_theory.md)
- 内存安全理论见[11_memory_management/02_memory_safety.md](../../11_memory_management/02_memory_safety.md)
- Drop特质见[12.05_drop.md](./12.05_drop.md)

---

## 边界情况与常见错误

- **边界情况**：
  - Rc/Arc循环借用。
  - FFI或unsafe代码分配的内存。
- **常见错误**：
  - 忽略Weak指针导致泄漏。
  - 手动管理内存未释放。
  - 工具未覆盖全部泄漏场景。

---

## FAQ

- **Q: Rust如何避免内存泄漏？**
  - A: 避免循环借用，合理使用Weak指针，配合工具检测。
- **Q: 如何检测Rust项目中的内存泄漏？**
  - A: 使用valgrind、cargo-geiger等工具。
- **Q: 内存泄漏常见应用场景？**
  - A: 长生命周期服务、复杂数据结构、FFI等。

---

（本示例可直接用`rustc`编译验证，理论与代码一一对应，便于教学与自动化校验。）
