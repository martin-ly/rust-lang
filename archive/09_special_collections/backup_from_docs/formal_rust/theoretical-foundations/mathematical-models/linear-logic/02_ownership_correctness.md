# 02 所有权系统正确性证明

## 章节简介

本章系统梳理Rust所有权系统的理论基础、形式化定义、核心定理与证明思路，涵盖所有权、借用、生命周期、内存安全、借用检查、资源自动管理等。通过分离逻辑、状态机等建模，给出安全性定理、推理过程与工程意义。

## 目录

1. 理论基础与所有权模型
2. 内存安全与借用检查
3. 生命周期与资源管理
4. Rust所有权正确性形式化思路
5. 代码示例与工程意义
6. 参考文献

## 1. 理论基础与所有权模型

- **所有权（Ownership）**：每个值有唯一所有者，离开作用域自动释放。
- **借用（Borrowing）**：允许临时访问资源，分为可变借用与不可变借用。
- **生命周期（Lifetime）**：静态追踪借用的有效期，防止悬垂指针。

> **形式化定义**：
>
> - $\forall v.\ \exists!\ owner(v)$
> - $\forall borrow.\ lifetime(borrow) \leq lifetime(owner)$

## 2. 内存安全与借用检查

- **借用检查器**：编译期静态分析，确保借用规则不被违反。
- **规则**：
  - 同一时刻只能有一个可变借用，或任意多个不可变借用。
  - 借用不能超出所有者的生命周期。

> **安全性定理**：
>
> - 无悬垂指针：$\forall ref.\ valid(ref) \implies lifetime(ref) \leq lifetime(owner)$
> - 无二次释放：$\forall v.\ released(v) \implies \neg access(v)$

## 3. 生命周期与资源管理

- **生命周期参数**（如 `'a`）：标注借用作用域，保证借用不悬垂。
- **生命周期推断**：编译器自动分析大部分生命周期。
- **资源自动释放**：RAII模式下，所有权离开作用域即自动释放。

> **推理**：生命周期系统保证借用的所有访问均在有效期内，资源自动释放避免内存泄漏。

## 4. Rust所有权正确性形式化思路

- **形式化模型**：以状态机、类型系统或分离逻辑建模所有权转移与借用关系。
- **安全性定理**：证明在所有权规则下，程序不会出现悬垂指针、二次释放等内存错误。
- **RustBelt/Iris**：采用分离逻辑与不变式，机械化证明Rust所有权模型的正确性。

## 5. 代码示例与工程意义

```rust
fn main() {
    let s = String::from("hello"); // s 拥有所有权
    let r = &s; // 不可变借用
    println!("{}", r); // 合法
    // s 离开作用域自动释放
}
```

- **工程意义**：
  - 编译期消除悬垂指针、二次释放等内存安全隐患
  - 支持高性能、无GC的系统级开发

## 6. 参考文献

1. Jung, R., Jourdan, J. H., Krebbers, R., & Dreyer, D. (2017). RustBelt: Securing the foundations of the Rust programming language. POPL 2018.
2. Matsakis, N. D., & Klock, F. S. (2014). The Rust language. ACM SIGAda Ada Letters, 34(3), 103-104.
3. Walker, D. (2005). Substructural type systems. In Advanced Topics in Types and Programming Languages, MIT Press.
