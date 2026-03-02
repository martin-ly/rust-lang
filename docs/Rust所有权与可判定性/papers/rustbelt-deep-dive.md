# RustBelt 深度解读

> RustBelt: Securing the Foundations of the Rust Programming Language (POPL 2018)

---

## 1. 论文概述

### 核心问题

如何证明Rust的类型系统确实提供了它所承诺的内存安全保证？

### 主要贡献

1. **λ_Rust**: Rust核心语言的CPS形式化
2. **分离逻辑语义**: 使用Iris框架定义所有权
3. **标准库验证**: 验证Cell, RefCell, Rc, Arc, Mutex等

---

## 2. λ_Rust 核心语言

### 语法

```text
e ::= x | () | (e, e) | ℓ := e; e | !ℓ | ref(e) | ...
v ::= () | n | (v, v) | ℓ | &ℓ | &mut ℓ | ...
```

### 关键设计

- **CPS风格**: 显式continuation，简化控制流
- **位置(ℓ)**: 显式内存地址
- **引用(&ℓ, &mut ℓ)**: 作为一等公民

---

## 3. 所有权谓词

### 定义

```text
[T].own(t, v̄)  // 线程t拥有值v̄作为T类型
```

### 示例

```text
[i32].own(t, n) ≡ n ∈ ℤ

[Box<T>].own(t, ℓ) ≡ ℓ ↦ v̄ * [T].own(t, v̄)

[&mut τ].own(t, ℓ) ≡ ∃v̄. ℓ ↦ v̄ * [τ].own(t, v̄) * borrowed(ℓ)
```

---

## 4. 标准库验证

### `Cell<T>`

```rust
// 规范
{[T].shr(t, c)} c.get() {x. x = v}
```

### `RefCell<T>`

运行时借用检查的形式化。

### `Rc<T>`

引用计数不变量的证明。

---

## 5. Coq实现

- **总代码量**: ~19,000行
- **完全机器检查**
- **项目地址**: <https://gitlab.mpi-sws.org/iris/lambda-rust>

---

*RustBelt建立了Rust形式化验证的基础框架。*
