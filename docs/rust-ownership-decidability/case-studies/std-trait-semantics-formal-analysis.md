# Rust标准库核心Trait语义形式化分析

> **主题**: Drop/Clone/Send/Sync/Any的语义与安全性
>
> **形式化框架**: 类型类 + 效果系统
>
> **参考**: Rust Standard Library; Trait Semantics

---

## 目录

- [Rust标准库核心Trait语义形式化分析](#rust标准库核心trait语义形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. Drop trait](#2-drop-trait)
    - [2.1 析构语义](#21-析构语义)
    - [定义 2.1 (Drop trait)](#定义-21-drop-trait)
    - [定理 2.1 (RAII保证)](#定理-21-raii保证)
    - [2.2 Drop顺序](#22-drop顺序)
    - [定理 2.2 (Drop顺序规则)](#定理-22-drop顺序规则)
    - [2.3 析构保证](#23-析构保证)
    - [定理 2.3 (析构幂等性)](#定理-23-析构幂等性)
  - [3. Clone trait](#3-clone-trait)
    - [3.1 拷贝语义](#31-拷贝语义)
    - [定义 3.1 (Clone trait)](#定义-31-clone-trait)
    - [定理 3.1 (Clone语义)](#定理-31-clone语义)
    - [3.2 Clone vs Copy](#32-clone-vs-copy)
    - [定义 3.2 (Copy trait)](#定义-32-copy-trait)
    - [定理 3.2 (Copy的隐式性)](#定理-32-copy的隐式性)
  - [4. Send与Sync](#4-send与sync)
    - [4.1 线程安全边界](#41-线程安全边界)
    - [定义 4.1 (Send与Sync)](#定义-41-send与sync)
    - [定理 4.1 (Send语义)](#定理-41-send语义)
    - [定理 4.2 (Sync语义)](#定理-42-sync语义)
    - [4.2 自动实现规则](#42-自动实现规则)
    - [定理 4.3 (自动实现)](#定理-43-自动实现)
  - [5. Any trait](#5-any-trait)
    - [5.1 类型擦除](#51-类型擦除)
    - [定义 5.1 (Any trait)](#定义-51-any-trait)
    - [定理 5.1 (类型擦除)](#定理-51-类型擦除)
    - [5.2 向下转换](#52-向下转换)
    - [定理 5.2 (downcast\_ref安全性)](#定理-52-downcast_ref安全性)
  - [6. Sized与?Sized](#6-sized与sized)
    - [定义 6.1 (Sized)](#定义-61-sized)
    - [定理 6.1 (?Sized类型)](#定理-61-sized类型)
  - [7. 反例](#7-反例)
    - [反例 7.1 (自定义Drop后使用)](#反例-71-自定义drop后使用)
    - [反例 7.2 (Rc跨线程)](#反例-72-rc跨线程)
    - [反例 7.3 (Any非'static)](#反例-73-any非static)
  - [参考文献](#参考文献)

---

## 1. 引言

核心trait定义Rust的类型系统行为:

- **Drop**: 资源清理
- **Clone/Copy**: 复制语义
- **Send/Sync**: 线程安全边界
- **Any**: 运行时类型信息

---

## 2. Drop trait

### 2.1 析构语义

### 定义 2.1 (Drop trait)

```rust
pub trait Drop {
    fn drop(&mut self);
}
```

### 定理 2.1 (RAII保证)

> 值离开作用域时自动调用drop。

**形式化**:

$$
\forall x: T. \text{scope\_end}(x) \Rightarrow \text{Drop}::\text{drop}(x)
$$

**保证**:

- 无论正常返回还是panic
- 即使是部分构造的值
- 栈展开时正确调用

∎

### 2.2 Drop顺序

### 定理 2.2 (Drop顺序规则)

> 变量按相反于声明顺序drop。

**示例**:

```rust
{
    let a = A;
    let b = B;
    let c = C;
}  // drop顺序: c, b, a
```

**结构体字段**:

```rust
struct S { a: A, b: B, c: C }
// drop顺序: c, b, a (按声明相反)
```

∎

### 2.3 析构保证

### 定理 2.3 (析构幂等性)

> 值被drop后不应再次使用。

**实现**:

```rust
let v = vec![1, 2, 3];
drop(v);
// v.push(4);  // 编译错误! v已被移动
```

**双重drop防止**:

```rust
impl Drop for MyType {
    fn drop(&mut self) {
        if self.already_dropped { return; }
        // 清理
        self.already_dropped = true;
    }
}
```

∎

---

## 3. Clone trait

### 3.1 拷贝语义

### 定义 3.1 (Clone trait)

```rust
pub trait Clone: Sized {
    fn clone(&self) -> Self;
    fn clone_from(&mut self, source: &Self) { ... }
}
```

### 定理 3.1 (Clone语义)

> clone()产生独立副本，不共享所有权。

**形式化**:

$$
\text{clone}: \&T \rightarrow T \text{ (独立值)}
$$

**对比引用**:

```rust
let a = vec![1, 2, 3];
let b = &a;       // 借用，不复制
let c = a.clone(); // 复制，独立所有权
```

∎

### 3.2 Clone vs Copy

### 定义 3.2 (Copy trait)

```rust
pub trait Copy: Clone { }
```

### 定理 3.2 (Copy的隐式性)

> Copy类型在赋值时隐式复制，Clone需要显式调用。

**对比**:

| 特性 | Copy | Clone |
|------|------|-------|
| 调用 | 隐式 | 显式(.clone()) |
| 开销 | 位复制 | 可能昂贵 |
| 约束 | 简单类型 | 任意类型 |
| 实现 | 自动/derive | 手动/Derive |

**形式化**:

$$
\begin{aligned}
\text{Copy}: x \rightarrow y &\equiv \text{memcpy}(x, y) \\
\text{Clone}: x \rightarrow y &\equiv \text{可能复杂构造}
\end{aligned}
$$

∎

---

## 4. Send与Sync

### 4.1 线程安全边界

### 定义 4.1 (Send与Sync)

```rust
pub unsafe auto trait Send { }
pub unsafe auto trait Sync { }
```

### 定理 4.1 (Send语义)

> T: Send表示T可以安全地移动到另一个线程。

**形式化**:

$$
T: \text{Send} \iff \forall t_1, t_2. \text{move}(v: T, t_1 \rightarrow t_2) \text{ 安全}
$$

**示例**:

```rust
// Send: i32, String, Vec<T>
// !Send: Rc<T>, *const T, *mut T
```

∎

### 定理 4.2 (Sync语义)

> T: Sync表示&T可以安全地在线程间共享。

**形式化**:

$$
T: \text{Sync} \iff \&T: \text{Send}
$$

**示例**:

```rust
// Sync: i32, String, Arc<T>
// !Sync: Cell<T>, RefCell<T>, Rc<T>
```

∎

### 4.2 自动实现规则

### 定理 4.3 (自动实现)

> Send和Sync是自动trait，默认实现。

**规则**:

- 如果类型的所有字段都实现Send，则类型自动实现Send
- 如果类型的所有字段都实现Sync，则类型自动实现Sync
- 使用 `impl !Send for T` 否定实现

**例外**:

```rust
struct MyType {
    data: *const u8,  // 原始指针!Send/!Sync
}
// MyType 自动 !Send/!Sync
```

∎

---

## 5. Any trait

### 5.1 类型擦除

### 定义 5.1 (Any trait)

```rust
pub trait Any: 'static {
    fn type_id(&self) -> TypeId;
}
```

### 定理 5.1 (类型擦除)

> Any允许将具体类型擦除为动态类型。

**形式化**:

$$
\text{Box}\langle T \rangle \xrightarrow{\text{as\_any}} \&dyn \text{Any}
$$

**用途**:

```rust
fn handle_error(err: Box<dyn Any>) {
    if let Some(e) = err.downcast_ref::<MyError>() {
        // 处理 MyError
    }
}
```

∎

### 5.2 向下转换

### 定理 5.2 (downcast_ref安全性)

> downcast_ref在类型匹配时成功，否则返回None。

**实现**:

```rust
fn downcast_ref<T: Any>(&self) -> Option<&T> {
    if self.type_id() == TypeId::of::<T>() {
        Some(unsafe { self.downcast_ref_unchecked() })
    } else {
        None
    }
}
```

**安全**:

- 运行时类型检查
- 不匹配时安全失败
- 无未定义行为

∎

---

## 6. Sized与?Sized

### 定义 6.1 (Sized)

```rust
pub trait Sized {
    // 自动为编译时大小已知的类型实现
}
```

### 定理 6.1 (?Sized类型)

> ?Sized类型编译时大小未知，只能通过引用使用。

**类型**:

| 类型 | Sized? | 使用方式 |
|------|--------|----------|
| i32 | ✅ | 直接值 |
| [T] | ❌ | &[T] |
| dyn Trait | ❌ | &dyn Trait |
| str | ❌ | &str |

**约束**:

```rust
fn foo<T>(t: T) {}           // T: Sized (默认)
fn bar<T: ?Sized>(t: &T) {} // T可能!Sized
```

∎

---

## 7. 反例

### 反例 7.1 (自定义Drop后使用)

```rust
let v = vec![1, 2, 3];
drop(v);
// v.len();  // 编译错误! v已移动
```

### 反例 7.2 (Rc跨线程)

```rust
let rc = Rc::new(42);
thread::spawn(move || {
    // *rc;  // 编译错误! Rc不是Send
});
```

### 反例 7.3 (Any非'static)

```rust
let x = 42;
let r = &x;
// let any: &dyn Any = r;  // 错误! &i32不是'static
```

---

## 参考文献

1. **Rust Standard Library.** (2024). `std::ops::Drop`, `std::clone::Clone`, `std::marker::{Send, Sync}`. <https://doc.rust-lang.org/std/>

---

*文档版本: 1.0.0*
*形式化深度: 高*
*定理数量: 10个*
*最后更新: 2026-03-04*
