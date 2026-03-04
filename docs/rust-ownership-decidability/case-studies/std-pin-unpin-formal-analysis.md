# Rust标准库 Pin & Unpin 形式化分析

> **主题**: 自引用结构的安全固定
>
> **形式化框架**: 仿射类型 + 所有权约束
>
> **参考**: Rust Standard Library; Rust Async Book

---

## 目录

- [Rust标准库 Pin \& Unpin 形式化分析](#rust标准库-pin--unpin-形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 自引用问题](#2-自引用问题)
    - [2.1 移动安全性](#21-移动安全性)
    - [定义 2.1 (自引用结构)](#定义-21-自引用结构)
    - [定理 2.1 (自引用结构的移动危险)](#定理-21-自引用结构的移动危险)
    - [2.2 悬垂指针风险](#22-悬垂指针风险)
    - [定义 2.2 (悬垂指针)](#定义-22-悬垂指针)
  - [3. `Pin<P>` 形式化定义](#3-pinp-形式化定义)
    - [3.1 类型定义](#31-类型定义)
    - [定义 3.1 (Pin类型)](#定义-31-pin类型)
    - [3.2 固定不变式](#32-固定不变式)
    - [定义 3.2 (固定不变式)](#定义-32-固定不变式)
  - [4. Unpin trait 分析](#4-unpin-trait-分析)
    - [4.1 自动实现](#41-自动实现)
    - [定义 4.1 (Unpin trait)](#定义-41-unpin-trait)
    - [定理 4.1 (Unpin的传递性)](#定理-41-unpin的传递性)
    - [4.2 !Unpin 类型](#42-unpin-类型)
    - [定义 4.2 (!Unpin类型示例)](#定义-42-unpin类型示例)
    - [定理 4.2 (PhantomPinned的效果)](#定理-42-phantompinned的效果)
  - [5. Pin 操作语义](#5-pin-操作语义)
    - [5.1 创建固定指针](#51-创建固定指针)
    - [定义 5.1 (Pin创建)](#定义-51-pin创建)
    - [定理 5.1 (Pin::new的安全性)](#定理-51-pinnew的安全性)
    - [5.2 安全操作](#52-安全操作)
    - [定理 5.2 (Pin的安全操作)](#定理-52-pin的安全操作)
    - [5.3 unsafe 操作](#53-unsafe-操作)
    - [定理 5.3 (Pin的unsafe操作)](#定理-53-pin的unsafe操作)
  - [6. 与 async/await 的关系](#6-与-asyncawait-的关系)
    - [6.1 Future 固定](#61-future-固定)
    - [定义 6.1 (Future trait)](#定义-61-future-trait)
    - [定理 6.1 (Future需要Pin的原因)](#定理-61-future需要pin的原因)
    - [6.2 状态机转换](#62-状态机转换)
    - [定理 6.2 (状态机固定保证)](#定理-62-状态机固定保证)
  - [7. 内存布局影响](#7-内存布局影响)
    - [定理 7.1 (Pin不改变内存布局)](#定理-71-pin不改变内存布局)
    - [定理 7.2 (`Pin<Box<T>>`的堆固定)](#定理-72-pinboxt的堆固定)
  - [8. 反例与常见错误](#8-反例与常见错误)
    - [反例 8.1 (错误地从Pin创建可变引用)](#反例-81-错误地从pin创建可变引用)
    - [反例 8.2 (错误实现Unpin)](#反例-82-错误实现unpin)
    - [反例 8.3 (Pin投影错误)](#反例-83-pin投影错误)
  - [参考文献](#参考文献)

---

## 1. 引言

`Pin<P>` 是Rust中处理**自引用结构**的关键类型，确保数据在内存中的位置不会被移动。

**核心问题**:

- 自引用结构包含指向自身的指针
- 移动结构体会使自引用悬垂
- Pin提供编译时保证，防止此类移动

---

## 2. 自引用问题

### 2.1 移动安全性

### 定义 2.1 (自引用结构)

```rust
struct SelfRef {
    data: String,
    ptr: *const String,  // 指向 data
}

impl SelfRef {
    fn new() -> Self {
        let mut s = SelfRef {
            data: String::from("hello"),
            ptr: ptr::null(),
        };
        s.ptr = &s.data;  // 自引用
        s
    }
}
```

### 定理 2.1 (自引用结构的移动危险)

> 移动自引用结构体会导致悬垂指针。

**证明**:

**栈布局**:

```text
初始状态 (地址 0x1000):
┌─────────────────────┐
│ data: String        │ 0x1000
│ ptr: *const String ─┼──► 0x1000
└─────────────────────┘

移动后 (地址 0x2000):
┌─────────────────────┐
│ data: String        │ 0x2000
│ ptr: *const String ─┼──► 0x1000 (悬垂!)
└─────────────────────┘
```

**Rust阻止此情况**:

- 编译错误: cannot move out of borrowed content
- 或运行时Pin约束

∎

### 2.2 悬垂指针风险

### 定义 2.2 (悬垂指针)

指向已释放或已移动内存的指针。

**在自引用结构中的风险**:

```rust
let s = SelfRef::new();
let ptr = s.ptr;  // 指向 s.data
let s2 = s;       // 移动 s 到 s2
// ptr 现在悬垂!
```

---

## 3. `Pin<P>` 形式化定义

### 3.1 类型定义

### 定义 3.1 (Pin类型)

```rust
#[repr(transparent)]
pub struct Pin<P> {
    pointer: P,
}
```

**约束**: `P: Deref` 或 `P: DerefMut`

**形式化**:

$$
\text{Pin}\langle P \rangle = \{p: P \mid \text{pinned}(p)\}
$$

其中 $\text{pinned}(p)$ 表示指针 $p$ 指向的数据保证不会被移动。

### 3.2 固定不变式

### 定义 3.2 (固定不变式)

如果 `T: !Unpin`，则:

1. **固定后不可移动**: `Pin<&mut T>` 不能转换为 `&mut T`
2. **地址稳定**: 数据的内存地址保持不变
3. **自引用有效**: 任何自引用在整个固定期间保持有效

**形式化**:

$$
\text{PinInvariant}(T) \iff \forall t: T. \text{!Unpin}(T) \Rightarrow \text{addr}(t) = \text{const}
$$

---

## 4. Unpin trait 分析

### 4.1 自动实现

### 定义 4.1 (Unpin trait)

```rust
pub auto trait Unpin {}
```

**自动实现规则**:

- 如果类型的所有字段都实现 `Unpin`，则类型自动实现 `Unpin`
- `!Unpin` 需要显式标记: `impl !Unpin for MyType {}`

### 定理 4.1 (Unpin的传递性)

> 如果 `T: Unpin`，则包含 `T` 的结构体也是 `Unpin`。

**证明**:

由自动trait实现规则:

```rust
struct Container<T> {
    inner: T,
}

// 如果 T: Unpin，则 Container<T>: Unpin
// 这是自动的，无需显式实现
```

∎

### 4.2 !Unpin 类型

### 定义 4.2 (!Unpin类型示例)

```rust
// 标记为 !Unpin
pub struct PhantomPinned;

impl !Unpin for PhantomPinned {}

// 使用 PhantomPinned 使结构体 !Unpin
struct SelfRef {
    data: String,
    _pin: PhantomPinned,
}
```

### 定理 4.2 (PhantomPinned的效果)

> 包含 `PhantomPinned` 字段的结构体自动成为 `!Unpin`。

**证明**:

```rust
struct MyFuture {
    data: String,
    ptr: *const String,
    _marker: PhantomPinned,  // 使结构体 !Unpin
}

// 自动 trait 规则:
// - PhantomPinned: !Unpin
// - 因此 MyFuture: !Unpin
```

这确保 `MyFuture` 必须被Pin才能安全使用。∎

---

## 5. Pin 操作语义

### 5.1 创建固定指针

### 定义 5.1 (Pin创建)

```rust
impl<P: Deref> Pin<P> {
    pub unsafe fn new_unchecked(pointer: P) -> Pin<P> {
        Pin { pointer }
    }
}

impl<P: Deref<Target: Unpin>> Pin<P> {
    pub fn new(pointer: P) -> Pin<P> {
        unsafe { Pin::new_unchecked(pointer) }
    }
}
```

### 定理 5.1 (Pin::new的安全性)

> `Pin::new` 只对 `Unpin` 类型安全。

**证明**:

- 如果 `T: Unpin`，移动是安全的
- 因此固定约束不要求地址稳定
- `Pin::new` 可以安全调用

对于 `!Unpin`:

- 必须使用 `Pin::new_unchecked`
- 调用者必须保证数据不会被移动
- 通常是堆分配 + `Pin<Box<T>>`

∎

### 5.2 安全操作

### 定理 5.2 (Pin的安全操作)

> 以下操作对任意 `Pin<P>` 安全:

```rust
impl<P: Deref> Pin<P> {
    // 获取共享引用 (始终安全)
    pub fn as_ref(&self) -> Pin<&P::Target>;

    // 获取地址 (始终安全)
    pub fn as_ptr(&self) -> *const P::Target;

    // 解引用 (只读)
    pub fn get_ref(&self) -> &P::Target;
}
```

**证明**:

这些操作不暴露可变性，因此:

- 不会移动数据
- 不会破坏固定不变式
- 安全用于所有类型

∎

### 5.3 unsafe 操作

### 定理 5.3 (Pin的unsafe操作)

> 以下操作需要 `unsafe`，只应在知道类型是 `Unpin` 或特殊处理时使用:

```rust
impl<P: DerefMut> Pin<P> {
    // 获取可变引用
    pub unsafe fn get_unchecked_mut(self) -> &mut P::Target;

    // 映射内部值
    pub unsafe fn map_unchecked_mut<F, U>(self, f: F) -> Pin<&mut U>
    where F: FnOnce(&mut P::Target) -> &mut U;
}
```

**安全条件**:

```rust
// 安全情况1: T: Unpin
let mut x = 5;
let mut pinned = Pin::new(&mut x);
let r = unsafe { pinned.as_mut().get_unchecked_mut() };
*r = 10;  // OK，i32: Unpin

// 安全情况2: 投影到已固定的Pin字段
struct MyFuture {
    field: String,
}

impl MyFuture {
    fn field_mut(self: Pin<&mut Self>) -> Pin<&mut String> {
        unsafe { self.map_unchecked_mut(|s| &mut s.field) }
    }
}
// 安全因为 field 随 Self 一起固定
```

∎

---

## 6. 与 async/await 的关系

### 6.1 Future 固定

### 定义 6.1 (Future trait)

```rust
trait Future {
    type Output;
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output>;
}
```

**关键**: `poll` 使用 `Pin<&mut Self>`，而非 `&mut Self`。

### 定理 6.1 (Future需要Pin的原因)

> 异步状态机可能包含自引用，因此需要Pin保证。

**证明**:

**async fn展开**:

```rust
async fn foo() {
    let x = [1, 2, 3];
    let y = &x[0];  // 借用局部变量
    bar().await;    // 可能挂起，状态机保存
    println!("{}", y);  // 恢复后使用
}
```

**生成的状态机** (简化):

```rust
enum FooFuture {
    Start,
    Waiting {
        x: [i32; 3],
        y: *const i32,  // 指向 x[0] 的指针!
    },
    Done,
}
```

状态机在 `.await` 点可能移动(存储在堆上)。

如果 `y` 是普通引用 `&i32`，移动后悬垂。

实际是原始指针，需要Pin保证地址稳定。∎

### 6.2 状态机转换

### 定理 6.2 (状态机固定保证)

> 由 `async fn` 生成的Future自动是 `!Unpin` (如果有自引用)。

**证明**:

编译器分析:

1. 检查是否有跨await点的借用
2. 如果有，状态体包含自引用
3. 自动生成 `!Unpin`

```rust
async fn has_borrow() {
    let x = [1, 2, 3];
    let y = &x[0];
    yield_now().await;
    dbg!(y);
}

// 生成的Future自动 !Unpin
// 必须通过 Pin<&mut Self> poll
```

∎

---

## 7. 内存布局影响

### 定理 7.1 (Pin不改变内存布局)

> `Pin<P>` 与 `P` 有相同的内存布局。

**证明**:

```rust
#[repr(transparent)]
pub struct Pin<P> {
    pointer: P,
}
```

`#[repr(transparent)]` 保证:

- 与内部类型相同的表示
- ABI兼容
- 零运行时开销

$$
\text{size_of::<Pin<P>>} = \text{size_of::<P>()}
$$

∎

### 定理 7.2 (`Pin<Box<T>>`的堆固定)

> `Pin<Box<T>>` 保证 `T` 在堆上且地址稳定。

**证明**:

```rust
let data: Pin<Box<MyFuture>> = Box::pin(MyFuture::new());
```

- `Box` 分配在堆上
- `Pin` 保证不会移动(除非实现Unpin)
- 地址在整个生命周期内稳定

这是自引用结构的标准模式。∎

---

## 8. 反例与常见错误

### 反例 8.1 (错误地从Pin创建可变引用)

```rust
struct SelfRef {
    data: String,
    ptr: *const String,
    _pin: PhantomPinned,
}

impl SelfRef {
    // 危险!
    fn get_data_mut(&mut self) -> &mut String {
        &mut self.data
    }
}

let mut s = Box::pin(SelfRef::new());
// let r = s.as_mut().get_unchecked_mut().get_data_mut();
// 未定义行为! 可能移动 String，破坏自引用
```

**正确做法**:

```rust
impl SelfRef {
    fn get_data(self: Pin<&mut Self>) -> Pin<&mut String> {
        unsafe { self.map_unchecked_mut(|s| &mut s.data) }
    }
}

let r = s.as_mut().get_data();  // 返回 Pin<&mut String>
// String 仍被固定
```

### 反例 8.2 (错误实现Unpin)

```rust
struct Bad {
    data: String,
    ptr: *const String,  // 指向 data
}

// 错误: 手动实现 Unpin，即使结构体有自引用
impl Unpin for Bad {}

let b = Bad { ... };
let p = Pin::new(&b);  // 使用 Pin::new (安全版本)
// 但移动 b 实际上会破坏自引用!
```

**规则**: 只有真正可以安全移动的类型才实现 `Unpin`。

### 反例 8.3 (Pin投影错误)

```rust
struct MyFuture {
    field1: String,
    field2: String,
    self_ref: *const String,  // 指向 field1
}

impl MyFuture {
    fn field2_mut(self: Pin<&mut Self>) -> &mut String {
        // 错误: 直接返回可变引用
        unsafe { &mut self.get_unchecked_mut().field2 }
    }
}
```

**问题**: 调用者获得 `&mut String` 后可以移动它!

**正确**:

```rust
fn field2_mut(self: Pin<&mut Self>) -> Pin<&mut String> {
    unsafe { self.map_unchecked_mut(|s| &mut s.field2) }
}
```

---

## 参考文献

1. **Rust Standard Library.** (2024). `std::pin::Pin`. <https://doc.rust-lang.org/std/pin/>

2. **Rust Async Book.** (2024). *Pinning*. <https://rust-lang.github.io/async-book/04_pinning/>

3. **Futures Crate Documentation.** (2024). *Futures and Pinning*. <https://docs.rs/futures/>

4. **Tmandry.** (2019). *Pin and Suffering*. Rust Latam.
   - 关键贡献: Pin的直观解释
   - 关联: 第6节

5. **Withoutboats.** (2018). *Async/Await I: Self-Referential Structs*.
   - 关键贡献: 自引用结构与Pin设计
   - 关联: 全文

---

*文档版本: 1.0.0*
*形式化深度: 高*
*定理数量: 10个*
*最后更新: 2026-03-04*
