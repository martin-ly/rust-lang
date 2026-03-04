# Rust标准库 智能指针形式化分析

> **主题**: Box、Rc、Arc的内存管理与所有权语义
>
> **形式化框架**: 所有权代数 + 引用计数
>
> **参考**: Rust Standard Library; Smart Pointer Patterns

---

## 目录

- [Rust标准库 智能指针形式化分析](#rust标准库-智能指针形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. `Box<T>` 堆分配](#2-boxt-堆分配)
    - [2.1 唯一所有权](#21-唯一所有权)
    - [定义 2.1 (Box)](#定义-21-box)
    - [定理 2.1 (Box唯一所有权)](#定理-21-box唯一所有权)
    - [2.2 Deref与解引用强制](#22-deref与解引用强制)
    - [定理 2.2 (Deref强制)](#定理-22-deref强制)
    - [2.3 递归类型](#23-递归类型)
    - [定理 2.3 (递归类型)](#定理-23-递归类型)
  - [3. `Rc<T>` 引用计数](#3-rct-引用计数)
    - [3.1 共享所有权](#31-共享所有权)
    - [定义 3.1 (Rc)](#定义-31-rc)
    - [定理 3.1 (Rc共享所有权)](#定理-31-rc共享所有权)
    - [3.2 非线程安全](#32-非线程安全)
    - [定理 3.2 (Rc非线程安全)](#定理-32-rc非线程安全)
    - [3.3 循环引用问题](#33-循环引用问题)
    - [定理 3.3 (Rc循环引用泄漏)](#定理-33-rc循环引用泄漏)
  - [4. `Arc<T>` 原子引用计数](#4-arct-原子引用计数)
    - [4.1 线程安全共享](#41-线程安全共享)
    - [定理 4.1 (Arc线程安全)](#定理-41-arc线程安全)
    - [4.2 内存序保证](#42-内存序保证)
    - [定理 4.2 (Arc内存序)](#定理-42-arc内存序)
  - [5. `Cell<T>` 与 `RefCell<T>`](#5-cellt-与-refcellt)
    - [5.1 内部可变性](#51-内部可变性)
    - [定义 5.1 (Cell)](#定义-51-cell)
    - [定理 5.1 (Cell内部可变性)](#定理-51-cell内部可变性)
    - [5.2 运行时借用检查](#52-运行时借用检查)
    - [定义 5.2 (RefCell)](#定义-52-refcell)
    - [定理 5.2 (RefCell运行时检查)](#定理-52-refcell运行时检查)
  - [6. 智能指针对比](#6-智能指针对比)
  - [7. 内存布局分析](#7-内存布局分析)
    - [`Box<T>`](#boxt)
    - [`Rc<T>/Arc<T>`](#rctarct)
  - [8. 反例与陷阱](#8-反例与陷阱)
    - [反例 8.1 (Rc多线程)](#反例-81-rc多线程)
    - [反例 8.2 (RefCell panic)](#反例-82-refcell-panic)
    - [反例 8.3 (Box泄漏)](#反例-83-box泄漏)
  - [参考文献](#参考文献)

---

## 1. 引言

Rust智能指针提供高级内存管理:

- **`Box<T>`**: 堆分配，唯一所有权
- **`Rc<T>`**: 单线程引用计数
- **`Arc<T>`**: 多线程原子引用计数
- **`Cell<T>`/`RefCell<T>`**: 内部可变性

---

## 2. `Box<T>` 堆分配

### 2.1 唯一所有权

### 定义 2.1 (Box)

```rust
pub struct Box<T: ?Sized>(Unique<T>);
```

### 定理 2.1 (Box唯一所有权)

> `Box<T>` 保证对堆数据有且只有一个所有者。

**证明**:

```rust
let b = Box::new(42);
let b2 = b;  // 移动所有权
// b 不再可用
```

- Box不实现Copy
- 移动语义转移所有权
- Drop时释放堆内存

∎

### 2.2 Deref与解引用强制

### 定理 2.2 (Deref强制)

> `Box<T>` 自动解引用为 &T 或 &mut T。

**实现**:

```rust
impl<T: ?Sized> Deref for Box<T> {
    type Target = T;

    fn deref(&self) -> &T {
        &self.0.as_ref()
    }
}

impl<T: ?Sized> DerefMut for Box<T> {
    fn deref_mut(&mut self) -> &mut T {
        &mut self.0.as_mut()
    }
}
```

**强制规则**:

```rust
fn foo(x: &i32) {}

let b = Box::new(42);
foo(&b);  // 自动解引用: &Box<i32> -> &i32
```

∎

### 2.3 递归类型

### 定理 2.3 (递归类型)

> Box使递归类型成为可能。

**示例**:

```rust
enum List<T> {
    Nil,
    Cons(T, Box<List<T>>),  // Box允许递归
}

// 内存布局已知: Cons的大小 = T + Box大小(固定)
```

∎

---

## 3. `Rc<T>` 引用计数

### 3.1 共享所有权

### 定义 3.1 (Rc)

```rust
pub struct Rc<T: ?Sized> {
    ptr: NonNull<RcInner<T>>,
    phantom: PhantomData<RcInner<T>>,
}

struct RcInner<T: ?Sized> {
    strong: Cell<usize>,
    weak: Cell<usize>,
    value: T,
}
```

### 定理 3.1 (Rc共享所有权)

> `Rc<T>` 允许多个所有者共享堆数据。

**证明**:

```rust
let rc1 = Rc::new(42);
let rc2 = rc1.clone();  // 引用计数+1
let rc3 = rc2.clone();  // 引用计数+1

// 三个Rc共享同一个值
// 最后一个Rc drop时释放内存
```

∎

### 3.2 非线程安全

### 定理 3.2 (Rc非线程安全)

> `Rc<T>` 不是 Send 也不是 Sync。

**证明**:

```rust
impl<T: ?Sized> !Send for Rc<T> {}
impl<T: ?Sized> !Sync for Rc<T> {}
```

**原因**:

- 使用 `Cell<usize>` 作为引用计数
- 非原子操作
- 多线程访问导致数据竞争

∎

### 3.3 循环引用问题

### 定理 3.3 (Rc循环引用泄漏)

> Rc循环引用导致内存泄漏。

**证明**:

```rust
struct Node {
    value: i32,
    next: Option<Rc<RefCell<Node>>>,
}

let node1 = Rc::new(RefCell::new(Node { value: 1, next: None }));
let node2 = Rc::new(RefCell::new(Node { value: 2, next: Some(node1.clone()) }));
node1.borrow_mut().next = Some(node2.clone());

// 循环引用: node1 <-> node2
// 引用计数永远不会归零
// 内存泄漏!
```

**解决方案**: 使用 `Weak<T>`。

∎

---

## 4. `Arc<T>` 原子引用计数

### 4.1 线程安全共享

### 定理 4.1 (Arc线程安全)

> `Arc<T>` 是 Send + Sync(如果T是Send + Sync)。

**证明**:

```rust
unsafe impl<T: ?Sized + Sync + Send> Send for Arc<T> {}
unsafe impl<T: ?Sized + Sync + Send> Sync for Arc<T> {}
```

- 使用 `AtomicUsize` 作为引用计数
- 原子操作保证线程安全

∎

### 4.2 内存序保证

### 定理 4.2 (Arc内存序)

> Arc使用Acquire-Release保证数据可见性。

**证明**:

```rust
impl<T> Clone for Arc<T> {
    fn clone(&self) -> Arc<T> {
        let old_size = self.inner().strong.fetch_add(1, Relaxed);
        if old_size > MAX_REFCOUNT {
            abort();
        }
        Arc { ptr: self.ptr }
    }
}

impl<T> Drop for Arc<T> {
    fn drop(&mut self) {
        if self.inner().strong.fetch_sub(1, Release) == 1 {
            fence(Acquire);
            // 释放内存
        }
    }
}
```

∎

---

## 5. `Cell<T>` 与 `RefCell<T>`

### 5.1 内部可变性

### 定义 5.1 (Cell)

```rust
pub struct Cell<T: ?Sized> {
    value: UnsafeCell<T>,
}
```

### 定理 5.1 (Cell内部可变性)

> `Cell<T>` 允许通过不可变引用修改值。

**实现**:

```rust
impl<T: Copy> Cell<T> {
    pub fn get(&self) -> T {
        unsafe { *self.value.get() }
    }

    pub fn set(&self, val: T) {
        unsafe { *self.value.get() = val; }
    }
}
```

**限制**:

- T必须实现Copy
- 不支持内部借用

∎

### 5.2 运行时借用检查

### 定义 5.2 (RefCell)

```rust
pub struct RefCell<T: ?Sized> {
    borrow: Cell<BorrowFlag>,
    value: UnsafeCell<T>,
}
```

### 定理 5.2 (RefCell运行时检查)

> RefCell在运行时强制执行借用规则。

**实现**:

```rust
impl<T: ?Sized> RefCell<T> {
    pub fn borrow(&self) -> Ref<T> {
        match self.try_borrow() {
            Ok(ret) => ret,
            Err(_) => panic!("already mutably borrowed"),
        }
    }

    pub fn borrow_mut(&self) -> RefMut<T> {
        match self.try_borrow_mut() {
            Ok(ret) => ret,
            Err(_) => panic!("already borrowed"),
        }
    }
}
```

**规则**:

- 多个不可变借用，或
- 一个可变借用
- 违反则panic

∎

---

## 6. 智能指针对比

| 智能指针 | 所有权 | 线程安全 | Copy | 适用场景 |
|----------|--------|----------|------|----------|
| `Box<T>` | 唯一 | Send | No | 堆分配、递归类型 |
| `Rc<T>` | 共享 | !Send/!Sync | No | 单线程共享 |
| `Arc<T>` | 共享 | Send+Sync | No | 多线程共享 |
| `Cell<T>` | 唯一 | !Sync | No | 内部可变性(Copy类型) |
| `RefCell<T>` | 唯一 | !Sync | No | 内部可变性(运行时检查) |

---

## 7. 内存布局分析

### `Box<T>`

```text
Stack          Heap
┌─────┐        ┌───────┐
│ ptr │───────►│   T   │
└─────┘        └───────┘
```

### `Rc<T>/Arc<T>`

```text
Stack          Heap
┌─────┐        ┌─────────────┐
│ ptr │───────►│ strong      │
└─────┘        │ weak        │
               │ T           │
               └─────────────┘
```

---

## 8. 反例与陷阱

### 反例 8.1 (Rc多线程)

```rust
let rc = Rc::new(42);
thread::spawn(move || {
    println!("{}", *rc);  // 编译错误! Rc不是Send
});

// 正确做法
let arc = Arc::new(42);
thread::spawn(move || {
    println!("{}", *arc);  // OK
});
```

### 反例 8.2 (RefCell panic)

```rust
let cell = RefCell::new(42);
let r1 = cell.borrow();
let r2 = cell.borrow_mut();  // panic! 已有不可变借用
```

### 反例 8.3 (Box泄漏)

```rust
let b = Box::new(42);
let ptr = Box::into_raw(b);  // 手动管理
// 忘记释放导致泄漏

// 正确做法
let b = unsafe { Box::from_raw(ptr) };
drop(b);
```

---

## 参考文献

1. **Rust Standard Library.** (2024). `std::boxed::Box`, `std::rc::Rc`, `std::sync::Arc`. <https://doc.rust-lang.org/std/>

2. **Klabnik, S., & Nichols, C.** (2018). *The Rust Programming Language*. No Starch Press.
   - 关键章节: 第15章(智能指针)
   - 关联: 全文

---

*文档版本: 1.0.0*
*形式化深度: 高*
*定理数量: 10个*
*最后更新: 2026-03-04*
