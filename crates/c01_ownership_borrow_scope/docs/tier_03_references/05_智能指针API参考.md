# Tier 3: 智能指针 API 完整参考

> **文档类型**: API参考
> **适用版本**: Rust 1.90+

---

## 📊 目录

- [Tier 3: 智能指针 API 完整参考](#tier-3-智能指针-api-完整参考)
  - [📊 目录](#-目录)
  - [`Box<T>` API](#boxt-api)
  - [`Rc<T>` API](#rct-api)
  - [`Arc<T>` API](#arct-api)
  - [`RefCell<T>` API](#refcellt-api)
  - [`Weak<T>` API](#weakt-api)

## `Box<T>` API

```rust
// 创建
let b = Box::new(5);

// 解引用
let value = *b;

// From trait
let b: Box<i32> = Box::from(5);

// 内存布局
// Box::new(x) 在堆上分配 x，栈上存储指针
```

---

## `Rc<T>` API

```rust
use std::rc::Rc;

// 创建
let a = Rc::new(5);

// 克隆（增加引用计数）
let b = Rc::clone(&a);
let c = a.clone(); // 也可以

// 引用计数
let count = Rc::strong_count(&a);
let weak_count = Rc::weak_count(&a);

// 尝试获取可变引用
if let Some(data) = Rc::get_mut(&mut a) {
    *data += 1;
}
```

---

## `Arc<T>` API

```rust
use std::sync::Arc;

// API 与 Rc 相同，但线程安全
let a = Arc::new(5);
let b = Arc::clone(&a);
```

---

## `RefCell<T>` API

```rust
use std::cell::RefCell;

let data = RefCell::new(5);

// 借用
let r = data.borrow(); // Ref<i32>
let value = *r;

// 可变借用
let mut r = data.borrow_mut(); // RefMut<i32>
*r += 1;

// try 版本
let r = data.try_borrow(); // Result<Ref<i32>, BorrowError>
let r = data.try_borrow_mut(); // Result<RefMut<i32>, BorrowMutError>
```

---

## `Weak<T>` API

```rust
use std::rc::{Rc, Weak};

let strong = Rc::new(5);

// 创建弱引用
let weak: Weak<i32> = Rc::downgrade(&strong);

// 升级为强引用
if let Some(strong) = weak.upgrade() {
    println!("Value: {}", strong);
}

// 引用计数
let strong_count = weak.strong_count();
let weak_count = weak.weak_count();
```

---

**相关文档**:

- [Tier 2: 05_智能指针实践](../tier_02_guides/05_智能指针实践.md)

---

**文档维护**: Documentation Team
**创建日期**: 2025-10-22
