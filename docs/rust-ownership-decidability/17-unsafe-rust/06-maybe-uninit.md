# MaybeUninit 完全指南

> **Rust 版本**: 1.94.0
> **难度**: 🔴 高级
> **前置知识**: 未初始化内存

---

## 目录

- [MaybeUninit 完全指南](#maybeuninit-完全指南)
  - [目录](#目录)
  - [1. MaybeUninit 是什么](#1-maybeuninit-是什么)
    - [1.1 核心特性](#11-核心特性)
  - [2. 基本用法](#2-基本用法)
    - [2.1 创建与初始化](#21-创建与初始化)
    - [2.2 读取值](#22-读取值)
    - [2.3 部分初始化数组](#23-部分初始化数组)
  - [3. 高级模式](#3-高级模式)
    - [3.1 类型级未初始化](#31-类型级未初始化)
    - [3.2 延迟初始化](#32-延迟初始化)
  - [4. 实现原理](#4-实现原理)
    - [4.1 Union 实现](#41-union-实现)
    - [4.2 repr(transparent)](#42-reprtransparent)
  - [5. 性能考量](#5-性能考量)
    - [5.1 零成本抽象](#51-零成本抽象)
    - [5.2 避免不必要的初始化](#52-避免不必要的初始化)
  - [参考](#参考)

---

## 1. MaybeUninit 是什么

`MaybeUninit<T>` 是一个**可能已初始化也可能未初始化**的类型。它是 Rust 中处理未初始化内存的唯一安全方式。

### 1.1 核心特性

```rust
use std::mem::MaybeUninit;

// 1. 可以创建未初始化
let uninit: MaybeUninit<i32> = MaybeUninit::uninit();

// 2. 与 T 有相同的内存布局
assert_eq!(std::mem::size_of::<MaybeUninit<i32>>(), 4);

// 3. 不自动调用 Drop
{
    let m: MaybeUninit<String> = MaybeUninit::new(String::from("hello"));
    // m 离开作用域时，String 不会被 drop！
}
```

---

## 2. 基本用法

### 2.1 创建与初始化

```rust
// 方式 1: 从未初始化开始
let mut slot = MaybeUninit::uninit();
unsafe {
    slot.as_mut_ptr().write(42);
}

// 方式 2: 直接创建已初始化
let slot = MaybeUninit::new(42);

// 方式 3: 从已有值转换
let x = String::from("hello");
let slot = MaybeUninit::new(x);  // x 被移动
```

### 2.2 读取值

```rust
let mut slot = MaybeUninit::new(String::from("hello"));

// 方式 1: 引用 (不移动)
let len = unsafe { slot.assume_init_ref().len() };

// 方式 2: 可变引用
unsafe {
    slot.assume_init_mut().push_str(" world");
}

// 方式 3: 取出值 (消耗 slot)
let s = unsafe { slot.assume_init() };
// 现在 slot 不可用，s 拥有值
```

### 2.3 部分初始化数组

```rust
fn partial_init_example() {
    let mut arr: [MaybeUninit<String>; 5] =
        unsafe { MaybeUninit::uninit().assume_init() };

    // 只初始化前 3 个
    for i in 0..3 {
        arr[i].write(format!("item {}", i));
    }

    // 使用前 3 个
    for i in 0..3 {
        let s = unsafe { arr[i].assume_init_ref() };
        println!("{}", s);
    }

    // 必须手动 drop 已初始化的
    for i in 0..3 {
        unsafe {
            arr[i].assume_init_drop();
        }
    }
}
```

---

## 3. 高级模式

### 3.1 类型级未初始化

```rust
use std::marker::PhantomData;

// 状态标记类型
struct Uninit;
struct Init;

struct SafeSlot<T, State> {
    data: MaybeUninit<T>,
    _state: PhantomData<State>,
}

impl<T> SafeSlot<T, Uninit> {
    fn new() -> Self {
        Self {
            data: MaybeUninit::uninit(),
            _state: PhantomData,
        }
    }

    fn init(self, value: T) -> SafeSlot<T, Init> {
        self.data.write(value);
        SafeSlot {
            data: self.data,
            _state: PhantomData,
        }
    }
}

impl<T> SafeSlot<T, Init> {
    fn get(&self) -> &T {
        unsafe { self.data.assume_init_ref() }
    }

    fn into_inner(self) -> T {
        unsafe { self.data.assume_init() }
    }
}

// 使用
let slot = SafeSlot::<i32, _>::new();
let slot = slot.init(42);  // 初始化
println!("{}", slot.get());  // 42
```

### 3.2 延迟初始化

```rust
use std::sync::Once;

struct Lazy<T> {
    data: MaybeUninit<T>,
    once: Once,
}

impl<T> Lazy<T> {
    const fn new() -> Self {
        Self {
            data: MaybeUninit::uninit(),
            once: Once::new(),
        }
    }

    fn get(&self, f: impl FnOnce() -> T) -> &T {
        self.once.call_once(|| {
            unsafe {
                (*(&self.data as *const _ as *mut _)).write(f());
            }
        });
        unsafe { self.data.assume_init_ref() }
    }
}
```

---

## 4. 实现原理

### 4.1 Union 实现

```rust
#[repr(transparent)]
pub union MaybeUninit<T> {
    uninit: (),
    value: ManuallyDrop<T>,
}
```

**为什么是 union?**

- Union 的所有 variant 共享同一内存
- 编译器不假设哪个 variant 是 active
- 允许未初始化状态

### 4.2 repr(transparent)

```rust
// MaybeUninit<T> 和 T 有完全相同的内存布局
assert_eq!(
    std::mem::size_of::<MaybeUninit<i64>>(),
    std::mem::size_of::<i64>()
);
```

这使得 FFI 和类型双关安全。

---

## 5. 性能考量

### 5.1 零成本抽象

```rust
// MaybeUninit 在运行时是零成本的
// 只是编译时的类型标记

let x = MaybeUninit::new(42);
let y = unsafe { x.assume_init() };
// 生成的代码与直接 let y = 42; 相同
```

### 5.2 避免不必要的初始化

```rust
// 慢：先零初始化，再写入实际数据
let mut vec = vec![0; 1000];  // 写 1000 个 0
read_data_into(&mut vec);      // 再写 1000 个实际值

// 快：分配未初始化内存，直接写入
let mut vec: Vec<MaybeUninit<u8>> = Vec::with_capacity(1000);
unsafe { vec.set_len(1000); }
read_data_into_uninit(&mut vec);
// 后续转换为 Vec<u8>
```

---

## 参考

- [std::mem::MaybeUninit](https://doc.rust-lang.org/std/mem/union.MaybeUninit.html)

---

*文档版本: 1.0.0*
