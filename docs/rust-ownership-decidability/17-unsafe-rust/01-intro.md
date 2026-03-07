# Unsafe Rust 概述

> **权威来源**: The Rustonomicon, The Rust Reference Chapter 16
> **Rust 版本**: 1.94.0
> **难度**: 🔴 高级
> **前置知识**: 所有权、生命周期、借用规则

---

## 目录

- [Unsafe Rust 概述](#unsafe-rust-概述)
  - [目录](#目录)
  - [1. 什么是 Unsafe Rust](#1-什么是-unsafe-rust)
    - [1.1 核心概念](#11-核心概念)
    - [1.2 为什么需要 Unsafe](#12-为什么需要-unsafe)
    - [1.3 安全契约模型](#13-安全契约模型)
  - [2. Unsafe 的五种超能力](#2-unsafe-的五种超能力)
    - [2.1 解引用原始指针](#21-解引用原始指针)
    - [2.2 调用 Unsafe 函数或方法](#22-调用-unsafe-函数或方法)
    - [2.3 实现 Unsafe Trait](#23-实现-unsafe-trait)
    - [2.4 访问或修改可变静态变量](#24-访问或修改可变静态变量)
    - [2.5 访问 Union 的字段](#25-访问-union-的字段)
  - [3. Unsafe 的形式化定义](#3-unsafe-的形式化定义)
    - [3.1 操作语义](#31-操作语义)
    - [3.2 类型系统扩展](#32-类型系统扩展)
    - [3.3 安全性不变量](#33-安全性不变量)
  - [4. Unsafe 块与 Unsafe 函数](#4-unsafe-块与-unsafe-函数)
    - [4.1 Unsafe 块](#41-unsafe-块)
    - [4.2 Unsafe 函数](#42-unsafe-函数)
    - [4.3 Unsafe Trait](#43-unsafe-trait)
  - [5. 安全抽象的设计](#5-安全抽象的设计)
    - [5.1 核心原则](#51-核心原则)
    - [5.2 实战: 实现安全的原始指针包装](#52-实战-实现安全的原始指针包装)
    - [5.3 不变量的封装](#53-不变量的封装)
  - [6. 常见陷阱与 UB](#6-常见陷阱与-ub)
    - [6.1 未定义行为 (UB) 列表](#61-未定义行为-ub-列表)
    - [6.2 调试技巧](#62-调试技巧)
  - [7. 调试与验证](#7-调试与验证)
    - [7.1 Miri - Rust 的内存检查器](#71-miri---rust-的内存检查器)
    - [7.2 静态分析工具](#72-静态分析工具)
  - [8. 参考资源](#8-参考资源)
    - [官方文档](#官方文档)
    - [学术论文](#学术论文)
    - [相关文档](#相关文档)
  - [检查清单](#检查清单)

---

## 1. 什么是 Unsafe Rust

### 1.1 核心概念

Unsafe Rust 是 Rust 的一个**超集**，它允许程序员执行编译器无法验证安全的操作。
这并不意味着 Unsafe Rust 就是"危险的"，而是意味着**安全责任从编译器转移到了程序员**。

```rust
// Safe Rust - 编译器保证安全
let mut v = vec![1, 2, 3];
v.push(4); // 编译器检查所有权、生命周期

// Unsafe Rust - 程序员负责安全
let ptr = v.as_mut_ptr();
unsafe {
    *ptr.add(3) = 4; // 编译器信任程序员知道这是安全的
}
```

### 1.2 为什么需要 Unsafe

| 场景 | 为什么需要 Unsafe | 示例 |
|-----|------------------|------|
| **底层系统编程** | 直接操作内存 | 操作系统、嵌入式 |
| **性能优化** | 避免边界检查 | 高性能计算 |
| **FFI** | 与 C/C++ 交互 | 调用系统 API |
| **数据结构** | 实现底层容器 | Vec, HashMap |
| **并发原语** | 原子操作 | Mutex, Arc |

### 1.3 安全契约模型

```
┌─────────────────────────────────────────────────────────────────┐
│                      Safe ↔ Unsafe 边界                          │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│   Safe Rust                     Unsafe Rust                     │
│   ─────────                     ───────────                     │
│   • 编译器验证所有操作           • 程序员验证操作安全              │
│   • 运行时无 UB (保证)           • 可能导致 UB (风险)              │
│   • 零成本抽象                  • 可能不安全                     │
│                                                                 │
│   安全边界: unsafe 关键字标记的块或函数                           │
│   契约: Safe API 必须封装 Unsafe 实现，暴露安全接口               │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## 2. Unsafe 的五种超能力

Rust 的 `unsafe` 关键字提供了五种编译器无法验证安全的超能力：

### 2.1 解引用原始指针

```rust
let mut x = 5;
let r1 = &x as *const i32;  // *const T - 不可变原始指针
let r2 = &mut x as *mut i32; // *mut T - 可变原始指针

unsafe {
    println!("r1 is: {}", *r1); // 解引用原始指针
    *r2 = 10;                    // 通过可变指针修改
}
```

**与引用的区别**:

| 特性 | 引用 (`&T`, `&mut T`) | 原始指针 (`*const T`, `*mut T`) |
|-----|----------------------|--------------------------------|
| 生命周期 | 编译器检查 | 不检查 |
| 有效性 | 保证有效 | 可能空或悬垂 |
| 别名规则 | 严格 (XOR) | 无限制 |
| 解引用 | 安全 | 需要 `unsafe` |

### 2.2 调用 Unsafe 函数或方法

```rust
unsafe fn dangerous() {
    // 这个函数内部可能有不安全操作
}

fn main() {
    unsafe {
        dangerous(); // 调用 unsafe 函数
    }
}
```

### 2.3 实现 Unsafe Trait

```rust
unsafe trait Send {
    // Send 标记 trait，实现者保证可以安全跨线程传输
}

unsafe impl Send for MyType {}
```

### 2.4 访问或修改可变静态变量

```rust
static mut COUNTER: i32 = 0;

fn increment() {
    unsafe {
        COUNTER += 1; // 修改可变静态变量
    }
}
```

**警告**: 可变静态变量不是线程安全的！

### 2.5 访问 Union 的字段

```rust
union MyUnion {
    i: i32,
    f: f32,
}

fn main() {
    let u = MyUnion { i: 42 };
    unsafe {
        println!("{}", u.f); // 读取 union 的其他字段
    }
}
```

---

## 3. Unsafe 的形式化定义

### 3.1 操作语义

```
定义 3.1 (Unsafe 上下文)

Unsafe 上下文 U 是一个程序区域，其中以下操作被允许:
1. 解引用原始指针: *p
2. 调用 unsafe 函数: f_unsafe()
3. 实现 unsafe trait: impl unsafe Trait
4. 访问 static mut: STATIC_MUT
5. 访问 union 字段: union.field

安全契约:
∀ op ∈ U: programmer_verifies(op) ⟹ safe_execution(op)
```

### 3.2 类型系统扩展

```rust
// 在类型系统中，unsafe 函数有不同类型
fn safe_fn(x: i32) -> i32 { x }           // type: fn(i32) -> i32
unsafe fn unsafe_fn(x: i32) -> i32 { x }  // type: unsafe fn(i32) -> i32

// 调用 unsafe 函数需要 unsafe 块
// safe_fn(5);        // OK
// unsafe_fn(5);     // Error!
unsafe { unsafe_fn(5) }; // OK
```

### 3.3 安全性不变量

```
定理 3.1 (Safe 封装安全性)

如果一个库的公开 API 都是 safe 的，且实现满足以下条件:
1. 所有 unsafe 操作都封装在 unsafe 块内
2. 所有 unsafe 函数都标记为 unsafe
3. 不破坏 Rust 的安全不变量

则该库是内存安全的。

证明概要:
- Safe API 保证输入满足前置条件
- Unsafe 实现假设输入有效
- 封装确保无效输入无法到达 unsafe 代码
- 因此 unsafe 代码的操作是安全的
```

---

## 4. Unsafe 块与 Unsafe 函数

### 4.1 Unsafe 块

```rust
// unsafe 块: 一小段需要 unsafe 能力的代码
let mut num = 5;
let r1 = &num as *const i32;
let r2 = &mut num as *mut i32;

unsafe {
    println!("r1 is: {}", *r1);
    println!("r2 is: {}", *r2);
}
```

**最佳实践**: 保持 unsafe 块尽可能小。

```rust
// 不好的做法 - 整个函数都是 unsafe
unsafe fn bad_split_at_mut(slice: &mut [i32], mid: usize) -> (&mut [i32], &mut [i32]) {
    // ... 很多代码
}

// 好的做法 - 只包装必要的部分
fn good_split_at_mut(slice: &mut [i32], mid: usize) -> (&mut [i32], &mut [i32]) {
    assert!(mid <= slice.len());
    let ptr = slice.as_mut_ptr();
    let len = slice.len();

    unsafe {
        (
            std::slice::from_raw_parts_mut(ptr, mid),
            std::slice::from_raw_parts_mut(ptr.add(mid), len - mid),
        )
    }
}
```

### 4.2 Unsafe 函数

```rust
// unsafe 函数: 调用者必须验证安全条件
/// # Safety
/// `ptr` 必须是非空且对齐的，且指向有效的 `i32`
unsafe fn read_i32(ptr: *const i32) -> i32 {
    *ptr
}

// 使用
let x = 42;
let ptr = &x;
unsafe {
    println!("{}", read_i32(ptr)); // 调用者负责验证安全
}
```

**文档要求**: Unsafe 函数必须有 `# Safety` 文档节。

### 4.3 Unsafe Trait

```rust
// unsafe trait: 实现者必须保证不变量
/// # Safety
/// 实现者必须保证类型可以安全地跨线程发送 (无数据竞争)
unsafe trait Send {}

unsafe impl Send for MyType {
    // 实现者保证 MyType 满足 Send 的条件
}
```

---

## 5. 安全抽象的设计

### 5.1 核心原则

```
安全抽象原则:

1. 最小化 unsafe 代码
   - 将 unsafe 代码限制在最小必要范围

2. 验证前置条件
   - 在 safe API 层验证所有输入

3. 文档化不变量
   - 明确文档化安全条件和不变量

4. 封装实现细节
   - unsafe 实现不应泄漏到公共 API

5. 模块化安全证明
   - 每个 unsafe 块独立证明安全性
```

### 5.2 实战: 实现安全的原始指针包装

```rust
/// 安全的原始指针包装
///
/// 封装原始指针，提供安全的 API
pub struct SafePtr<T> {
    ptr: *mut T,
    len: usize,
}

impl<T> SafePtr<T> {
    /// 创建 SafePtr
    ///
    /// # Safety
    /// - `ptr` 必须指向至少 `len` 个有效 `T`
    /// - `ptr` 必须是对齐的
    pub unsafe fn new(ptr: *mut T, len: usize) -> Self {
        Self { ptr, len }
    }

    /// 安全地获取元素 (safe API)
    ///
    /// 前置条件检查确保 unsafe 操作安全
    pub fn get(&self, index: usize) -> Option<&T> {
        if index >= self.len {
            return None;
        }
        // 现在我们知道 index < len，解引用是安全的
        unsafe { Some(&*self.ptr.add(index)) }
    }

    /// 安全地修改元素
    pub fn set(&mut self, index: usize, value: T) -> Result<(), T> {
        if index >= self.len {
            return Err(value);
        }
        unsafe {
            *self.ptr.add(index) = value;
        }
        Ok(())
    }
}

// 使用示例 - 完全安全
fn main() {
    let mut data = vec![1, 2, 3, 4, 5];
    let ptr = data.as_mut_ptr();
    let len = data.len();

    let safe_ptr = unsafe { SafePtr::new(ptr, len) };

    // 以下都是安全操作
    println!("{:?}", safe_ptr.get(2));     // Some(3)
    println!("{:?}", safe_ptr.get(10));    // None (安全地处理越界)
}
```

### 5.3 不变量的封装

```rust
/// 一个不变的 SafeString，一旦创建就不能修改
pub struct ImmutableString {
    // 私有字段，外部无法直接修改
    data: *const u8,
    len: usize,
}

impl ImmutableString {
    /// 从 &str 创建
    pub fn new(s: &str) -> Self {
        Self {
            data: s.as_ptr(),
            len: s.len(),
        }
    }

    /// 获取字符串内容 - 安全因为数据不会改变
    pub fn as_str(&self) -> &str {
        unsafe {
            // SAFETY:
            // 1. data 指向有效的 UTF-8 (由构造函数保证)
            // 2. len 是正确的 (由构造函数保证)
            // 3. 数据不会改变 (类型不变量)
            std::str::from_utf8_unchecked(
                std::slice::from_raw_parts(self.data, self.len)
            )
        }
    }
}

// 注意: 没有提供 &mut self 的方法，确保不可变性
```

---

## 6. 常见陷阱与 UB

### 6.1 未定义行为 (UB) 列表

```rust
// ❌ UB 1: 解引用空指针
let ptr: *const i32 = std::ptr::null();
unsafe { *ptr; } // UB!

// ❌ UB 2: 解引用悬垂指针
let ptr: *const i32 = {
    let x = 5;
    &x
}; // x 在这里被释放
unsafe { *ptr; } // UB!

// ❌ UB 3: 数据竞争
static mut COUNTER: i32 = 0;
// 线程 A
unsafe { COUNTER += 1; }
// 线程 B (同时)
unsafe { COUNTER += 1; } // 数据竞争 - UB!

// ❌ UB 4: 读取未初始化内存
let x: i32 = unsafe { std::mem::uninitialized() }; // UB!

// ❌ UB 5: 类型双关导致无效值
let x: bool = unsafe { std::mem::transmute(2u8) }; // UB! bool 只能是 0 或 1

// ❌ UB 6: 违反借用规则 (即使通过原始指针)
let mut x = 5;
let r1 = &mut x as *mut i32;
let r2 = &mut x as *mut i32; // 创建两个可变指针是允许的...
unsafe {
    *r1 = 10;
    *r2 = 20; // ...但同时使用它们导致 UB!
}
```

### 6.2 调试技巧

```rust
// 使用 debug_assert! 验证条件
debug_assert!(!ptr.is_null(), "指针不应为空");
debug_assert!(ptr.is_aligned(), "指针应对齐");

// 使用 Miri 检测 UB
// $ cargo miri run

// 使用 AddressSanitizer
// $ RUSTFLAGS="-Z sanitizer=address" cargo run
```

---

## 7. 调试与验证

### 7.1 Miri - Rust 的内存检查器

```bash
# 安装 Miri
rustup component add miri

# 运行测试
cargo miri test

# 运行程序
cargo miri run
```

Miri 可以检测:

- 使用未初始化内存
- 解引用悬垂指针
- 数据竞争
- 内存泄漏
- 类型双关错误

### 7.2 静态分析工具

| 工具 | 用途 | 命令 |
|-----|------|------|
| Clippy | 静态分析 | `cargo clippy` |
| Miri | 运行时检查 | `cargo miri test` |
| Sanitizers | 内存/线程检查 | `RUSTFLAGS="-Z sanitizer=address"` |

---

## 8. 参考资源

### 官方文档

- [The Rustonomicon](https://doc.rust-lang.org/nomicon/) - Unsafe Rust 权威指南
- [The Rust Reference - Unsafety](https://doc.rust-lang.org/reference/unsafety.html)
- [std::ptr](https://doc.rust-lang.org/std/ptr/)
- [std::mem](https://doc.rust-lang.org/std/mem/)

### 学术论文

1. Jung et al. (2018). RustBelt: Securing the Foundations of Rust. *POPL*.
2. Jung et al. (2020). Stacked Borrows: An Aliasing Model for Rust. *POPL*.
3. Vytiniotis et al. (2011). Modular Type Inference with Local Assumptions. *JFP*.

### 相关文档

- [02-raw-pointers.md](02-raw-pointers.md) - 原始指针深度解析
- [05-uninitialized-memory.md](05-uninitialized-memory.md) - 未初始化内存
- [06-maybe-uninit.md](06-maybe-uninit.md) - MaybeUninit 详解

---

## 检查清单

- [ ] 理解 Unsafe Rust 的核心概念
- [ ] 掌握五种 unsafe 超能力
- [ ] 理解安全抽象的设计原则
- [ ] 知道常见的 UB 陷阱
- [ ] 了解调试工具 (Miri)

---

*文档版本: 1.0.0*
*形式化深度: L2*
*最后更新: 2026-03-07*
