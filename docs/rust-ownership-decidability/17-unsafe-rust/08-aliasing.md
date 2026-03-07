# 别名规则与优化

> **Rust 版本**: 1.94.0
> **难度**: 🔴 高级
> **前置知识**: 借用检查器、Unsafe Rust

---

## 目录

- [别名规则与优化](#别名规则与优化)
  - [目录](#目录)
  - [1. 什么是别名](#1-什么是别名)
    - [1.1 定义](#11-定义)
    - [1.2 Unsafe 中的别名](#12-unsafe-中的别名)
  - [2. Stacked Borrows](#2-stacked-borrows)
    - [2.1 基本模型](#21-基本模型)
    - [2.2 示例](#22-示例)
    - [2.3 与原始指针的交互](#23-与原始指针的交互)
  - [3. Tree Borrows](#3-tree-borrows)
    - [3.1 改进的模型](#31-改进的模型)
    - [3.2 启用 Tree Borrows](#32-启用-tree-borrows)
    - [3.3 允许的别名模式](#33-允许的别名模式)
  - [4. 别名规则](#4-别名规则)
    - [4.1 核心规则](#41-核心规则)
    - [4.2 Unsafe 中的责任](#42-unsafe-中的责任)
    - [4.3 LLVM noalias](#43-llvm-noalias)
  - [5. 实战建议](#5-实战建议)
    - [5.1 避免别名冲突](#51-避免别名冲突)
    - [5.2 使用 NonNull](#52-使用-nonnull)
    - [5.3 Miri 检测](#53-miri-检测)
  - [参考](#参考)

---

## 1. 什么是别名

### 1.1 定义

别名是指**多个指针/引用指向同一内存位置**。

```rust
let mut x = 5;
let r1 = &mut x;
let r2 = &mut x;  // 两个可变引用指向同一位置
```

在 Safe Rust 中，编译器阻止同时存在两个可变引用。

### 1.2 Unsafe 中的别名

```rust
let mut x = 5;
let r1 = &mut x as *mut i32;
let r2 = &mut x as *mut i32;  // 允许！

unsafe {
    *r1 = 10;
    *r2 = 20;  // 危险！
}
```

---

## 2. Stacked Borrows

### 2.1 基本模型

Stacked Borrows 是 Rust 的内存模型，定义了引用如何交互。

```
内存访问规则：
- 每个内存位置有一个 "借用栈"
- 读操作可以使用栈中任何引用
- 写操作只能使用栈顶的引用
- 新引用入栈，旧引用失效
```

### 2.2 示例

```rust
fn main() {
    let mut x = 0;
    let r1 = &mut x;      // 栈: [&mut x]
    let r2 = &mut *r1;    // 栈: [&mut x, r2]
    *r2 = 1;              // OK, r2 在栈顶
    *r1 = 2;              // 错误！r1 已被 r2 "冻结"
}
```

### 2.3 与原始指针的交互

```rust
let mut x = 0;
let r = &mut x;
let ptr = r as *mut i32;

unsafe {
    *ptr = 1;  // 使用原始指针
}
*r = 2;        // 仍然有效
```

**规则**: 从引用派生的原始指针使用不会使引用失效。

---

## 3. Tree Borrows

### 3.1 改进的模型

Tree Borrows 是 Stacked Borrows 的替代模型，更宽松。

```
主要区别：
- 允许更多的别名模式
- 更精确地追踪借用关系
- 与 C 代码更兼容
```

### 3.2 启用 Tree Borrows

```bash
MIRI_TREE_BORROWS=1 cargo miri test
```

### 3.3 允许的别名模式

```rust
// Tree Borrows 允许的模式
fn tree_borrows_example() {
    let mut x = 0;
    let r1 = &mut x as *mut i32;
    let r2 = &mut x as *mut i32;

    unsafe {
        *r1 = 1;  // OK in Tree Borrows
        *r2 = 2;  // OK in Tree Borrows
    }
}
```

---

## 4. 别名规则

### 4.1 核心规则

```
1. 读-读共享: 多个只读引用可以共存
2. 读-写互斥: 读写不能同时存在
3. 写-写互斥: 两个写不能同时存在
```

### 4.2 Unsafe 中的责任

```rust
// 程序员必须自己保证：
unsafe {
    // 1. 没有活动可变引用时，才使用原始指针写入
    // 2. 没有活动时，才创建新的可变引用
    // 3. 不违反 LLVM 的 noalias 假设
}
```

### 4.3 LLVM noalias

Rust 的 `&mut T` 和 `&T` 会生成 LLVM 的 `noalias` 属性：

```llvm
; &mut i32 -> noalias
; &i32 -> noalias readonly
```

这允许 LLVM 进行激进的优化，但也意味着违反别名规则是 UB。

---

## 5. 实战建议

### 5.1 避免别名冲突

```rust
// ✅ 好的做法：明确所有权转移
fn process(data: &mut [u8]) {
    let ptr = data.as_mut_ptr();
    let len = data.len();

    // 不再使用 data，只使用 ptr
    unsafe {
        process_raw(ptr, len);
    }
}
```

### 5.2 使用 NonNull

```rust
use std::ptr::NonNull;

struct Buffer<T> {
    ptr: NonNull<T>,  // 保证非空
    len: usize,
}

impl<T> Buffer<T> {
    fn get(&self, idx: usize) -> Option<&T> {
        if idx < self.len {
            unsafe { Some(&*self.ptr.as_ptr().add(idx)) }
        } else {
            None
        }
    }
}
```

### 5.3 Miri 检测

```bash
# 使用 Stacked Borrows (默认)
cargo miri test

# 使用 Tree Borrows
MIRI_TREE_BORROWS=1 cargo miri test

# 检测别名违规
MIRI_CHECK_NUMBER_VALIDITY=1 cargo miri test
```

---

## 参考

- [Stacked Borrows Paper](https://plv.mpi-sws.org/rustbib/)
- [Tree Borrows](https://github.com/Vanille-N/tree-borrows)

---

*文档版本: 1.0.0*
