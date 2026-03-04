# CXX 安全FFI形式化分析

> **主题**: C++与Rust安全互操作
>
> **形式化框架**: 边界类型系统 + 所有权桥接
>
> **参考**: CXX Documentation

---

## 目录

- [CXX 安全FFI形式化分析](#cxx-安全ffi形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 桥接模块](#2-桥接模块)
    - [定理 2.1 (桥接声明)](#定理-21-桥接声明)
  - [3. 类型映射](#3-类型映射)
    - [定理 3.1 (共享类型)](#定理-31-共享类型)
  - [4. 所有权语义](#4-所有权语义)
    - [定理 4.1 (UniquePtr)](#定理-41-uniqueptr)
    - [定理 4.2 (SharedPtr)](#定理-42-sharedptr)
  - [5. 异常安全](#5-异常安全)
    - [定理 5.1 (异常转换)](#定理-51-异常转换)
  - [6. 反例](#6-反例)
    - [反例 6.1 (原始指针逃逸)](#反例-61-原始指针逃逸)
    - [反例 6.2 (异常跨越)](#反例-62-异常跨越)

---

## 1. 引言

CXX提供:

- 安全的C++/Rust绑定
- 自动生成粘合代码
- 零开销抽象
- 编译时类型检查

---

## 2. 桥接模块

### 定理 2.1 (桥接声明)

> #[cxx::bridge]定义共享接口。

```rust
#[cxx::bridge]
mod ffi {
    unsafe extern "C++" {
        type MyCppClass;

        fn create() -> UniquePtr<MyCppClass>;
        fn method(self: &MyCppClass, arg: i32) -> i32;
    }
}
```

∎

---

## 3. 类型映射

### 定理 3.1 (共享类型)

| Rust | C++ |
|------|-----|
| String | std::string |
| Vec<T> | rust::Vec<T> |
| &str | rust::Str |
| UniquePtr<T> | std::unique_ptr<T> |
| SharedPtr<T> | std::shared_ptr<T> |

∎

---

## 4. 所有权语义

### 定理 4.1 (UniquePtr)

> 单向所有权转移。

```rust
// Rust -> C++
let obj = ffi::create();  // UniquePtr<MyCppClass>
// 自动delete当离开作用域
```

∎

### 定理 4.2 (SharedPtr)

> 共享所有权，引用计数。

```rust
let shared1 = ffi::create_shared();
let shared2 = shared1.clone();  // 引用计数+1
```

∎

---

## 5. 异常安全

### 定理 5.1 (异常转换)

> C++异常转换为Rust panic。

```rust
// C++抛出 -> Rust panic (需catch_unwind)
let result = catch_unwind(|| {
    ffi::may_throw();
});
```

∎

---

## 6. 反例

### 反例 6.1 (原始指针逃逸)

```rust
// 危险: 获取原始指针
let ptr = obj.get();  // *const T
// obj销毁后ptr悬垂

// CXX避免此问题，返回引用绑定生命周期
```

### 反例 6.2 (异常跨越)

```rust
// C++析构函数不能panic
// 否则terminate
```

---

*文档版本: 1.0.0*
*定理数量: 6个*
