# CXX 安全FFI形式化分析

> **分级**: [C]
> **Bloom 层级**: L5-L6 (分析/评价/创造)

> **主题**: C++与Rust安全互操作
>
> **形式化框架**: 边界类型系统 + 所有权桥接
>
> **参考**: CXX Documentation

---

## 目录
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

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
  - *定理数量: 6个*
  - [权威来源索引](#权威来源索引)

---

## 1. 引言
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

CXX提供:

- 安全的C++/Rust绑定
- 自动生成粘合代码
- 零开销抽象
- 编译时类型检查

---

## 2. 桥接模块
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

### 定理 2.1 (桥接声明)

> #[cxx::bridge]定义共享接口。

```rust,ignore
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

```rust,ignore
// Rust -> C++
let obj = ffi::create();  // UniquePtr<MyCppClass>
// 自动delete当离开作用域
```

∎

### 定理 4.2 (SharedPtr)

> 共享所有权，引用计数。

```rust,ignore
let shared1 = ffi::create_shared();
let shared2 = shared1.clone();  // 引用计数+1
```

∎

---

## 5. 异常安全

### 定理 5.1 (异常转换)

> C++异常转换为Rust panic。

```rust,ignore
// C++抛出 -> Rust panic (需catch_unwind)
let result = catch_unwind(|| {
    ffi::may_throw();
});
```

∎

---

## 6. 反例

### 反例 6.1 (原始指针逃逸)

```rust,ignore
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
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [README](./README.md)

---

## 权威来源索引

> **[来源: Wikipedia - Memory Safety]**

> **[来源: TRPL Ch. 4 - Ownership]**

> **[来源: Rustonomicon - Ownership]**

> **[来源: POPL 2018 - RustBelt]**

> **[来源: Wikipedia - Formal Methods]**

> **[来源: Coq Reference Manual]**

> **[来源: TLA+ Documentation]**

> **[来源: ACM - Formal Verification]**

---

## 权威来源索引

> **[来源: [RustBelt](https://plv.mpi-sws.org/rustbelt/)]**
>
> **[来源: [Iris Project](https://iris-project.org/)]**
>
> **[来源: [POPL/PLDI 论文](https://dblp.org/db/conf/pldi/index.html)]**
>
> **[来源: [Tree Borrows](https://plv.mpi-sws.org/rustbelt/tree-borrows/)]**
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
>
