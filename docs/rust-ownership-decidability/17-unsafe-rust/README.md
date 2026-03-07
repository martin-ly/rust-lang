# 17. Unsafe Rust

本目录包含关于 Unsafe Rust 的深入文档，涵盖从基础概念到高级应用的所有方面。

---

## 文档列表

### 基础概念

| 文件 | 主题 | 难度 |
|------|------|------|
| [`01-intro.md`](./01-intro.md) | Unsafe Rust 入门 | 🟢 初级 |
| [`02-raw-pointers.md`](./02-raw-pointers.md) | 原始指针详解 | 🟡 中级 |
| [`03-unsafe-functions.md`](./03-unsafe-functions.md) | Unsafe 函数与 FFI | 🟡 中级 |

### 核心机制

| 文件 | 主题 | 难度 |
|------|------|------|
| [`04-uninitialized-memory.md`](./04-uninitialized-memory.md) | 未初始化内存处理 | 🟡 中级 |
| [`05-maybeuninit.md`](./05-maybeuninit.md) | MaybeUninit 类型 | 🟡 中级 |
| [`06-atomics.md`](./06-atomics.md) | 原子操作与内存序 | 🔴 高级 |
| [`07-drop-flags.md`](./07-drop-flags.md) | Drop 检查与析构安全 | 🔴 高级 |
| [`08-aliasing.md`](./08-aliasing.md) | 别名规则与优化 | 🔴 高级 |

### 高级应用

| 文件 | 主题 | 难度 |
|------|------|------|
| [`09-inline-asm.md`](./09-inline-asm.md) | 内联汇编 | 🔴 高级 |
| [`10-ffi-boundaries.md`](./10-ffi-boundaries.md) | FFI 边界安全 | 🔴 高级 |
| [`11-impl-vec.md`](./11-impl-vec.md) | 实现 Vec<T> | 🔴 高级 |

---

## 学习路径

### 路径 1：快速入门

```
01-intro → 02-raw-pointers → 03-unsafe-functions
```

### 路径 2：系统学习

```
01-intro → 02-raw-pointers → 03-unsafe-functions → 04-uninitialized-memory
→ 05-maybeuninit → 06-atomics → 07-drop-flags → 08-aliasing
```

### 路径 3：实战导向

```
01-intro → 02-raw-pointers → 05-maybeuninit → 10-ffi-boundaries → 11-impl-vec
```

---

## 目录

- [1. Unsafe Rust 入门](01-intro.md)
- [2. 原始指针](02-raw-pointers.md)
- [3. Unsafe 函数与 FFI](03-unsafe-functions.md)
- [4. 未初始化内存](04-uninitialized-memory.md)
- [5. MaybeUninit 类型](05-maybeuninit.md)
- [6. 原子操作](06-atomics.md)
- [7. Drop 检查](07-drop-flags.md)
- [8. 别名规则](08-aliasing.md)
- [9. 内联汇编](09-inline-asm.md)
- [10. FFI 边界](10-ffi-boundaries.md)
- [11. 实现 Vec<T>](11-impl-vec.md)

---

## 状态

**完成度**: ✅ 100% (11/11 文档)

---

*最后更新: 2026-03-07*
