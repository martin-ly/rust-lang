# 17 - Unsafe Rust

> **Rust 版本**: 1.94.0
> **难度**: 🔴 高级
> **前置知识**: 所有权、生命周期、原始指针基础

---

## 目录结构

```text
17-unsafe-rust/
├── README.md                    # 本文件 - 导航
├── 01-intro.md                  # Unsafe Rust 概述
├── 02-raw-pointers.md           # 原始指针深度解析
├── 03-unsafe-functions.md       # Unsafe 函数与 trait
├── 04-extern-ffi.md             # FFI 与外部代码
├── 05-uninitialized-memory.md   # 未初始化内存处理
├── 06-maybe-uninit.md           # MaybeUninit 详解
├── 07-drop-flags.md             # Drop 检查与析构
├── 08-aliasing.md               # 别名规则与优化
├── 09-atomics.md                # 原子操作与内存序
├── 10-inline-asm.md             # 内联汇编
├── 11-impl-vec.md               # 实现 Vec (实战)
└── 12-safety-proof.md           # 安全性证明方法论
```

---

## 学习路径

### 路径 A: Unsafe 基础 (必读)

```
01-intro → 02-raw-pointers → 03-unsafe-functions → 05-uninitialized-memory
```

**时间**: 4-6 小时
**产出**: 能阅读和理解 unsafe 代码

### 路径 B: 系统编程 (进阶)

```
路径 A → 04-extern-ffi → 09-atomics → 10-inline-asm → 11-impl-vec
```

**时间**: 10-15 小时
**产出**: 能编写系统级 unsafe 代码

### 路径 C: 安全抽象 (专家)

```
路径 B → 07-drop-flags → 08-aliasing → 12-safety-proof
```

**时间**: 20+ 小时
**产出**: 能设计安全的 unsafe 抽象

---

## 核心概念速查

| 概念 | 说明 | 文档 |
|-----|------|------|
| `unsafe` 关键字 | 切换到 unsafe 上下文 | [01-intro.md](01-intro.md) |
| 原始指针 (`*const T`, `*mut T`) | 无约束指针 | [02-raw-pointers.md](02-raw-pointers.md) |
| `MaybeUninit<T>` | 安全处理未初始化内存 | [06-maybe-uninit.md](06-maybe-uninit.md) |
| FFI | 与其他语言交互 | [04-extern-ffi.md](04-extern-ffi.md) |
| 原子操作 | 无锁并发原语 | [09-atomics.md](09-atomics.md) |
| Drop 检查 | 确保析构安全 | [07-drop-flags.md](07-drop-flags.md) |

---

## Unsafe Rust 五大能力

```rust
// 1. 解引用原始指针
let x = 5;
let r = &x as *const i32;
unsafe { println!("{}", *r); }

// 2. 调用 unsafe 函数
unsafe { dangerous_operation(); }

// 3. 实现 unsafe trait
unsafe trait Send {}

// 4. 访问/修改可变静态变量
static mut COUNTER: i32 = 0;
unsafe { COUNTER += 1; }

// 5. 访问 union 的字段
union MyUnion { i: i32, f: f32 }
```

---

## 安全契约

```
┌─────────────────────────────────────────────────────────────────┐
│                     Unsafe Rust 安全契约                         │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  编译器保证:                                                    │
│  • 类型系统检查 (在 safe 边界)                                  │
│  • 生命周期检查 (在 safe 边界)                                  │
│  • 借用规则检查 (在 safe 边界)                                  │
│                                                                 │
│  程序员责任 (unsafe 块/函数内):                                 │
│  • 原始指针有效                                                 │
│  • 无数据竞争                                                  │
│  • 内存对齐正确                                                 │
│  • 无悬垂引用                                                  │
│  • 不破坏不变量                                                │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## 常见陷阱

| 陷阱 | 后果 | 避免方法 |
|-----|------|---------|
| 解引用空指针 | UB (未定义行为) | 始终检查 `!ptr.is_null()` |
| 数据竞争 | UB | 使用原子或互斥锁 |
| 悬垂指针 | 内存损坏 | 严格生命周期管理 |
| 类型双关 | UB | 使用 `std::mem::transmute` 谨慎 |
| 未初始化内存读取 | UB | 使用 `MaybeUninit` |

---

## 参考资源

### 官方文档

- [The Rustonomicon](https://doc.rust-lang.org/nomicon/) - Unsafe Rust 权威指南
- [The Rust Reference - Unsafety](https://doc.rust-lang.org/reference/unsafety.html)
- [std::ptr 文档](https://doc.rust-lang.org/std/ptr/)

### 学术论文

- [RustBelt (Jung et al., 2018)](https://plv.mpi-sws.org/rustbelt/) - Rust 安全性证明
- [Stacked Borrows (Jung et al., 2020)](https://plv.mpi-sws.org/rustbib/) - 别名模型

### 相关文档

- [01-core-concepts](../01-core-concepts/README.md) - 所有权基础
- [12-concurrency-patterns](../12-concurrency-patterns/README.md) - 并发模式

---

## 贡献与反馈

发现错误或有改进建议？请提交 Issue 或 PR。

---

**维护者**: Rust Unsafe SIG
**最后更新**: 2026-03-07
