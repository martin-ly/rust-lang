# Rust 所有权系统 - 可视化思维指南

> **Bloom 层级**: L5-L6 (分析/评价/创造)

**目标**: 通过视觉化思维导图和图解，建立对 Rust 语义特性的直观理解

---

## 📑 目录
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [Rust 所有权系统 - 可视化思维指南](#rust-所有权系统---可视化思维指南)
  - [📑 目录](#-目录)
  - [1. 核心概念视觉化](#1-核心概念视觉化)
    - [1.1 所有权的视觉隐喻](#11-所有权的视觉隐喻)
    - [1.2 生命周期的时间线视图](#12-生命周期的时间线视图)
    - [1.3 借用规则的 Venn 图](#13-借用规则的-venn-图)
  - [2. 决策流程图](#2-决策流程图)
    - [2.1 是否需要所有权转移？](#21-是否需要所有权转移)
    - [2.2 选择引用类型](#22-选择引用类型)
    - [2.3 生命周期标注决策](#23-生命周期标注决策)
  - [3. 层次结构图](#3-层次结构图)
    - [3.1 Rust 抽象层次塔](#31-rust-抽象层次塔)
    - [3.2 类型系统层次](#32-类型系统层次)
  - [4. 状态转换图](#4-状态转换图)
    - [4.1 变量的生命周期状态](#41-变量的生命周期状态)
    - [4.2 引用的状态机](#42-引用的状态机)
  - [5. 对比矩阵](#5-对比矩阵)
    - [5.1 所有权 vs 借用 vs 引用](#51-所有权-vs-借用-vs-引用)
    - [5.2 Copy vs Clone vs Move](#52-copy-vs-clone-vs-move)
    - [5.3 生命周期标注场景](#53-生命周期标注场景)
  - [6. 实例图解](#6-实例图解)
    - [6.1 向量操作的内存布局](#61-向量操作的内存布局)
    - [6.2 借用检查器的工作原理](#62-借用检查器的工作原理)
  - [7. 学习路径图](#7-学习路径图)
    - [7.1 从初学者到专家的进阶](#71-从初学者到专家的进阶)
    - [7.2 常见错误的诊断流程](#72-常见错误的诊断流程)
  - [8. 快速参考卡](#8-快速参考卡)
    - [8.1 所有权规则速查](#81-所有权规则速查)
    - [8.2 类型选择决策卡](#82-类型选择决策卡)
  - [总结](#总结)
  - [**建议**: 将这些可视化与代码实践结合，加深理解](#建议-将这些可视化与代码实践结合加深理解)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)

## 1. 核心概念视觉化
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

### 1.1 所有权的视觉隐喻
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

```text
🏠 房子类比

所有权 (Ownership):
  ┌─────────────────────┐
  │     🏠 房子          │  ← String (拥有堆内存)
  │   你拥有地契         │
  │   可以装修、出售      │
  │   决定何时拆除        │
  └─────────────────────┘

借用 (Borrowing):
  ┌─────────────────────┐
  │  🔑 钥匙 (不可变借用) │
  │  ├─ 可以参观         │
  │  ├─ 不能装修         │
  │  └─ 可以复制多把      │
  └─────────────────────┘

  ┌─────────────────────┐
  │  🗝️ 主钥匙 (可变借用) │
  │  ├─ 可以居住         │
  │  ├─ 可以装修         │
  │  └─ 只有一把         │
  └─────────────────────┘

移动 (Move):
  地契转移给新主人
  原主人不再拥有
```

### 1.2 生命周期的时间线视图
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

```text
时间 →

变量 x (所有者):
───────────────────────────────────────
[ 出生           活跃            死亡 ]
  │                                │
  let x = 5;                      作用域结束

引用 &x:
───────────────────────────────────────
          [=======]
            │
         let r = &x;
         r 有效

无效引用:
───────────────────────────────────────
                     [=======]  ❌
                       │
                    x 已死亡
                    引用悬空！
```

### 1.3 借用规则的 Venn 图
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```text
数据访问方式:

┌─────────────────────────────────────┐
│           所有访问方式               │
│  ┌─────────┐    ┌─────────┐        │
│  │  读取   │    │  写入   │        │
│  │  (R)   │    │  (W)   │        │
│  └────┬────┘    └────┬────┘        │
│       │              │             │
│       └──────┬───────┘             │
│              │                      │
│         ┌────┴────┐                 │
│         │  R + W  │  ← 不允许同时！  │
│         └─────────┘                 │
└─────────────────────────────────────┘

Rust 允许的组合:
✅ 多个 R (多个不可变借用)
✅ 单个 W (单个可变借用)
❌ R + W (混合借用 - 禁止)
❌ 多个 W (多个可变借用 - 禁止)
```

---

## 2. 决策流程图
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

### 2.1 是否需要所有权转移？
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```text
                    需要传递值？
                        │
            ┌───────────┴───────────┐
            │                       │
          是                        否
            │                       │
    ┌───────┴───────┐               │
    │               │               │
实现 Copy？       不实现            │
    │               │               │
  ┌─┴─┐           ┌─┴─┐             │
  │   │           │   │             │
 是   否          │   │             │
  │    │           │   │             │
复制  移动      clone 借用          │
隐式  转移      显式   & 或 &mut    │
```

### 2.2 选择引用类型
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

```text
          需要访问数据？
                │
    ┌───────────┴───────────┐
    │                       │
  只读                     读写
    │                       │
    │              ┌────────┴────────┐
    │              │                 │
    │           独占访问           共享访问
    │              │                 │
    │              │                 │
    │            &mut T            内部可变性
    │            可变借用            Cell/RefCell
    │                              Mutex/RwLock
    │
  &T
  不可变借用
  (可以多个)
```

### 2.3 生命周期标注决策
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

```text
              函数返回引用？
                    │
        ┌───────────┴───────────┐
        │                       │
       否                       是
        │                       │
   不需要标注             ┌──────┴──────┐
                        │             │
                   单一输入引用    多个输入引用
                        │             │
                   自动推断            │
                   (规则1-3)       必须显式标注
```

---

## 3. 层次结构图
>
> **[来源: [crates.io](https://crates.io/)]**

### 3.1 Rust 抽象层次塔
>
> **[来源: [docs.rs](https://docs.rs/)]**

```text
        ┌─────────────────┐
        │   应用逻辑层     │  ← 业务代码、算法
        │  (你的代码)      │
        ├─────────────────┤
        │   标准库层       │  ← Vec, String, HashMap
        │  (std::*)       │
        ├─────────────────┤
        │   所有权层       │  ← Owner, Borrow, Lifetime
        │  (核心抽象)      │
        ├─────────────────┤
        │   类型系统层     │  ← Type, Trait, Generic
        │  (静态检查)      │
        ├─────────────────┤
        │   内存模型层     │  ← Stack, Heap, Pointer
        │  (运行时)        │
        ├─────────────────┤
        │   机器码层       │  ← x86/ARM, 寄存器
        │  (硬件)          │
        └─────────────────┘
```

### 3.2 类型系统层次
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

```text
类型分类:

                    类型
                     │
        ┌────────────┼────────────┐
        │            │            │
     标量类型     复合类型      抽象类型
        │            │            │
   ┌────┴────┐   ┌───┴───┐    ┌───┴───┐
   │         │   │       │    │       │
 整数      浮点  元组   结构体  Trait  泛型
 (i32)    (f64) (T,U)  struct  dyn    T
 布尔      字符  数组   枚举          impl
 (bool)   (char) [T;n] enum
```

---

## 4. 状态转换图
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 4.1 变量的生命周期状态
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```text
状态: Uninitialized → Initialized → Moved → Dropped

Uninitialized:
  let x: String;
  // x 未初始化，不能使用

    │ let x = String::from("hello");
    ▼
Initialized:
  // x 拥有字符串
  // 可以使用 x

    │ let y = x;  (Move)
    ▼
Moved:
  // x 不再有效
  // 不能使用 x
  // y 现在拥有字符串

    │ (作用域结束)
    ▼
Dropped:
  // y 调用 drop
  // 内存释放
```

### 4.2 引用的状态机
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```text
引用状态:

           ┌─────────────┐
           │   有效引用   │
           │  (可以使用)  │
           └──────┬──────┘
                  │
        ┌─────────┼─────────┐
        │         │         │
    解引用    重新赋值    作用域结束
        │         │         │
        ▼         ▼         ▼
   ┌─────────┐ ┌─────────┐ ┌─────────┐
   │  访问值  │ │ 新引用  │ │  失效   │
   │         │ │         │ │ (dangling│
   └─────────┘ └────┬────┘ │  risk)  │
                    │      └─────────┘
                    ▼
           ┌─────────────┐
           │   新引用     │
           └─────────────┘
```

---

## 5. 对比矩阵
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

### 5.1 所有权 vs 借用 vs 引用
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

| 特性 | 所有权 | 不可变借用 | 可变借用 |
|------|--------|-----------|---------|
| 符号 | `T` | `&T` | `&mut T` |
| 数量 | 1个所有者 | 多个 | 1个 |
| 读取 | ✅ | ✅ | ✅ |
| 写入 | ✅ | ❌ | ✅ |
| 释放 | ✅ (Drop) | ❌ | ❌ |
| 转移 | ✅ (Move) | ❌ | ❌ |

### 5.2 Copy vs Clone vs Move
>
> **[来源: [crates.io](https://crates.io/)]**

| 特性 | Copy | Clone | Move |
|------|------|-------|------|
| 隐式 | ✅ | ❌ | ✅ |
| 成本 | 低 (栈复制) | 高 (堆分配) | 低 (指针) |
| 原变量 | 仍可用 | 仍可用 | 失效 |
| 使用场景 | 基本类型 | 深拷贝需要 | 所有权转移 |
| Trait | `Copy` | `Clone` | 默认 |

### 5.3 生命周期标注场景
>
> **[来源: [docs.rs](https://docs.rs/)]**

| 场景 | 是否需要标注 | 示例 |
|------|-------------|------|
| 单一输入引用 | ❌ | `fn foo(x: &i32) -> &i32` |
| 多个输入引用 | ✅ | `fn longest<'a>(x: &'a str, y: &'a str)` |
| 返回内部引用 | ✅ | `impl<'a> Iterator<'a> for ...` |
| 结构体含引用 | ✅ | `struct Foo<'a> { x: &'a i32 }` |

---

## 6. 实例图解
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

### 6.1 向量操作的内存布局
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```text
代码: let mut v = vec![1, 2, 3];

栈上 (Stack):
┌─────────────────────────────┐
│ v (Vec<i32>)                │
│ ├─ ptr: *──┐                │
│ ├─ len: 3  │                │
│ └─ cap: 4  │                │
└────────────┼────────────────┘
             │
             ▼
堆上 (Heap):
┌─────────────────────────────┐
│ [1] [2] [3] [ ]             │
│  │   │   │                  │
│  └───┴───┘                  │
│   连续内存块                 │
└─────────────────────────────┘

操作: let r = &mut v[1];

引用 r:
┌─────────────────────────────┐
│ r: &mut i32                 │
│ 指向堆上第2个元素            │
│  (&v[1] = 2)                │
└─────────────────────────────┘
```

### 6.2 借用检查器的工作原理
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```text
代码分析:

1. let mut x = 5;
   ┌─────────┐
   │ x: i32  │  ← 所有者
   │ value: 5│
   └─────────┘

2. let y = &mut x;
   ┌─────────┐     ┌─────────────┐
   │ x: i32  │◄────┤ y: &mut i32 │  ← 可变借用
   │ value: 5│     │ (写入权限)  │
   └─────────┘     └─────────────┘

   借用记录: [mut x]

3. let z = &x;  ❌
   错误! 已有可变借用

   借用检查器:
   ┌──────────────────┐
   │ 检查: 是否已有    │
   │    冲突借用？     │
   │                  │
   │ 当前借用: [mut x]│
   │ 请求借用: [x]    │
   │                  │
   │ 冲突! ❌         │
   └──────────────────┘

4. *y = 10;
   ┌─────────┐     ┌─────────────┐
   │ x: i32  │◄────┤ y: &mut i32 │
   │ value:10│     │ (已使用)    │
   └─────────┘     └─────────────┘

5. // y 不再使用
   借用记录: []

6. let z = &x;  ✅
   ┌─────────┐     ┌───────────┐
   │ x: i32  │◄────┤ z: &i32   │  ← 现在可以
   │ value:10│     │ (读取权限)│
   └─────────┘     └───────────┘
```

---

## 7. 学习路径图
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

### 7.1 从初学者到专家的进阶
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

```text
阶段 1: 基础理解
├── 所有权概念
├── 移动语义
└── 基本借用

    ↓ 练习: 修复所有权错误

阶段 2: 生命周期
├── 生命周期标注
├── 省略规则
└── 结构体生命周期

    ↓ 练习: 设计带引用的结构体

阶段 3: 高级借用
├── 多重借用
├── Reborrow
└── 生命周期子类型

    ↓ 练习: 实现迭代器

阶段 4: 内部可变性
├── Cell/RefCell
├── Mutex/RwLock
└── 内部可变性模式

    ↓ 练习: 实现线程安全数据结构

阶段 5: 精通
├── 自引用结构体
├── Pin
├── 异步生命周期
└── unsafe 边界

    ↓ 练习: 实现异步运行时组件
```

### 7.2 常见错误的诊断流程
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

```text
遇到编译错误
     │
     ▼
错误是否关于所有权？
     │
   ┌─┴─┐
  是   否 → 其他错误
   │
   ▼
是否是 "use of moved value"？
   │
 ┌─┴─┐
是   否 → 检查借用规则
   │
   ▼
解决方案:
1. 使用 .clone()
2. 使用引用 (&)
3. 重新设计数据结构
```

---

## 8. 快速参考卡
>
> **[来源: [crates.io](https://crates.io/)]**

### 8.1 所有权规则速查
>
> **[来源: [docs.rs](https://docs.rs/)]**

```text
┌────────────────────────────────────┐
│         所有权三大规则              │
├────────────────────────────────────┤
│                                    │
│ 1. 每个值有且仅有一个所有者         │
│                                    │
│ 2. 当所有者离开作用域，值被释放     │
│                                    │
│ 3. 所有权可以转移 (Move)            │
│                                    │
└────────────────────────────────────┘

┌────────────────────────────────────┐
│         借用三大规则                │
├────────────────────────────────────┤
│                                    │
│ 1. 任意时刻：要么一个可变引用       │
│              要么任意多个不可变引用  │
│                                    │
│ 2. 引用必须始终有效                 │
│                                    │
│ 3. 引用不能超过被引用者的生命周期   │
│                                    │
└────────────────────────────────────┘
```

### 8.2 类型选择决策卡
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

```text
需要存储数据？
├── 已知大小 → 栈上: T
│             └── 大/可变 → 堆上: Box<T>
├── 可能不存在 → Option<T>
├── 两种可能 → Result<T, E> 或 Enum
└── 多个同类型 → Vec<T> 或 [T; n]

需要共享数据？
├── 只读共享 → &T
├── 可变共享 → &mut T
└── 多所有者共享 → Rc<T> 或 Arc<T>

需要运行时多态？
├── 编译时确定大小 → Box<dyn Trait>
└── 借用 → &dyn Trait
```

---

## 总结
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

本文档通过视觉化方法帮助理解 Rust 的所有权系统：

1. **隐喻和类比** - 建立直观理解
2. **流程图** - 决策过程可视化
3. **层次图** - 抽象层次清晰化
4. **状态图** - 动态行为可视化
5. **对比矩阵** - 快速参考
6. **实例图解** - 具体场景理解

**建议**: 将这些可视化与代码实践结合，加深理解
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

## 相关概念
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

- [rust-ownership-decidability 目录](./README.md)
- [上级目录](../README.md)

---

## 权威来源索引

> **[来源: Wikipedia - Memory Safety]**

> **[来源: TRPL Ch. 4 - Ownership]**

> **[来源: Rustonomicon - Ownership]**

> **[来源: POPL 2018 - RustBelt]**

---

## 权威来源索引

> **[来源: [RustBelt](https://plv.mpi-sws.org/rustbelt/)]**
>
> **[来源: [Tree Borrows](https://plv.mpi-sws.org/rustbelt/tree-borrows/)]**
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
>

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**
