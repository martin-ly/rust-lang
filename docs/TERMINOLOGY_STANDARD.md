# Rust 术语标准化文档

> **创建日期**: 2026-02-28
> **最后更新**: 2026-02-28
> **Rust 版本**: 1.94.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **对齐标准**: [Ferrocene FLS (Formal Language Specification)](https://spec.ferrocene.dev/)

---

## 📋 目录 {#-目录}

- [Rust 术语标准化文档](#rust-术语标准化文档)
  - [📋 目录 {#-目录}](#-目录--目录)
  - [🎯 概述 {#-概述}](#-概述--概述)
    - [本文档的目标](#本文档的目标)
    - [Ferrocene FLS 简介](#ferrocene-fls-简介)
  - [📊 核心术语对照表 {#-核心术语对照表}](#-核心术语对照表--核心术语对照表)
    - [所有权与内存安全](#所有权与内存安全)
    - [类型系统](#类型系统)
    - [泛型与 Trait](#泛型与-trait)
    - [模式与表达式](#模式与表达式)
    - [异步与并发](#异步与并发)
    - [宏与元编程](#宏与元编程)
    - [编译器与工具链](#编译器与工具链)
    - [Unsafe 与 FFI](#unsafe-与-ffi)
  - [🔗 Ferrocene FLS 引用索引 {#-ferrocene-fls-引用索引}](#-ferrocene-fls-引用索引--ferrocene-fls-引用索引)
    - [第 4 章：类型与 Trait](#第-4-章类型与-trait)
    - [第 5 章：模式](#第-5-章模式)
    - [第 6 章：表达式](#第-6-章表达式)
    - [第 7 章：作用域与命名空间](#第-7-章作用域与命名空间)
    - [第 12 章：泛型](#第-12-章泛型)
    - [第 13 章：Trait](#第-13-章trait)
    - [第 15 章：所有权与析构](#第-15-章所有权与析构)
    - [第 16 章：生命周期分析](#第-16-章生命周期分析)
    - [第 17 章：宏](#第-17-章宏)
    - [第 18 章：FFI](#第-18-章ffi)
  - [📝 术语使用规范 {#-术语使用规范}](#-术语使用规范--术语使用规范)
    - [中英文使用规则](#中英文使用规则)
    - [大小写规范](#大小写规范)
    - [代码块中的术语规范](#代码块中的术语规范)
    - [文档交叉引用规范](#文档交叉引用规范)
  - [🚫 禁用与避免术语 {#-禁用与避免术语}](#-禁用与避免术语--禁用与避免术语)
    - [不一致的翻译](#不一致的翻译)
    - [过时的术语](#过时的术语)
    - [非标准缩写](#非标准缩写)
    - [模糊或不准确的术语](#模糊或不准确的术语)
  - [📚 参考资料 {#-参考资料}](#-参考资料--参考资料)
    - [官方规范](#官方规范)
    - [本项目参考文档](#本项目参考文档)
    - [社区资源](#社区资源)
  - [🔄 更新日志 {#-更新日志}](#-更新日志--更新日志)

---

## 🎯 概述 {#-概述}

本文档定义了 Rust 学习系统的**术语标准化规范**，所有术语均与 [Ferrocene FLS (Formal Language Specification)](https://spec.ferrocene.dev/) 对齐。Ferrocene FLS 是 Rust 语言的官方形式化规范，由 Ferrous Systems 和 AdaCore 维护，于 2024 年被 Rust 项目采纳为官方语言规范。

### 本文档的目标

1. **统一术语翻译**：确保中文文档中的术语翻译一致、准确
2. **对齐官方规范**：所有术语与 Ferrocene FLS 的英文原文保持一致
3. **提供参考链接**：为每个核心术语提供 Ferrocene FLS 的对应章节链接
4. **规范使用场景**：明确术语在不同上下文中的使用规则

### Ferrocene FLS 简介

| 属性 | 说明 |
| :--- | :--- |
| **全称** | Ferrocene Formal Language Specification |
| **官网** | <https://spec.ferrocene.dev/> |
| **GitHub** | <https://github.com/ferrocene/specification> |
| **采用时间** | 2024年（成为 Rust 官方语言规范） |
| **维护方** | Ferrous Systems, AdaCore |
| **许可证** | MIT / Apache 2.0 |

---

## 📊 核心术语对照表 {#-核心术语对照表}

### 所有权与内存安全

| 中文术语 | 英文原文 | FLS 章节 | 简要说明 |
| :--- | :--- | :--- | :--- |
| 所有权 | **Ownership** | [Chapter 15](https://spec.ferrocene.dev/ownership-and-destruction.html) | 值有且仅有一个所有者的机制 |
| 借用 | **Borrowing** | [§15.4](https://spec.ferrocene.dev/ownership-and-destruction.html#borrowing) | 临时获取值的引用而不转移所有权 |
| 不可变借用 | **Immutable Borrow** / **Shared Borrow** | [§15.4.2](https://spec.ferrocene.dev/ownership-and-destruction.html#immutable-borrows) | 允许多个读者同时访问的借用 |
| 可变借用 | **Mutable Borrow** / **Unique Borrow** | [§15.4.3](https://spec.ferrocene.dev/ownership-and-destruction.html#mutable-borrows) | 仅允许一个写者访问的独占借用 |
| 生命周期 | **Lifetime** | [Chapter 16](https://spec.ferrocene.dev/lifetime-analysis.html) | 引用有效的程序点集合 |
| 所有权转移 | **Move** | [§15.3](https://spec.ferrocene.dev/ownership-and-destruction.html#moves) | 值的所有权从一个变量转移到另一个 |
| 复制语义 | **Copy** | [§15.2.2](https://spec.ferrocene.dev/ownership-and-destruction.html#the-copy-trait) | 按位复制而非移动的语义 |
| 克隆 | **Clone** | [§15.2.1](https://spec.ferrocene.dev/ownership-and-destruction.html#the-clone-trait) | 显式创建值的深拷贝 |
| 丢弃/析构 | **Drop** / **Destruction** | [§15.5](https://spec.ferrocene.dev/ownership-and-destruction.html#destruction) | 值离开作用域时的清理操作 |
| 释放 | **Deallocation** | [§15.5](https://spec.ferrocene.dev/ownership-and-destruction.html#deallocation) | 内存空间的回收 |
| 作用域 | **Scope** | [Chapter 7](https://spec.ferrocene.dev/scopes.html) | 名称有效的程序区域 |
| 悬垂引用 | **Dangling Reference** | [§16.3](https://spec.ferrocene.dev/lifetime-analysis.html) | 指向已释放内存的引用 |
| 未定义行为 | **Undefined Behavior (UB)** | [§7.8](https://spec.ferrocene.dev/undefined-behavior.html) | 违反语言契约的行为，编译器可做任意假设 |
| 内存安全 | **Memory Safety** | [Chapter 15](https://spec.ferrocene.dev/ownership-and-destruction.html) | 防止悬垂指针、双重释放等内存错误 |
| 数据竞争 | **Data Race** | [§10.8.2](https://spec.ferrocene.dev/expressions.html#unsafe-operations) | 非同步的并发读写冲突 |
| 内部可变性 | **Interior Mutability** | [标准库文档](https://doc.rust-lang.org/std/cell/) | 通过不可变引用修改值的能力 |
| RAII | **Resource Acquisition Is Initialization** | - | 资源获取即初始化，Rust 的所有权模型基础 |

### 类型系统

| 中文术语 | 英文原文 | FLS 章节 | 简要说明 |
| :--- | :--- | :--- | :--- |
| 类型 | **Type** | [Chapter 4](https://spec.ferrocene.dev/types-and-traits.html) | 值的静态分类 |
| 标量类型 | **Scalar Type** | [§4.1](https://spec.ferrocene.dev/types-and-traits.html#scalar-types) | 单个值的原子类型（整数、浮点等） |
| 复合类型 | **Compound Type** | [§4.2](https://spec.ferrocene.dev/types-and-traits.html#compound-types) | 包含多个值的类型（元组、数组等） |
| 结构体 | **Struct** | [§3.13](https://spec.ferrocene.dev/items.html#structs) | 命名字段的复合类型 |
| 枚举 | **Enum** / **Enumeration** | [§3.8](https://spec.ferrocene.dev/items.html#enumerations) | 变体类型的和类型 |
| 变体 | **Variant** | [§3.8](https://spec.ferrocene.dev/items.html#variants) | 枚举的成员 |
| 联合 | **Union** | [§3.21](https://spec.ferrocene.dev/items.html#unions) | C 风格的内存共享类型 |
| 类型别名 | **Type Alias** | [§3.19](https://spec.ferrocene.dev/items.html#type-aliases) | 类型的替代名称 |
| 永不类型 | **Never Type** (`!`) | [§4.8](https://spec.ferrocene.dev/types-and-traits.html#the-never-type) | 无值的类型，发散函数的返回类型 |
| 单元类型 | **Unit Type** (`()`) | [§4.2.1](https://spec.ferrocene.dev/types-and-traits.html#tuple-types) | 空元组，默认返回类型 |
| 原始指针 | **Raw Pointer** (`*const`, `*mut`) | [§4.11](https://spec.ferrocene.dev/types-and-traits.html#raw-pointers) | 无生命周期约束的裸指针 |
| 引用 | **Reference** (`&T`, `&mut T`) | [§4.10](https://spec.ferrocene.dev/types-and-traits.html#reference-types) | 有生命周期的借用指针 |
| 切片 | **Slice** (`[T]`) | [§4.4](https://spec.ferrocene.dev/types-and-traits.html#slice-types) | 动态大小的连续序列视图 |
| 字符串切片 | **Str** (`str`) | [§4.5](https://spec.ferrocene.dev/types-and-traits.html#str-type) | UTF-8 编码的字符串切片 |
| 动态大小类型 | **Dynamically Sized Type (DST)** | [§4.9](https://spec.ferrocene.dev/types-and-traits.html#dynamically-sized-types) | 编译时大小未知的类型 |
| 零大小类型 | **Zero-Sized Type (ZST)** | - | 运行时大小为 0 的类型 |
| 类型推导 | **Type Inference** | [§6.3](https://spec.ferrocene.dev/expressions.html#type-inference) | 编译器自动推断类型的能力 |
| 型变 | **Variance** | [§12.1.40](https://spec.ferrocene.dev/generics.html#generic-parameters) | 类型参数在子类型关系中的变化 |
| 协变 | **Covariance** | [§12.1.40](https://spec.ferrocene.dev/generics.html#generic-parameters) | 子类型关系保持方向 |
| 逆变 | **Contravariance** | [§12.1.40](https://spec.ferrocene.dev/generics.html#generic-parameters) | 子类型关系反向 |
| 不变 | **Invariance** | [§12.1.40](https://spec.ferrocene.dev/generics.html#generic-parameters) | 无子类型关系 |

### 泛型与 Trait

| 中文术语 | 英文原文 | FLS 章节 | 简要说明 |
| :--- | :--- | :--- | :--- |
| 泛型 | **Generics** | [Chapter 12](https://spec.ferrocene.dev/generics.html) | 参数化类型的机制 |
| 类型参数 | **Type Parameter** | [§12.1.16](https://spec.ferrocene.dev/generics.html#generic-parameters) | 泛型的类型占位符 |
| 生命周期参数 | **Lifetime Parameter** | [§12.1.14](https://spec.ferrocene.dev/generics.html#generic-parameters) | 泛型的生命周期占位符 |
| 常量参数 | **Constant Parameter** / **Const Generic** | [§12.1.10](https://spec.ferrocene.dev/generics.html#generic-parameters) | 编译时常量作为泛型参数 |
| 特征 / Trait | **Trait** | [Chapter 13](https://spec.ferrocene.dev/traits.html) | 定义类型行为的接口 |
| Trait 对象 | **Trait Object** (`dyn Trait`) | [§4.13](https://spec.ferrocene.dev/types-and-traits.html#trait-objects) | 运行时多态的动态分发 |
| 自动 Trait | **Auto Trait** | [§13.10](https://spec.ferrocene.dev/traits.html#auto-traits) | 编译器自动实现的 Trait（如 `Send`, `Sync`） |
| 标记 Trait | **Marker Trait** | [§13.10](https://spec.ferrocene.dev/traits.html#auto-traits) | 无方法的 Trait，仅用于标记类型属性 |
| 派生 | **Derive** | [§3.6](https://spec.ferrocene.dev/items.html#derive-macro-invocations) | 自动实现 Trait 的宏 |
| 实现 | **Implementation** / **Impl** | [§3.11](https://spec.ferrocene.dev/items.html#implementations) | 为类型提供 Trait 或方法定义 |
| 孤儿规则 | **Orphan Rule** | [§13.1.4](https://spec.ferrocene.dev/traits.html#orphan-rules) | 限制跨 crate 实现 Trait 的规则 |
| 特化 | **Specialization** | [ nightly 特性 ] | 为特定类型提供优化的实现 |
| 关联类型 | **Associated Type** | [§13.2](https://spec.ferrocene.dev/traits.html#associated-types) | Trait 中定义的输出类型 |
| 泛型关联类型 | **Generic Associated Types (GATs)** | [§13.2](https://spec.ferrocene.dev/traits.html#associated-types) | 带泛型参数的关联类型 |
| Trait 约束 | **Trait Bound** | [§12.2.4](https://spec.ferrocene.dev/generics.html#where-clauses) | 对泛型参数的能力要求 |
| Where 子句 | **Where Clause** | [§12.2](https://spec.ferrocene.dev/generics.html#where-clauses) | 泛型约束的显式声明 |
| 高阶 Trait 约束 | **Higher-Ranked Trait Bounds (HRTB)** | [§12.2](https://spec.ferrocene.dev/generics.html#where-clauses) | 对任意生命周期的 Trait 约束 |
| 单态化 | **Monomorphization** | [编译器实现] | 泛型代码编译为具体类型的过程 |
|  turbo fish | **Turbofish** (`::<>`) | [§6.4](https://spec.ferrocene.dev/expressions.html#type-inference) | 显式指定泛型参数的语法 |

### 模式与表达式

| 中文术语 | 英文原文 | FLS 章节 | 简要说明 |
| :--- | :--- | :--- | :--- |
| 模式 | **Pattern** | [Chapter 5](https://spec.ferrocene.dev/patterns.html) | 匹配值的结构 |
| 模式匹配 | **Pattern Matching** | [Chapter 5](https://spec.ferrocene.dev/patterns.html) | 根据模式解构值的过程 |
| 绑定 | **Binding** | [§5.1](https://spec.ferrocene.dev/patterns.html#identifier-patterns) | 将值绑定到变量 |
| 可辩驳模式 | **Refutable Pattern** | [§5](https://spec.ferrocene.dev/patterns.html) | 可能不匹配的模式 |
| 无可辩驳模式 | **Irrefutable Pattern** | [§5](https://spec.ferrocene.dev/patterns.html) | 总是匹配的模式 |
| 解构 | **Destructuring** | [§5](https://spec.ferrocene.dev/patterns.html) | 分解复合类型的值 |
| 守卫 | **Guard** | [§8.4.2](https://spec.ferrocene.dev/statements.html#if-let-guards) | 模式匹配的额外条件 |
| 表达式 | **Expression** | [Chapter 6](https://spec.ferrocene.dev/expressions.html) | 产生值的代码片段 |
| 语句 | **Statement** | [Chapter 8](https://spec.ferrocene.dev/statements.html) | 执行动作的代码片段 |
| 块表达式 | **Block Expression** | [§6.3](https://spec.ferrocene.dev/expressions.html#block-expressions) | 用大括号包围的表达式序列 |
| 闭包 | **Closure** / **Closure Expression** | [§6.7](https://spec.ferrocene.dev/expressions.html#closure-expressions) | 匿名函数，可捕获环境 |
| 立即求值闭包 | **Closure Expression** | [§6.7](https://spec.ferrocene.dev/expressions.html#closure-expressions) | 延迟求值的闭包 |
| 捕获 | **Capture** | [§6.7](https://spec.ferrocene.dev/expressions.html#closure-expressions) | 闭包引用外部变量的方式 |
| 移动捕获 | **Move Closure** | [§6.7](https://spec.ferrocene.dev/expressions.html#closure-expressions) | 强制将捕获变量移入闭包 |

### 异步与并发

| 中文术语 | 英文原文 | FLS 章节 | 简要说明 |
| :--- | :--- | :--- | :--- |
| 异步 | **Async** / **Asynchronous** | [§6.2](https://spec.ferrocene.dev/expressions.html#async-expressions) | 非阻塞的异步执行 |
| 等待 | **Await** | [§6.2.1](https://spec.ferrocene.dev/expressions.html#await-expressions) | 挂起异步任务等待完成 |
| Future | **Future** | [标准库](https://doc.rust-lang.org/std/future/trait.Future.html) | 异步计算的抽象 |
| 轮询 | **Poll** | [标准库](https://doc.rust-lang.org/std/task/enum.Poll.html) | 检查 Future 状态 |
| 执行器 | **Executor** | [生态系统] | 调度执行异步任务的运行时 |
| 反应器 | **Reactor** | [生态系统] | 处理 I/O 事件的组件 |
| 任务 | **Task** | [tokio 文档] | 异步执行的单元 |
| 固定/钉住 | **Pin** | [标准库](https://doc.rust-lang.org/std/pin/struct.Pin.html) | 保证值在内存中不移动的抽象 |
| 自引用 | **Self-Referential** | [标准库] | 包含指向自身引用的类型 |
| 线程 | **Thread** | [标准库](https://doc.rust-lang.org/std/thread/) | 操作系统线程 |
| 线程安全 | **Thread Safety** | [标准库] | 跨线程访问的安全性 |
| 可发送 | **Send** | [§13.10](https://spec.ferrocene.dev/traits.html#auto-traits) | 可安全跨线程转移所有权的标记 |
| 可同步 | **Sync** | [§13.10](https://spec.ferrocene.dev/traits.html#auto-traits) | 可安全跨线程共享引用的标记 |
| 互斥锁 | **Mutex** | [标准库](https://doc.rust-lang.org/std/sync/struct.Mutex.html) | 互斥访问的同步原语 |
| 读写锁 | **RwLock** | [标准库](https://doc.rust-lang.org/std/sync/struct.RwLock.html) | 多读单写的同步原语 |
| 原子操作 | **Atomic** | [标准库](https://doc.rust-lang.org/std/sync/atomic/) | 无锁的原子操作 |
| 通道 | **Channel** | [标准库](https://doc.rust-lang.org/std/sync/mpsc/) | 线程间通信机制 |
| 条件变量 | **Condition Variable** | [标准库](https://doc.rust-lang.org/std/sync/struct.Condvar.html) | 线程同步原语 |
| 栅栏 | **Barrier** | [标准库](https://doc.rust-lang.org/std/sync/struct.Barrier.html) | 多线程同步点 |

### 宏与元编程

| 中文术语 | 英文原文 | FLS 章节 | 简要说明 |
| :--- | :--- | :--- | :--- |
| 宏 | **Macro** | [Chapter 17](https://spec.ferrocene.dev/macros.html) | 元编程代码生成机制 |
| 声明宏 | **Declarative Macro** (`macro_rules!`) | [§17.1](https://spec.ferrocene.dev/macros.html#declarative-macros) | 基于模式的宏定义 |
| 过程宏 | **Procedural Macro** | [§17.2](https://spec.ferrocene.dev/macros.html#procedural-macros) | 编译时执行的 Rust 代码 |
| 派生宏 | **Derive Macro** | [§17.2.1](https://spec.ferrocene.dev/macros.html#derive-macro) | 自动实现 Trait 的过程宏 |
| 属性宏 | **Attribute Macro** | [§17.2.2](https://spec.ferrocene.dev/macros.html#attribute-macro) | 修改项的属性的过程宏 |
| 函数式宏 | **Function-like Macro** | [§17.2.3](https://spec.ferrocene.dev/macros.html#function-like-macro) | 类似函数调用的过程宏 |
| Token 树 | **Token Tree** | [§17](https://spec.ferrocene.dev/macros.html) | 宏处理的基本单元 |
| 卫生宏 | **Hygienic Macro** | [§17.1](https://spec.ferrocene.dev/macros.html#declarative-macros) | 避免命名冲突的宏机制 |
| 元变量 | **Metavariable** | [§17.1](https://spec.ferrocene.dev/macros.html#declarative-macros) | 宏规则中的模式变量 |
| 重复 | **Repetition** | [§17.1](https://spec.ferrocene.dev/macros.html#declarative-macros) | 宏模式中的重复匹配 |
| 编译时求值 | **Const Evaluation** | [§6.8](https://spec.ferrocene.dev/expressions.html#constant-expressions) | 编译期执行代码 |
| 常量上下文 | **Constant Context** | [§6.8](https://spec.ferrocene.dev/expressions.html#constant-expressions) | 编译时求值的代码环境 |

### 编译器与工具链

| 中文术语 | 英文原文 | FLS 章节 | 简要说明 |
| :--- | :--- | :--- | :--- |
| Crate | **Crate** | [§2.1](https://spec.ferrocene.dev/lexical-elements.html#crates) | 编译单元，库或可执行文件 |
| 模块 | **Module** | [§3.4](https://spec.ferrocene.dev/items.html#modules) | 代码组织和可见性单元 |
| 包 | **Package** | [Cargo 文档] | Cargo 的构建单元，可含多个 crate |
| 工作空间 | **Workspace** | [Cargo 文档] | 多个相关包的集合 |
| 特性/功能 | **Feature** | [Cargo 文档] | 条件编译和可选依赖的标志 |
| 版本 | **Edition** | [文档](https://doc.rust-lang.org/edition-guide/) | Rust 语言的兼容性版本 |
| HIR | **High-Level IR** | [编译器文档] | 高级中间表示 |
| MIR | **Mid-Level IR** | [编译器文档] | 中级中间表示，借用检查在此进行 |
| LLVM IR | **LLVM IR** | [编译器文档] | LLVM 的低级中间表示 |
| 单态化 | **Monomorphization** | [编译器实现] | 泛型代码实例化为具体类型 |
| 静态链接 | **Static Linking** | [Cargo 文档] | 编译时链接库 |
| 动态链接 | **Dynamic Linking** | [Cargo 文档] | 运行时链接库 |
| 静态分发 | **Static Dispatch** | [编译器实现] | 编译时确定调用的函数 |
| 动态分发 | **Dynamic Dispatch** | [§4.13](https://spec.ferrocene.dev/types-and-traits.html#trait-objects) | 运行时确定调用的函数 |
| 优化 | **Optimization** | [编译器文档] | 改进代码性能的转换 |
| 内联 | **Inline** | [§9.8](https://spec.ferrocene.dev/functions.html#inline-attribute) | 函数调用替换为函数体 |
| 生命周期省略 | **Lifetime Elision** | [§16.2](https://spec.ferrocene.dev/lifetime-analysis.html#lifetime-elision) | 自动推断生命周期参数的语法糖 |

### Unsafe 与 FFI

| 中文术语 | 英文原文 | FLS 章节 | 简要说明 |
| :--- | :--- | :--- | :--- |
| 不安全代码 | **Unsafe Code** / **Unsafe Rust** | [§10.8](https://spec.ferrocene.dev/expressions.html#unsafe-expressions) | 绕过安全检查的代码块 |
| 不安全块 | **Unsafe Block** (`unsafe { }`) | [§10.8](https://spec.ferrocene.dev/expressions.html#unsafe-expressions) | 包含不安全操作的代码块 |
| 不安全函数 | **Unsafe Function** (`unsafe fn`) | [§9.2](https://spec.ferrocene.dev/functions.html#unsafe-functions) | 调用需满足额外安全条件的函数 |
| 原始指针 | **Raw Pointer** (`*const`, `*mut`) | [§4.11](https://spec.ferrocene.dev/types-and-traits.html#raw-pointers) | 无生命周期检查的裸指针 |
| 解引用原始指针 | **Dereference Raw Pointer** | [§10.8.1](https://spec.ferrocene.dev/expressions.html#unsafe-operations) | 不安全的原始指针解引用 |
| 调用不安全函数 | **Call Unsafe Function** | [§10.8.1](https://spec.ferrocene.dev/expressions.html#unsafe-operations) | 在 unsafe 块中调用 unsafe 函数 |
| 读取 `union` 字段 | **Access Union Field** | [§10.8.1](https://spec.ferrocene.dev/expressions.html#unsafe-operations) | 读取 union 的未标记字段 |
| 静态可变变量 | **Static Mutable** (`static mut`) | [§3.18](https://spec.ferrocene.dev/items.html#static-items) | 全局可变状态，访问需 unsafe |
| 外部函数接口 | **Foreign Function Interface (FFI)** | [Chapter 18](https://spec.ferrocene.dev/ffi.html) | 与其他语言交互的接口 |
| 外部块 | **Extern Block** (`extern {}`) | [§18](https://spec.ferrocene.dev/ffi.html) | 声明外部函数的块 |
| 链接属性 | **Link Attribute** | [§18](https://spec.ferrocene.dev/ffi.html) | 指定链接的库 |
| ABI | **Application Binary Interface** | [§9.1](https://spec.ferrocene.dev/functions.html#extern-function-qualifier) | 函数调用约定 |
| C ABI | **C ABI** (`extern "C"`) | [§9.1](https://spec.fer-lang.org/stable/std/keyword.extern.html) | C 语言的调用约定 |

---

## 🔗 Ferrocene FLS 引用索引 {#-ferrocene-fls-引用索引}

以下按 FLS 章节组织核心术语，便于查阅官方规范：

### 第 4 章：类型与 Trait

- [Chapter 4: Types and Traits](https://spec.ferrocene.dev/types-and-traits.html)
- 核心术语：Type, Trait, Struct, Enum, Reference, Slice, Trait Object, Function Pointer

### 第 5 章：模式

- [Chapter 5: Patterns](https://spec.ferrocene.dev/patterns.html)
- 核心术语：Pattern, Binding, Destructuring, Refutable, Irrefutable

### 第 6 章：表达式

- [Chapter 6: Expressions](https://spec.ferrocene.dev/expressions.html)
- 核心术语：Expression, Block, Closure, Async, Await, Unsafe

### 第 7 章：作用域与命名空间

- [Chapter 7: Scopes and Namespaces](https://spec.ferrocene.dev/scopes.html)
- 核心术语：Scope, Namespace, Shadowing

### 第 12 章：泛型

- [Chapter 12: Generics](https://spec.ferrocene.dev/generics.html)
- 核心术语：Generic Parameter, Type Parameter, Lifetime Parameter, Const Generic, Where Clause, Trait Bound

### 第 13 章：Trait

- [Chapter 13: Traits](https://spec.ferrocene.dev/traits.html)
- 核心术语：Trait, Implementation, Associated Type, Auto Trait, Orphan Rule

### 第 15 章：所有权与析构

- [Chapter 15: Ownership and Destruction](https://spec.ferrocene.dev/ownership-and-destruction.html)
- 核心术语：Ownership, Move, Copy, Clone, Drop, Borrowing, Immutable Borrow, Mutable Borrow

### 第 16 章：生命周期分析

- [Chapter 16: Lifetime Analysis](https://spec.ferrocene.dev/lifetime-analysis.html)
- 核心术语：Lifetime, Lifetime Parameter, Lifetime Elision, Non-Lexical Lifetime (NLL)

### 第 17 章：宏

- [Chapter 17: Macros](https://spec.ferrocene.dev/macros.html)
- 核心术语：Macro, Declarative Macro, Procedural Macro, Derive Macro, Attribute Macro

### 第 18 章：FFI

- [Chapter 18: Foreign Function Interface](https://spec.ferrocene.dev/ffi.html)
- 核心术语：FFI, Extern Block, ABI, Link Attribute

---

## 📝 术语使用规范 {#-术语使用规范}

### 中英文使用规则

| 场景 | 规则 | 示例 |
| :--- | :--- | :--- |
| **首次出现** | 中文（英文原文） | 所有权（Ownership） |
| **后续使用** | 优先使用中文 | 所有权规则、借用检查器 |
| **代码上下文** | 保留英文 | `T: Clone`、`*const T` |
| **API 文档** | 英文为主，中文解释 | `Drop::drop` 方法用于释放资源 |
| **标题/标题** | 中英文并列 | ## 所有权（Ownership） |
| **表格/列表** | 中英文对照 | 见本文档术语对照表 |

### 大小写规范

| 术语类型 | 规范 | 示例 |
| :--- | :--- | :--- |
| **类型名称** | PascalCase | `String`, `Vec<T>`, `MyStruct` |
| **函数/方法** | snake_case | `drop()`, `clone()`, `as_ref()` |
| **常量** | SCREAMING_SNAKE_CASE | `const MAX_SIZE: usize` |
| **生命周期参数** | 单引号 + 小写 | `'a`, `'static`, `'lifetime` |
| **泛型参数** | PascalCase，单字母优先 | `T`, `U`, `Item`, `Error` |
| **Trait 名称** | PascalCase，形容词优先 | `Clone`, `Send`, `Display`, `Default` |
| **模块/包名** | snake_case | `std::collections`, `my_crate` |
| **宏** | snake_case 或 PascalCase | `macro_rules!`, `derive` |

### 代码块中的术语规范

```rust
// ✅ 正确：在注释中使用中文术语，代码中使用英文术语
// 所有权转移示例
fn take_ownership(s: String) {  // s 获得所有权
    println!("{}", s);
} // s 离开作用域，调用 drop

// ✅ 正确：类型参数使用大写字母
fn identity<T>(value: T) -> T {
    value
}

// ✅ 正确：生命周期参数使用小写
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}

// ❌ 错误：在代码中使用中文术语
// fn 获取所有权(字符串: 字符串) { ... }
```

### 文档交叉引用规范

| 引用类型 | 格式 | 示例 |
| :--- | :--- | :--- |
| 本文档内术语 | 加粗 + 链接 | **[所有权](#所有权与内存安全)** |
| 其他文档术语 | 相对路径 | [所有权速查卡](./02_reference/quick_reference/ownership_cheatsheet.md) |
| FLS 官方链接 | 完整 URL | [FLS §15](https://spec.ferrocene.dev/ownership-and-destruction.html) |
| 标准库文档 | docs.rs URL | [std::clone::Clone](https://doc.rust-lang.org/std/clone/trait.Clone.html) |

---

## 🚫 禁用与避免术语 {#-禁用与避免术语}

### 不一致的翻译

| 避免使用 | 推荐用法 | 说明 |
| :--- | :--- | :--- |
| 特质 / 特征对象 | **Trait** / **Trait 对象** | "特质" 是早期翻译，现统一为 "Trait" |
| 生命周期省略 | **生命周期省略** (Elision) | 注意不是 "省略" 或 "消隐" |
| 借用检查 | **借用检查器** (Borrow Checker) | 使用完整名称，指编译器组件 |
| 自动 trait | **自动 Trait** (Auto Trait) | Auto Trait 是专有名词 |
| 原始类型 | **标量类型** (Scalar Type) | 与 "原始指针" (Raw Pointer) 区分 |

### 过时的术语

| 避免使用 | 推荐用法 | 说明 |
| :--- | :--- | :--- |
| ~const Trait | **Const Trait** / 编译时常量 | Rust 1.83+ 已稳定 |
| 装箱 (Box) | **堆分配** / `Box<T>` | 直接使用类型名称 |
| 解装箱 | **解引用** / **解包** | 根据上下文选择 |
| 智能指针 | **智能指针** (Smart Pointer) | 保留此翻译，但优先使用类型名 |
| 语法糖 | **语法糖** (Syntactic Sugar) | 可用，但建议解释具体机制 |

### 非标准缩写

| 避免使用 | 推荐用法 | 说明 |
| :--- | :--- | :--- |
| BC | **Borrow Checker** / 借用检查器 | 首次使用全称 |
| UB (中文文档) | **未定义行为** / Undefined Behavior (UB) | 中文文档优先使用全称 |
| NLL (中文文档) | **非词法生命周期** / NLL | 解释后可用缩写 |
| HRTB (中文文档) | **高阶 Trait 约束** / HRTB | 解释后可用缩写 |
| GATs (中文文档) | **泛型关联类型** / GATs | 解释后可用缩写 |
| DST (中文文档) | **动态大小类型** / DST | 解释后可用缩写 |
| ZST (中文文档) | **零大小类型** / ZST | 解释后可用缩写 |

### 模糊或不准确的术语

| 避免使用 | 推荐用法 | 说明 |
| :--- | :--- | :--- |
| 引用计数 | **`Rc<T>`** / **`Arc<T>`** | 具体指明类型 |
| 互斥 | **`Mutex<T>`** / 互斥锁 | 具体指明类型或机制 |
| 通道 | **`mpsc`** / 通道 | 具体指明类型 |
| 原子 | **原子操作** / `Atomic*` | 具体指明操作类型 |
| 不安全 | **Unsafe** / 不安全代码 / 不安全块 | 区分概念层级 |
| 线程安全 | **Send + Sync** / 线程安全 | 具体指明 Trait |

---

## 📚 参考资料 {#-参考资料}

### 官方规范

| 资源 | 链接 | 说明 |
| :--- | :--- | :--- |
| Ferrocene FLS | <https://spec.ferrocene.dev/> | Rust 官方形式化语言规范 |
| The Rust Reference | <https://doc.rust-lang.org/reference/> | Rust 官方参考文档 |
| The Rust Programming Language | <https://doc.rust-lang.org/book/> | Rust 官方教程 |
| Rust RFCs | <https://rust-lang.github.io/rfcs/> | Rust 设计文档 |

### 本项目参考文档

| 资源 | 路径 | 说明 |
| :--- | :--- | :--- |
| 术语表 | [docs/research_notes/GLOSSARY.md](./research_notes/GLOSSARY.md) | 研究笔记术语表 |
| 所有权速查卡 | [docs/02_reference/quick_reference/ownership_cheatsheet.md](./02_reference/quick_reference/ownership_cheatsheet.md) | 所有权系统速查 |
| 泛型速查卡 | [docs/02_reference/quick_reference/generics_cheatsheet.md](./02_reference/quick_reference/generics_cheatsheet.md) | 泛型系统速查 |
| 类型系统速查卡 | [docs/02_reference/quick_reference/type_system.md](./02_reference/quick_reference/type_system.md) | 类型系统速查 |

### 社区资源

| 资源 | 链接 | 说明 |
| :--- | :--- | :--- |
| Rust 术语对照表 (中文) | <https://github.com/rust-lang-cn/> | 中文社区术语对照 |
| Rust By Example | <https://doc.rust-lang.org/rust-by-example/> | 示例驱动的学习 |
| Rustlings | <https://github.com/rust-lang/rustlings> | 交互式练习 |

---

## 🔄 更新日志 {#-更新日志}

| 日期 | 版本 | 变更内容 |
| :--- | :--- | :--- |
| 2026-02-28 | 1.0.0 | 初始版本，包含 80+ 核心术语，与 Ferrocene FLS 对齐 |

---

**维护团队**: Rust Learning Community
**最后更新**: 2026-02-28
**状态**: ✅ **与 Ferrocene FLS 对齐完成**

---

🦀 **统一术语，精准表达，与官方规范保持一致！** 🦀
