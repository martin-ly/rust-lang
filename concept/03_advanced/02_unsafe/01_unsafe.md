> **内容分级**: [专家级]

# Unsafe Rust 安全编程
>
> **EN**: Safe and Effective Unsafe Rust
> **Summary**: Unsafe Rust is a carefully scoped escape hatch for operations the compiler cannot verify, such as raw-pointer dereferencing, calling foreign functions, and implementing low-level data structures. This chapter explains the unsafe contract, the five unsafe superpowers, soundness invariants, and how to keep safe abstractions reliable.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **📎 交叉引用（Reference）**
>
> 本主题在 knowledge 中有系统化的知识索引：[Unsafe Rust](../../../knowledge/03_advanced/unsafe)
>
> **受众**: [专家]
> **权威来源**: 本文件为 `concept/` 权威页。
> **层级**: L3 高级概念
> **A/S/P 标记**: **S+P** — Structure + Procedure
> **双维定位**: P×Eva — 评判 unsafe 契约的充分性
> **前置概念**: [Ownership](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md) · [Borrowing](../../01_foundation/01_ownership_borrow_lifetime/02_borrowing.md) · [Memory Management](../../02_intermediate/02_memory_management/01_memory_management.md) · [Concurrency](../00_concurrency/01_concurrency.md)
> **后置概念**: [FFI] · [Embedded] · [Custom Allocators]
> **主要来源**: · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
> [TRPL: Ch19.1](https://doc.rust-lang.org/book/ch19-01-unsafe-rust.html) ·
> [Rust Reference: Unsafe Rust](https://doc.rust-lang.org/reference/introduction.html) ·
> [Rustonomicon](https://doc.rust-lang.org/nomicon/index.html) ·
> [RFC 2585](https://rust-lang.github.io/rfcs/2585-unsafe-block-in-unsafe-fn.html) ·
> [RFC 3325](https://rust-lang.github.io/rfcs/3325-unsafe-attributes.html) ·
> [RFC 3484](https://rust-lang.github.io/rfcs/3484-unsafe-extern-blocks.html) ·
> [Rust Edition Guide 2024 — unsafe_op_in_unsafe_fn](https://doc.rust-lang.org/edition-guide/rust-2024/unsafe-op-in-unsafe-fn.html) ·
> [Rust Edition Guide 2024 — unsafe extern blocks](https://doc.rust-lang.org/edition-guide/rust-2024/unsafe-extern.html) ·
> [Rust Edition Guide 2024 — unsafe attributes](https://doc.rust-lang.org/edition-guide/rust-2024/unsafe-attributes.html)
>
> **内容去重提示**: 本文是 Unsafe Rust 的 `concept/` 权威来源。[`knowledge/03_advanced/unsafe/04_unsafe_rust.md`](../../../knowledge/03_advanced/unsafe/04_unsafe_rust.md) 与 [`concept/03_advanced/02_unsafe/04_unsafe_rust_patterns.md`](04_unsafe_rust_patterns.md) 已重定向至本文件，相关内容已在本文件中统一维护。

---

> **Bloom 层级**: L3-L5
**变更日志**:

- v1.0 (2026-05-12): 初始版本，完成权威定义、unsafe 操作矩阵、UB 分类、Safety Contract 规范、思维导图、示例反例
- v1.1 (2026-05-13): 重构增强——定理一致性（Coherence）矩阵扩展至10行（⟹推理链）、反命题决策树×4、认知路径六步递进、章节过渡段落、层次一致性标注
- v1.3 (2026-05-13): Phase BC 形式化深化——新增§2.2b Unsafe Code Guidelines 完整 UB 分类（内存访问/类型系统（Type System）/并发/其他四大类 15 子类 + UB 检测不可判定性定理）；新增§7.2b Miri 检测算法原理（核心解释循环、与 LLVM 优化假设关系、MIRIFLAGS 完整选项速查）
- v1.2 (2026-05-13): 深度重构——新增 §5.5 Stacked Borrows 操作语义、§5.6 Tree Borrows 演进；增强 §7.2 Miri 检测边界（覆盖范围表格+MIRIFLAGS使用）；补充层次一致性（Coherence）标注（L1/L4映射）与章节过渡段落
- v2.0 (2026-06-23): 全面对齐 Rust 2024 Edition Unsafe/FFI 变更——重写第九章，补充 `unsafe extern` blocks（RFC 3484）与 `#[unsafe(...)]` 属性（RFC 3325），更新稳定版本信息为 Rust 1.85.0

---

> **对应练习**: [`exercises/src/unsafe_rust/`](../../exercises/src/unsafe_rust)

## 📑 目录

- [Unsafe Rust 安全编程](#unsafe-rust-安全编程)
  - [📑 目录](#-目录)
  - [一、权威定义（Definition）](#一权威定义definition)
    - [1.1 Wikipedia 权威定义](#11-wikipedia-权威定义)
    - [1.2 TRPL 官方定义](#12-trpl-官方定义)
    - [1.3 Rustonomicon 定义](#13-rustonomicon-定义)
    - [1.4 形式化定义](#14-形式化定义)
  - [二、概念属性矩阵（Attribute Matrix）](#二概念属性矩阵attribute-matrix)
    - [2.1 Unsafe 操作分类矩阵](#21-unsafe-操作分类矩阵)
    - [2.2 UB（未定义行为）分类矩阵](#22-ub未定义行为分类矩阵)
    - [2.2b Unsafe Code Guidelines 完整 UB 分类](#22b-unsafe-code-guidelines-完整-ub-分类)
      - [内存访问类 UB](#内存访问类-ub)
      - [类型系统类 UB](#类型系统类-ub)
      - [并发与同步类 UB](#并发与同步类-ub)
      - [其他 UB](#其他-ub)
      - [UB 检测的不可判定性边界](#ub-检测的不可判定性边界)
    - [2.3 Safety Contract 责任矩阵](#23-safety-contract-责任矩阵)
  - [三、形式化理论根基（Formal Foundation）](#三形式化理论根基formal-foundation)
    - [3.1 Unsafe 作为公理缺口](#31-unsafe-作为公理缺口)
    - [3.2 Safety Invariant vs Validity Invariant](#32-safety-invariant-vs-validity-invariant)
  - [四、认知路径（Cognitive Path）](#四认知路径cognitive-path)
    - [Step 1 — 动机：为什么需要 unsafe？](#step-1--动机为什么需要-unsafe)
    - [Step 2 — 机制：unsafe 到底关掉了什么？](#step-2--机制unsafe-到底关掉了什么)
    - [Step 3 — 保证：怎么保证 unsafe 代码安全？](#step-3--保证怎么保证-unsafe-代码安全)
    - [Step 4 — 边界：UB 和安全的边界在哪？](#step-4--边界ub-和安全的边界在哪)
    - [Step 5 — 验证：Miri 能检测什么？](#step-5--验证miri-能检测什么)
    - [Step 6 — 决策：什么时候必须写 unsafe？](#step-6--决策什么时候必须写-unsafe)
    - [4.1 国际课程与论文对齐](#41-国际课程与论文对齐)
  - [五、思维导图（Mind Map）](#五思维导图mind-map)
    - [5.5 Stacked Borrows 操作语义](#55-stacked-borrows-操作语义)
    - [5.6 Tree Borrows 演进](#56-tree-borrows-演进)
  - [六、决策/边界判定树（Decision / Boundary Tree）](#六决策边界判定树decision--boundary-tree)
    - [6.1 "我需要用 unsafe 吗？" 决策树](#61-我需要用-unsafe-吗-决策树)
    - [6.2 UB 边界判定](#62-ub-边界判定)
    - [6.3 反命题决策树](#63-反命题决策树)
      - [反命题 1: "unsafe 块内没有安全检查"](#反命题-1-unsafe-块内没有安全检查)
      - [反命题 2: "只要用了 unsafe 就会触发 UB"](#反命题-2-只要用了-unsafe-就会触发-ub)
      - [反命题 3: "raw pointer 和引用等价"](#反命题-3-raw-pointer-和引用等价)
      - [反命题 4: "FFI 调用总是安全的"](#反命题-4-ffi-调用总是安全的)
  - [七、定理推理链（Theorem Chain）](#七定理推理链theorem-chain)
    - [7.1 安全抽象定理](#71-安全抽象定理)
    - [7.2 Miri 的验证边界](#72-miri-的验证边界)
    - [7.2b Miri 检测算法原理与编译器优化关系](#72b-miri-检测算法原理与编译器优化关系)
      - [Miri 检测的核心算法](#miri-检测的核心算法)
      - [Miri 与编译器优化的关系](#miri-与编译器优化的关系)
      - [MIRIFLAGS 完整选项速查](#miriflags-完整选项速查)
    - [7.3 定理一致性矩阵（⟹ 推理链）](#73-定理一致性矩阵-推理链)
  - [八、示例与反例（Examples \& Counter-examples）](#八示例与反例examples--counter-examples)
    - [8.1 正确示例：安全封装裸指针（Vec 简化版）](#81-正确示例安全封装裸指针vec-简化版)
    - [8.2 正确示例：手动实现 Send/Sync](#82-正确示例手动实现-sendsync)
    - [8.3 反例：悬垂裸指针（UB）](#83-反例悬垂裸指针ub)
    - [8.4 反例：transmute 滥用（UB）](#84-反例transmute-滥用ub)
    - [8.5 反例：无效枚举值（UB）](#85-反例无效枚举值ub)
    - [8.6 边界极限测试](#86-边界极限测试)
      - [命题: "unsafe 代码可以安全地封装"](#命题-unsafe-代码可以安全地封装)
      - [命题: "Miri 可以检测所有 UB"](#命题-miri-可以检测所有-ub)
      - [边界极限测试代码](#边界极限测试代码)
  - [十、知识来源关系（Provenance）](#十知识来源关系provenance)
  - [十一、演进方向](#十一演进方向)
    - [补充章节：FFI 与 repr 属性完整规范](#补充章节ffi-与-repr-属性完整规范)
      - [ABI 与 Calling Convention](#abi-与-calling-convention)
      - [repr 属性语义对比矩阵](#repr-属性语义对比矩阵)
      - [内存布局与对齐分析](#内存布局与对齐分析)
      - [FFI 边界使用场景](#ffi-边界使用场景)
      - [对齐、填充与风险边界](#对齐填充与风险边界)
    - [补充章节：Miri 的使用方法与限制](#补充章节miri-的使用方法与限制)
      - [安装与基本使用](#安装与基本使用)
      - [能检测的问题（覆盖范围）](#能检测的问题覆盖范围)
      - [不能检测的问题（边界限制）](#不能检测的问题边界限制)
      - [正确示例：Miri 检测出 UB](#正确示例miri-检测出-ub)
      - [反例：Miri 无法检测的逻辑错误](#反例miri-无法检测的逻辑错误)
      - [Miri 常用标志详解](#miri-常用标志详解)
      - [Miri 与 Valgrind / ASan / TSan 的对比](#miri-与-valgrind--asan--tsan-的对比)
    - [补充章节：`std::ptr::read/write` vs `*ptr` 解引用的语义差异](#补充章节stdptrreadwrite-vs-ptr-解引用的语义差异)
      - [语义精确定义](#语义精确定义)
        - [`std::ptr::read<T>(src: *const T) -> T`](#stdptrreadtsrc-const-t---t)
          - [Rust 1.96 `valid for read/write` 语义变更详解](#rust-196-valid-for-readwrite-语义变更详解)
        - [`std::ptr::write<T>(dst: *mut T, src: T)`](#stdptrwritetdst-mut-t-src-t)
        - [`*ptr` 解引用（`DerefMut`）](#ptr-解引用derefmut)
      - [关键差异对比表格](#关键差异对比表格)
      - [典型使用场景](#典型使用场景)
        - [`ptr::read`： `Vec::pop` 内部实现与 `ManuallyDrop` 配合](#ptrread-vecpop-内部实现与-manuallydrop-配合)
        - [`ptr::write`：未初始化内存填充与 `MaybeUninit::write` 的前身模式](#ptrwrite未初始化内存填充与-maybeuninitwrite-的前身模式)
      - [危险模式与常见错误](#危险模式与常见错误)
        - [危险模式 1：`ptr::read` 后原位置未失效导致的 double-free](#危险模式-1ptrread-后原位置未失效导致的-double-free)
        - [危险模式 2：`ptr::write` 覆盖已初始化值导致的内存泄漏](#危险模式-2ptrwrite-覆盖已初始化值导致的内存泄漏)
        - [危险模式 3：对未初始化内存使用 `*ptr = val`](#危险模式-3对未初始化内存使用-ptr--val)
      - [`ptr::read_volatile` / `ptr::write_volatile`：MMIO 与硬件寄存器场景](#ptrread_volatile--ptrwrite_volatilemmio-与硬件寄存器场景)
      - [边界分析：`ptr::replace` 的契约](#边界分析ptrreplace-的契约)
    - [补充章节：`NonNull<T>` / `Unique<T>` / `Shared<T>` 的演进](#补充章节nonnullt--uniquet--sharedt-的演进)
      - [`Unique<T>`：曾经的 Box 内部表示](#uniquet曾经的-box-内部表示)
      - [`Shared<T>`：曾经的 Rc/Arc 内部表示](#sharedt曾经的-rcarc-内部表示)
      - [`NonNull<T>`：统一后的稳定抽象](#nonnullt统一后的稳定抽象)
      - [演进时间线](#演进时间线)
      - [反例：误用 `NonNull` 导致的问题](#反例误用-nonnull-导致的问题)
      - [`NonNull<T>` 在标准库中的实际使用](#nonnullt-在标准库中的实际使用)
      - [为什么 `NonNull<T>` 是协变的，而 `*mut T` 是不变的](#为什么-nonnullt-是协变的而-mut-t-是不变的)
    - [补充章节：`MaybeUninit` 数组初始化模式](#补充章节maybeuninit-数组初始化模式)
      - [核心语义对比](#核心语义对比)
      - [正确示例：逐个元素初始化数组](#正确示例逐个元素初始化数组)
      - [正确示例：安全封装数组初始化](#正确示例安全封装数组初始化)
      - [反例：错误使用 `assume_init()` 导致 UB](#反例错误使用-assume_init-导致-ub)
      - [边界：`MaybeUninit` 与 `ManuallyDrop`](#边界maybeuninit-与-manuallydrop)
      - [安全替代：`array::map` 与 `array::from_fn`](#安全替代arraymap-与-arrayfrom_fn)
      - [与 C 的 `malloc` + 手动初始化的对比](#与-c-的-malloc--手动初始化的对比)
  - [九、Unsafe/FFI 2024：权限分离与显式契约](#九unsafeffi-2024权限分离与显式契约)
    - [9.1 问题：权限的混淆](#91-问题权限的混淆)
    - [9.2 2024 Edition 的权限分离](#92-2024-edition-的权限分离)
    - [9.3 形式化模型：权限的模块化](#93-形式化模型权限的模块化)
    - [9.4 与 `unsafe extern` + `safe` 的关系](#94-与-unsafe-extern--safe-的关系)
    - [9.5 `unsafe extern` blocks：FFI 边界的显式 unsafe（Rust 2024）](#95-unsafe-extern-blocksffi-边界的显式-unsaferust-2024)
      - [9.5.1 问题：谁为 FFI 签名负责？](#951-问题谁为-ffi-签名负责)
      - [9.5.2 语法与语义](#952-语法与语义)
      - [9.5.3 版本迁移示例](#953-版本迁移示例)
      - [9.5.4 边界与反模式](#954-边界与反模式)
    - [9.6 `#[unsafe(...)]` 属性：链接级 unsafe 契约（Rust 2024）](#96-unsafe-属性链接级-unsafe-契约rust-2024)
      - [9.6.1 哪些属性是 unsafe 的？](#961-哪些属性是-unsafe-的)
      - [9.6.2 语法变化](#962-语法变化)
      - [9.6.3 为什么需要 unsafe 包装？](#963-为什么需要-unsafe-包装)
      - [9.6.4 迁移与 lint](#964-迁移与-lint)
  - [判定表：unsafe 使用与 UB 边界判定](#判定表unsafe-使用与-ub-边界判定)
  - [相关概念链接](#相关概念链接)
  - [Wikipedia 概念对齐](#wikipedia-概念对齐)
  - [权威来源索引](#权威来源索引)
  - [十五、内存模型深度对比：C++ / Java / Rust](#十五内存模型深度对比c--java--rust)
    - [15.1 内存模型的本质](#151-内存模型的本质)
    - [15.2 C++ Memory Model：RC11 与 Promising Semantics](#152-c-memory-modelrc11-与-promising-semantics)
    - [15.3 Java Memory Model：Happens-Before 与 Final 字段](#153-java-memory-modelhappens-before-与-final-字段)
    - [15.4 Rust 内存模型演进](#154-rust-内存模型演进)
      - [Stacked Borrows（POPL 2019）](#stacked-borrowspopl-2019)
      - [Tree Borrows（PLDI 2023）](#tree-borrowspldi-2023)
      - [Provenance（PLDI 2022）](#provenancepldi-2022)
    - [15.5 跨语言内存模型对比矩阵](#155-跨语言内存模型对比矩阵)
  - [十六、边界测试：Unsafe 代码的编译错误与运行时灾难](#十六边界测试unsafe-代码的编译错误与运行时灾难)
    - [16.1 边界测试：裸指针解引用前的空检查（编译错误）](#161-边界测试裸指针解引用前的空检查编译错误)
    - [16.2 边界测试：将 \&T 转换为 \&mut T（编译错误）](#162-边界测试将-t-转换为-mut-t编译错误)
    - [16.3 边界测试：无效 UTF-8 的 str::from\_utf8\_unchecked（运行时 UB）](#163-边界测试无效-utf-8-的-strfrom_utf8_unchecked运行时-ub)
    - [16.4 边界测试：通过 `&T` 获取 `&mut T`（编译错误）](#164-边界测试通过-t-获取-mut-t编译错误)
    - [16.5 边界测试：裸指针算术越界（运行时 UB）](#165-边界测试裸指针算术越界运行时-ub)
    - [16.6 边界测试：`std::mem::transmute` 类型大小不匹配（编译错误）](#166-边界测试stdmemtransmute-类型大小不匹配编译错误)
    - [10.4 边界测试：`union` 的字段访问与活跃字段跟踪（运行时 UB）](#104-边界测试union-的字段访问与活跃字段跟踪运行时-ub)
  - [逆向推理链（Backward Reasoning）](#逆向推理链backward-reasoning)
  - [参考来源](#参考来源)
    - [16.7 前沿方向：Unsafe Fields（字段级 unsafe，Rust 2026 Project Goal）](#167-前沿方向unsafe-fields字段级-unsaferust-2026-project-goal)
  - [Null 指针有效性定义](#null-指针有效性定义)
  - [实践](#实践)
    - [对应代码示例](#对应代码示例)
    - [建议练习](#建议练习)
  - [导航：下一步去哪？](#导航下一步去哪)
  - [嵌入式测验](#嵌入式测验)
    - [测验 1：unsafe 块的能力（记忆层）](#测验-1unsafe-块的能力记忆层)
    - [测验 2：unsafe fn 与 unsafe 块的区别（理解层）](#测验-2unsafe-fn-与-unsafe-块的区别理解层)
    - [测验 3：裸指针安全解引用（应用层）](#测验-3裸指针安全解引用应用层)
    - [测验 4：unsafe impl 的契约（分析层）](#测验-4unsafe-impl-的契约分析层)
  - [九、Rustonomicon 实现深度](#九rustonomicon-实现深度)
    - [9.1 实现 `Vec<T>` 的核心 unsafe 技术](#91-实现-vect-的核心-unsafe-技术)
    - [9.2 实现 `Arc<T>`：原子引用计数](#92-实现-arct原子引用计数)
    - [9.3 实现 `Mutex<T>`：互斥与 poisoning](#93-实现-mutext互斥与-poisoning)
    - [9.4 Drop-Check（dropck）与 `#[may_dangle]`](#94-drop-checkdropck与-may_dangle)
      - [9.4.1 基本问题](#941-基本问题)
      - [9.4.2 `#[may_dangle]`](#942-may_dangle)
      - [9.4.3 `PhantomData<T>` 与 dropck](#943-phantomdatat-与-dropck)
  - [自 docs/05\_guides/05\_unsafe\_rust\_guide.md 合并的补充内容](#自-docs05_guides05_unsafe_rust_guidemd-合并的补充内容)
    - [🔗 推荐学习路径](#-推荐学习路径)
    - [📖 Rustonomicon 逐章对标表](#-rustonomicon-逐章对标表)

<!-- L3::权威定义 -->

## 一、权威定义（Definition）

> 从形式系统角度看，`unsafe` 是 Rust 类型证明系统的显式边界突破。理解 unsafe 的权威定义，是区分"编译器保证"与"人工保证"的第一道门槛。

### 1.1 Wikipedia 权威定义

> **[Wikipedia: Undefined behavior](https://en.wikipedia.org/wiki/Undefined_behavior)** In computer programming, undefined behavior (UB) is the result of executing computer code whose behavior is not prescribed by the language specification to which the code can adhere, for the current state of the program. This happens when the translator of the source code makes certain assumptions, but these assumptions are not satisfied during execution.
> **[Wikipedia: Memory safety](https://en.wikipedia.org/wiki/Memory_safety)** Memory safety is the state of being protected from various software bugs and security vulnerabilities when dealing with memory access, such as buffer overflows and dangling pointers. A programming language is memory-safe if it prevents such issues through its design, type system, or automatic memory management.
> **[Wikipedia: Foreign function interface](https://en.wikipedia.org/wiki/Foreign_function_interface)** A foreign function interface (FFI) is a mechanism by which a program written in one programming language can call routines or make use of services written in another. FFI is the primary mechanism used by Rust to interoperate with C and other languages.

### 1.2 TRPL 官方定义

> **[TRPL Ch19.1](https://doc.rust-lang.org/book/ch19-01-unsafe-rust.html)** Rust has a second language hiding out inside it, unsafe Rust, which works just like regular Rust but gives you extra superpowers. Unsafe Rust exists because, by nature, static analysis is conservative. When the compiler tries to determine whether or not code upholds the guarantees, it's better for it to reject some valid programs than to accept some invalid programs.

### 1.3 Rustonomicon 定义

> **[Rustonomicon](https://doc.rust-lang.org/nomicon/index.html)** A block of code prefixed with `unsafe` does not permit the writing of arbitrary code. The `unsafe` keyword has two meanings: it declares the existence of a contract the compiler doesn't know about, and it declares that you have verified that contract.
> **[Rustonomicon: What is unsafe?](https://doc.rust-lang.org/nomicon/what-unsafe-does.html)** unsafe 不是关闭检查器，而是声明程序员已人工验证某个编译器无法知晓的契约。安全抽象 = unsafe 实现 + safe 接口 + 人工证明。✅ 已验证
>
> **[TRPL Ch19.1](https://doc.rust-lang.org/book/ch19-01-unsafe-rust.html)** Safe Rust = 编译器可证明安全的程序集合；Unsafe Rust = Safe Rust ∪ 需要人工证明安全性的操作集合。✅ 已验证

### 1.4 形式化定义

`unsafe` 是**形式系统的显式边界突破**：

```text
Safe Rust = { 程序 P | 编译器可证明 P 满足内存安全 + 类型安全 + 并发安全 }
Unsafe Rust = Safe Rust ∪ { 操作 O | O 需要人工证明安全性 }

关键洞察:
  unsafe 不是"关闭检查器"，而是"程序员承担证明责任"
  安全抽象（Safe Abstraction）= unsafe 实现 + safe 接口 + 人工证明内部正确
```

---

<!-- L3::操作分类 -->

## 二、概念属性矩阵（Attribute Matrix）

> 在明确定义后，我们需要对 unsafe 提供的操作进行系统分类。以下三个矩阵分别覆盖：操作能力、未定义行为类型、以及各角色的安全责任。
> **来源: [Rust Reference: Unsafe Rust; Rustonomicon](https://doc.rust-lang.org/reference/introduction.html)** Unsafe 操作分为 7 类，每类有明确的安全契约。

### 2.1 Unsafe 操作分类矩阵

| **操作** | **语法** | **安全风险** | **典型用途** | **Safe 封装示例** |
|:---|:---|:---|:---|:---|
| **裸指针解引用** | `*raw_ptr` | UAF, 悬垂, 类型混淆 | FFI, 数据结构内部 | `Box::from_raw` |
| **调用 unsafe 函数** | `unsafe_fn()` | 依赖函数契约 | 底层系统调用 | `std::fs::read` |
| **实现 unsafe trait** | `unsafe impl Trait` | 破坏全局假设 | Send/Sync 标记：`Send` trait 表示值可跨线程转移(move)，`Sync` 表示 `&T` 可跨线程共享引用 | `Arc<T>` |
| **访问 union 字段** | `union.field` | 类型混淆 | C 互操作 | `std::mem::ManuallyDrop` |
| **调用 extern 函数** | `extern "C"` | ABI 不匹配, UAF | 系统库调用 | `libc` crate |
| **修改可变静态变量** | `static mut` | 数据竞争 | 全局状态（避免） | `lazy_static!` |
| **内联汇编（Inline Assembly）** | `asm!()` | 完全不受控 | 极致优化 | 极少数场景 |

> **[Rust Reference: Behavior considered undefined](https://doc.rust-lang.org/reference/behavior-considered-undefined.html)** Rust 的 UB 清单包括：数据竞争、悬垂指针解引用、越界访问、类型混淆、无效枚举（Enum）值、未对齐访问、读取未初始化内存等。✅ 已验证
> **[Rustonomicon: UB](https://doc.rust-lang.org/nomicon/index.html)** 未定义行为意味着编译器可据此做任何优化假设；触发 UB 后程序行为完全不可预测。✅ 已验证

### 2.2 UB（未定义行为）分类矩阵
>

| **UB 类型** | **描述** | **检测难度** | **示例** |
|:---|:---|:---|:---|
| **内存访问** | 悬垂指针解引用、越界访问、空指针解引用 | 中等（ASan/Miri） | `*ptr` after free |
| **类型系统（Type System）** | 无效枚举（Enum）值、数据竞争、对齐违规 | 难 | `mem::transmute` 滥用 |
| **并发** | 数据竞争、锁顺序错误（C++ style） | 难 | 非原子访问共享可变状态 |
| **ABI** | 调用约定不匹配、布局假设错误 | 难 | FFI 类型宽度不匹配 |
| **特殊** | 递归 panic、栈溢出、除以零 | 中等 | `panic!` in `Drop` |

### 2.2b Unsafe Code Guidelines 完整 UB 分类

> **来源: [Rust Reference: Behavior considered undefined; The Rust Unsafe Code Guidelines (UCG) Book; Ralf Jung Blog](https://doc.rust-lang.org/reference/behavior-considered-undefined.html)** Rust 的 UB 清单不是封闭的——随着编译器优化假设的演进，新的 UB 类别可能被加入。以下分类基于 Rust Reference 和 UCG 的最权威定义。
> **来源: [Rust Reference: Behavior considered undefined](https://doc.rust-lang.org/reference/behavior-considered-undefined.html)** 内存访问类 UB 是最常见的未定义行为，Miri 检测覆盖率高。

#### 内存访问类 UB

| **UB 子类** | **精确条件** | **Miri 检测** | **典型触发代码** |
|:---|:---|:---:|:---|
| **悬垂指针解引用** | 解引用已释放/已重新分配的内存地址 | ✅ | `let r = &x; drop(x); *r` |
| **越界访问** | 通过指针/引用访问分配区域之外的内存 | ✅ | `let v = vec![1]; v[10]` |
| **未对齐访问** | 访问地址不满足类型的 align 要求 | ✅ | `ptr::read_unaligned` 误用 |
| **读取未初始化内存** | 读取 `MaybeUninit::uninit()` 或 padding 字节 | ✅ | `mem::uninitialized::<bool>()` |
| **空指针解引用** | 解引用 `ptr::null()` / `ptr::null_mut()` | ✅ | `*ptr::null::<i32>()` |

> **来源: [Rust Reference: Invalid values](https://doc.rust-lang.org/reference/introduction.html)** 类型系统（Type System）类 UB 涉及编译器对值表示的优化假设。

#### 类型系统类 UB

| **UB 子类** | **精确条件** | **Miri 检测** | **典型触发代码** |
|:---|:---|:---:|:---|
| **无效枚举（Enum）值** | discriminant 不在枚举声明的变体范围内 | ✅ | `mem::transmute::<u8, Option<bool>>(3)` |
| **类型混淆（Type punning）** | 通过 `union` 读取非活跃变体；或 `transmute` 到不兼容布局 | ✅ | `union.u32` 写入后读 `union.f32` |
| **无效布尔值** | bool 的内存表示不是 0x00 或 0x01 | ✅ | `mem::transmute::<u8, bool>(2)` |
| **无效字符值** | char 的内存表示不是合法 Unicode scalar value | ✅ | `mem::transmute::<u32, char>(0xD800)` |
| **无效引用/Box** | `&T` 为 dangling/null/unaligned；`Box<T>` 指向已释放内存 | ✅ | `mem::transmute::<usize, &i32>(0)` |

> **来源: [Rust Reference: Data races](https://doc.rust-lang.org/reference/introduction.html)** 并发类 UB 在 Miri 中无法检测，需用 Loom 或 ThreadSanitizer。

#### 并发与同步类 UB

| **UB 子类** | **精确条件** | **Miri 检测** | **典型触发代码** |
|:---|:---|:---:|:---|
| **数据竞争** | 两个线程无同步地访问同一内存，至少一个写 | ❌（单线程解释器） | `static mut X: i32 = 0;` 多线程读写 |
| **原子操作（Atomic Operations）序违规** | `AtomicOrdering::Relaxed` 用于保护数据依赖 | ⚠️（部分） | `Relaxed` load 读另一线程的 `Release` store |

#### 其他 UB

| **UB 子类** | **精确条件** | **Miri 检测** | **典型触发代码** |
|:---|:---|:---:|:---|
| **ABI 不匹配** | FFI 调用时参数类型/调用约定与声明不符 | ❌ | `extern "C"` 函数签名与 C 头不匹配 |
| **内联汇编（Inline Assembly）违规** | 汇编约束与实际副作用不符 | ❌ | `asm!("..." : "=r"(x))` 但实际修改内存 |
| **栈溢出** | 递归/大数组导致栈空间耗尽 | ⚠️（OS 信号） | 无限递归 |

> **来源**: [Rust Reference: Behavior considered undefined — 完整清单](https://doc.rust-lang.org/reference/behavior-considered-undefined.html) · [UCG Book: What is undefined behavior?] · [Ralf Jung Blog: The scope of unsafe]

#### UB 检测的不可判定性边界

```text
定理（UB 检测的停机问题归约）:
  判定"程序 P 是否触发 UB" 是不可判定的。
    ↓
  证明概要: 可将其归约为停机问题
    - 构造程序 P': "若原程序停机，则执行某个 UB 操作"
    - 判定 P' 是否触发 UB ⟺ 判定原程序是否停机
    - 由停机问题不可知 ⟹ UB 检测不可判定

  工程影响:
    - Miri 是**近似检测器**：它检测常见 UB 模式，但不保证发现所有 UB
    - Kani 等符号执行工具可覆盖更多路径，但仍受状态空间爆炸限制
    - 形式化证明（RustBelt/Iris）覆盖 safe 子集，unsafe 仍需人工验证
```

> **来源**: [Miri Book](https://github.com/rust-lang/miri) · [Kani Documentation: Verification bounds] · [Rice 1953 — Theorem: All non-trivial semantic properties are undecidable]

### 2.3 Safety Contract 责任矩阵
>

| **角色** | **责任** | **证明对象** | **工具支持** |
|:---|:---|:---|:---|
| **unsafe 实现者** | 保证 unsafe 块内部不触发 UB | 局部代码正确性 | Miri、Kani、审阅 |
| **safe 接口设计者** | 保证 safe API 不泄露 UB | 所有调用路径安全 | 类型系统（Type System）、测试 |
| **safe 用户** | 正确使用 safe API | 无需证明（编译器保证） | 编译器 |
| **unsafe trait 实现者** | 满足 trait 的 unsafe 契约 | 全局语义约束 | 文档、审阅 |

---

<!-- L3::理论根基 -->

## 三、形式化理论根基（Formal Foundation）

> 概念分类之后，需要从类型系统（Type System）视角理解 unsafe 的本质。unsafe 不是"关闭编译器"，而是在封闭证明系统中引入新的公理，并由程序员人工保证其一致性（Coherence）。
> **[Rustonomicon: The Safe/Unsafe Boundary](https://doc.rust-lang.org/nomicon/index.html)** Safe Rust 是封闭的证明系统；unsafe 是显式引入新公理并人工保证一致性（Coherence）的扩展。类比：Safe Rust = 欧氏几何，Unsafe = 非欧几何。💡 原创分析
> **来源: [Rustonomicon: The Safe/Unsafe Boundary](https://doc.rust-lang.org/nomicon/index.html)** Unsafe 不是关闭检查器，而是引入人工验证的公理。

### 3.1 Unsafe 作为公理缺口
>

```text
Safe Rust 类型系统是一个封闭的证明系统:
  公理: 所有权、借用、生命周期规则
  定理: 通过编译 = 满足安全保证

Unsafe 是公理系统的显式扩展:
  unsafe { ... } = "我在此区域引入新的公理，并人工保证其一致性"

类比数学:
  Safe Rust = 欧氏几何（5条公设封闭）
  Unsafe    = 非欧几何（修改平行公设，需重新证明一致性）
```

> **[Ralf Jung Blog (PLDI 2019)]** Rust 区分 Validity Invariant（编译器/优化器依赖的底层约束，违反即 UB）与 Safety Invariant（Safe API 要求的高层约束，违反可能通过 safe API 触发 UB）。✅ 已验证
> **[Rustonomicon: What is unsafe?](https://doc.rust-lang.org/nomicon/what-unsafe-does.html)** unsafe 代码的核心责任：不破坏 Validity Invariant（对编译器负责），维护 Safety Invariant（对 safe 用户负责）。✅ 已验证

### 3.2 Safety Invariant vs Validity Invariant

**Safe ↔ Unsafe 边界状态机（Mermaid stateDiagram）**:

```mermaid
stateDiagram-v2
    [*] --> Safe: 编写 Rust 代码
    Safe --> Safe: 常规操作

    Safe --> UnsafeBlock: 进入 unsafe { }
    note right of UnsafeBlock
        编译器暂停检查
        程序员承担证明责任
    end note

    UnsafeBlock --> Safe: 块结束
    UnsafeBlock --> UB: 违反安全契约

    Safe --> UnsafeFn: 调用 unsafe fn
    note right of UnsafeFn
        调用方需验证
        被调用方的不变式
    end note

    UnsafeFn --> Safe: 返回安全值
    UnsafeFn --> UB: 前置条件不满足

    Safe --> UnsafeTrait: impl unsafe Trait
    note right of UnsafeTrait
        全局影响:
        所有使用该 Trait 的代码
        都依赖此 impl 的正确性
    end note

    UnsafeTrait --> Safe: 编译通过
    UnsafeTrait --> UB: 契约违反

    UB --> [*]: 未定义行为发生

    state Safe {
        [*] --> TypeSafe: 类型检查
        TypeSafe --> MemorySafe: 借用检查
        MemorySafe --> ThreadSafe: Send/Sync 检查
        ThreadSafe --> [*]: 编译通过
    }
```

> **认知功能**:
> 将 Safe/Unsafe 边界建模为显式状态转换系统，帮助读者建立"编译器保护态→人工证明态→错误态"的三态直觉。
> 建议在编写 unsafe 代码前对照此图确认当前所处状态。
> 关键洞察：所有进入 Unsafe 的转移必须有 `unsafe` 关键字标记，且转移前提是程序员人工验证安全契约。[💡 原创分析](../../00_meta/00_framework/methodology.md)
> [来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/index.html)]
> **思维表征说明**:
> `stateDiagram-v2` 将 Safe/Unsafe 边界建模为**状态转换系统**——Safe 是「编译器保护态」，UnsafeBlock/UnsafeFn/UnsafeTrait 是「人工证明态」，UB 是「不可恢复的错误态」。
> 关键洞察：从 Safe 进入 Unsafe 的每次转移都必须有**显式标记**（`unsafe` 关键字），且转移条件是「程序员已验证安全契约」。
> 这与 `graph TD` 流程图（展示知识结构）形成互补——状态机图展示的是**运行时（Runtime）/编码时的状态约束**。
> [来源: Rustonomicon §1; [RFC 2585](https://rust-lang.github.io/rfcs//2585-unsafe-block-in-unsafe-fn.html); Rust Reference §19]

```text
Rust 区分两种不变式:

Validity Invariant（有效性不变式）:
  - 编译器和优化器依赖的底层约束
  - 违反 = 立即 UB
  - 例: bool 必须是 0 或 1，引用必须非空对齐

Safety Invariant（安全性不变式）:
  - Safe API 的用户必须维护的高层约束
  - 违反 = 可能通过 safe API 触发 UB
  - 例: Vec 的 len ≤ cap，String 是有效 UTF-8

unsafe 代码的责任:
  - 不破坏 Validity Invariant（对编译器负责）
  - 维护 Safety Invariant（对 safe 用户负责）
```

---

<!-- L3::认知路径 -->

## 四、认知路径（Cognitive Path）

> 理论需要转化为可遵循的认知路径。以下六步递进从"为什么"到"什么时候"，构建完整的 unsafe 决策思维链。

### Step 1 — 动机：为什么需要 unsafe？

静态分析是保守的。编译器为了绝对安全，会拒绝一些**实际上安全但无法自动证明**的程序。unsafe 是程序员对编译器的显式声明："此处交给我人工验证。"

> **[TRPL Ch19.1](https://doc.rust-lang.org/book/ch19-01-unsafe-rust.html)** Safe Rust = 编译器可证明安全的程序集合；Unsafe Rust = 需要人工证明安全性的操作集合。✅ 已验证

### Step 2 — 机制：unsafe 到底关掉了什么？

`unsafe` **不关闭类型系统**。类型检查、泛型（Generics）约束、trait bound 检查仍在运行。它仅关闭编译器无法自动验证的**特定检查**：

- 裸指针解引用的生命周期（Lifetimes）/别名追踪
- FFI 外部函数契约验证
- `unsafe trait`（如 Send/Sync）的语义约束验证
- `union` 活跃变体检査

### Step 3 — 保证：怎么保证 unsafe 代码安全？

三层防御体系：

1. **最小化范围**：unsafe 块尽可能小
2. **Safety Contract**：文档化所有前置条件、后置条件和不变量
3. **安全抽象**：`unsafe 实现 + safe 接口 + 人工证明内部正确`

> **[Rustonomicon](https://doc.rust-lang.org/nomicon/index.html)** 安全抽象定理：unsafe 实现 + safe 接口 + 人工证明 = 用户无需了解内部 unsafe 即可安全使用。✅ 已验证

### Step 4 — 边界：UB 和安全的边界在哪？

| 不变量 | 违反后果 | 责任对象 |
|:---|:---|:---|
| **Validity Invariant** | 立即 UB | unsafe 实现者 → 编译器 |
| **Safety Invariant** | 可能通过 safe API 触发 UB | safe 接口设计者 → 用户 |

边界判定原则：**不破坏 Validity Invariant**是底线；**维护 Safety Invariant**是安全抽象的契约。

### Step 5 — 验证：Miri 能检测什么？

```text
Miri (Rust 解释器) 可检测:
  ✅ 悬垂指针解引用
  ✅ 越界访问
  ✅ 未对齐访问
  ✅ 数据竞争（部分）
  ✅ 无效枚举值
  ❌ 所有可能的 UB（停机问题）
  ❌ 与硬件相关的行为（如内联汇编）
  ❌ FFI 边界错误（外部代码不透明）
```

> 详见 §7.2 的完整覆盖范围表格与 `MIRIFLAGS` 使用方式。
> **[Miri Documentation: Limitations]** Miri 无法检测所有 UB（停机问题不可解），且不支持与硬件相关的行为（如内联汇编（Inline Assembly））。 ✅ 已验证
> **[Stacked Borrows — POPL 2021](https://plv.mpi-sws.org/rustbelt/stacked-borrows/)** Miri implements the Stacked Borrows operational semantics for dynamic UB detection, later relaxed by Tree Borrows to cover more legitimate unsafe patterns. ✅ 已验证

### Step 6 — 决策：什么时候必须写 unsafe？

仅当 Safe Rust 无法表达需求，且已确认无 safe 替代方案时：

- **FFI 调用**（C 库互操作）
- **极致性能优化**（已 profile 确认瓶颈）
- **底层内存布局控制**（自定义数据结构、零拷贝）
- **实现 unsafe trait**（Send/Sync 等全局语义标记）

```text
六步递进总览:

为什么需要 unsafe？ ──→ unsafe 到底关掉了什么？ ──→ 怎么保证 unsafe 代码安全？
        │                       │                       │
        ▼                       ▼                       ▼
   静态分析保守性          仅关闭特定检查            Safety Contract
   某些合法程序            （借用/别名/FFI）          + 人工证明
   无法被自动证明

UB 和安全的边界在哪？ ──→ Miri 能检测什么？ ──→ 什么时候必须写 unsafe？
        │                       │                       │
        ▼                       ▼                       ▼
   Validity vs Safety       动态检测子集            Safe Rust 无法实现
   Invariant 二分           （非完备）               且已确认无替代方案
```

> **[Rustonomicon](https://doc.rust-lang.org/nomicon/index.html)** 类比：unsafe 像手术刀——精确、强大，但需要专业训练和明确的安全协议。✅ 已验证
> **[TRPL Ch19.1](https://doc.rust-lang.org/book/ch19-01-unsafe-rust.html)** 反直觉点：unsafe 块不意味着代码一定有 UB，而是意味着编译器不再保证无 UB。✅ 已验证
> **[Ralf Jung Blog + RustBelt]** 形式化过渡路径：编译器不检查 → 安全契约 → 公理化语义 → RustBelt 逐步覆盖。🔍 待验证（RustBelt 对 unsafe 的覆盖仍在进行中）

**认知脚手架**:

- **类比**: `unsafe` 像"手术刀"——精确、强大，但需要专业训练和明确的安全协议。
- **反直觉点**: `unsafe` 块**不意味着**代码一定有 UB，而是意味着**编译器不再保证**无 UB。
- **形式化过渡**: 从"编译器不检查" → "安全契约" → "公理化语义" → "RustBelt 对 unsafe 的逐步覆盖"。 💡 原创分析

### 4.1 国际课程与论文对齐

| 来源 | 核心内容 | 与本文件对应 |
|:---|:---|:---|
| **[CMU 17-350: Safe Systems Programming]** | Unsafe、FFI、UB 边界、Safety Contracts | L3 Unsafe 完整覆盖 |
| **[CMU 17-363: Programming Language Pragmatics]** | unsafe 作为类型系统边界突破 | 形式化视角 |
| **[Rustonomicon](https://doc.rust-lang.org/nomicon/index.html)** | Unsafe 编程规范、安全抽象设计 | 实践指南 |
| **[Stacked Borrows](https://plv.mpi-sws.org/rustbelt/stacked-borrows/)** | 别名模型操作语义 | 内存模型 §3 |
| **[Tree Borrows — PLDI 2025](https://perso.crans.org/vanille/treebor/)** | 更宽松的别名模型 | Miri 检测基础 |
| **[RustHornBelt: PLDI 2022]** | unsafe 代码功能正确性验证 | 形式化验证 |

---

<!-- L3::思维导图 -->

## 五、思维导图（Mind Map）

> 以下思维导图提供 Unsafe Rust 的全局知识结构，覆盖操作分类、UB 类型、安全抽象、验证工具与常见模式。

```mermaid
graph TD
    A[Unsafe Rust] --> B[unsafe 操作]
    A --> C[UB 分类]
    A --> D[安全抽象]
    A --> E[验证工具]
    A --> F[常见模式]

    B --> B1[裸指针 *const/*mut]
    B --> B2[unsafe fn / unsafe trait]
    B --> B3[extern 函数]
    B --> B4[union 访问]
    B --> B5[static mut]

    C --> C1[内存: UAF, OOB, 对齐]
    C --> C2[类型: 无效枚举, transmute]
    C --> C3[并发: 数据竞争]
    C --> D1[Validity Invariant]
    C --> D2[Safety Invariant]

    D --> D3[unsafe 实现 + safe 接口]
    D --> D4[Document Safety Contract]

    E --> E1[Miri]
    E --> E2[Kani]
    E --> E3[ASan / MSan]
    E --> E4[Creusot]

    F --> F1[FFI 边界]
    F --> F2[自定义数据结构]
    F --> F3["Send/Sync 实现: Send = 可跨线程转移所有权(move), Sync = 可跨线程共享引用"]
    F --> F4[零拷贝解析]
```

> **认知功能**: 提供 Unsafe Rust 的知识全景导航，帮助读者在五大知识分支间快速定位概念归属。建议作为"目录式"参考，在学习或查阅时先浏览此图建立全局坐标。关键洞察：unsafe 的核心挑战不在"操作能力"而在"安全抽象"——unsafe 实现 + safe 接口的封装才是工程实践的正交分解点。[💡 原创分析](../../00_meta/00_framework/methodology.md)
> [来源: [TRPL: Ch19.1](https://doc.rust-lang.org/book/ch19-01-unsafe-rust.html)]
> 思维导图展示了 Unsafe Rust 的知识全景，但 unsafe 代码与内存模型的精确交互需要更深入的别名语义。以下两节引入 Stacked Borrows 与 Tree Borrows 两种操作语义模型，建立 unsafe 代码在运行时（Runtime）的权限边界。

<!-- L3::别名模型 -->

### 5.5 Stacked Borrows 操作语义

> **权威来源**: Jung et al., *Stacked Borrows: An Aliasing Model for Rust*, POPL 2019
> **状态**: ⚠️ **历史模型** — Tree Borrows 自 2024 年末起成为 Miri 默认别名模型。Stacked Borrows 退为 `-Zmiri-stacked-borrows` 兼容选项。
> **核心思想**: 为每个内存位置维护一个访问权限栈（Borrow Stack），在解释执行时动态验证引用与裸指针的别名规则是否被违反。

**动机**：Rust 的引用规则（`&T` 不可变共享、`&mut T` 唯一可变）在编译时静态检查，但 `unsafe` 代码中的裸指针可以绕过这些检查。Stacked Borrows 提供了**第一代**操作语义模型，使 Miri 能够动态检测别名违规。尽管其严格性导致部分合法模式被误判，但理解 Stacked Borrows 仍是理解 Tree Borrows 演进的基础。

**核心概念：Borrow Stack**

每个内存位置关联一个权限栈，栈中的每个条目代表一种**访问权限**（Permission）：

| 权限类型 | 符号 | 创建方式 | 语义 |
|:---|:---|:---|:---|
| **Unique** | `Unique` | `&mut T` | 独占读写；不允许其他活跃引用/指针访问同一位置 |
| **SharedReadOnly** | `ShrRo` | `&T` | 只读共享；允许任意多个 `&T` 同时存在 |
| **SharedReadWrite** | `ShrRw` | `UnsafeCell` 内部可变借用（Mutable Borrow） | 允许读写，但不保证独占性 |
| **Foreign** | `Fr` | `*const T` / `*mut T`（裸指针） | 无别名保证；与栈中所有权（Ownership）限兼容，但会触发弹栈 |

**规则**

1. **`&T` 创建 SharedReadOnly**：当通过引用读取时，在栈顶压入 `ShrRo`。多个 `&T` 可共存。
2. **`&mut T` 创建 Unique**：当通过可变引用（Mutable Reference）访问时，在栈顶压入 `Unique`。如果栈顶已存在不兼容权限（如另一个 `Unique`），则触发 UB。
3. **裸指针创建 Foreign**：从引用转换而来的裸指针获得 `Foreign` 权限。它不享有别名保证。
4. **失效规则（Pop）**：当新访问与**栈顶**权限不兼容时，不断 pop 栈顶，直到栈顶兼容或栈空。如果最终仍不兼容，则触发 UB。

**代码示例：合法代码**

```rust
fn stacked_borrows_legal() {
    let mut x = 0i32;
    let r1 = &mut x;      // 栈: [Unique(r1)]
    *r1 = 1;
    let r2 = &*r1;        // 栈: [Unique(r1), ShrRo(r2)]
    println!("{}", r2);   // 读取 ShrRo，合法
    // r2 生命周期结束，弹出 ShrRo
    *r1 = 2;              // 回到 Unique(r1)，合法
}
```

**代码示例：触发 UB**

```rust
fn stacked_borrows_ub() {
    let mut x = 0i32;
    let r1 = &mut x;          // 栈: [Unique(r1)]
    let raw = r1 as *mut i32; // raw 获得 Foreign，但 r1 的 Unique 仍在栈顶
    let r2 = &mut x;          // ❌ 新 Unique(r2) 与栈顶 Unique(r1) 不兼容
                              //    弹出 Unique(r1) → raw 也失效
    unsafe {
        *raw = 1;             // UB! raw 已被弹出，悬垂/失效
    }
}
```

> **注意**：上面的简化示例在最新编译器中可能因优化而表现不同，但 Miri 在解释模式下会精确追踪 Borrow Stack。
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/introduction.html)]

**Borrow Stack 状态变化图**

```mermaid
graph LR
    S0["栈: [Root]"] -->|&mut x → r1| S1["栈: [Root, Unique(r1)]"]
    S1 -->|&*r1 → r2| S2["栈: [Root, Unique(r1), ShrRo(r2)]"]
    S2 -->|r2 结束| S3["栈: [Root, Unique(r1)]"]
    S3 -->|&mut x → r3| S4{"兼容?"}
    S4 -->|是| S5["栈: [Root, Unique(r3)]"]
    S4 -->|否<br/>Unique 冲突| S6["弹出 Unique(r1)"]
    S6 --> S7["栈: [Root, Foreign(raw)]"]
    S7 -->|*raw| S8["✅ 合法"]
    S6 -->|弹出到 Root<br/>raw 也失效| S9["❌ UB: raw 失效"]
```

> **认知功能**: 将 Stacked Borrows 的抽象规则转化为可视化的栈状态推演工具，帮助读者逐行追踪代码执行时的权限变化。建议在遇到 Miri 别名违规报错时，用此图手动复盘 Borrow Stack 的演变过程。关键洞察：裸指针的 `Foreign` 权限不享有别名保证——当新的 `Unique` 与栈顶冲突时，裸指针可能随着 pop 操作一起失效。[💡 原创分析](../../00_meta/00_framework/methodology.md)
> [来源: [Rust Reference: Unsafe Rust](https://doc.rust-lang.org/reference/unsafe-blocks.html)]
> Stacked Borrows 提供了直观的栈式别名模型，但其严格性导致部分合法 unsafe 模式被误判。Tree Borrows 在此基础上放宽约束，形成更贴近实际需求的树形结构。

<!-- L3::TreeBorrows -->

### 5.6 Tree Borrows 演进

> **权威来源**: Jung & Villani, *Tree Borrows*, 2023
> **层级标注**: `L3::别名模型` → `L4::RustBelt` 放宽前提 · `L1::借用` 重叠读取扩展

**动机**：Stacked Borrows 对许多**合法的 unsafe 模式**过于严格。例如，某些链表操作、自引用结构、以及从同一原始指针（Raw Pointer）派生出的多个只读指针的交替使用，在 Stacked Borrows 下会被判定为 UB，但它们在直觉上是安全的。

**核心变化：从栈到树**

Tree Borrows 用**树形结构**替代线性栈：

- **根节点（Root）**：原始指针（Raw Pointer）（最初分配内存时获得）
- **子节点（Child）**：从父节点派生的借用（Borrowing）分支
- **路径兼容**：两个借用（Borrowing）是否冲突取决于它们在树中的**路径关系**，而不仅仅是时间顺序

关键改进：

| 特性 | Stacked Borrows | Tree Borrows |
|:---|:---|:---|
| 结构 | 线性栈（LIFO） | 树（父子路径） |
| 节点类型 | `Unique`/`SharedReadOnly`/`SharedReadWrite`/`Foreign` | `Reserved`/`Active`/`Frozen`/`Disabled` |
| 重叠读取 | 严格时序依赖 | 支持来自不同路径的多个 `&T` |
| 裸指针宽容度 | 低（容易弹栈失效） | 高（保留更多合法模式） |
| 链表/自引用 | 常被误判为 UB | 覆盖更多合法模式 |
| 重借用（reborrow） | 按时间顺序失效 | 按路径兼容性判断 |
| `UnsafeCell` 交互 | Foreign 标签限制 | 更精确的路径追踪 |
| Miri 默认 | ❌（曾默认） | ✅（2023 年后默认） |
| RustBelt 验证 | 已部分证明 | 🔍 待完整证明 |

**精确对比：代码模式覆盖**

| 代码模式 | Stacked Borrows | Tree Borrows | 状态 |
|:---|:---|:---|:---|
| 交替使用两个 `&T`（同一原始指针（Raw Pointer））| ❌ UB | ✅ 安全 | Tree Borrows 更精确 |
| `get_or_insert` 模式（先读后备变）| ❌ UB | ✅ 安全 | Polonius + Tree Borrows |
| Lending Iterator（自引用迭代器）| ❌ UB | ✅ 安全 | GATs + Tree Borrows |
| 链表内部可变性 | ⚠️ 受限 | ✅ 更宽松 | 路径兼容 |
| 简单 `Box::into_raw`/`from_raw` | ✅ 安全 | ✅ 安全 | 两者一致 |
| `mem::swap` 两个 `&mut T` | ✅ 安全 | ✅ 安全 | 两者一致 |

**与 RustBelt 的关系**

| 维度 | Stacked/Tree Borrows | RustBelt |
|:---|:---|:---|
| **类型** | 操作语义（Operational Semantics） | 逻辑关系（Logical Relation） |
| **目标** | 定义"哪些程序行为是 UB" | 证明"类型系统保证内存安全（Memory Safety）" |
| **工具** | Miri 动态检查 | Iris/Coq 形式化证明 |
| **关系** | 为 RustBelt 提供**执行层面的 UB 定义** | 为别名模型提供**类型安全定理** |

> **[Ralf Jung Blog]** Tree Borrows 是向 RustBelt 逐步对齐的桥梁：操作语义定义了 Miri 可检测的边界，而 RustBelt 试图证明 Safe Rust 在该边界内永远不会触发 UB。🔍 待验证（RustBelt 对 unsafe 的完整覆盖仍在进行中）
> **跨层映射**: `L3::别名模型` ↔ [`L1::借用规则`](../../01_foundation/01_ownership_borrow_lifetime/02_borrowing.md) 静态检查 · [`L4::RustBelt`](../../04_formal/02_separation_logic/01_rustbelt.md) 形式化证明
> 理解了别名模型的操作语义后，我们可以将 unsafe 的决策从"直觉判断"转化为"规则判定"。以下决策树提供工程实践中的判别工具。

---

<!-- L3::决策树 -->

## 六、决策/边界判定树（Decision / Boundary Tree）

> 将知识结构转化为工程决策能力。本节提供三类决策工具：是否需要 unsafe 的判别、UB 边界判定、以及四个常见反命题的澄清。
> **来源: [TRPL Ch19.1](https://doc.rust-lang.org/book/ch19-01-unsafe-rust.html)** 决策树帮助判断是否真的需要 unsafe。

### 6.1 "我需要用 unsafe 吗？" 决策树

```mermaid
graph TD
    Q1[Safe Rust 能实现需求?] -->|是| A1[不要用 unsafe]
    Q1 -->|否| Q2[需求是 FFI 调用?]
    Q2 -->|是| A2[用 unsafe 封装 FFI]
    Q2 -->|否| Q3[需求是极致性能优化?]
    Q3 -->|是| Q4[profile 确认瓶颈?]
    Q3 -->|否| Q5[需求是底层内存控制?]
    Q4 -->|是| A3[用 unsafe，配合基准测试]
    Q4 -->|否| A1
    Q5 -->|是| A4[用 unsafe，最小化范围]
    Q5 -->|否| A1

    A1[Safe Rust 优先]
    A2[unsafe FFI 边界]
    A3[性能关键路径]
    A4[内存布局控制]
```

> **认知功能**: 工程决策判别工具，将"是否使用 unsafe"的模糊直觉转化为结构化的问题分支。建议在开始任何底层实现前，先按此树自顶向下验证是否真的没有 safe 替代方案。关键洞察：四条通往 unsafe 的路径（FFI、性能优化、内存布局、unsafe trait）中，"性能优化"路径必须附加 `profile` 确认——未经验证的性能假设是 unsafe 滥用的首要根源。[💡 原创分析](../../00_meta/00_framework/methodology.md)
> [来源: [Rust Reference: Behavior considered undefined](https://doc.rust-lang.org/reference/behavior-considered-undefined.html)]

### 6.2 UB 边界判定

```mermaid
graph TD
    B1[解引用可能为 null 的裸指针] -->|运行时| E1[UB: 段错误 / 任意行为]
    B2[创建悬垂裸指针] -->|编译合法| W1[⚠️ 仅在解引用时 UB]
    B3[transmute 无关类型] -->|编译合法| E2[UB: 类型混淆 / 对齐错误]
    B4[unsafe impl Send for Rc<T>] -->|编译合法| E3[UB: 数据竞争]
    B5[读取未初始化内存] -->|运行时| E4[UB: 读取任意值]
```

> **认知功能**: 快速识别五类常见操作的 UB 风险边界，将"编译通过"与"运行安全"脱钩。建议在代码审查时对照此图检查 unsafe 操作是否被正确分类。关键洞察：编译器对 unsafe 操作的合法性检查极为有限——`unsafe impl Send` 和 `transmute` 都能编译通过，但前者可能引发数据竞争，后者直接导致类型混淆 UB。[💡 原创分析](../../00_meta/00_framework/methodology.md)
> [来源: [Rustonomicon: What is unsafe?](https://doc.rust-lang.org/nomicon/meet-safe-and-unsafe.html)]

### 6.3 反命题决策树

反命题用于澄清 unsafe Rust 的常见误解。每个决策树从**错误命题**出发，通过条件分支到达正确结论。

#### 反命题 1: "unsafe 块内没有安全检查"

```mermaid
graph TD
    P1["❌ 命题: unsafe 块内没有安全检查"] --> Q1{"类型检查是否运行?"}
    Q1   -->|"✅ 仍运行"| A1["类型系统未关闭<br/>泛型约束、trait bound 仍生效"]
    Q1   -->|"仅特定检查关闭"| Q2{"哪些检查关闭?"}
    Q2   -->|"裸指针解引用"| A2["借用检查器对 *const/*mut 不追踪"]
    Q2   -->|"FFI 调用"| A3["编译器不验证外部函数契约"]
    Q2   -->|"unsafe trait impl"| A4["编译器不验证 Send/Sync 语义"]

    style P1 fill:#f66,color:#fff
    style A1 fill:#6f6
    style A2 fill:#ff9
    style A3 fill:#ff9
    style A4 fill:#ff9
```

> **认知功能**: 概念校准工具，通过条件分支逐步拆解"unsafe 关闭所有检查"的常见误解。建议初学者在首次编写 unsafe 代码前阅读此图，建立"局部关闭而非全局关闭"的精确认知。关键洞察：`unsafe` 仅关闭编译器无法自动验证的特定检查（裸指针解引用、FFI 契约、trait 语义），类型系统、生命周期（Lifetimes）检查（对引用而言）和 trait bound 推导仍在正常运行。[💡 原创分析](../../00_meta/00_framework/methodology.md)
> [来源: [Rust Reference: Raw pointers](https://doc.rust-lang.org/reference/types/pointer.html)]
> **正确结论**: `unsafe` 不是关闭整个类型系统，而是**局部关闭**编译器无法自动验证的特定检查。类型检查、生命周期（Lifetimes）检查（对引用而言）仍在运行。

#### 反命题 2: "只要用了 unsafe 就会触发 UB"

```mermaid
graph TD
    P2["❌ 命题: 用 unsafe = 必然 UB"] --> Q1{"unsafe 块内是否违反 Validity Invariant?"}
    Q1   -->|"否"| Q2{"Safety Contract 是否完整?"}
    Q1   -->|"是"| A1["UB 触发"]
    Q2   -->|"是"| A2["✅ 正确使用 unsafe 是安全的"]
    Q2   -->|"否"| A3["可能通过 safe API 泄露 UB"]

    style P2 fill:#f66,color:#fff
    style A1 fill:#f66,color:#fff
    style A2 fill:#6f6
    style A3 fill:#f96
```

> **认知功能**: 建立"正确使用 unsafe 是安全的"这一核心信心，通过 Validity Invariant 和 Safety Contract 的双层检查消除对 unsafe 的恐惧。建议在审查标准库源码 unsafe 实现时，用此图验证其安全抽象是否满足两层条件。关键洞察：Rust 标准库（Vec、String、Arc 等）全部是 unsafe 实现 + safe 接口——unsafe 的危险性不在于其本身，而在于契约的完整性和证明的严谨性。[💡 原创分析](../../00_meta/00_framework/methodology.md)
> [来源: [Rust Reference: FFI](https://doc.rust-lang.org/reference/items/external-blocks.html)]
> **正确结论**: 正确使用 unsafe（满足所有契约、不破坏不变量）**不会**触发 UB。Rust 标准库大量底层代码（Vec、String、Arc）都是 unsafe 实现 + safe 接口。

#### 反命题 3: "raw pointer 和引用等价"

```mermaid
graph TD
    P3["❌ 命题: raw pointer ≡ 引用"] --> Q1{"是否有生命周期检查?"}
    Q1   -->|"引用: ✅ 有"| A1["编译器保证生命周期内有效"]
    Q1   -->|"裸指针: ❌ 无"| Q2{"是否有对齐保证?"}
    Q2   -->|"引用: ✅ 自动对齐"| A2["&T 必须对齐且非空"]
    Q2   -->|"裸指针: ❌ 无"| Q3{"是否有有效值保证?"}
    Q3   -->|"引用: ✅ 必须指向有效值"| A3["bool 必须是 0/1，enum 必须有效"]
    Q3   -->|"裸指针: ❌ 无"| A4["可指向任意位模式"]

    style P3 fill:#f66,color:#fff
    style A1 fill:#6f6
    style A2 fill:#6f6
    style A3 fill:#6f6
    style A4 fill:#ff9
```

> **认知功能**: 通过三维度对比（生命周期（Lifetimes）、对齐约束、有效值约束）建立裸指针与引用的本质差异认知。建议在将 `&T`/`&mut T` 转换为 `*const T`/`*mut T` 时，逐条核对此图中的保证缺失项。关键洞察：裸指针不仅是"没有生命周期检查的引用"，它在类型系统的所有三个核心假设（对齐、非空、有效值）上都不受保护，这是 `*ptr` 解引用比 `&*ptr` 危险得多的根本原因。[💡 原创分析](../../00_meta/00_framework/methodology.md)
> [来源: [Rustonomicon: FFI](https://doc.rust-lang.org/nomicon/ffi.html)]
> **正确结论**: 裸指针 `*const T` / `*mut T` **不是**引用（Reference） `&T` / `&mut T` 的等价物。差异体现在：**生命周期（Lifetimes）追踪**、**对齐约束**、**有效值约束**（Validity Invariant）三个方面。

#### 反命题 4: "FFI 调用总是安全的"

```mermaid
graph TD
    P4["❌ 命题: FFI 调用总是安全的"] --> Q1{"ABI 是否匹配?"}
    Q1   -->|"否"| A1["调用约定不匹配 → 栈损坏/崩溃"]
    Q1   -->|"是"| Q2{"内存布局是否兼容?"}
    Q2   -->|"否"| A2["#[repr(C)] 遗漏 → 字段偏移错误"]
    Q2   -->|"是"| Q3{"指针生命周期是否一致?"}
    Q3   -->|"否"| A3["C 返回悬垂指针 → UAF"]
    Q3   -->|"是"| Q4{"C 端是否遵守协议?"}
    Q4   -->|"否"| A4["数据竞争/内存篡改"]
    Q4   -->|"是"| A5["✅ FFI 调用可安全"]

    style P4 fill:#f66,color:#fff
    style A1 fill:#f66,color:#fff
    style A2 fill:#f66,color:#fff
    style A3 fill:#f66,color:#fff
    style A4 fill:#f96
    style A5 fill:#6f6
```

> **认知功能**: FFI 风险评估的层次化检查框架，将"外部代码是否可信"的模糊问题分解为 ABI、布局、生命周期（Lifetimes）、协议四个可验证的子问题。建议在每次添加 `extern` 函数声明或修改 `#[repr(C)]` 结构体（Struct）后，按此四层顺序自检。关键洞察：FFI 是 Rust 类型证明系统的完整公理缺口——编译器对 C 代码的假设为零，任何外部代码的"安全"都必须由程序员在四个维度上逐条人工保证。[💡 原创分析](../../00_meta/00_framework/methodology.md)
> [来源: [Miri Book](https://rustc-dev-guide.rust-lang.org/miri.html)]
> **正确结论**: FFI 是 Rust 形式系统的**公理缺口**。编译器无法验证外部代码，程序员必须人工保证 ABI 匹配、`#[repr(C)]` 布局一致、指针有效性和 C 端协议遵守。

---

<!-- L3::定理链 -->

## 七、定理推理链（Theorem Chain）

> 决策树背后需要定理支撑。本节建立从安全抽象到验证边界的推理链，并通过一致性矩阵将所有定理联结成网。
> **[Rustonomicon: Safe Abstractions](https://doc.rust-lang.org/nomicon/index.html)** 安全抽象定理：unsafe 实现 + safe 接口 + 人工证明 = 用户无需了解内部 unsafe 即可安全使用。Rust 标准库的核心类型（Vec, String, HashMap 等）均基于此模式构建。✅ 已验证
> **[Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)** 封装 unsafe 的 safe API 必须文档化 Safety Contract，且对所有合法输入保证不触发 UB。✅ 已验证

### 7.1 安全抽象定理

```text
前提 1: unsafe 块实现了某些底层操作
前提 2: safe 接口封装了 unsafe 块，并限制了输入
前提 3: 人工证明: 对所有合法 safe 输入，unsafe 块不触发 UB
    ↓
定理: safe 接口是"可信的"——用户无需了解内部 unsafe 即可安全使用
    ↓
推论: Rust 标准库的大部分功能基于 unsafe 实现，但接口是 safe 的
      例: Vec, String, HashMap, Rc, Arc, Box 都有 unsafe 内部实现
```

> **[Miri Documentation](https://github.com/rust-lang/miri)** Miri 是 Rust 的解释型 MIR 执行器，可动态检测悬垂指针、越界访问、未对齐访问、数据竞争（部分）和无效枚举（Enum）值等 UB。✅ 已验证
> **[Miri Documentation: Limitations]** Miri 无法检测所有 UB（停机问题不可解），且不支持与硬件相关的行为（如内联汇编（Inline Assembly））。✅ 已验证

### 7.2 Miri 的验证边界

> **权威来源**: [Miri Book](https://rustc-dev-guide.rust-lang.org/miri.html)
> **层级标注**: `L3::动态验证` → `L1::借用` Miri 可检测别名违规 · `L4::RustBelt` 操作语义动态近似

Miri 是 Rust 的 MIR（Mid-level IR）解释器，其核心功能之一是作为 **Stacked Borrows / Tree Borrows 的动态检查器**。它在解释执行时维护每个内存位置的 Borrow Stack（或 Borrow Tree），实时检测别名违规、悬垂指针、未初始化读取等 UB。

**覆盖范围表格**

| 问题类型 | Miri 检测 | 说明 | 工具补充 |
|:---|:---:|:---|:---|
| **别名违规** | ✅ | Stacked/Tree Borrows 动态追踪 | — |
| **未初始化内存读取** | ✅ | `MaybeUninit` 状态追踪 | — |
| **悬空指针解引用** | ✅ | 分配-释放追踪 | — |
| **越界访问** | ✅ | 内存边界检查 | — |
| **未对齐访问** | ✅ | 对齐约束验证 | — |
| **无效枚举值** | ✅ | discriminant 合法性检查 | — |
| **数据竞争** | ❌ | Miri 为单线程解释器 | [Loom](https://docs.rs/loom) |
| **死锁** | ❌ | 活性性质不可判定 | 静态分析 / 模型检测 |
| **逻辑错误** | ❌ | 功能正确性超出范围 | 测试 / [Kani](https://github.com/model-checking/kani) |
| **硬件相关行为** | ❌ | 如内联汇编（Inline Assembly）、SIMD | 真机测试 |
| **FFI 边界错误** | ❌ | 外部代码不透明 | 人工审查 |

**使用方式**

```bash
# 默认使用 Tree Borrows（推荐）
MIRIFLAGS=-Zmiri-tree-borrows cargo miri test

# 显式使用 Stacked Borrows（旧行为）
MIRIFLAGS=-Zmiri-stacked-borrows cargo miri test

# 仅运行单个测试
MIRIFLAGS=-Zmiri-tree-borrows cargo miri test --test integration test_name
```

> **[Miri Documentation: Limitations]** Miri 无法检测所有 UB（停机问题不可解），且不支持与硬件相关的行为（如内联汇编（Inline Assembly））。✅ 已验证
> **[Miri Book](https://github.com/rust-lang/miri)** Tree Borrows 自 2024 年末起成为 Miri 的**默认**别名模型（原 `-Zmiri-tree-borrows` 不再需显式指定；Stacked Borrows 退为 `-Zmiri-stacked-borrows` 兼容选项）。PLDI 2025 Distinguished Paper 正式确立了 Tree Borrows 作为 Rust 别名假设工业级标准的地位。✅ 已验证

### 7.2b Miri 检测算法原理与编译器优化关系

> **来源: [Miri Book](https://github.com/rust-lang/miri)** Miri 不是普通解释器——它维护了一个与编译器优化假设一致的内存模型，因此其检测具有"如果 Miri 报错，则 rustc/LLVM 可能基于此做危险优化"的语义。
> **来源: [Miri Book](https://github.com/rust-lang/miri)** Miri 基于 MIR 解释执行，维护内存和别名模型的完整状态。

#### Miri 检测的核心算法

```text
Miri 解释执行循环:

  1. 读取下一条 MIR 指令
  2. 若指令涉及内存访问（load/store/retag）：
     a. 确定访问的内存位置 loc 和大小 size
     b. 确定访问的标签 tag（引用的 provenance）
     c. 查询该 loc 的 Borrow Stack / Borrow Tree 状态
     d. 根据 SB/TB 规则验证访问合法性
     e. 若不合法 → 报告 UB（panic + 堆栈跟踪）
  3. 若指令是函数调用：
     a. 若是 safe 函数 → 正常解释
     b. 若是 unsafe 函数 → 同样解释，但标记为 unsafe 上下文
     c. 若是 extern 函数 → 若提供 shim 则解释，否则 stub（默认 panic）
  4. 更新程序状态，继续下一条指令

关键数据结构:
  - Memory: HashMap<AllocId, Allocation>，每个 Allocation 含 bytes + relocations + borrow stack
  - Borrow Stack/Tree: 每个 Allocation 关联的别名追踪结构
  - Frame Stack: 调用栈，含局部变量和 resume 点
```

> **来源**: [Miri Book](https://github.com/rust-lang/miri) · [rustc-dev-guide: MIR interpretation] · [Miri src/machine.rs]
> **[LLVM LangRef: Function Attributes](https://llvm.org/docs/LangRef.html#function-attributes)** Miri 的检测与 LLVM 优化假设一一对应。

#### Miri 与编译器优化的关系

```text
为什么 Miri 的检测不是"过度敏感"？

  编译器优化假设（以 LLVM 为例）:
    - `noalias` 属性: &mut T 指向的内存不会被其他指针访问
    - `dereferenceable` 属性: &T 在生命周期内始终指向有效内存
    - `noundef` 属性: bool/enum/char 等类型的值始终在合法范围内

  Miri 的检测 = 这些优化假设的动态验证:
    - 悬垂指针 → LLVM 可能做 dead store elimination，导致值"消失"
    - 无效枚举值 → LLVM 可能将 match 优化为跳转表，非法 discriminant 跳转到任意位置
    - 数据竞争 → LLVM 可能重排内存操作，导致观察到不一致状态

  关键洞察:
    Miri 报错 ⟹ "该程序违反了 rustc/LLVM 的优化假设"
    这不等于"程序一定会崩溃"，但等于"程序行为不再由 Rust 语义定义"
```

> **来源**: [LLVM LangRef: Function Attributes — noalias, dereferenceable, noundef] · [Rustonomicon: What is undefined behavior?](https://doc.rust-lang.org/nomicon/index.html) · [Ralf Jung Blog: Why undefined behavior is scary]
> **[rustc-dev-guide: Miri flags](https://rustc-dev-guide.rust-lang.org/miri.html)** MIRIFLAGS 控制 Miri 的检测严格度和并发行为。

#### MIRIFLAGS 完整选项速查

```bash
# 别名模型
-Zmiri-tree-borrows          # Tree Borrows（默认，无需显式指定）
-Zmiri-stacked-borrows       # Stacked Borrows（兼容模式）

# 并发与隔离
-Zmiri-disable-isolation     # 允许文件系统/网络/环境变量访问
-Zmiri-preemption-rate=N     # 线程抢占频率（默认 100，越低越确定式）
-Zmiri-seed=N                # 随机数种子（可重现的并发交错）

# 内存与检查严格度
-Zmiri-check-number-validity # 检查整数有效性（如 bool 必须是 0/1）
-Zmiri-tag-raw-pointers      # 为裸指针分配标签（更严格）
-Zmiri-permissive-provenance # 宽松来源模式（实验性）

# 其他
-Zmiri-ignore-leaks          # 不报告内存泄漏
-Zmiri-panic-on-unsupported  # 遇到不支持的操作时 panic 而非跳过
```

> **来源**: [Miri Book](https://github.com/rust-lang/miri) · [rustc-dev-guide: Miri flags]

---

### 7.3 定理一致性矩阵（⟹ 推理链）

| 编号 | 定理（前提 ⟹ 结论） | 推理链 | 失效条件 | 典型场景 | 层级标注 |
|:---|:---|:---|:---|:---|:---|
| **L1** | `unsafe {}` 或 `unsafe fn` ⟹ 程序员承担不变量责任 | 标记存在 ⟹ 编译器移交证明义务 ⟹ 程序员手动验证局部不变量 | 安全契约遗漏或证明不完整 | 任何 unsafe 块入口 | `L3::责任转移` |
| **L2** | raw pointer 解引用 ⟹ 绕过借用（Borrowing）检查器 | `*const T` / `*mut T` ⟹ 无生命周期（Lifetimes）检查 ⟹ 无别名追踪 ⟹ 程序员保证内存有效且合法别名 | 悬垂指针、未对齐、已释放、非法别名 | FFI、底层数据结构、自引用结构 | `L3::借用绕过` |
| **L3** | `unsafe fn` 调用 ⟹ 需满足函数安全契约 | 调用发生 ⟹ 前置条件必须成立 ⟹ 否则调用方触发 UB | 前置条件未验证即调用 | `std::ptr::read`、`std::mem::transmute` | `L3::契约调用` |
| **T1** | unsafe 不关闭类型系统 ⟹ 仅关闭特定检查 | `unsafe` 关键字 ⟹ 类型检查仍运行 ⟹ 仅裸指针/FFI/trait/union 等特定检查关闭 | 误以为类型系统完全失效、在 unsafe 内放松类型约束 | 泛型（Generics）在 unsafe 块内、trait bound 推导 | `L3::类型保持` |
| **T2** | FFI 边界 ⟹ 类型布局兼容性要求 | `extern "C"` ⟹ `#[repr(C)]` 保证布局一致 ⟹ ABI 调用约定匹配 ⟹ 调用行为可预期 | 布局不匹配、ABI 错误、字节序差异 | C 结构体（Struct）互操作、系统 API 调用 | `L3::FFI布局` |
| **T3** | Union 字段访问 ⟹ 程序员追踪活跃变体 | `union.field` ⟹ 编译器不检查活跃性 ⟹ 程序员保证读取的变体是最后写入的 | 读取未初始化/非活跃字段、类型混淆 | C 兼容解析、手动内存复用 | `L3::联合类型` |
| **C1** | 未定义行为条件 ⟹ Miri 可检测子集 | UB 触发 ⟹ Miri 解释执行 MIR ⟹ 检测内存/对齐/枚举（Enum）/别名违规 ⟹ 无法检测全部（停机问题不可解） | 依赖硬件行为、FFI 不透明调用、活性问题 | 测试阶段验证、CI 集成 Miri | `L3::动态验证` |
| **C2** | `unsafe impl Send/Sync` ⟹ 人工证明安全性 | trait 契约 ⟹ 全局语义约束 ⟹ 人工证明线程安全/无数据竞争 ⟹ 编译器信任并开放全局使用 | 实际非线程安全、内部可变性未同步 | `Arc<T>`、自定义外部句柄、FFI 包装 | `L3::并发契约` |
| **C3** | `static mut` 修改 ⟹ 数据竞争风险 | 可变静态变量 ⟹ 无所有权（Ownership）保护 ⟹ 多线程同时访问 ⟹ 数据竞争（UB） | 未同步访问、跨线程读写无原子保护 | 全局状态（应极力避免使用 `static mut`） | `L3::静态可变` |
| **C4** | 内联汇编（Inline Assembly） `asm!` ⟹ 完全人工验证 | 汇编指令 ⟹ 编译器无分析能力 ⟹ 程序员负责所有副作用、内存模型、寄存器约定 | 任意错误（完全不受控） | 极致优化、内核代码、特殊指令 | `L3::汇编边界` |

> **[Rustonomicon](https://doc.rust-lang.org/nomicon/index.html)** 一致性说明: unsafe 领域的定理不依赖 L4 形式化——它们处于证明范围之外。Miri 提供动态检测作为近似验证手段。RustBelt 正在扩展以覆盖部分 unsafe 模式。✅ 已验证
> **[🔍 待验证]** RustBelt 对 unsafe 的完整形式化覆盖仍在活跃研究中，目前仅覆盖部分常见模式（如 Vec、Rc、Arc 等）。
> **跨层映射**: 本文件定理 ↔ `00_meta/inter_layer_map.md` §4.1 "内存安全（Memory Safety）完备性" · §6.1 "形式化保证失效条件"
> **新增跨层映射**: `L3::别名模型` ↔ [`L1::所有权`](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md) 运行时动态验证 · [`L4::RustBelt`](../../04_formal/02_separation_logic/01_rustbelt.md) 操作语义实例与逻辑关系

---

<!-- L3::示例 -->

## 八、示例与反例（Examples & Counter-examples）

> 定理需要通过代码验证。本节提供正确示例（安全抽象模式）与反例（常见 UB 触发模式），以及 Stacked Borrows 的边界极限测试。

### 8.1 正确示例：安全封装裸指针（Vec 简化版）

```rust,ignore
// ✅ 正确: unsafe 实现 + safe 接口
pub struct MyVec<T> {
    ptr: *mut T,
    len: usize,
    cap: usize,
}

impl<T> MyVec<T> {
    pub fn new() -> Self {
        Self { ptr: std::ptr::NonNull::dangling().as_ptr(), len: 0, cap: 0 }
    }

> **[Rust Reference: NonNull](https://doc.rust-lang.org/reference/introduction.html)** `std::ptr::NonNull<T>` evolved from the experimental `Unique<T>` and `Shared<T>` to provide a covariant raw pointer with a non-null invariant. ✅ 已验证

    pub fn push(&mut self, value: T) {
        if self.len == self.cap { self.grow(); }
        unsafe {
            // Safety: ptr 已分配且 len < cap
            std::ptr::write(self.ptr.add(self.len), value);
        }
        self.len += 1;
    }

    pub fn get(&self, index: usize) -> Option<&T> {
        if index >= self.len { return None; }
        Some(unsafe {
            // Safety: index < len，且所有 0..len 位置已初始化
            &*self.ptr.add(index)
        })
    }

    fn grow(&mut self) { /* 使用 alloc::GlobalAlloc 重新分配 */ }
}

impl<T> Drop for MyVec<T> {
    fn drop(&mut self) {
        unsafe {
            // Safety: 我们只释放自己分配的内存
            std::alloc::dealloc(/*...*/);
        }
    }
}
```

### 8.2 正确示例：手动实现 Send/Sync

```rust,ignore
// ✅ 正确: 为线程安全的外部类型实现 Send/Sync
pub struct MyHandle { raw: *mut libc::c_void }

// Safety: 底层 C 库保证此句柄可跨线程安全使用
unsafe impl Send for MyHandle {}
unsafe impl Sync for MyHandle {}
```

### 8.3 反例：悬垂裸指针（UB）

```rust,compile_fail
// ❌ 反例: 返回局部变量的裸指针
unsafe fn dangling_ptr() -> *const i32 {
    let x = 42;
    &x as*const i32  // x 在函数返回后被释放
}

fn main() {
    let ptr = dangling_ptr();
    println!("{}", unsafe { *ptr });  // UB: UAF
}
```

### 8.4 反例：transmute 滥用（UB）

```rust,compile_fail
// ❌ 反例: transmute 不相关类型
unsafe fn evil_transmute() {
    let f: f32 = 1.0;
    let b: bool = std::mem::transmute(f);  // UB! f32 位模式不全是有效 bool
}
```

### 8.5 反例：无效枚举值（UB）

```rust
// ❌ 反例: 创建无效枚举值
enum Color { Red, Green, Blue }

unsafe fn invalid_enum() -> Color {
    std::mem::transmute(42u8)  // UB! 42 不是有效变体索引
}
```

### 8.6 边界极限测试

> **[Miri Documentation](https://github.com/rust-lang/miri)** Miri 自 2024 年末起默认使用 Tree Borrows 别名模型；Stacked Borrows 退为 `-Zmiri-stacked-borrows` 兼容选项。Tree Borrows 更宽松，可覆盖更多合法 unsafe 模式。✅ 已验证
> **[Ralf Jung Blog]** Miri 无法检测 FFI 边界错误和活性性质（死锁/无限循环），因为 FFI 调用不透明且活性问题不可判定。✅ 已验证

#### 命题: "unsafe 代码可以安全地封装"

```mermaid
graph TD
    P["命题: unsafe 可安全封装"] --> Q1{"安全契约是否完整?"}
    Q1 -->|否| F1["反例: 前置条件遗漏<br/>→ 调用方传入非法参数 → UB"]
    Q1 -->|是| Q2{"unsafe 块内部假设是否成立?"}
    Q2 -->|否| F2["反例: 内部断言失败<br/>→ 即使调用方合法也 UB"]
    Q2 -->|是| Q3{"编译器优化是否破坏假设?"}
    Q3 -->|是| F3["反例: LLVM 优化假设内存模型<br/>→ 未定义行为被触发"]
    Q3 -->|否| T["定理成立: safe API 封装内部 unsafe<br/>✅ 契约完备性保证"]

    style F1 fill:#f66
    style F2 fill:#f66
    style F3 fill:#f96
    style T fill:#6f6
```

> **认知功能**: 安全抽象完备性的三层验证框架，帮助 unsafe 实现者和 safe 接口设计者检查"封装定理"是否成立。建议在提交包含 unsafe 的 PR 前，用此图审视：安全契约是否完整、内部假设是否成立、优化边界是否被突破。关键洞察：即使契约完备且内部逻辑正确，LLVM 优化假设与内存模型的不匹配仍可能触发 UB——这是 unsafe 代码最难察觉的失效模式。[💡 原创分析](../../00_meta/00_framework/methodology.md)
> [来源: [Rust Reference: MaybeUninit](https://doc.rust-lang.org/std/mem/union.MaybeUninit.html)]

#### 命题: "Miri 可以检测所有 UB"

| 条件 | 结果 | 说明 |
|:---|:---|:---|
| Stacked Borrows 模型 | ⚠️ 兼容模式 | 历史默认模型，部分合法模式被误判 |
| Tree Borrows 模型 | ✅ 默认检测 | 2024 年末起为 Miri 默认，覆盖更多合法模式 |
| 数据竞争 | ✅ 检测 | happens-before 分析 |
| 未初始化读取 | ✅ 检测 | `MaybeUninit` 追踪 |
| 悬垂指针解引用 | ✅ 检测 | 内存分配追踪 |
| 与外部代码交互 | ❌ 不检测 | FFI 调用不透明 |
| 无限循环 / 死锁 | ❌ 不检测 | 活性性质 |

#### 边界极限测试代码

```rust
// 边界: 未定义行为（UB）的微妙性

fn undefined_behavior_example() {
    let mut x = 0i32;
    let r1 = &mut x as *mut i32;
    let r2 = &mut x as *mut i32;  // 两个 &mut x 同时存在！但立即转为裸指针
    // 在 safe Rust 中这会被编译器拒绝，但在 unsafe 中...
    unsafe {
        *r1 = 1;
        *r2 = 2;  // UB! 两个 &mut 同时活跃（即使已转为裸指针）
    }
    // 根据 Stacked Borrows，从 &mut 创建的裸指针不能同时活跃
}

// 正确: 使用指针算术替代重叠引用
fn safe_raw_pointer() {
    let mut arr = [1, 2, 3, 4];
    let ptr = arr.as_mut_ptr();
    unsafe {
        let first = ptr;
        let second = ptr.add(2);  // 不重叠
        *first = 10;
        *second = 30;  // ✅ 合法
    }
}
```

---

<!-- L3::来源 -->

## 十、知识来源关系（Provenance）

| **论断** | **来源** | **可信度** |
|:---|:---|:---|
| unsafe 提供 5 种超能力 | [TRPL Ch19.1](https://doc.rust-lang.org/book/ch19-01-unsafe-rust.html) | ✅ |
| unsafe 是程序员承担证明责任 | [Rustonomicon](https://doc.rust-lang.org/nomicon/index.html) | ✅ |
| UB 清单 | [Rust Reference: Behavior considered undefined](https://doc.rust-lang.org/reference/behavior-considered-undefined.html) | ✅ |
| Validity vs Safety Invariant | [Rustonomicon: What is unsafe?](https://doc.rust-lang.org/nomicon/what-unsafe-does.html) · [Ralf Jung Blog] | ✅ |
| Miri 可检测部分 UB | [Miri Documentation](https://github.com/rust-lang/miri) | ✅ |
| 安全抽象封装 unsafe | [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/) | ✅ |
| Stacked Borrows / Tree Borrows | [POPL 2019] · [Miri 实验性文档] | ✅ |
| RustBelt 覆盖部分 unsafe 模式 | [PLDI 2017] · [后续论文] | 🔍 进行中 |
| 未定义行为（UB）定义 | [Wikipedia: Undefined behavior](https://en.wikipedia.org/wiki/Undefined_behavior) · [Rust Reference](https://doc.rust-lang.org/reference/introduction.html) | ✅ |
| 内存安全（Memory Safety） | [Wikipedia: Memory safety](https://en.wikipedia.org/wiki/Memory_safety) · [Rustonomicon](https://doc.rust-lang.org/nomicon/index.html) | ✅ |
| Miri 形式化验证工具 | [Miri Documentation](https://github.com/rust-lang/miri) · [Stacked Borrows — POPL 2021](https://plv.mpi-sws.org/rustbelt/stacked-borrows/) | ✅ |
| unsafe 操作分类 | [Rust Reference: Unsafe Rust](https://doc.rust-lang.org/reference/introduction.html) · [TRPL Ch19.1](https://doc.rust-lang.org/book/ch19-01-unsafe-rust.html) | ✅ |
| Validity Invariant | [Rustonomicon: What is unsafe?](https://doc.rust-lang.org/nomicon/what-unsafe-does.html) · [UCG Book] | ✅ |
| 裸指针语义 | [Rust Reference: Pointer types](https://doc.rust-lang.org/reference/introduction.html) · [std::ptr docs] | ✅ |
| FFI 边界安全 | [Rust Reference: External blocks](https://doc.rust-lang.org/reference/introduction.html) · [Rustonomicon: FFI](https://doc.rust-lang.org/nomicon/ffi.html) | ✅ |
| 内存布局控制 | [Rust Reference: Type Layout](https://doc.rust-lang.org/reference/type-layout.html) · [Rustonomicon: Data Layout](https://doc.rust-lang.org/nomicon/index.html) | ✅ |
| Stacked/Tree Borrows | [POPL 2019 · Jung et al.] · [Miri Book](https://github.com/rust-lang/miri) | ✅ |
| Miri 动态检测 | [Miri Book](https://github.com/rust-lang/miri) · [rustc-dev-guide: Miri] | ✅ |
| unsafe_op_in_unsafe_fn | [Rust 2024 Edition Guide](https://doc.rust-lang.org/edition-guide/rust-2024/index.html) · [RFC 2585](https://rust-lang.github.io/rfcs/2585-unsafe-block-in-unsafe-fn.html) | ✅ |
| FFI 与外部函数接口 | [Wikipedia: Foreign function interface](https://en.wikipedia.org/wiki/Foreign_function_interface) · [Rust Reference: FFI](https://doc.rust-lang.org/reference/introduction.html) | ✅ |
| 类型双关（Type punning） | [Wikipedia: Type punning](https://en.wikipedia.org/wiki/Type_punning) · [Rust Reference: Unions](https://doc.rust-lang.org/reference/items/unions.html) | ✅ |

---

<!-- L3::FFI（FFI）补充 -->

## 十一、演进方向

本节围绕「演进方向」展开，依次讨论补充章节：FFI 与 repr 属性完整规范、补充章节：Miri 的使用方法与限制、补充章节：`std::ptr::read/write` vs `*pt…、补充章节：`NonNull<T>` / `Unique<T>` / `…等5个方面。

### 补充章节：FFI 与 repr 属性完整规范

> FFI 是 unsafe 最常见的使用场景之一。以下补充 ABI、内存布局和对齐属性的完整规范，作为 unsafe 实践的具体延伸。

#### ABI 与 Calling Convention

```rust
// extern "C" = 使用 C 调用约定
unsafe extern "C" {
    fn c_function(x: i32) -> i32;  // 声明 C 函数
}

// Rust 函数的 C 导出
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rust_function(x: i32) -> i32 {
    x * 2
}
```

#### repr 属性语义对比矩阵

| **属性** | **布局规则** | **字段顺序** | **对齐/填充** | **单字段要求** | **FFI 场景** |
|:---|:---|:---|:---|:---|:---|
| `#[repr(C)]` | 与 C 兼容 | 声明顺序 | 自然对齐 + padding | 无 | C 结构体（Struct）互操作 |
| `#[repr(transparent)]` | 与内部类型一致 | 同内部类型 | 同内部类型 | 仅一个非 ZST 字段 | 新类型包装（如 `NonZeroU32`） |
| `#[repr(packed)]` | 紧凑排列 | 声明顺序 | 1 字节对齐，无 padding | 无 | 网络协议、硬件寄存器 |

#### 内存布局与对齐分析

```rust
use std::mem::{size_of, align_of};

// 默认 Rust 布局：编译器可重排字段
struct RustLayout { a: u8, b: u32, c: u16 }
// size ≈ 8, align = 4; 编译器可能重排为 b→c→a 以减少 padding

// #[repr(C)]: 字段顺序固定，C 兼容但可能有 padding
#[repr(C)]
struct CLayout { a: u8, b: u32, c: u16 }
// 布局: [a:1][pad:3][b:4][c:2][pad:2] = size 12, align 4

// #[repr(transparent)]: 布局与内部类型完全相同
#[repr(transparent)]
struct Wrapper(u32);
assert_eq!(size_of::<Wrapper>(), size_of::<u32>());  // 4
assert_eq!(align_of::<Wrapper>(), align_of::<u32>()); // 4

// #[repr(packed)]: 无 padding，但可能未对齐
#[repr(packed)]
struct Packed { a: u8, b: u32 }
// 布局: [a:1][b:4] = size 5, align 1
// ⚠️ b 的偏移为 1，未按 4 字节对齐 → 可能触发未对齐访问 UB
```

#### FFI 边界使用场景

```rust
// ✅ repr(C) + 指针传递：C 结构体互操作
#[repr(C)]
pub struct Point {
    pub x: f64,
    pub y: f64,
}

unsafe extern "C" {
    fn distance(p: *const Point) -> f64;
}

// ✅ repr(transparent)：零成本类型安全包装
#[repr(transparent)]
pub struct SocketFd(i32);
unsafe extern "C" {
    fn socket_create() -> SocketFd;  // ABI 与 i32 完全相同
}

// ✅ repr(packed)：解析网络协议包头
#[repr(packed)]
pub struct TcpHeader {
    pub src_port: u16,
    pub dst_port: u16,
    pub seq: u32,
    // ... 紧凑排列，无 padding
}
```

#### 对齐、填充与风险边界

| **场景** | `#[repr(C)]` | `#[repr(transparent)]` | `#[repr(packed)]` |
|:---|:---|:---|:---|
| 字段借用（Borrowing） | ✅ 安全对齐 | ✅ 安全对齐 | ⚠️ 可能未对齐，需 unsafe |
| 跨平台 ABI | ✅ 稳定 | ✅ 稳定 | ⚠️ 未对齐访问在部分架构触发 SIGBUS |
| 编译器重排 | ❌ 禁止 | ❌ 禁止 | ❌ 禁止 |
| 性能 | 可能有 padding 开销 | 零开销 | 未对齐访问可能更慢 |

> **[Rust Reference: Type Layout](https://doc.rust-lang.org/reference/type-layout.html)** `#[repr(C)]` 保证字段按声明顺序排列；`#[repr(transparent)]` 要求只有一个非 ZST 字段且布局与该字段相同；`#[repr(packed)]` 将对齐设为 1，字段间无 padding。✅ 已验证
> **[Rustonomicon: FFI](https://doc.rust-lang.org/nomicon/ffi.html)** 未对齐访问（如 `&packed.u32`）是 UB，必须通过 `ptr::read_unaligned` 或 `unsafe` 块读取。✅ 已验证

---

- **演进方向**: 补充 FFI 完整规范（ABI、layout、calling convention） —— 优先级: 高 —— 已完成 v1.1
- **演进方向**: 补充 `#[repr(C)]` / `#[repr(transparent)]` / `#[repr(packed)]` —— 优先级: 高 —— 已完成 v1.1

### 补充章节：Miri 的使用方法与限制

> **权威来源**: [Miri Book](https://rustc-dev-guide.rust-lang.org/miri.html) · [Rust Blog: Miri is available on CI](https://github.com/rust-lang/miri)
> **层级标注**: `L3::动态验证` → `L1::借用` 别名违规检测 · `L4::RustBelt` 操作语义动态近似

**定义**：Miri（Memory Inspector for Rust）是 Rust 编译器 MIR（Mid-level IR）的解释执行器。它不生成机器码，而是在 MIR 层面逐步解释程序，同时维护精确的内存状态（包括初始化状态、别名权限栈/树、分配生命周期（Lifetimes）），从而动态检测未定义行为（UB）。

> **[Miri Documentation](https://github.com/rust-lang/miri)** Miri is an interpreter for Rust's mid-level intermediate representation (MIR). It can detect many classes of undefined behavior, including memory errors, invalid use of uninitialized data, and violation of aliasing rules. ✅ 已验证

#### 安装与基本使用

```bash
# 安装 Miri（需要每日构建版工具链）
rustup component add miri

# 运行测试
MIRIFLAGS=-Zmiri-tree-borrows cargo miri test

# 运行单文件/程序
cargo miri run

# CI 集成（GitHub Actions 示例）
# .github/workflows/miri.yml
# - run: rustup toolchain install <每日构建版工具链> --component miri
# - run: MIRIFLAGS=-Zmiri-tree-borrows cargo +<每日构建版工具链> miri test
```

> **[Rust Blog: Miri on CI]** Miri 已集成到 Rust CI 中，成为标准库 unsafe 代码的持续验证工具。第三方项目同样可在 CI 中运行 `cargo miri test` 以捕获 UB。✅ 已验证

#### 能检测的问题（覆盖范围）

| 问题类型 | 检测机制 | 示例 |
|:---|:---|:---|
| **Use-after-free** | 分配-释放追踪 | 悬垂裸指针解引用 |
| **越界访问** | 内存边界检查 | `ptr.add(10)` 后访问未分配区域 |
| **未对齐访问** | 对齐约束验证 | `*(ptr as *mut u32)` 当 ptr 未按 4 字节对齐 |
| **数据竞争** | Tree Borrows + happens-before | 非同步的共享可变访问 |
| **无效枚举值** | discriminant 合法性 | `transmute::<u8, Color>(42)` |
| **未初始化内存读取** | `MaybeUninit` 状态追踪 | 读取未初始化的局部变量或数组元素 |
| **别名违规** | Stacked/Tree Borrows | 从同一 `&mut T` 创建两个重叠活跃指针 |

#### 不能检测的问题（边界限制）

| 问题类型 | 原因 | 替代方案 |
|:---|:---|:---|
| **所有可能的 UB** | 停机问题不可解；Miri 仅覆盖已定义的操作语义 | 形式化验证（Kani、RustBelt） |
| **逻辑错误** | 功能正确性超出 Miri 范围 | 单元测试、属性测试（proptest） |
| **FFI 边界错误** | 外部代码不透明，Miri 无法进入 C 函数内部 | 人工审查、Valgrind/ASan |
| **硬件相关行为** | 内联汇编（Inline Assembly）、SIMD、内存映射 I/O 不在 MIR 层面 | 真机测试、QEMU |
| **活性问题（死锁/饥饿）** | Miri 检测安全性（safety），不检测活性（liveness） | `loom` 模型检查 |
| **性能回归** | Miri 解释执行比原生慢 100x~1000x | 基准测试（criterion） |

#### 正确示例：Miri 检测出 UB

```rust
// ❌ 反例: Use-after-free（Miri 会报错）
fn miri_detects_uaf() {
    let ptr: *const i32;
    {
        let x = 42;
        ptr = &x;  // ptr 指向栈变量 x
    }              // x 在此处释放
    unsafe {
        println!("{}", *ptr);  // Miri: "dangling pointer was dereferenced"
    }
}
```

```rust,ignore
// ❌ 反例: 未初始化内存读取（Miri 会报错）
fn miri_detects_uninit() {
    let x: i32;
    let y = unsafe { std::ptr::read(&x) };  // Miri: "reading uninitialized memory"
}
```

#### 反例：Miri 无法检测的逻辑错误

```rust,ignore
// ⚠️ 逻辑错误: 求和时溢出（Miri 不报错，因为非 UB）
fn logic_error_not_ub() -> u32 {
    let mut sum: u32 = 0;
    for i in 1..=100000 {
        sum += i;  // 逻辑错误：最终溢出，但 release 模式下不 panic
    }
    sum
}

// ⚠️ 逻辑错误: 死锁（Miri 不报错，属于活性问题）
fn deadlock_not_detected() {
    use std::sync::{Mutex, Arc};
    let a = Arc::new(Mutex::new(0));
    let b = Arc::new(Mutex::new(0));
    let (a2, b2) = (Arc::clone(&a), Arc::clone(&b));
    std::thread::spawn(move || { let _ = a2.lock().unwrap(); let _ = b.lock().unwrap(); });
    let _ = b2.lock().unwrap();
    let _ = a.lock().unwrap();  // 死锁！Miri 不会报错，只会 hang 住
}
```

> **定理边界**: Miri 检测 ⊂ UB 集合 ⊂ 程序错误集合。Miri 通过 ≠ 程序正确；Miri 报错 = 存在 UB。

#### Miri 常用标志详解

Miri 的行为通过 `MIRIFLAGS` 环境变量控制。以下是与工程实践最相关的标志：

| **标志** | **作用** | **典型场景** |
|:---|:---|:---|
| `-Zmiri-disable-isolation` | 禁用隔离，允许文件系统、网络、环境变量访问 | 测试涉及 `std::fs` 或 `std::env` 的代码 |
| `-Zmiri-ignore-leaks` | 不报告内存泄漏 | 全局分配器或循环引用场景（故意不释放） |
| `-Zmiri-tree-borrows` | 使用 Tree Borrows 别名模型（默认，无需显式指定） | 现代 Miri 默认行为 |
| `-Zmiri-stacked-borrows` | 使用 Stacked Borrows 别名模型（兼容旧代码） | 验证旧代码或对比两种模型 |
| `-Zmiri-check-number-validity` | 检查整数类型有效性（如 `bool` 必须是 0/1） | 严格的值表示验证 |
| `-Zmiri-tag-raw-pointers` | 为裸指针分配来源标签（更严格检测） | 裸指针密集型代码 |
| `-Zmiri-permissive-provenance` | 宽松来源模式（实验性，允许更多整数-指针转换） | 特定 FFI 或旧代码兼容 |
| `-Zmiri-preemption-rate=N` | 设置线程抢占频率（默认 100，0 为确定式调度） | 并发测试的可重现性控制 |
| `-Zmiri-seed=N` | 设置随机数种子，使并发交错可重现 | CI 中稳定复现并发问题 |

```bash
# 示例：允许文件系统访问 + 忽略内存泄漏
MIRIFLAGS="-Zmiri-disable-isolation -Zmiri-ignore-leaks" cargo miri test

# 示例：确定式调度 + 可重现种子
MIRIFLAGS="-Zmiri-preemption-rate=0 -Zmiri-seed=42" cargo miri test
```

> **来源: [Miri Book](https://github.com/rust-lang/miri)** `-Zmiri-disable-isolation` 使 Miri 不再虚拟化系统调用，而是直接代理到宿主 OS。这在测试 IO 相关代码时是必需的，但会降低可移植性和确定性。 ✅ 已验证
> **来源: [Miri Book](https://github.com/rust-lang/miri)** `-Zmiri-ignore-leaks` 适用于全局缓存或单例模式——这些内存 intentionally 存活到进程结束，不算真正的泄漏。 ✅ 已验证

#### Miri 与 Valgrind / ASan / TSan 的对比

Miri 不是唯一的动态检测工具。根据错误类型和检测阶段，Valgrind（memcheck）、AddressSanitizer（ASan）、ThreadSanitizer（TSan）各有优势。以下从**检测时机**、**覆盖范围**和**运行时开销**三维度对比：

| **维度** | **Miri** | **Valgrind (memcheck)** | **AddressSanitizer (ASan)** | **ThreadSanitizer (TSan)** |
|:---|:---|:---|:---|:---|
| **检测时机** | MIR 解释执行（编译后） | 机器码动态插桩（运行时） | 编译期插桩 + 运行时库 | 编译期插桩 + 运行时库 |
| **内存错误** | ✅ UAF、OOB、未对齐、未初始化 | ✅ UAF、未初始化、泄漏 | ✅ UAF、OOB、堆栈缓冲区溢出 | ❌ 不专门检测 |
| **数据竞争** | ⚠️ 部分（单线程解释器模拟） | ❌ 不检测 | ❌ 不检测 | ✅ 核心功能 |
| **别名违规** | ✅ Stacked/Tree Borrows | ❌ 不检测 | ❌ 不检测 | ❌ 不检测 |
| **无效枚举值** | ✅ discriminant 检查 | ❌ 不检测 | ❌ 不检测 | ❌ 不检测 |
| **FFI / 外部代码** | ❌ 不透明（stub 或 panic） | ✅ 可检测 C 代码 | ✅ 可检测 C/C++ 代码 | ✅ 可检测 C/C++ 代码 |
| **运行时开销** | 极慢（100x~1000x） | 慢（10x~50x） | 中等（2x~3x） | 中等（5x~15x） |
| **硬件相关行为** | ❌ 不支持（内联汇编（Inline Assembly）、SIMD） | ✅ 支持 | ✅ 支持 | ✅ 支持 |
| **Rust 语义精确度** | ✅ 精确到 MIR 语义 | ⚠️ 机器码级，可能漏掉 Rust 特定 UB | ⚠️ 机器码级 | ⚠️ 机器码级 |

**工具选择决策树**：

```text
需要检测 Rust 特定的 UB（无效枚举、别名违规）?
  └── 是 → Miri（唯一选择）
  └── 否 → 涉及 FFI 或 C 依赖?
      └── 是 → Valgrind / ASan / TSan（覆盖 C 代码）
      └── 否 → 性能敏感且需频繁运行?
          └── 是 → ASan（开销最低，适合 CI 集成）
          └── 否 → Miri（最精确的 Rust 语义检测）
```

> **[LLVM SanitizerCoverage Docs](https://clang.llvm.org/docs/SanitizerCoverage.html)** ASan 使用影子内存（shadow memory）检测堆/栈/全局变量的越界访问，运行时开销约 2x，是 C/C++/Rust FFI 项目的首选工具。 ✅ 已验证
> **[Valgrind Documentation](https://valgrind.org/docs/)** Valgrind 的 memcheck 通过 JIT 重编译检测未初始化读取和内存泄漏，无需重编译目标程序，但运行速度极慢（10x~50x）。 ✅ 已验证
> **[TSan Documentation](https://clang.llvm.org/docs/ThreadSanitizer.html)** TSan 使用 happens-before 向量时钟检测数据竞争，对 Rust 的 `std::sync` 原子操作（Atomic Operations）和锁结构均有效，但要求所有代码都经过插桩。 ✅ 已验证
> **跨层映射**: `L3::Miri` ↔ [`L6::工具链`](../../06_ecosystem/00_toolchain/01_toolchain.md) CI 集成 · [`L4::形式化`](../../04_formal/02_separation_logic/01_rustbelt.md) 操作语义动态验证

---

### 补充章节：`std::ptr::read/write` vs `*ptr` 解引用的语义差异

> **权威来源**: [Rust Reference: Pointer operators](https://doc.rust-lang.org/reference/introduction.html) · [Rust Reference: Behavior considered undefined](https://doc.rust-lang.org/reference/behavior-considered-undefined.html) · [The Rustonomicon: Ownership and Move Semantics](https://doc.rust-lang.org/nomicon/index.html) · [std::ptr API docs](https://doc.rust-lang.org/std/ptr/) · [Rustonomicon: Working With Memory](https://doc.rust-lang.org/nomicon/index.html)
> **层级标注**: `L3::裸指针语义` → `L1::所有权` 移动语义延伸 · `L2::内存管理` drop 触发控制 · `L4::形式化` Validity Invariant 边界

**核心区别**：裸指针的 `*` 解引用操作与 `std::ptr::read`/`std::ptr::write` 在**所有权（Ownership）语义**、**drop 触发**和**借用（Borrowing）检查器介入程度**方面存在本质差异。`*ptr` 是**引用语义**的延伸——它假设目标位置已初始化、对齐且有效，并受 Rust 所有权规则约束；而 `ptr::read`/`ptr::write` 是**原始内存操作**，仅执行 bitwise copy 或按位覆盖，不调用 `Clone`，也不自动触发 `Drop`。

> **[std::ptr::read docs](https://doc.rust-lang.org/std/ptr/fn.read.html)** `ptr::read` 创建目标位置的按位副本，无论该位置是否已初始化。调用者必须确保后续不会导致原位置和新位置的值同时被 drop。✅ 已验证
> **[std::ptr::write docs](https://doc.rust-lang.org/std/ptr/fn.write.html)** `ptr::write` 将 `src` 按位写入 `dst` 指向的内存，不读取或 drop `dst` 指向的旧内容。这使其成为未初始化内存初始化的唯一安全方式。✅ 已验证

---

#### 语义精确定义

「语义精确定义」部分按 `std::ptr::read<T>(src: *const T) -…、`std::ptr::write<T>(dst: *mut T, sr…与`*ptr` 解引用（`DerefMut`）的顺序逐层展开。

##### `std::ptr::read<T>(src: *const T) -> T`

从 `src` 指向的内存位置执行 **bitwise copy（按位浅拷贝）**，返回一个类型为 `T` 的值。

- **不调用 `Clone`**：即使 `T: Clone`，`ptr::read` 也只做 `memcpy` 级别的复制。
- **不触发 `Drop`**：原位置的内容**不会被销毁**，其位模式原封不动保留。
- **不转移所有权（Ownership）**（从内存模型角度）：原位置的 bytes 仍被视为"有效"的 `T` 实例，直到被覆盖或内存释放。
- **不安全契约**：`src` 必须对齐且指向已初始化的 `T`；读取后，调用者必须确保原位置和新位置的值**不会同时被 drop**。

> **Rust 1.96 更新**: `"valid for read/write"` 定义重构——`ptr` 方法的文档现在明确排除 null 指针作为"有效"地址，将 null 例外作为单独说明添加到各方法上。这与 `NonNull<T>` 的语义一致：null 指针**不是**任何 Rust 引用的有效值，即使在 unsafe 代码中解引用 null 也是立即 UB。
> **来源: [Rustonomicon: Ownership and Move Semantics](https://doc.rust-lang.org/nomicon/index.html)** Move 语义在底层就是 bitwise copy + 使原位置失效。`ptr::read` 只做前半部分，后半部分由程序员负责。✅ 已验证

###### Rust 1.96 `valid for read/write` 语义变更详解

Rust 1.96 对标准库指针方法中"valid for read/write"的前提条件进行了**文档与形式化语义层面的重构**，统一了 Miri、编译器优化假设与文档描述：

1. **基础定义不再包含 null**
   - 旧文档中，`ptr::read`/`ptr::write` 等方法的 Safety 说明常将 null 指针作为"某些情况下可接受"的边界案例。
   - 新定义明确：一个指针要"valid for read/write"，首先必须是非空指针；null 指针**默认不是**有效地址。

2. **null 例外下沉到具体方法**
   - 对于历史上允许 null 的特殊场景（主要是零大小类型 `T` 的 `<*const T>::read` / `<*mut T>::write`，因为 ZST 不实际访问内存），标准库在相应方法的 Safety 说明中**单独注明 null 例外**，而不是让基础定义包容 null。
   - 这意味着：阅读某个具体方法的 Safety 契约时，必须查看该方法是否显式声明了 null 例外；不能默认"ZST 所以可以传 null"。

3. **与 `NonNull<T>` 语义对齐**
   - `NonNull<T>` 本身即表示"非空裸指针"。此次重构使 `std::ptr` 文档与 `NonNull` 的不变量保持一致：null 不是任何 Rust 引用的有效值。
   - 对开发者而言，如果代码中使用了 `NonNull<T>`，其 `as_ptr()` 的结果自然满足新的 `valid for read/write` 定义。

4. **对 Miri 与 UB 检测的影响**
   - Miri 的 UB 检测 already 将 null 指针的 read/write 视为 UB。文档重构**不改变 Miri 行为**，但消除了文档与 Miri 之间的语义_gap，使形式化推理更一致。
   - 编译器优化也依赖"valid for read/write"的定义；明确排除 null 后，某些基于非空假设的优化在语义上更加坚实。

5. **实际代码影响**
   - 对于绝大多数已有代码，此次重构**无行为变化**，只是文档更严格。
   - 如果你曾在 unsafe 代码中依赖"ZST 指针可以是 null"这一隐含假设，请显式检查所调用方法的安全说明是否允许该例外；否则应使用 `ptr::without_provenance` / `ptr::dangling` 等明确构造非空指针。

```rust,ignore
// ❌ Rust 1.96 语义下：null 指针不再默认 valid for read/write
let p: *const u8 = std::ptr::null();
unsafe { std::ptr::read(p); } // UB，即使 T 非 ZST 也已是 UB

// ✅ 使用 NonNull 或 ensure 非空
let p = std::ptr::NonNull::new(&x as *const i32).unwrap();
unsafe { std::ptr::read(p.as_ptr()); }
```

> **来源**: Rust 1.96.0 Release Notes · [Rust Reference: Behavior considered undefined](https://doc.rust-lang.org/reference/behavior-considered-undefined.html) · [PR #157226](https://github.com/rust-lang/rust/pull/157226)

##### `std::ptr::write<T>(dst: *mut T, src: T)`

将 `src` **按位覆盖**到 `dst` 指向的内存位置。

- **不触发 `Drop`**：`dst` 指向的旧值（如果有）不会被 drop。这是它与 `*dst = src` 最关键的区别。
- **转移所有权（Ownership）**：`src` 被 move 进 `dst` 指向的内存。此后 `src` 在调用者作用域中失效。
- **不安全契约**：`dst` 必须对齐；若 `dst` 指向已初始化的内存，旧值将被静默覆盖——导致内存泄漏（若旧值含堆分配）。

> **来源: [Rust Reference: Assignment expressions](https://doc.rust-lang.org/reference/introduction.html)** `*ptr = val` 会先计算左值（place expression），若目标位置已初始化，编译器会插入 `Drop::drop` 调用，再执行 move/复制。✅ 已验证

##### `*ptr` 解引用（`DerefMut`）

裸指针的 `*` 解引用在 `unsafe` 块内产生一个**place expression（位置表达式）**，其语义取决于上下文：

- **读取上下文**（`let x = *ptr`）：等价于从该位置 move 出一个值。若 `T` 非 `Copy`，原位置**逻辑上失效**（但编译器不追踪裸指针的失效状态）。
- **写入上下文**（`*ptr = val`）：编译器会生成**先 drop 旧值、再写入新值**的代码序列。若目标位置未初始化，drop 旧值 = 读取未初始化内存 = **UB**。
- **受借用（Borrowing）检查器保护的程度**：`unsafe` 块内的裸指针解引用**完全绕过**借用检查器。编译器不验证 `ptr` 的生命周期（Lifetimes）、对齐或有效性。

> **来源: [TRPL Ch19.1](https://doc.rust-lang.org/book/ch19-01-unsafe-rust.html)** 裸指针解引用是 `unsafe` 的五大超能力之一，它关闭了编译器对生命周期（Lifetimes）和别名的自动追踪。✅ 已验证

---

#### 关键差异对比表格

| **维度** | `std::ptr::read` | `std::ptr::write` | `*ptr`（读取） | `*ptr = val`（写入） |
|:---|:---|:---|:---|:---|
| **底层操作** | bitwise copy（`memcpy`） | bitwise overwrite（`memcpy`） | move / copy（视 `T`） | drop + move / copy |
| **是否调用 `Clone`** | ❌ 否 | ❌ 否 | ❌ 否（move）/ ✅ 是（`Copy`） | ❌ 否（move）/ ✅ 是（`Copy`） |
| **是否触发 `Drop`** | ❌ 否 | ❌ **否** | ❌ 否（仅读取） | ✅ **是**（先 drop 旧值） |
| **是否转移所有权（Ownership）** | 否（复制后两位置同时"有效"） | 是（`src` move 入 `dst`） | 是（原位置失效） | 是（`val` move 入） |
| **是否需要 `unsafe`** | ✅ 是（函数本身 unsafe） | ✅ 是（函数本身 unsafe） | ✅ 是（裸指针解引用） | ✅ 是（裸指针解引用） |
| **是否受借用（Borrowing）检查器保护** | ❌ 否 | ❌ 否 | ❌ 否 | ❌ 否 |
| **对未初始化内存的安全性** | ⚠️ 可读，但读取后原+新值不能双 drop | ✅ **安全**（唯一正确方式） | ⚠️ 读取 = UB | ❌ **UB**（drop 未初始化值） |
| **对已初始化内存的安全性** | ⚠️ 复制后需避免 double-free | ⚠️ 旧值被覆盖 = 内存泄漏 | ✅ 安全 | ✅ 安全 |
| **典型场景** | `Vec::pop`、手工 move | 未初始化内存初始化 | 简单访问（不推荐裸指针） | 赋值更新（不推荐裸指针） |

> **来源: [Rust Reference: Behavior considered undefined](https://doc.rust-lang.org/reference/behavior-considered-undefined.html)** 读取未初始化内存是 UB；`ptr::write` 是向未初始化内存写入值的正确方式，因为它不尝试读取旧值。✅ 已验证
> **来源: [Rustonomicon: RAII](https://doc.rust-lang.org/nomicon/index.html)** 混淆 `*ptr = val` 与 `ptr::write` 是 unsafe 代码中内存泄漏和 double-free 的首要原因。💡 原创分析
> [来源: [Rust Reference: NonNull](https://doc.rust-lang.org/std/ptr/struct.NonNull.html)]

---

#### 典型使用场景

「典型使用场景」部分包含 `ptr::read`： `Vec::pop` 内部实现与 `Manu… 与`ptr::write`：未初始化内存填充与`MaybeUninit… 两条主线，本节依次说明。

##### `ptr::read`： `Vec::pop` 内部实现与 `ManuallyDrop` 配合

Rust 标准库中 `Vec::pop` 的核心逻辑正是 `ptr::read` 的典型应用——从数组尾部"取出"值，同时避免触发尾部元素的 `drop`（因为该位置逻辑上已被截断，后续 `push` 会覆盖它）。

```rust,ignore
// ✅ 正确: Vec::pop 的简化实现
impl<T> MyVec<T> {
    pub fn pop(&mut self) -> Option<T> {
        if self.len == 0 { return None; }
        self.len -= 1;
        unsafe {
            // Safety: index self.len 之前已初始化，且取出后 Vec 逻辑长度缩减
            // ptr::read 执行按位复制，不调用 drop，原位置位模式保留但不再被访问
            Some(std::ptr::read(self.ptr.add(self.len)))
        }
    }
}
```

`ManuallyDrop<T>` 与 `ptr::read` 的协同是更精妙的模式：当需要**有条件地**决定某个值是否应被 drop 时，先用 `ManuallyDrop` 包装，再通过 `ptr::read` 提取。

```rust,ignore
use std::mem::ManuallyDrop;
use std::ptr;

// ✅ 正确: 有条件地提取值，避免自动 drop
fn conditional_extract<T>(slot: &mut ManuallyDrop<T>, should_take: bool) -> Option<T> {
    if should_take {
        unsafe {
            // Safety: ManuallyDrop 阻止自动 drop，ptr::read 按位复制提取值
            // 提取后 slot 的内容逻辑上失效，但不会被自动 drop
            let val = ptr::read(slot);
            // 必须手动标记 slot 为"已取走"状态，防止二次使用
            // 实际工程中通常用 Option<ManuallyDrop<T>> 或接管内存所有权
            Some(val)
        }
    } else {
        None
    }
}
```

> **[std::mem::ManuallyDrop docs](https://doc.rust-lang.org/std/mem/struct.ManuallyDrop.html)** `ManuallyDrop` 包装的值不会在其作用域结束时自动调用 `drop`，配合 `ptr::read` 可实现"手动控制资源释放时机"。✅ 已验证
> **跨层映射**: `L3::ManuallyDrop` ↔ [`L2::内存管理`](../../02_intermediate/02_memory_management/01_memory_management.md) RAII 与自定义 drop 控制

##### `ptr::write`：未初始化内存填充与 `MaybeUninit::write` 的前身模式

在 `MaybeUninit<T>` 稳定之前，向未初始化内存写入值的唯一正确方式就是 `ptr::write`。即便在今天，`MaybeUninit::write` 的底层实现仍然是 `ptr::write`。

```rust
use std::mem::MaybeUninit;

// ✅ 正确: MaybeUninit::write 的底层等价形式
fn init_via_ptr_write<T>(slot: &mut MaybeUninit<T>, value: T) {
    unsafe {
        // Safety: MaybeUninit 不保证内部已初始化，ptr::write 不读取旧值
        // 这与 slot.write(value) 的语义完全一致
        std::ptr::write(slot.as_mut_ptr(), value);
    }
}

// 等价于:
// slot.write(value);  // MaybeUninit 的稳定 API
```

`ptr::write` 的另一个关键场景是**在堆上构造值而不触发中间状态的 drop**。例如，自定义 `Box::new` 或需要在特定内存地址放置对象时：

```rust
// ✅ 正确: 在已分配的原始内存上直接构造值
unsafe fn construct_in_place<T>(ptr: *mut T, f: impl FnOnce() -> T) {
    // ptr 指向已分配但未初始化的内存（如 GlobalAlloc::alloc 返回）
    std::ptr::write(ptr, f());
}
```

> **来源: [Rust Reference: MaybeUninit](https://doc.rust-lang.org/reference/introduction.html)** `MaybeUninit::write` is implemented as `ptr::write(self.as_mut_ptr(), value)`. It is the standard way to initialize uninitialized memory. ✅ 已验证
> **跨层映射**: `L3::未初始化内存` ↔ [`L1::所有权`](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md) 初始化要求 · [`L2::内存管理`](../../02_intermediate/02_memory_management/01_memory_management.md) 堆栈分配语义

---

#### 危险模式与常见错误

本节围绕「危险模式与常见错误」展开，依次讨论危险模式 1：`ptr::read` 后原位置未失效导致的 doubl…、危险模式 2：`ptr::write` 覆盖已初始化值导致的内存泄漏与危险模式 3：对未初始化内存使用 `*ptr = val`。

##### 危险模式 1：`ptr::read` 后原位置未失效导致的 double-free

`ptr::read` 执行后，**原位置和新位置同时持有相同位模式的值**。若两者最终都被视为"有效"并被 drop，则发生 double-free。

```rust
// ❌ 反例: ptr::read 后未处理原位置，导致 double-free
fn double_free_via_read<T>(ptr: *const T) {
    unsafe {
        let val = std::ptr::read(ptr);  // 按位复制: val 和 *ptr 内容相同
        drop(val);                       // drop val（第一次）
        // *ptr 仍被视为有效值！若后续再次 drop → double-free
        let val2 = std::ptr::read(ptr);  // 再次读取同一位置
        drop(val2);                      // UB! 同一资源被释放两次
    }
}

// ✅ 修正: read 后应立即用 ptr::write 覆盖原位置，或确保原位置不再被 drop
fn safe_read_pattern<T>(ptr: *mut T) -> T {
    unsafe {
        let val = std::ptr::read(ptr);
        // 选项 A: 立即写入一个"无害"的值（如零初始化）
        // std::ptr::write(ptr, std::mem::zeroed());  // 仅对允许零值的类型安全
        // 选项 B: 确保调用方知道 *ptr 已失效，不再使用或 drop
        val
    }
}
```

> **来源: [Rustonomicon: Working With Memory](https://doc.rust-lang.org/nomicon/index.html)** Using `ptr::read` without ensuring the source is no longer considered initialized can lead to double-drops, which is undefined behavior. ✅ 已验证

##### 危险模式 2：`ptr::write` 覆盖已初始化值导致的内存泄漏

`ptr::write` 不 drop 旧值。若目标位置**已经持有有效值**（如已初始化的堆内存、文件描述符），直接覆盖将导致资源泄漏。

```rust
// ❌ 反例: ptr::write 覆盖已初始化的 Box，导致内存泄漏
fn leak_via_write() {
    let mut x = Box::new(1);
    let ptr = &mut x as *mut Box<i32>;
    unsafe {
        std::ptr::write(ptr, Box::new(2));
        // Box::new(1) 没有被 drop！旧 Box 指向的堆内存泄漏
    }
    // x = Box::new(2)，作用域结束时正常 drop
}

// ✅ 修正: 覆盖前先显式 read/drop 旧值，或始终只对未初始化内存使用 ptr::write
fn safe_overwrite<T>(ptr: *mut T, new_value: T) {
    unsafe {
        // 先 read 出旧值（由调用者或本函数负责 drop），再 write 新值
        let old = std::ptr::read(ptr);
        std::ptr::write(ptr, new_value);
        drop(old);  // 显式释放旧资源
    }
}
// 注: 上面的 safe_overwrite 实际上就是 ptr::replace 的语义
```

> **[std::ptr::write docs](https://doc.rust-lang.org/std/ptr/fn.write.html)** `ptr::write` does not drop the contents of `dst`. If `dst` points to a valid object, that object will be leaked. ✅ 已验证

##### 危险模式 3：对未初始化内存使用 `*ptr = val`

这是初学者最常犯的错误——误以为 `*ptr = val` 和 `ptr::write(ptr, val)` 等价。

```rust,ignore
// ❌ 反例: 对未初始化内存使用 *ptr = val → UB
fn write_to_uninit_ub<T>(ptr: *mut T, value: T) {
    unsafe {
        *ptr = value;  // UB! 编译器先尝试 drop *ptr 的旧值
                       // 若 ptr 指向未初始化内存，drop = 读取未初始化 = UB
    }
}

// ❌ 反例: 错误使用 *ptr 读取导致 double drop（与 ptr::read 混淆）
fn double_drop_bug<T>(ptr: *mut T) {
    unsafe {
        let val = *ptr;      // 解引用转移所有权 → ptr 指向的位置被"move 走"
        let val2 = *ptr;     // UB! 再次从同一失效位置读取，导致双重释放
    }
}

// ✅ 修正: 使用 ptr::read（不转移所有权，仅按位复制）
fn correct_read<T>(ptr: *const T) -> T {
    unsafe { std::ptr::read(ptr) }  // 调用者负责确保原位置后续不再被 drop
}
```

> **来源: [Rust Reference: Behavior considered undefined](https://doc.rust-lang.org/reference/behavior-considered-undefined.html)** Reading uninitialized memory, including during a drop glue invocation, is undefined behavior. ✅ 已验证

---

#### `ptr::read_volatile` / `ptr::write_volatile`：MMIO 与硬件寄存器场景

> **权威来源**: [std::ptr::read_volatile docs] · [Rust Embedded Book: Memory-mapped I/O]
> **层级标注**: `L3::硬件交互` → `L6::嵌入式` 寄存器访问

`ptr::read_volatile` 和 `ptr::write_volatile` 在语义上与 `ptr::read`/`ptr::write` 相同（不触发 drop，按位操作），但额外保证：

1. **编译器不会优化掉访问**：即使读取的值未被使用，也不会被死码消除。
2. **访问不会被重排**：volatile 操作之间保持程序顺序（与 CPU 内存序不同，需配合 fencing）。
3. **每次调用都产生实际的内存访问**：不会缓存到寄存器中。

这些保证使其成为**内存映射 I/O（MMIO）**和硬件寄存器操作的唯一正确工具。

```rust
// ✅ 正确: 嵌入式系统中访问硬件寄存器
const GPIOA_ODR: *mut u32 = 0x4002_0014 as *mut u32;

unsafe fn set_led_on() {
    // 必须用 write_volatile，否则编译器可能优化掉此写入
    std::ptr::write_volatile(GPIOA_ODR, 1 << 5);
}

unsafe fn read_button_state() -> u32 {
    // 必须用 read_volatile，否则编译器可能复用之前的缓存值
    std::ptr::read_volatile(GPIOA_ODR)
}
```

| 特性 | `ptr::read` / `ptr::write` | `ptr::read_volatile` / `ptr::write_volatile` |
|:---|:---|:---|
| 按位复制/覆盖 | ✅ | ✅ |
| 触发 drop | ❌ | ❌ |
| 编译器优化抑制 | ❌ 可能被消除/重排 | ✅ 强制保留 |
| 实际内存访问保证 | ❌ | ✅ |
| 典型场景 | 堆内存管理、数据结构 | 硬件寄存器、MMIO、信号量 |

> **[LLVM LangRef: volatile](https://llvm.org/docs/LangRef.html#volatile-memory-accesses)** Volatile operations are required to execute in program order relative to other volatile operations, and must produce actual memory accesses. ✅ 已验证
> **来源: [Rust Embedded Book](https://doc.rust-lang.org/stable/embedded-book/)** In embedded programming, memory-mapped registers must be accessed with volatile operations to prevent the compiler from optimizing away hardware state changes. ✅ 已验证

---

#### 边界分析：`ptr::replace` 的契约

`ptr::replace` 是 `ptr::read` + `ptr::write` 的原子组合，但语义上**不等于**两者的简单叠加——它先 read 出旧值，再 write 进新值，并**返回旧值由调用者负责 drop**。

```rust,ignore
// ✅ 正确: ptr::replace 先 read 再 write，返回旧值由调用者负责 drop
fn replace_demo() {
    let mut x = Box::new(1);
    let old = std::ptr::replace(&mut x, Box::new(2));
    // old = Box::new(1)，在作用域结束时自动 drop（不泄漏）
    // x = Box::new(2)
    drop(x);
}

// ✅ 正确: 在裸指针场景下使用 replace 安全地交换值
unsafe fn swap_via_replace<T>(a: *mut T, b: *mut T) {
    let tmp = std::ptr::read(b);           // 保存 b 的值
    let old_a = std::ptr::replace(a, tmp); // a 写入 b 的旧值，返回 a 的旧值
    std::ptr::write(b, old_a);             // b 写入 a 的旧值
}
// 注: 上面的逻辑实际上就是 std::ptr::swap 的展开形式
```

> **[std::ptr::replace docs](https://doc.rust-lang.org/std/ptr/fn.replace.html)** `replace` reads the value at `dest` without dropping it, writes `src` into it, and returns the old value. It is semantically equivalent to `read` followed by `write`. ✅ 已验证

---

> **定理**：`ptr::read` + `ptr::write` 组合 ≠ `*ptr` 解引用。前者是**内存层面的按位操作**，后者是**所有权（Ownership）层面的语义操作**。在 unsafe 代码中混淆两者是 UAF、double-free 和内存泄漏的常见根源。
> **定理（安全性边界）**：`ptr::write` 是向未初始化内存写入的**唯一安全 primitive**；`*ptr = val` 是更新已初始化内存的**安全 primitive**（在 safe Rust 中）。二者不可互换。💡 原创分析
> **跨层映射**: `L3::裸指针语义` ↔ [`L1::所有权`](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md) move 与 copy 语义 · [`L2::内存管理`](../../02_intermediate/02_memory_management/01_memory_management.md) drop 触发规则 · [`L4::形式化`](../../04_formal/01_ownership_logic/02_ownership_formal.md) Validity Invariant 与初始化要求

---

### 补充章节：`NonNull<T>` / `Unique<T>` / `Shared<T>` 的演进

> **权威来源**: [Rust [RFC 1184](https://rust-lang.github.io/rfcs//1184-stabilize-no_std.html): Rename `Unique` to `NonNull`] · [std::ptr::NonNull docs] · [Rust PR #45207: Introduce NonNull]
> **层级标注**: `L3::指针类型` → `L2::智能指针` Box/Arc 内部实现 · `L1::类型系统` 协变与不变

**历史演进**：Rust 标准库内部指针类型经历了从 `Unique<T>` / `Shared<T>` 到 `NonNull<T>` 的统一化过程，核心动机是**简化内部表示**、**提供稳定的外部 API**，并**统一协变语义**。

| 类型 | 时期 | 核心语义 | 状态 |
| :--- | :--- | :--- | :--- |
| `Unique<T>` | Rust 1.0 ~ 1.25 | 协变、非空、拥有语义（`Own`） | ❌ 已移除（内部使用） |
| `Shared<T>` | Rust 1.0 ~ 1.25 | 协变、非空、共享语义（`Rc`/`Arc` 内部） | ❌ 已移除 |
| `NonNull<T>` | Rust 1.25+ | 协变、非空、裸指针包装，不携带所有权（Ownership）语义 | ✅ 稳定 API |

> **[Rust RFC 1184](https://github.com/rust-lang/rfcs/pull/1184)** `NonNull<T>` replaces `Unique<T>` as the standard covariant, non-null raw pointer abstraction.
> Unlike `Unique`, `NonNull` does not encode ownership semantics—it is purely a pointer utility type. ✅ 已验证

#### `Unique<T>`：曾经的 Box 内部表示

```text
// 历史背景（已不存在的内部类型）
pub struct Unique<T: ?Sized> {
    pointer: *const T,  // 实际为 *mut T，用 *const 实现协变
    _marker: PhantomData<T>,  // 拥有语义标记
}
// Unique 曾用于 Box<T> 的内部表示：Box<T> = Unique<T>
// 问题：Unique 同时承载"非空"+"协变"+"拥有"三重语义，过于特化
```

#### `Shared<T>`：曾经的 Rc/Arc 内部表示

```text
// Shared<T> 曾与 Unique<T> 对称存在，用于 Rc/Arc 内部
// 核心问题：Shared 与 Unique 的区分仅在于"拥有 vs 共享"，但两者都提供非空+协变
// 维护两个几乎相同的内部类型增加了 std 复杂度，且无法暴露为稳定 API
```

#### `NonNull<T>`：统一后的稳定抽象

```rust,ignore
use std::ptr::NonNull;

// ✅ NonNull<T> 的核心特性
pub struct NonNull<T: ?Sized> {
    pointer: *const T,  // 用 *const T 包装 *mut T 以实现协变
}

// 1. 非空保证: NonNull::new(ptr) 返回 Option<NonNull<T>>，null 时返回 None
let maybe = NonNull::new(std::ptr::null_mut::<i32>());  // None

// 2. 协变: NonNull<&'a T> 可协变为 NonNull<&'static T>
fn demo_variance<'a>(ptr: NonNull<&'a i32>) -> NonNull<&'static i32> { ptr }

// 3. as_ptr() 获取 *mut T
let mut x = 42;
let nn = NonNull::new(&mut x).unwrap();
unsafe { *nn.as_ptr() = 100; }  // 通过裸指针修改

// 4. Box::from_raw 接收 *mut T，但内部曾使用 NonNull 保证非空
```

#### 演进时间线

```text
Rust 1.0   ──→ Unique<T> 和 Shared<T> 作为内部不稳定类型存在
              Box<T> 内部使用 Unique<T>
              Rc<T>/Arc<T> 内部使用 Shared<T>

Rust 1.25  ──→ PR #45207 引入 NonNull<T> 作为稳定 API
              Unique<T> 和 Shared<T> 被标记为内部使用/弃用
              动机：提供一个与所有权语义解耦的通用非空指针类型

Rust 1.26+ ──→ std 内部逐步用 NonNull 替换 Unique/Shared
              Vec<T> 的 buffer 指针使用 NonNull<T>
              Box<T> 内部表示改为 Unique<T> → 后又调整为直接使用 NonNull

当前状态  ──→ NonNull<T> 是稳定的公开 API
              Unique<T> 在内部仍短暂存在，但已从公开 API 移除
              Shared<T> 完全移除
```

#### 反例：误用 `NonNull` 导致的问题

```rust
use std::ptr::NonNull;

// ❌ 反例: NonNull 不保证指向有效内存，仅保证非空
let dangling = NonNull::<i32>::dangling();  // 合法！但指向对齐的虚假地址
unsafe { *dangling.as_ptr() };  // UB! dangling 指向未分配内存

// ❌ 反例: NonNull 不携带所有权，不会自动 drop
struct BadBox<T> {
    ptr: NonNull<T>,  // 错误：NonNull 不表示所有权，drop 时不会释放内存
}
// 正确做法: Box<T> 在 Drop 中显式 dealloc，NonNull 仅作为内部指针存储
```

> **定理**：`NonNull<T>` 是**类型系统层面的约束**（非空 + 协变），而非**运行时保证**（有效性、生命周期（Lifetimes））。它与 `*mut T` 的边界区别在于：编译器可利用非空性做优化，程序员可利用协变性做类型转换。💡 原创分析

#### `NonNull<T>` 在标准库中的实际使用

`NonNull<T>` 是 Rust 标准库中所有"拥有指向堆内存指针"类型的内部基石。它不携带所有权（Ownership）语义，但提供**非空保证**和**协变性**，使智能指针（Smart Pointer）的实现既高效又类型安全。

| **类型** | **内部指针字段** | **使用 NonNull 的目的** |
|:---|:---|:---|
| `Vec<T>` | `RawVec<T>` → `NonNull<T>` | 保证 buffer 非空（即使空 Vec 也指向对齐的 dangling 地址） |
| `Box<T>` | `Unique<T>` → 后来改为 `NonNull<T>` + `PhantomData<T>` | 非空 + 协变；所有权（Ownership）由 `Box` 结构本身和 `Drop` 实现承担 |
| `Rc<T>` | `NonNull<RcBox<T>>` | 非空 + 协变；共享所有权由引用计数管理 |
| `Arc<T>` | `NonNull<ArcInner<T>>` | 同上，但额外要求 `T: Send` 时 `Arc<T>: Send` |
| `String` | `Vec<u8>` 间接使用 | 通过 `Vec<u8>` 继承 NonNull 保证 |

```rust,ignore
// Vec<T> 的简化内部结构（Rust 1.80+）
pub struct Vec<T> {
    buf: RawVec<T>,           // RawVec 内部持有 NonNull<T>
    len: usize,
}

struct RawVec<T> {
    ptr: NonNull<T>,          // 非空、协变
    cap: usize,
    alloc: Global,            // 分配器
}

impl<T> Vec<T> {
    pub const fn new() -> Vec<T> {
        Vec {
            // 即使空 Vec，ptr 也不是 null，而是 dangling（对齐的合法地址）
            buf: RawVec::NEW, // ptr = NonNull::dangling()
            len: 0,
        }
    }
}

// Box<T> 的简化内部结构
pub struct Box<T: ?Sized>(Unique<T>);  // Unique 内部仍是 NonNull<T> + PhantomData<T>
// 等价语义: NonNull<T> + PhantomData<T> + 自定义 Drop 释放内存
```

> **来源: [Rust RFC 1184](https://github.com/rust-lang/rfcs/pull/1184)** `NonNull<T>` 被设计为与所有权语义解耦：`Box` 通过 `PhantomData<T>` 和自定义 `Drop` 表达所有权，`Rc` 通过引用计数表达共享所有权，`NonNull` 仅负责指针的"非空+协变"类型系统约束。 ✅ 已验证

#### 为什么 `NonNull<T>` 是协变的，而 `*mut T` 是不变的

这是 Rust 类型系统中一个关键的设计决策，涉及**子类型关系**与**内存安全（Memory Safety）**的权衡。

**`*mut T` 为什么是不变的（invariant）**

```text
*mut T 在 T 上是 不变的(invariant):
  如果 T1 ≠ T2，则 *mut T1 既不是 *mut T2 的子类型，也不是超类型。

原因：*mut T 允许写入。若 *mut T 是协变的：
  假设 *mut &'a str <: *mut &'static str（协变假设）
  令 ptr: *mut &'static str = 某个 *mut &'a str 的指针
  通过 ptr 写入一个生命周期更短的 &'b str（b < a）
  然后原指针的持有者将其当作 &'static str 读取
  → 悬垂引用！UB！
```

```rust,ignore
// 若 *mut T 协变，以下代码将不安全：
fn broken_if_covariant<'a>(ptr: *mut &'a str) {
    // 假设 *mut &'a str 可协变为 *mut &'static str
    let static_ptr: *mut &'static str = ptr;  // 非法！如果协变则合法
    unsafe {
        // 写入一个短生命周期的字符串
        *static_ptr = "temp";  // 'static 字面量，暂时安全
    }
    // 但调用方可能传入局部变量的引用，后续再读取...
}
```

**`NonNull<T>` 为什么可以是协变的（covariant）**

```text
NonNull<T> 在 T 上是 协变的(covariant):
  如果 T1 <: T2，则 NonNull<T1> <: NonNull<T2>。

关键技巧：内部使用 *const T 实现！
  pub struct NonNull<T: ?Sized> {
      pointer: *const T,   // ← 用 *const T 而非 *mut T
  }
```

`*const T`（不可变裸指针）天然是**协变的**，因为它只读不写。通过将 `*mut T` 包装在 `*const T` 的字段中，`NonNull<T>` 获得了协变性。但 `NonNull<T>` 仍提供 `as_mut()` 返回 `&mut T`，这是安全的，因为：

1. `NonNull::new()` 保证指针非空
2. `as_mut()` 需要 `unsafe` 调用，调用者需保证别名规则
3. 协变性在**类型转换层面**发生，不涉及运行时写入

```rust,ignore
use std::ptr::NonNull;

// ✅ 协变性演示：NonNull<&'a str> 可协变为 NonNull<&'static str>
fn demo_covariance<'a>(ptr: NonNull<&'a str>) -> NonNull<&'static str> {
    ptr  // 合法！因为 NonNull<&'a str> <: NonNull<&'static str>
}

// 对比：*mut T 是不变的，以下代码会编译失败
fn demo_invariance<'a>(ptr: *mut &'a str) -> *mut &'static str {
    ptr  // ❌ 编译错误：*mut T 在 T 上是不变的
}
```

> **来源: [Rust Reference: Variance](https://doc.rust-lang.org/reference/introduction.html)**
> `*const T` 对 `T` 是协变的，`*mut T` 对 `T` 是不变的。
> `NonNull<T>` 通过内部存储 `*const T` 来实现协变，同时通过 API 设计（`as_mut()` 需要 unsafe）保持写入的安全性。
> ✅ 已验证
> **来源: [Rustonomicon: Variance](https://doc.rust-lang.org/nomicon/index.html)**
> 协变性对容器类型至关重要：`Vec<&'a str>` 可协变为 `Vec<&'static str>`，这使函数返回包含长生命周期（Lifetimes）引用的容器成为可能。
> 若 `Vec` 内部使用 `*mut T` 而非 `NonNull<T>`，它将是不变的，极大限制其可用性。 ✅ 已验证
> **定理**：`NonNull<T>` 的协变设计是**类型系统层面的精巧权衡**
> ——通过 `*const T` 的字段存储获得协变性，通过 `unsafe` API 控制写入风险，从而在"编译器优化假设"（非空性）和"程序员便利"（协变性）之间取得平衡。
> 💡 原创分析
> **跨层映射**: `L3::NonNull` ↔ [`L1::类型系统`](../../01_foundation/02_type_system/01_type_system.md) 协变/逆变/不变 · [`L2::智能指针`](../../02_intermediate/02_memory_management/01_memory_management.md) Box/Rc/Arc 内部实现

---

### 补充章节：`MaybeUninit` 数组初始化模式

> **权威来源**: [Rust Reference: MaybeUninit](https://doc.rust-lang.org/reference/introduction.html) · [Unsafe Code Guidelines: Validity Invariants] · [TRPL Ch19.3](https://doc.rust-lang.org/book/ch20-01-unsafe-rust.html)
> **层级标注**: `L3::未初始化内存` → `L1::所有权` 初始化要求 · `L2::内存管理` 堆栈分配

**定义**：`std::mem::MaybeUninit<T>` 是 Rust 处理**未初始化内存**的官方抽象。
它告知编译器"此位置的 `T` 可能尚未初始化"，从而避免编译器假设所有 `T` 实例都满足 Validity Invariant。

> **[Unsafe Code Guidelines]**
> `MaybeUninit<T>` is the standard and safe way to work with uninitialized memory.
> Its contents are not subject to the validity invariant of `T` until explicitly initialized.
> ✅ 已验证

#### 核心语义对比

| 写法 | 结果 | 是否 UB |
| :--- | :--- | :---: |
| `let x: T = std::mem::uninitialized();` | 假装已初始化 | ❌ UB（读取未初始化 = UB） |
| `let x = MaybeUninit::<T>::uninit().assume_init();` | 假设已初始化 | ⚠️ 若实际未写入则 UB |
| `let mut x = MaybeUninit::<T>::uninit(); x.write(val); x.assume_init()` | 先写后假设 | ✅ 安全（前提是确实写入） |

> **[Rust Reference](https://doc.rust-lang.org/reference/introduction.html)**
> Calling `assume_init()` on a `MaybeUninit<T>` that has not been fully initialized is immediate undefined behavior,
> because it produces a `T` that violates the validity invariant. ✅ 已验证

#### 正确示例：逐个元素初始化数组

```rust
use std::mem::MaybeUninit;

// ✅ 正确: [MaybeUninit<T>; N] 模式，逐个初始化后一次性转换为 [T; N]
fn init_array<T, F>(mut f: F) -> [T; 5]
where
    F: FnMut(usize) -> T,
{
    // 1. 创建未初始化的 MaybeUninit 数组
    let mut arr: [MaybeUninit<T>; 5] = unsafe {
        // Safety: MaybeUninit 不需要初始化
        MaybeUninit::uninit().assume_init()
    };

    // 2. 逐个写入
    for i in 0..5 {
        arr[i].write(f(i));
    }

    // 3. 转换为 [T; 5]（关键：必须确认所有元素已初始化）
    let arr = arr.map(|mut slot| unsafe {
        // Safety: 上面循环保证每个 slot 都已写入
        slot.assume_init()
    });
    arr
}

fn demo() {
    let arr: [i32; 5] = init_array(|i| i as i32 * 10);
    assert_eq!(arr, [0, 10, 20, 30, 40]);
}
```

#### 正确示例：安全封装数组初始化

```rust
use std::mem::MaybeUninit;

// ✅ 更安全的封装：使用指针避免中间状态的 unsafe 暴露
fn init_array_safe<T, const N: usize, F>(mut f: F) -> [T; N]
where
    F: FnMut(usize) -> T,
{
    let mut arr: [MaybeUninit<T>; N] = unsafe { MaybeUninit::uninit().assume_init() };

    for i in 0..N {
        arr[i].write(f(i));
    }

    // 使用 ptr::read 将 MaybeUninit<T> 转为 T，不触发 drop（因为 MaybeUninit 没有实现 Drop）
    unsafe {
        let ptr = arr.as_mut_ptr() as *mut T;
        let result = std::ptr::read(ptr as *const [T; N]);
        // 注意：arr 不会被 drop（MaybeUninit 不 drop 内容），但 result 已拥有所有值
        std::mem::forget(arr);  // 防止 arr 被 drop（虽然无实际影响，但语义清晰）
        result
    }
}
```

#### 反例：错误使用 `assume_init()` 导致 UB

```rust
use std::mem::MaybeUninit;

// ❌ 反例: 对未写入的 MaybeUninit 调用 assume_init()
fn ub_from_uninit() -> String {
    let mut slot = MaybeUninit::<String>::uninit();
    // 忘记调用 slot.write(...)
    unsafe { slot.assume_init() }  // UB! 返回未初始化的 String，其指针字段是随机值
}

// ❌ 反例: 数组部分初始化就转换
fn partial_init_ub() -> [String; 3] {
    let mut arr: [MaybeUninit<String>; 3] = unsafe { MaybeUninit::uninit().assume_init() };
    arr[0].write(String::from("hello"));
    // arr[1] 和 arr[2] 未初始化！
    unsafe {
        std::mem::transmute::<[MaybeUninit<String>; 3], [String; 3]>(arr)
        // UB! 构造包含未初始化 String 的数组
    }
}

// ❌ 反例: 对已初始化的 MaybeUninit 再次 write（内存泄漏）
fn leak_from_overwrite() {
    let mut slot = MaybeUninit::new(String::from("first"));
    slot.write(String::from("second"));  // "first" 被覆盖但未 drop → 内存泄漏（非 UB，但不良）
    let _ = unsafe { slot.assume_init() };  // drop "second"
}
```

#### 边界：`MaybeUninit` 与 `ManuallyDrop`

| 维度 | `MaybeUninit<T>` | `ManuallyDrop<T>` |
|:---|:---|:---|
| 核心目的 | 允许未初始化状态 | 阻止自动 drop |
| `assume_init()` | 提取值后自身失效 | 无此操作 |
| `Drop` 行为 | 不自动 drop 内容 | 包装的值不自动 drop |
| 适用场景 | 延迟初始化 | FFI 边界、联合体字段 |

> **定理**：`MaybeUninit<T>` 是 Rust 中处理**未初始化内存**的**唯一正确抽象**。`std::mem::uninitialized()` 已被弃用；直接使用 `assume_init()` 而不先 `write()` 是触发 UB 的最常见 unsafe 模式之一。💡 原创分析

#### 安全替代：`array::map` 与 `array::from_fn`

Rust 1.63 起，`[T; N]` 上稳定了 `map` 方法；`std::array::from_fn` 在 Rust 1.63 稳定。这两个 API 为**数组初始化**提供了完全安全的替代方案，在多数场景下无需手动使用 `MaybeUninit`。

| **方法** | **签名** | **适用场景** | **与 MaybeUninit 的关系** |
|:---|:---|:---|:---|
| `array::from_fn` | `from_fn(f: FnMut(usize) -> T) -> [T; N]` | 元素值由索引计算得出 | 内部可能使用 MaybeUninit，但对外完全安全 |
| `[T; N]::map` | `map(self, f: FnMut(T) -> U) -> [U; N]` | 已有 `[T; N]`，转换为 `[U; N]` | 消费原数组，安全转换 |
| `[T; N]::try_map`（不稳定） | `try_map(self, f: FnMut(T) -> Result<U, E>) -> Result<[U; N], E>` | 可能失败的转换 | 失败时安全丢弃已创建元素 |

```rust,ignore
// ✅ 安全替代 1: array::from_fn（Rust 1.63+）
use std::array::from_fn;

fn init_with_index() -> [i32; 5] {
    from_fn(|i| i as i32 * 10)  // [0, 10, 20, 30, 40]
}

// ✅ 安全替代 2: array::map（Rust 1.63+）
fn transform_array() -> [String; 3] {
    let nums = [1, 2, 3];
    nums.map(|n| format!("item-{}", n))  // ["item-1", "item-2", "item-3"]
}

// ✅ 安全替代 3: 配合迭代器（若元素由迭代器生成）
fn from_iterator() -> [i32; 5] {
    let iter = (0..5).map(|i| i * 10);
    // 注意：Iterator::collect 到 Vec 再转数组，或直接使用 array::from_fn
    std::array::from_fn(|i| i * 10)
}
```

**什么时候仍需要 `MaybeUninit`？**

```text
安全替代无法覆盖的场景：
  1. 初始化逻辑复杂，无法表示为 FnMut(usize) -> T
  2. 需要逐个处理错误，部分初始化后回滚
  3. 与 unsafe FFI 边界交互（如 C 函数填充数组）
  4. 性能极致优化（避免 array::from_fn 的潜在栈拷贝）
  5. 自定义分配器上的数组分配（非栈/堆标准路径）
```

> **[Rust 1.63 Release Notes](https://releases.rs/docs/1.63.0/)** `array::from_fn` and `array::map` were stabilized to provide safe, ergonomic array initialization without requiring unsafe `MaybeUninit` patterns. ✅ 已验证
> **[std::array::from_fn docs](https://doc.rust-lang.org/std/array/fn.from_fn.html)** `from_fn` 的内部实现使用 unsafe 代码（可能涉及 MaybeUninit）来避免中间状态的泄漏风险，但对外暴露完全 safe 的 API。 ✅ 已验证

#### 与 C 的 `malloc` + 手动初始化的对比

C 语言中动态数组的经典模式与 Rust 的 `MaybeUninit` 模式在**语义**和**安全性**上有本质差异。理解这种对比有助于从系统编程视角把握 `MaybeUninit` 的设计动机。

| **维度** | **C: `malloc` + 手动初始化** | **Rust: `MaybeUninit<T>`** |
|:---|:---|:---|
| **分配方式** | `malloc(N * sizeof(T))` 返回 `void*`，未初始化 | `MaybeUninit::<T>::uninit()` 在栈或堆上分配，标记为未初始化 |
| **类型安全** | ❌ 无类型，`void*` 需强制转换，大小计算易出错 | ✅ 强类型，`[MaybeUninit<T>; N]` 的元素类型是 `MaybeUninit<T>` |
| **初始化方式** | 逐元素赋值或 `memset`/`memcpy` | `slot.write(val)` 或 `ptr::write(ptr, val)` |
| **初始化验证** | ❌ 无编译器验证，忘记初始化某个元素 = 静默 bug | ✅ Miri 可追踪初始化状态，未初始化读取 = 明确 UB 报错 |
| **转换为已初始化** | 隐式：赋值后即视为初始化，无显式边界 | 显式：`assume_init()` 是 unsafe 的，强制程序员确认"已初始化" |
| **Drop 安全** | ❌ C 无析构函数，资源释放完全手动 | ✅ `MaybeUninit` 不自动 drop，但 `assume_init()` 后获得 `T`，离开作用域时自动 drop |
| **部分初始化回滚** | 手动追踪已初始化元素，错误时逐一 `free` | 利用 `Drop` 守卫或 `ManuallyDrop` 实现 RAII 回滚 |

```c
// C 模式：malloc + 手动初始化（无类型安全，无初始化验证）
int* arr = malloc(5 * sizeof(int));  // void* → int*，未初始化内存
if (!arr) { /* 错误处理 */ }

for (int i = 0; i < 5; i++) {
    arr[i] = i * 10;  // 初始化
}
// ⚠️ 如果循环提前 break，arr[3] 和 arr[4] 未初始化，但编译器不报错
// ⚠️ 使用结束后必须 free(arr)，否则泄漏

free(arr);
```

```rust
// Rust 模式：MaybeUninit（强类型 + 状态追踪 + 显式转换）
use std::mem::MaybeUninit;

fn rust_init_array() -> [i32; 5] {
    let mut arr: [MaybeUninit<i32>; 5] = unsafe {
        MaybeUninit::uninit().assume_init()  // 创建未初始化数组
    };

    for i in 0..5 {
        arr[i].write(i as i32 * 10);  // 类型安全：只能写入 i32
    }

    // 显式转换：unsafe 块提醒程序员"必须已初始化"
    arr.map(|slot| unsafe { slot.assume_init() })
}
```

**关键差异分析**

```text
1. 类型系统的角色
   C: malloc 返回 void*，类型信息完全丢失。sizeof 计算错误导致缓冲区溢出。
   Rust: [MaybeUninit<T>; N] 保留完整的类型和长度信息。arr[i].write() 接受 T，
         类型不匹配在编译期报错。

2. 初始化状态的追踪
   C: 编译器不追踪哪些元素已初始化。读取未初始化元素是 UB，但通常表现为"随机值"。
   Rust: Miri 在解释执行时追踪每个 MaybeUninit 槽位的初始化状态。
         未初始化读取 = 明确报错："reading uninitialized memory"。

3. 所有权与资源管理
   C: 分配与释放必须手动配对。异常路径（如中间 return）容易导致泄漏或重复释放。
   Rust: MaybeUninit<T> 本身不实现 Drop，但转换为 T 后由 Rust 所有权系统自动管理。
         可利用 scope guard 模式实现异常安全回滚。
```

```rust,ignore
// Rust 的异常安全回滚模式（对比 C 的复杂错误处理）
fn init_with_rollback<T, const N: usize, F, E>(mut f: F) -> Result<[T; N], E>
where
    F: FnMut(usize) -> Result<T, E>,
{
    let mut arr: [MaybeUninit<T>; N] = unsafe { MaybeUninit::uninit().assume_init() };
    let mut initialized = 0;

    for i in 0..N {
        match f(i) {
            Ok(val) => {
                arr[i].write(val);
                initialized += 1;
            }
            Err(e) => {
                // 安全回滚：只 drop 已初始化的元素
                for j in 0..initialized {
                    unsafe { std::ptr::drop_in_place(arr[j].assume_init_mut()); }
                }
                return Err(e);
            }
        }
    }

    Ok(arr.map(|slot| unsafe { slot.assume_init() }))
}
```

> **[C11 Standard](https://www.iso.org/standard/57853.html)** Reading uninitialized automatic variables results in indeterminate values; this is not explicitly UB in all cases, but using such values can lead to UB. ✅ 已验证
> **来源: [Rust Reference: Behavior considered undefined](https://doc.rust-lang.org/reference/behavior-considered-undefined.html)** Reading uninitialized memory in Rust is immediate undefined behavior, and Miri can detect it precisely. ✅ 已验证
> **定理**：`MaybeUninit<T>` 是 C `malloc` + 手动初始化模式的**类型安全升级版**——它将"未初始化内存"从隐式的 `void*` 状态提升为显式的 `MaybeUninit<T>` 类型，使编译器能够验证类型一致性，使 Miri 能够动态验证初始化完整性，使程序员能够通过 `unsafe { assume_init() }` 的显式边界承担证明责任。💡 原创分析
> **跨层映射**: `L3::MaybeUninit` ↔ [`L1::所有权`](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md) 初始化要求 ·
> [`L2::内存管理`](../../02_intermediate/02_memory_management/01_memory_management.md) RAII ·
> [`L5::对比`](../../05_comparative/01_systems_languages/01_rust_vs_cpp.md) Rust vs C/C++ 内存模型

---

- **演进方向**: 补充 Miri 的使用方法与限制（含 Miri 标志详解与 Valgrind/ASan/TSan 对比） —— 优先级: 低 —— 已完成 2026-05-14
- **演进方向**: 补充 `std::ptr::read/write` vs `*ptr` 解引用的区别 —— 优先级: 中 —— 已完成 2026-05-14
- **演进方向**: 补充 `NonNull<T>` / `Unique<T>` / `Shared<T>` 的演进（含 Vec/Box/Rc/Arc 实际使用与协变原理） —— 优先级: 低 —— 已完成 2026-05-14
- **演进方向**: 补充 `MaybeUninit` 数组初始化模式（含 array::from_fn 安全替代与 C malloc 对比） —— 优先级: 低 —— 已完成 2026-05-14

> **过渡: L3 → L4**
> `unsafe` 块的安全性契约由程序员保证，但这种保证能否被形式化验证？
> RustBelt 将 safe Rust 的语义嵌入 Iris 逻辑并证明其 soundness，而 Aeneas 和 Kani 等工具则尝试将 unsafe 边界上的手工推理自动化。
> 形式化方法不消除 `unsafe`，但能将 "我相信这是安全的" 转化为 "机器验证了这是安全的"。
> 验证框架见 [`../04_formal/04_rustbelt.md`](../../04_formal/02_separation_logic/01_rustbelt.md)，
> 别名模型的精确规则见 [`../04_formal/03_ownership_formal.md`](../../04_formal/01_ownership_logic/02_ownership_formal.md) §5（Tree Borrows / Stacked Borrows 对比）。

---

## 九、Unsafe/FFI 2024：权限分离与显式契约

> **稳定版本**: Rust 2024 Edition（默认行为） · **Rust 1.85.0 随 Edition 2024 稳定**
> **覆盖范围**: `unsafe_op_in_unsafe_fn`、`unsafe extern` blocks、`#[unsafe(...)]` 属性
> **形式化意义**: **调用者权限（unsafe fn / unsafe extern 声明）与实现者权限（unsafe {} 块）的显式分离**

### 9.1 问题：权限的混淆

在 Rust 2021 及之前，`unsafe fn` 的函数体被视为一个**隐式的 `unsafe` 块**：

```rust
// Rust 2021：隐式 unsafe
unsafe fn old_style(ptr: *mut u32) -> u32 {
    *ptr  // 隐式 unsafe，直接解引用
}
```

这混淆了两种权限：

- **`unsafe fn`**: "调用此函数需要 unsafe 权限"（约束**调用者**）
- **`unsafe {}`**: "此块内的操作需要 unsafe 权限"（约束**实现者**）

### 9.2 2024 Edition 的权限分离

```rust
// Rust 2024：显式权限分离
unsafe fn new_style(ptr: *mut u32) -> u32 {
    unsafe { *ptr }  // 实现者的 unsafe 块显式可见
}
```

| 权限层级 | 声明方式 | 约束对象 | 可见性 |
|:---|:---|:---|:---|
| 调用者权限 | `unsafe fn` | 调用者必须包裹 `unsafe {}` | 函数签名 |
| 实现者权限 | `unsafe {}` 块 | 实现者必须显式标记 unsafe 操作 | 函数体内 |

### 9.3 形式化模型：权限的模块化

```text
Rust 2021: unsafe fn f() { *ptr }   // 权限 A ∧ 权限 B 混合
Rust 2024: unsafe fn f() { unsafe { *ptr } }  // 权限 A → 权限 B（分离）

形式化表达：
    unsafe fn f:  ∀ caller. CallerHasUnsafePrivilege → CanCall(f)
    unsafe { e }: ∀ implementer. ImplementerAssertsSafety(e) → CanEvaluate(e)
```

**关键洞察**: 权限分离使代码审查更清晰——每一行 unsafe 操作都可见。这是安全契约的**模块（Module）化**：契约声明（`unsafe fn`）与契约实现（`unsafe {}`）分离。

### 9.4 与 `unsafe extern` + `safe` 的关系

| 机制 | 权限方向 | 粒度 |
|:---|:---|:---|
| `unsafe_op_in_unsafe_fn` | 实现者权限分离 | 函数体内 |
| `unsafe extern` block | 调用者权限声明 | FFI 边界 |
| `safe` in `extern` block | 调用者权限豁免 | FFI 函数级 |

三者共同构成 Rust **unsafe 权限的模块（Module）化体系**：从"块级"向"函数级/操作级"细化。

> **来源: [Rust 2024 Edition Guide](https://doc.rust-lang.org/edition-guide/rust-2024/index.html)** `unsafe_op_in_unsafe_fn` clarifies the separation between caller and implementer unsafe obligations.
> **来源: [RFC 2585](https://rust-lang.github.io/rfcs/2585-unsafe-block-in-unsafe-fn.html)** `unsafe_op_in_unsafe_fn` lint.

### 9.5 `unsafe extern` blocks：FFI 边界的显式 unsafe（Rust 2024）

> **稳定版本**: Rust 1.82.0+ 可用 · **Rust 2024 Edition 强制要求**
> **RFC**: [RFC 3484 — Unsafe Extern Blocks](https://rust-lang.github.io/rfcs/3484-unsafe-extern-blocks.html)
> **官方文档**: [Rust Edition Guide — Unsafe extern blocks](https://doc.rust-lang.org/edition-guide/rust-2024/unsafe-extern.html) · [Rust Reference — External blocks](https://doc.rust-lang.org/reference/items/external-blocks.html)

#### 9.5.1 问题：谁为 FFI 签名负责？

在 Rust 2021 及更早版本中，`extern` 块内的所有函数和静态量都隐式是 `unsafe` 的，但 `extern` 块本身**不必**写 `unsafe`：

```rust
// Rust 2021 及更早：extern 块本身没有 unsafe 标记
extern "C" {
    pub fn sqrt(x: f64) -> f64;        // 调用需要 unsafe {}
    pub fn strlen(p: *const c_char) -> usize; // 调用需要 unsafe {}
}
```

这里存在责任模糊：如果 `extern` 块内的签名写错了，调用时发生 UB，责任在**写 extern 块的人**还是**调用者**？
Rust 2024 的答案是：**写 extern 块的人负责保证签名正确**，因此 extern 块本身必须显式标记为 `unsafe`。

#### 9.5.2 语法与语义

```rust
// Rust 2024：extern 块必须 unsafe
unsafe extern "C" {
    // sqrt 签名简单、调用安全：可标记为 safe，调用时无需 unsafe {}
    pub safe fn sqrt(x: f64) -> f64;

    // strlen 需要合法指针：保持 unsafe，调用者需写 unsafe {}
    pub unsafe fn strlen(p: *const c_char) -> usize;

    // 默认未标注 safe/unsafe 的项，保守视为 unsafe
    pub fn free(p: *mut c_void);

    pub safe static TAU: f64;
}
```

| 写法 | 调用是否需要 `unsafe {}` | 适用场景 |
|:---|:---:|:---|
| `pub safe fn` / `pub safe static` | ❌ 不需要 | 签名已知正确、调用无额外前提 |
| `pub unsafe fn` / `pub unsafe static` | ✅ 需要 | 调用有额外安全前提（如有效指针） |
| 未标注 `safe`/`unsafe` | ✅ 需要（默认 unsafe） | 迁移中或保守处理 |

> **关键洞察**: `unsafe extern` 块表示"我作为作者保证块内所有签名正确"; `safe` 修饰表示"我还保证该项单独调用不会导致 UB"。

#### 9.5.3 版本迁移示例

```rust
// 2021 edition
extern "C" {
    pub fn sqrt(x: f64) -> f64;
}

// 2024 edition
unsafe extern "C" {
    pub safe fn sqrt(x: f64) -> f64;
}
```

迁移工具 `cargo fix --edition` 会自动将 `extern` 块改写为 `unsafe extern`，但不会自动推断哪些项可标 `safe`；开发者需根据 FFI 契约手动标注。

#### 9.5.4 边界与反模式

- `safe` 和 `unsafe` 关键字**仅允许出现在 `unsafe extern` 块内**；旧版 `extern` 块不能标注单个项。
- 在 2024 edition 中，`extern { ... }`（没有 `unsafe`）会编译错误：`extern blocks must be unsafe`。
- `unsafe extern` 在所有 edition 中都会触发 `unsafe_code` lint（若启用 `deny(unsafe_code)` 会被拒绝）。

### 9.6 `#[unsafe(...)]` 属性：链接级 unsafe 契约（Rust 2024）

> **稳定版本**: Rust 1.82.0+ 可用 · **Rust 2024 Edition 强制要求**
> **RFC**: [RFC 3325 — Unsafe Attributes](https://rust-lang.github.io/rfcs/3325-unsafe-attributes.html)
> **官方文档**: [Rust Edition Guide — Unsafe attributes](https://doc.rust-lang.org/edition-guide/rust-2024/unsafe-attributes.html)

#### 9.6.1 哪些属性是 unsafe 的？

Rust 2024 要求以下三个影响链接和符号的属性必须包裹在 `#[unsafe(...)]` 中：

| 属性 | 作用 | 安全要求 |
|:---|:---|:---|
| `no_mangle` | 关闭名称修饰，使用函数原名作为符号 | 必须保证全局符号不冲突 |
| `export_name = "..."` | 显式指定导出符号名 | 必须保证符号名唯一且合法 |
| `link_section = "..."` | 将项放入指定 ELF/Mach-O section | 必须保证 section 使用合法 |

这些属性影响链接器级别的全局命名空间，错误使用可能导致 UB（例如两个函数同名导致链接时冲突）。

#### 9.6.2 语法变化

```rust
// Rust 2021 及更早
#[no_mangle]
pub fn entry_point() {}

#[export_name = "my_custom_symbol"]
pub static FLAG: u32 = 1;

// Rust 2024
#[unsafe(no_mangle)]
pub fn entry_point() {}

#[unsafe(export_name = "my_custom_symbol")]
pub static FLAG: u32 = 1;
```

#### 9.6.3 为什么需要 unsafe 包装？

```rust
// 以下代码在旧版中只包含 safe 代码，但会崩溃（符号名冲突）
#[export_name = "malloc"]
fn foo() -> usize { 1 }

fn main() {
    println!("Hello, world!");
}
```

通过 `#[unsafe(export_name = "...")]`，编译器明确提示："此属性有编译器无法验证的安全要求，需要人工保证"。

#### 9.6.4 迁移与 lint

- 在 Rust 2024 中，`#[no_mangle]` / `#[export_name = ...]` / `#[link_section = ...]` 不加 `unsafe(...)` 会报错。
- 在 Rust 2021/2018/2015 中，Rust 1.82+ 已支持 `#[unsafe(...)]` 写法，旧写法会触发 `unsafe_attr_outside_unsafe` lint（当前 allow-by-default，未来可能收紧）。
- `cargo fix --edition` 可自动将旧写法迁移为 `#[unsafe(...)]`。

> **来源**: [Rust 2024 Edition Guide — Unsafe extern blocks](https://doc.rust-lang.org/edition-guide/rust-2024/unsafe-extern.html) · [Unsafe attributes](https://doc.rust-lang.org/edition-guide/rust-2024/unsafe-attributes.html) · [RFC 3484](https://rust-lang.github.io/rfcs/3484-unsafe-extern-blocks.html) · [RFC 3325](https://rust-lang.github.io/rfcs/3325-unsafe-attributes.html)

---

## 判定表：unsafe 使用与 UB 边界判定

| 场景/条件 | 判定结论 | 依据（定理/规则） | 反例或失效条件 |
|:---|:---|:---|:---|
| Safe Rust 能实现需求 | 不用 unsafe | §6.1 决策树 Q1/A1 | — |
| FFI 调用外部函数 | 用 unsafe 封装 FFI 边界 | §6.1 决策树 A2 | 未封装散落调用 ⟹ 安全审查困难 |
| 性能优化诉求 | 先 profile 确认瓶颈，再用 unsafe + 基准测试 | §6.1 决策树 Q4/A3 | 未经验证的性能假设 ⟹ unsafe 滥用首要根源 |
| 底层内存布局控制 | 用 unsafe，最小化范围 | §6.1 决策树 A4 | 范围越大，不变量维护成本越高 |
| 解引用可能为 null 的裸指针 | UB：段错误/任意行为 | §6.2 E1 | 仅创建不解引用 ⟹ 尚未 UB（§6.2 W1） |
| `transmute` 无关类型 | UB：类型混淆/对齐错误 | §6.2 E2 | 编译通过 ≠ 安全 |
| `unsafe impl Send for Rc<T>` | UB：数据竞争 | §6.2 E3 | auto trait 契约被破坏（见 Send/Sync 权威页） |
| 读取未初始化内存 | UB：读取任意值 | §6.2 E4 | `MaybeUninit` 是合法途径 |
| 验证 unsafe 代码行为 | 用 Miri 按 Tree Borrows 操作语义检测 | §五 别名模型 | Miri 未覆盖全部 UB 种类 ⟹ 通过 Miri ≠ 无 UB |

## 相关概念链接

- **上层概念**: [Ownership](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md) · [Borrowing](../../01_foundation/01_ownership_borrow_lifetime/02_borrowing.md) · [Memory Management](../../02_intermediate/02_memory_management/01_memory_management.md) · [Concurrency](../00_concurrency/01_concurrency.md)

| 概念 | 文件 | 关系 |
|:---|:---|:---|
| 所有权（Ownership） | [](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md) | safe 边界 |
| 借用（Borrowing）规则 | [](../../01_foundation/01_ownership_borrow_lifetime/02_borrowing.md) | unsafe 突破 |
| 内存管理 | [](../../02_intermediate/02_memory_management/01_memory_management.md) | 裸指针 |
| 形式化验证 | [](../../04_formal/02_separation_logic/01_rustbelt.md) | unsafe 证明边界 |
| 安全边界 | [](../../05_comparative/03_domain_comparisons/01_safety_boundaries.md) | 全局边界汇总 |
| Rust 版本特性演进 | [](../../07_future/00_version_tracking/01_rust_version_tracking.md) | `unsafe_op_in_unsafe_fn`、`naked_functions`、`unsafe extern` |
| 异步（Async）与 Unsafe | [](../01_async/01_async.md) | `AsyncFn` 与 unsafe 边界的交互 |
| Unsafe 边界全景 | [02_unsafe_boundary_panorama.md](02_unsafe_boundary_panorama.md) | 边界视角汇总（概念推导在本页，边界全景在该页） |

> **过渡: L3 → L1**
> `unsafe` 不是 Rust 的例外——它是所有权系统的延伸。`unsafe` 块中的原始指针（Raw Pointer）解引用之所以危险，正是因为它绕过了借用（Borrowing）检查器对 `&T`/`&mut T` 的约束。理解 unsafe 的安全契约，需要首先理解 safe Rust 中这些约束的精确含义。
> 安全基础见 [`../01_foundation/01_ownership_borrow_lifetime/02_borrowing.md`](../../01_foundation/01_ownership_borrow_lifetime/02_borrowing.md)（借用（Borrowing）规则）与 [`../01_foundation/01_ownership_borrow_lifetime/01_ownership.md`](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md)（所有权转移）。
> **过渡: L3 → L6**
> `cbindgen`、`cxx`、`diplomat` 等工具将 FFI 的 unsafe 边界自动化，而 `Miri` 和 `Kani` 则在 CI 中持续验证 unsafe 代码的正确性。unsafe 不是 "放弃安全"，而是 "将安全的责任从编译器转移到工具和流程"。
> 工具化实践见 [`../06_ecosystem/01_toolchain.md`](../../06_ecosystem/00_toolchain/01_toolchain.md)（工具链安全审计）与 [`../07_future/02_formal_methods.md`](../../07_future/04_research_and_experimental/02_formal_methods.md)（形式化验证工具）。
---

---

## Wikipedia 概念对齐

> **来源: [Wikipedia](https://en.wikipedia.org/wiki/Main_Page)** 核心概念与国际知识库映射。

| 概念 | Wikipedia 词条 | 说明 |
|:---|:---|:---|
| **Undefined behavior** | [Undefined behavior](https://en.wikipedia.org/wiki/Undefined_behavior) | 未定义行为 |
| **Pointer (computer programming)** | [Pointer (computer programming)](https://en.wikipedia.org/wiki/Pointer_(computer_programming)) | 指针 |
| **Dangling pointer** | [Dangling pointer](https://en.wikipedia.org/wiki/Dangling_pointer) | 悬垂指针 |
| **Buffer overflow** | [Buffer overflow](https://en.wikipedia.org/wiki/Buffer_overflow) | 缓冲区溢出 |
| **Memory safety** | [Memory safety](https://en.wikipedia.org/wiki/Memory_safety) | 内存安全 |
| **Foreign function interface** | [Foreign function interface](https://en.wikipedia.org/wiki/Foreign_function_interface) | FFI |

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/introduction.html), [The Rust Programming Language](https://doc.rust-lang.org/book/ch20-01-unsafe-rust.html), [Rustonomicon](https://doc.rust-lang.org/nomicon/index.html)
> **权威来源对齐变更日志**: 2026-05-19 补全权威来源标注（Rust Reference、TRPL、Rustonomicon、RFCs、学术论文） [Authority Source Sprint Batch 8](../../00_meta/02_sources/05_international_authority_index.md)

**文档版本**: 1.1
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 权威来源索引

---

## 十五、内存模型深度对比：C++ / Java / Rust

「内存模型深度对比：C++ / Java / Rust」部分按内存模型的本质、C++ Memory Model：RC11 与 Promising S…、Java Memory Model：Happens-Before 与…、Rust 内存模型演进等5个方面的顺序逐层展开。

### 15.1 内存模型的本质

内存模型（Memory Model）定义了多线程程序中**内存操作可见性**的规则。它回答：当线程 A 写入变量 `x` 后，线程 B 何时能读到新值？

```text
线程 A:        x = 1;        y = 1;
                  │              │
                  ▼              ▼
线程 B:        r1 = y;       r2 = x;

问题: r1 == 1 && r2 == 0 是否可能？
  - 顺序一致性（Sequential Consistency）: 不可能
  - C++ relaxed order: 可能！（因编译器重排序）
```

### 15.2 C++ Memory Model：RC11 与 Promising Semantics

C++11 引入了标准化的内存模型（C++11 MM），但其复杂性导致了许多 bug。RC11（Repaired C11）和 Promising Semantics 是后续修复工作。

**C++ 内存序（Memory Order）**:

| 顺序 | 保证 | 开销 | Rust 等价 |
|:---|:---|:---:|:---|
| `memory_order_relaxed` | 无同步保证 | 零 | `Ordering::Relaxed` |
| `memory_order_consume` | 数据依赖传递 | 低 | ❌ Rust 不支持 |
| `memory_order_acquire` | Acquire 语义 | 中 | `Ordering::Acquire` |
| `memory_order_release` | Release 语义 | 中 | `Ordering::Release` |
| `memory_order_acq_rel` | Acquire + Release | 中 | `Ordering::AcqRel` |
| `memory_order_seq_cst` | 顺序一致性 | 高 | `Ordering::SeqCst` |

**C++ 的问题**：

```cpp
// C++: 数据竞争 = 未定义行为（UB），即使使用原子变量！
std::atomic<int> x(0);
// 线程 A
x.store(1, std::memory_order_relaxed);
// 线程 B
int r = x.load(std::memory_order_relaxed); // 可能读到 stale 值
```

**Promising Semantics**（POPL 2017）解决了 C++ 模型的一个问题：它提供了一个**可操作的、可组合**的语义框架，将内存操作解释为"承诺"（promises）和"履行"（resolutions）。

### 15.3 Java Memory Model：Happens-Before 与 Final 字段

Java 内存模型基于 **happens-before** 关系：

```text
Happens-Before 规则:
  1. 程序顺序: 同一线程中的操作按代码顺序 happens-before
  2. 监视器锁: unlock(M) happens-before 后续 lock(M)
  3. volatile: volatile 写 happens-before 后续 volatile 读
  4. 线程启动: Thread.start() happens-before 线程内任何操作
  5. 线程终止: 线程内任何操作 happens-before Thread.join() 返回
```

**Java vs C++ 的关键差异**：

| 维度 | C++ | Java |
|:---|:---|:---|
| **数据竞争** | 数据竞争 = UB | 数据竞争 ≠ UB（有定义行为） |
| **普通变量** | 无保证 | 保证"因果性"（causality） |
| **volatile** | 不保证顺序一致 | 保证 happens-before |
| **final 字段** | `const` ≠ 线程安全 | `final` 保证初始化可见性 |
| **安全保证** | 弱（UB 即一切可能） | 强（语言定义所有行为） |

```java
// Java: final 字段保证初始化可见性
class SafePublication {
    final int x; // final 保证：构造完成后，所有线程看到 x 的初始化值
    SafePublication(int v) { this.x = v; }
}
// C++ 没有直接等价物——需用 std::atomic 或 mutex
```

### 15.4 Rust 内存模型演进

Rust 的内存模型继承了 C++11 的基础，但在**别名模型（Aliasing Model）**上经历了多次重大演进：

#### Stacked Borrows（POPL 2019）

Stacked Borrows（SB）是 Rust 第一个系统化的别名模型：

```text
内存位置的状态机:
  Unique（唯一可变引用 &mut T）
    ├── 创建 &mut T → push Unique(tag)
    ├── 创建 &T     → push SharedReadOnly(tag)
    ├── 解引用      → 检查栈顶是否匹配
    └── 引用过期    → pop 到匹配位置

关键规则:
  1. &mut T 是唯一的——创建新的 &mut T 或 &T 会使旧的 &mut T 失效
  2. &T 是共享的——多个 &T 可以共存
  3. 不允许 *mut T 和 &T/&mut T 混用（除非通过 UnsafeCell）
```

#### Tree Borrows（PLDI 2023）

Tree Borrows（TB）修复了 SB 的多个问题：

| SB 问题 | TB 修复 |
|:---|:---|
| `&T` 和 `*mut T` 的良性混用被禁止 | 引入 `Foreign` 读权限，允许外部读取 |
| 循环引用结构中的借用失效 | 树形结构追踪，局部失效而非全局失效 |
| 某些合法 unsafe 代码被误判 | 更精确的权限传播 |

```text
Tree Borrows 的权限树:
  root: Unique (起始 &mut T)
    ├── child1: SharedReadOnly (&T 派生)
    │     └── child1.1: SharedReadOnly (再派生 &T)
    ├── child2: Unique (重新借用 &mut T)
    │     └── child2.1: SharedReadOnly
    └── child3: Reserved (未来可能写)
```

#### Provenance（PLDI 2022）

Gheri & Watt 提出了 **Provenance** 模型：

```text
指针的 Provenance（来源）:
  - 每个指针值携带其"来源"（从哪个分配获得的）
  - 指针算术必须在同一 provenance 内进行
  - 不同 provenance 的指针不能比较或相减
```

> **关键洞察**: Rust 内存模型的演进反映了"安全保证与表达力之间的张力"。Stacked Borrows 过于严格，Tree Borrows 放宽了约束但仍保持安全保证，Provenance 则试图与 C 标准对齐。这种演进与 C++ 内存模型从 C++11 到 RC11 的修复过程形成镜像。[💡 原创分析](../../00_meta/00_framework/methodology.md) · [Jung et al.] ✅

### 15.5 跨语言内存模型对比矩阵

| 维度 | C++ (RC11) | Java | Rust (Tree Borrows) |
|:---|:---|:---|:---|
| **数据竞争** | UB | 定义行为（保留因果性） | UB（但 Miri 检测） |
| **原子操作（Atomic Operations）** | `memory_order` 六级 | `volatile` + `AtomicInteger` | `Ordering` 四级 |
| **别名分析** | 类型基础别名规则（TBAA） | 无（GC 管理） | Tree Borrows 动态追踪 |
| **指针 provenance** | 活跃讨论（P2188） | 无（引用不能算术） | Provenance 模型 |
| **形式化验证** | 困难（Promising Semantics） | JMM 已形式化 | RustBelt + Stacked/Tree Borrows |
| **工业工具** | ThreadSanitizer | JFR + JMC | Miri + Kani |

---

## 十六、边界测试：Unsafe 代码的编译错误与运行时灾难

本节将「边界测试：Unsafe 代码的编译错误与运行时灾难」分解为若干主题：边界测试：裸指针解引用前的空检查（编译错误）、边界测试：将 &T 转换为 &mut T（编译错误）、边界测试：无效 UTF-8 的 str::from_utf8_unch…、边界测试：通过 `&T` 获取 `&mut T`（编译错误）等7个方面。

### 16.1 边界测试：裸指针解引用前的空检查（编译错误）

```rust,ignore
fn main() {
    let ptr: *const i32 = std::ptr::null();
    // ❌ 编译错误: 即使 unsafe 块也不能解引用空指针而不检查
    // 实际上 unsafe { *ptr } 可以编译，但运行时 panic/UB
    unsafe {
        println!("{}", *ptr); // 运行时 UB: 空指针解引用
    }
}
```

> **修正**: 解引用裸指针前必须检查 `!ptr.is_null()`。即使如此，仍可能悬垂——unsafe 代码的正确性由程序员保证。

### 16.2 边界测试：将 &T 转换为 &mut T（编译错误）

```rust,compile_fail
fn main() {
    let x = 5;
    let r = &x as *const i32 as *mut i32;
    // ❌ 编译错误: cannot cast `*const i32` to `*mut i32`
    // Rust 禁止直接转换，防止共享引用变可变引用
    unsafe {
        *r = 10; // 若转换成功，这会破坏不可变性保证
    }
}
```

> **修正**: `&T` 到 `&mut T` 的转换必须通过 `UnsafeCell<T>` 进行，这是 Rust 中唯一允许从共享引用获取可变引用（Mutable Reference）的安全途径。

### 16.3 边界测试：无效 UTF-8 的 str::from_utf8_unchecked（运行时 UB）

```rust
fn main() {
    let invalid = vec![0x80, 0x81, 0x82]; // 无效 UTF-8 序列
    // ⚠️ 运行时 UB: from_utf8_unchecked 要求输入必须是有效 UTF-8
    let s = unsafe { std::str::from_utf8_unchecked(&invalid) };
    // 后续对 s 的操作可能导致 panic 或未定义行为
}
```

> **修正**: 除非 100% 确定输入有效，否则使用 `std::str::from_utf8`（返回 `Result`）而非 `from_utf8_unchecked`。
> **相关判定树**: [Unsafe 判定树](../../00_meta/00_framework/concept_definition_decision_forest.md#九unsafe-判定树)
> **相关 FTA**: [Unsafe 契约失效树](../../00_meta/00_framework/fault_tree_analysis_collection.md#六unsafe-契约失效树) · [内存安全（Memory Safety）失效树](../../00_meta/00_framework/fault_tree_analysis_collection.md#二内存安全失效树)

### 16.4 边界测试：通过 `&T` 获取 `&mut T`（编译错误）

```rust,compile_fail
fn main() {
    let x = 5;
    let r = &x;
    // ❌ 编译错误: 不能从共享引用 `&T` 获取可变引用 `&mut T`
    // 这是 Rust 借用检查器的核心保证
    let r_mut = r as *const i32 as *mut i32;
    unsafe {
        *r_mut = 10; // 即使 unsafe 块也不允许这种转换
    }
}
```

> **修正**: 从 `&T` 获取 `&mut T` 的唯一安全途径是通过 `UnsafeCell<T>`。任何绕过此限制的方式都破坏 Rust 的别名规则。

### 16.5 边界测试：裸指针算术越界（运行时 UB）

```rust
fn main() {
    let arr = [1, 2, 3];
    let ptr = arr.as_ptr();
    // ⚠️ 运行时 UB: 越界裸指针即使不立即解引用也构成 UB
    let bad = unsafe { ptr.add(100) }; // 越界，违反 LLVM 指针范围假设
    // unsafe { println!("{}", *bad); } // 若解引用则立即崩溃
}

// 正确: 始终在访问前检查边界
fn safe_access() {
    let arr = [1, 2, 3];
    let ptr = arr.as_ptr();
    let idx = 1usize;
    if idx < arr.len() {
        unsafe {
            println!("{}", *ptr.add(idx)); // ✅ 边界内访问
        }
    }
}
```

> **修正**: 裸指针算术（`.add()`, `.offset()`）必须保证结果指针在原始分配对象的范围内或刚好越过末尾（one-past-the-end）。越界裸指针是未定义行为，即使不立即解引用也可能触发编译器优化假设破坏。[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/index.html)]

### 16.6 边界测试：`std::mem::transmute` 类型大小不匹配（编译错误）

```rust,compile_fail
fn main() {
    let x: u32 = 0x12345678;
    // ❌ 编译错误: cannot transmute between types of different sizes
    let y: u64 = unsafe { std::mem::transmute(x) };
    // u32 (4 bytes) 与 u64 (8 bytes) 大小不同，禁止 transmute
}

// 正确: 仅 transmute 相同大小的类型
fn safe_transmute() {
    let x: u32 = 0x12345678;
    let y: [u8; 4] = unsafe { std::mem::transmute(x) }; // ✅ 同为 4 字节
    println!("{:?}", y);
}
```

> **修正**: `std::mem::transmute` 要求源类型和目标类型必须具有完全相同的内存布局大小。大小不匹配会在编译期报错。即使大小相同，transmute 也可能导致类型语义破坏（如将整数 transmute 为指针）。[来源: [Rust Reference](https://doc.rust-lang.org/reference/introduction.html)]
> **相关判定树**: [Unsafe 判定树](../../00_meta/00_framework/concept_definition_decision_forest.md#九unsafe-判定树)
> **相关 FTA**: [Unsafe 契约失效树](../../00_meta/00_framework/fault_tree_analysis_collection.md#六unsafe-契约失效树) · [内存安全（Memory Safety）失效树](../../00_meta/00_framework/fault_tree_analysis_collection.md#二内存安全失效树)

### 10.4 边界测试：`union` 的字段访问与活跃字段跟踪（运行时 UB）

```rust,ignore
union MyUnion {
    i: i32,
    f: f32,
}

fn main() {
    let mut u = MyUnion { i: 1 };
    // ❌ 运行时 UB: 读取未初始化的字段（上次写入的是 i，读取 f）
    unsafe {
        let f = u.f; // i32 的位模式 reinterpret 为 f32
        println!("{}", f);
    }
}
```

> **修正**:
> Rust 的 `union` 类似于 C 的 union：
> 所有字段共享同一内存，但 Rust 的借用检查器**不跟踪**哪个字段是"活跃的"（最近写入的）。
> 读取未初始化的字段（或写入一个字段后读取另一个字段）是**safe**的语法（在 `unsafe` 块中），但值是底层位的重新解释，可能无意义。
> 安全使用：
>
> 1) 使用 `ManuallyDrop<T>` 包装非 `Copy` 字段（union 的字段默认需实现 `Copy`）；
> 2) 手动跟踪活跃字段（通过外部状态）；
> 3) 优先使用 `enum`（tagged union，编译器跟踪变体）。
>
> `union` 的用途：
>
> 1) FFI（C 结构体（Struct）中的 union）；
> 2) 手动内存布局优化；
> 3) 类型双关（type punning）。
> 这与 C 的 union（无活跃字段跟踪，完全信任程序员）或 Swift 的 enum with associated values（ tagged union，安全）不同
> ——Rust 的 union 是底层原语，需 unsafe 使用。
> [来源: [Rust Reference — Unions](https://doc.rust-lang.org/reference/items/unions.html)] ·
> [来源: [The Rustonomicon](https://doc.rust-lang.org/nomicon/index.html)]

## 逆向推理链（Backward Reasoning）

> **从 UB 反推安全条件**：
>
> ```text
> safe 接口可信 ⟸ unsafe 实现正确 + safe 接口封装 + 人工证明
> Miri 报错 ⟸ 程序违反了 Stacked/Tree Borrows 别名模型
> ```
>
> **诊断方法**：
>
> - Miri: error: Undefined Behavior (dangling pointer) → 违反了 T2(引用有效性) → 检查裸指针生命周期
> - Miri: error: Undefined Behavior (data race) → 违反了 T5(无数据竞争) → 检查 UnsafeCell 使用或原子序数
> - Miri: error: invalid enum value → Validity Invariant 违反 → 检查 transmute 的目标类型

## 参考来源

> [来源: [RFC 2585 — Unsafe Op in Unsafe Fn](https://rust-lang.github.io/rfcs//2585-unsafe-block-in-unsafe-fn.html)]
> [来源: [Rust Unsafe Code Guidelines](https://rust-lang.github.io/unsafe-code-guidelines/)]
> [来源: [Miri — Undefined Behavior Detection](https://github.com/rust-lang/miri)]
> [来源: [Stacked Borrows Paper](https://plv.mpi-sws.org/rustbelt/stacked-borrows/)]
> [来源: [Tree Borrows](https://perso.crans.org/vanille/treebor/)]

### 16.7 前沿方向：Unsafe Fields（字段级 unsafe，Rust 2026 Project Goal）

> **[来源: [Rust Project Goals 2026 — Unsafe Fields](https://rust-lang.github.io/rust-project-goals/2026/unsafe-fields.html)]** ·
> **[来源: [RFC 3908 — Unsafe Fields](https://github.com/rust-lang/rfcs/pull/3908)]**

**核心命题**：
当前 Rust 的 `unsafe` 粒度是**整个结构体（Struct）**——如果结构体包含需要 unsafe 初始化的字段（如自引用、未对齐数据、原始句柄），则整个结构体的构造和使用都被 unsafe 污染。
Unsafe Fields 提议将 unsafe 粒度下沉到**字段级别**。

**语法草案**（仍在设计中）：

```rust,ignore
// 当前 Rust: 整个结构体被 unsafe 污染
pub struct IoUring {
    fd: i32,           // 普通字段
    sq: SubmissionQueue, // 包含裸指针，需 unsafe 初始化
    cq: CompletionQueue, // 包含裸指针，需 unsafe 初始化
}

// Unsafe Fields 目标: 仅特定字段标记为 unsafe
pub struct IoUring {
    fd: i32,
    unsafe sq: SubmissionQueue, // 仅此字段的访问需 unsafe
    unsafe cq: CompletionQueue,
}

// 使用方可以安全地访问 fd，但访问 sq/cq 需 unsafe
fn inspect(ring: &IoUring) {
    println!("fd = {}", ring.fd);        // ✅ safe
    // unsafe { println!("{:?}", ring.sq); } // 需 unsafe 块
}
```

**形式模型意义**：

| 维度 | 当前（结构体（Struct）级） | 目标（字段级） |
|:---|:---|:---|
| **安全契约粒度** | 整个类型 | 单个字段 |
| **API 设计** | 结构体（Struct）构造函数必须 unsafe | 仅 unsafe 字段的 setter/getter 需 unsafe |
| **误用风险** | 高——用户被迫在更大范围内使用 unsafe | 低——unsafe 范围精确到字段访问 |
| **编译器验证** | 无字段级追踪 | 需扩展借用检查器，追踪字段级 unsafe 状态 |

> **关键洞察**: Unsafe Fields 是 Rust "显式化 Unsafe 边界"趋势的延续（Rust 2024 Edition 的 `unsafe_op_in_unsafe_fn` 是同一方向的先前步骤）。
> 它将 Rust 的**效果系统**（effect system）从函数级扩展到字段级，为未来更细粒度的 effects（如 `const`、`async`、`unsafe` 的组合）铺平道路。
> [来源: [Rust Internals — Unsafe Fields Discussion](https://internals.rust-lang.org/t/semi-rfc-unsafe-fields/2550)] ·
> [来源: [Rust Project Goals 2026 — Unsafe Fields](https://rust-lang.github.io/rust-project-goals/2026/unsafe-fields.html)]
> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/introduction.html) ·
> [The Rust Programming Language](https://doc.rust-lang.org/book/ch20-01-unsafe-rust.html) ·
> [Rust Standard Library](https://doc.rust-lang.org/std/index.html) ·
> [Rustonomicon](https://doc.rust-lang.org/nomicon/index.html)

## Null 指针有效性定义

Rust 对 `std::ptr::null()` 和 `NonNull` 的有效性语义有精确定义，明确区分了**已分配但未初始化**与**未分配**的指针状态：

```rust
use std::ptr::NonNull;

// Rust 1.96+: NonNull::new 语义更清晰
let ptr: Option<NonNull<i32>> = NonNull::new(std::ptr::null_mut());
assert!(ptr.is_none());  // null 明确不被视为 valid

// 已分配但未初始化的内存指针是 valid（但不可安全解引用）
let layout = std::alloc::Layout::new::<i32>();
let raw = unsafe { std::alloc::alloc(layout) };
assert!(!raw.is_null());  // alloc 返回的指针保证 non-null
```

> **语义**: 此前 Rust 对 "valid pointer" 的定义在标准库文档、Reference 和 Miri 之间存在细微不一致。1.96 的统一定义明确了：
>
> 1. **null 不是 valid** — 即使不进行解引用，将 null 传递给期望 valid pointer 的 API 是 UB
> 2. **已分配但未初始化是 valid** — `NonNull::new_unchecked` 可用于 `alloc` 返回的指针
> 3. **dangling 指针在特定条件下 valid** — 只要偏移计算不越界，dangling pointer 的算术运算仍合法
>
> 这为 Miri 的严格检查、 unsafe 代码指南和形式化验证工具（如 RustBelt）提供了统一基础。[来源: [Rust 1.96 Release Notes](https://releases.rs/docs/1.96.0/)] · [来源: [Rust Reference — Pointer Validity](https://doc.rust-lang.org/reference/behavior-considered-undefined.html)]

---

---

## 实践

> 将本节概念转化为可编译代码。

### 对应代码示例

- **[crates/c01_ownership_borrow_scope](../../../crates/c01_ownership_borrow_scope)** — 与本节概念对应的可编译 crate 示例
- **[exercises/src/unsafe_rust/](../../../exercises/src/unsafe_rust)** — 配套练习题

### 建议练习

1. 阅读 `crates/c01_ownership_borrow_scope/` 中与"Unsafe Rust"相关的源码和示例
2. 运行 `cargo test -p c01_ownership_borrow_scope` 验证理解
3. 完成 `exercises/src/unsafe_rust/` 中的练习任务
4. 完成 [L3 Unsafe Rust 测验](05_quiz_unsafe.md) 验证理解程度

---

## 导航：下一步去哪？

> **自检**：你当前掌握的核心概念是否已能独立应用？

| 选择 | 条件 | 目标 |
|:---|:---|:---|
| 🔙 巩固基础 | 仍有模糊概念 | 回到 [L2 对应主题](../02_intermediate) 或 [MVP 学习路径](../../00_meta/04_navigation/08_learning_mvp_path.md) |
| 🔜 深入 L3 其他主题 | 想扩展高级技能 | [L3 README](../README.md) 选择其他主题 |
| 🎓 进入 L4 形式化 | 想理解"为什么"的数学证明 | [L4 形式化](../../04_formal/README.md) |
| 🏗️ 进入 L6 生态 | 想掌握生产工具链 | [L6 生态](../../06_ecosystem/README.md) |

---

## 嵌入式测验

「嵌入式测验」部分按测验 1：unsafe 块的能力（记忆层）、测验 2：unsafe fn 与 unsafe 块的区别（理解层）、测验 3：裸指针安全解引用（应用层）与测验 4：unsafe impl 的契约（分析层）的顺序逐层展开。

### 测验 1：unsafe 块的能力（记忆层）

**题目**: 在 Rust 中，`unsafe` 块允许执行以下哪些操作？（多选）

- A. 解引用裸指针
- B. 调用 `unsafe` 函数或方法
- C. 实现 `unsafe` trait
- D. 修改全局可变静态变量
- E. 访问 `union` 的字段

<details>
<summary>✅ 答案与解析</summary>

**正确答案是 A、B、C、D、E**（全部）。

Rust 中 `unsafe` 块的 **5 种能力** 来源: [Rust Reference](https://doc.rust-lang.org/reference/introduction.html)：

1. **解引用裸指针**（`let x = *raw_ptr;`）
2. **调用 `unsafe` 函数或方法**（包括 FFI 函数）
3. **实现 `unsafe` trait**（`unsafe impl Foo for Bar {}`）
4. **访问或修改可变静态变量**（`static mut`）
5. **访问 `union` 的字段**（需要知道当前激活的变体）

**关键理解**: `unsafe` 不是"关闭借用检查器"，而是将**证明安全性的责任**从编译器转移给程序员。`unsafe` 块内的操作仍需要满足 Rust 的安全不变量。
</details>

---

### 测验 2：unsafe fn 与 unsafe 块的区别（理解层）

**题目**: 以下代码的输出是什么？为什么？

```rust,compile_fail
unsafe fn dangerous() {
    println!("called");
}

fn main() {
    dangerous();
}
```

- A. 输出 "called"
- B. 编译错误：调用 `unsafe fn` 需要 `unsafe` 块
- C. 运行时 panic
- D. 编译错误：`dangerous` 不能在 `main` 中调用

<details>
<summary>✅ 答案与解析</summary>

**正确答案是 B**。

在 Rust 中：

- **`unsafe fn`**: 函数体内部可以执行 unsafe 操作，但调用者也必须在 `unsafe` 块中调用
- **`unsafe` 块**: 允许在其中执行 unsafe 操作

正确写法：

```rust,ignore
fn main() {
    unsafe {
        dangerous();
    }
}
```

**设计意图**: `unsafe fn` 的声明是一种**契约**——"这个函数有前置条件，调用者负责满足"。调用处必须使用 `unsafe` 块，明确标记"我承担了这个责任"。
</details>

---

### 测验 3：裸指针安全解引用（应用层）

**题目**: 以下代码有什么问题？如何修复？

```rust
fn main() {
    let x = 5;
    let r = &x as *const i32;
    let val = unsafe { *r };
    println!("{}", val);
}
```

- A. 没有使用 `unsafe` 块
- B. 代码是正确的，输出 5
- C. `r` 可能成为悬垂指针，因为 `x` 在作用域结束时释放
- D. 应该使用 `Box::into_raw` 而不是引用转裸指针

<details>
<summary>✅ 答案与解析</summary>

**正确答案是 B**。

这个代码是**正确的**：

- `x` 在 `main` 的作用域内有效
- `r` 指向 `x`
- 在 `x` 仍有效时解引用 `r` 是安全的

输出：`5`

但如果代码改成：

```rust
fn get_dangling() -> *const i32 {
    let x = 5;
    &x as *const i32  // ❌ x 在函数返回后释放
}
```

就会返回悬垂指针。**裸指针不保证生命周期正确性**，这是使用 `unsafe` 时需要手动保证的。

**安全替代**: 尽可能使用引用（`&T` / `&mut T`），它们有编译器检查的生命周期。
</details>

---

### 测验 4：unsafe impl 的契约（分析层）

**题目**: 以下代码试图为一个自定义类型实现 `Send`，为什么这是 `unsafe` 的？何时是安全的？

```rust
struct MyType {
    data: *const u8,
}

unsafe impl Send for MyType {}

fn main() {
    let x = MyType { data: std::ptr::null() };
    std::thread::spawn(move || {
        // 使用 x
    });
}
```

- A. 编译错误：`*const u8` 未实现 `Send`
- B. `unsafe impl Send` 总是安全的，因为 `Send` 只是标记 trait
- C. 仅当 `data` 指向的内存可以安全地跨线程共享时才安全
- D. 仅当 `MyType` 不包含任何字段时才安全

<details>
<summary>✅ 答案与解析</summary>

**正确答案是 C**。

`Send` 和 `Sync` 是 **unsafe auto trait**，它们的实现需要程序员手动保证线程安全：

- **`Send`**: 类型可以安全地转移到另一个线程
- **`Sync`**: 类型可以安全地在多个线程间共享引用

`MyType` 包含 `*const u8`，而原始指针（Raw Pointer）默认不实现 `Send`。`unsafe impl Send for MyType {}` 是**将证明责任转移给程序员**——你必须确保 `data` 指向的内存在跨线程移动后仍然有效且没有数据竞争。

**安全条件**:

1. `data` 指向的内存有有效的生命周期
2. 多个线程不会同时读写同一块内存（或适当的同步）
3. 目标类型遵循 `Send` 的语义契约

**常见正确做法**:

- 如果 `data` 实际上是一个 `Arc<T>` 的内部指针，通常不应该手动实现 `Send`
- 如果 `data` 指向的是线程局部或全局只读内存，可能可以安全实现

</details>

---

> **测验设计来源**: [Bloom Taxonomy 2001] · [Rust Reference — Unsafe Operations](https://doc.rust-lang.org/reference/unsafe-blocks.html) · [Rustonomicon](https://doc.rust-lang.org/nomicon/index.html)

## 九、Rustonomicon 实现深度

> **来源**: [The Rustonomicon](https://doc.rust-lang.org/nomicon/index.html) ·
> [Rust Standard Library Source](https://github.com/rust-lang/rust/tree/master/library) ·
> [Rust Reference: Drop Check](https://doc.rust-lang.org/reference/destructors.html)

本章节从 Rustonomicon 视角出发，拆解四个经典 unsafe 实现：**`Vec<T>`、`Arc<T>`、`Mutex<T>` 与 Drop-Check**。理解这些实现是掌握"安全抽象 = unsafe 实现 + safe 接口 + 人工证明"这一范式的关键。

### 9.1 实现 `Vec<T>` 的核心 unsafe 技术

`Vec<T>` 是 Rust 标准库中最具代表性的 unsafe 安全抽象。其内部结构可简化为：

```rust,ignore
pub struct Vec<T> {
    buf: RawVec<T>, // 管理容量与堆内存
    len: usize,     // 当前元素数量
}

struct RawVec<T> {
    ptr: NonNull<T>,
    cap: usize,
}
```

关键 unsafe 决策：

| 问题 | 解决方案 | 安全契约 |
|:---|:---|:---|
| 空 Vec 不分配堆内存 | `NonNull::dangling()` 提供对齐的非空占位指针 | 长度必须为 0，任何访问前检查 `len` |
| 增长 buffer | `alloc::alloc(Layout::array::<T>(new_cap).unwrap())` | 旧内存内容按位复制到新内存，旧 buffer 释放 |
| `push` | `ptr::write(self.as_mut_ptr().add(len), value)` | 目标位置未初始化，必须用 `ptr::write` 避免 drop 旧值 |
| `pop` | `ptr::read(self.as_mut_ptr().add(len - 1))` + `len -= 1` | 读取后原位置逻辑失效，不能再次 drop |
| `Drop` | 逐个调用 `ptr::drop_in_place`，再释放 buffer | 必须确保每个初始化元素被 drop 且仅 drop 一次 |

**`push` 的简化实现**：

```rust,ignore
pub fn push(&mut self, value: T) {
    if self.len == self.buf.cap {
        self.buf.grow();
    }
    unsafe {
        ptr::write(self.as_mut_ptr().add(self.len), value);
    }
    self.len += 1;
}
```

### 9.2 实现 `Arc<T>`：原子引用计数

`Arc<T>` 允许多线程共享所有权，核心是在堆上分配一个包含引用计数和数据的 `ArcInner<T>`：

```rust,ignore
struct ArcInner<T> {
    strong: AtomicUsize, // 强引用计数
    weak: AtomicUsize,   // 弱引用计数（含所有 Arc）
    data: T,
}

pub struct Arc<T> {
    ptr: NonNull<ArcInner<T>>,
    _marker: PhantomData<ArcInner<T>>,
}
```

关键 unsafe 技术：

- **`NonNull<ArcInner<T>>`**：保证内部指针非空，使 `Arc<T>` 本身可以是 covariant over `T`。
- **原子操作（Atomic Operations）**：
  - `clone`：`fetch_add(1, Acquire)` 或 `Relaxed`（视具体内存序要求）。
  - `drop`：`fetch_sub(1, Release)`；若减到 0，使用 `fence(Acquire)` 保证 `data` 的写操作对释放线程可见，再 drop `data`。
- **`unsafe impl Send/Sync`**：
  - `Arc<T>: Send` 要求 `T: Send + Sync`（共享引用可跨线程）。
  - `Arc<T>: Sync` 要求 `T: Send + Sync`。

### 9.3 实现 `Mutex<T>`：互斥与 poisoning

标准库 `Mutex<T>` 的简化核心：

```rust,ignore
pub struct Mutex<T> {
    inner: sys::Mutex, // 平台相关底层锁
    poison: Cell<bool>, // 标记是否在持有锁时 panic
    data: UnsafeCell<T>,
}

unsafe impl<T: Send> Send for Mutex<T> {}
unsafe impl<T: Send> Sync for Mutex<T> {}
```

- **`UnsafeCell<T>`**：提供内部可变性，允许在 `&Mutex<T>` 下修改 `T`。
- **`Send + Sync` 条件**：`Mutex<T>: Sync` 只要 `T: Send`，因为锁保证了任意时刻只有一个线程能访问 `T`。
- **Poisoning**：如果线程在持有 `MutexGuard` 时 panic，`Drop` 将 `poison` 设为 `true`，后续 `lock()` 返回 `PoisonError`，提示调用者数据可能处于不一致状态。

### 9.4 Drop-Check（dropck）与 `#[may_dangle]`

Drop-Check 是借用检查器的一个扩展，确保在 drop 时不会访问已经失效的引用。

#### 9.4.1 基本问题

```rust,ignore
pub struct Foo<'a> {
    x: &'a i32,
}

impl<'a> Drop for Foo<'a> {
    fn drop(&mut self) {
        println!("{}", self.x); // 若 'a 已失效，则悬垂引用
    }
}
```

Rust 要求：**若类型实现 `Drop`，则其生命周期参数必须严格长于该类型本身**。这就是 dropck 规则。

#### 9.4.2 `#[may_dangle]`

某些类型（如 `Box<T>`、`Vec<T>`）的 `Drop` 实现实际上不会访问泛型（Generics）参数 `T`。若严格遵守 dropck，会导致过度保守的借用错误。`#[may_dangle]` 属性告诉编译器：

> 此 `Drop` 实现不会访问标记为 `#[may_dangle]` 的类型参数，请放宽 dropck 检查。

```rust,ignore
unsafe impl<#[may_dangle] T: ?Sized> Drop for Box<T> {
    fn drop(&mut self) {
        // 仅释放内存，不访问 T 的内容
    }
}
```

**注意**：`#[may_dangle]` 是 `unsafe` 属性，因为错误使用会导致 drop 时访问已释放内存。标准库中仅对确实不访问 `T` 的类型使用。

#### 9.4.3 `PhantomData<T>` 与 dropck

对于自定义容器，若 `T` 不直接作为字段出现（如通过裸指针持有），需要用 `PhantomData<T>` 向编译器声明"逻辑上拥有 `T`"，以确保 dropck 正确推断：

```rust,ignore
pub struct MyBox<T: ?Sized> {
    ptr: NonNull<T>,
    _marker: PhantomData<T>, // 声明逻辑所有权
}
```

> **定理**: `PhantomData<T>` 不改变运行时表示，但影响编译期的 variance、dropck 与 auto trait 推导。

---

## 自 docs/05_guides/05_unsafe_rust_guide.md 合并的补充内容

> **合并说明**: 以下内容来自 `docs/05_guides/05_unsafe_rust_guide.md`（2026-06-10 最后更新），
> 该文档侧重工程实践与 Rustonomicon 逐章对标。因其内容已被 `concept/03_advanced/02_unsafe/01_unsafe.md`
> 覆盖或更具权威性，此处仅保留其独特的 Rustonomicon 对标表与学习路径，作为补充参考。

### 🔗 推荐学习路径
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**
> **对应 Nomicon 阅读顺序**:
> [Meet Safe and Unsafe](https://doc.rust-lang.org/nomicon/meet-safe-and-unsafe.html) →
> [How Safe and Unsafe Interact](https://doc.rust-lang.org/nomicon/safe-unsafe-meaning.html) →
> [What Unsafe Rust Can Do](https://doc.rust-lang.org/nomicon/what-unsafe-does.html) →
> [Working with Unsafe](https://doc.rust-lang.org/nomicon/working-with-unsafe.html)

1. **通读 Nomicon 前 4 节**（Meet Safe、Interact、What Unsafe Does、Working with Unsafe）
2. 学习 C01 的零成本抽象（Zero-Cost Abstraction）与高级所有权
3. 研究本项目 `formal_methods` 中的形式化证明
4. 实践：为现有安全 API 编写 `unsafe` 实现（如自定义集合）

---

### 📖 Rustonomicon 逐章对标表
>
> **[来源: [crates.io](https://crates.io/)]**

| Nomicon 章节 | 官方链接 | 本指南对应小节 |
| :--- | :--- | :--- |
| **Meet Safe and Unsafe** | [meet-safe-and-unsafe](https://doc.rust-lang.org/nomicon/meet-safe-and-unsafe.html) | § 文档定位、§ 何时使用 Unsafe |
| **How Safe and Unsafe Interact** | [safe-unsafe-meaning](https://doc.rust-lang.org/nomicon/safe-unsafe-meaning.html) | § 安全抽象原则 |
| **What Unsafe Can Do** | [what-unsafe-does](https://doc.rust-lang.org/nomicon/what-unsafe-does.html) | § 核心 Unsafe 操作、§ UB 案例 |
| **Working with Unsafe** | [working-with-unsafe](https://doc.rust-lang.org/nomicon/working-with-unsafe.html) | § 安全抽象原则、§ 推荐学习路径 |
| **Data Layout** | [data](https://doc.rust-lang.org/nomicon/data.html) | 本项目 [type_system](../../../docs/02_reference/quick_reference/02_type_system.md) |
| **Ownership** | [ownership](https://doc.rust-lang.org/nomicon/ownership.html) | [ownership_model](../../../docs/research_notes/formal_methods/10_ownership_model.md)、[ownership_cheatsheet](../../../docs/02_reference/quick_reference/02_ownership_cheatsheet.md) |
| **Subtyping and Variance** | [subtyping](https://doc.rust-lang.org/nomicon/subtyping.html) | [VARIANCE_CONCEPT_MINDMAP](../../../docs/research_notes/formal_methods/10_variance_concept_mindmap.md) |
| **Type Conversions / Transmutes** | [transmutes](https://doc.rust-lang.org/nomicon/transmutes.html) | § UB 案例 4 类型混淆 |
| **Uninitialized Memory** | [uninitialized](https://doc.rust-lang.org/nomicon/uninitialized.html) | § UB 案例 6 越界、§ Miri |
| **Destructors / Drop** | [destructors](https://doc.rust-lang.org/nomicon/destructors.html) | § UB 案例 8 不恰当的 Drop |
| **Exception Safety** | [exception-safety](https://doc.rust-lang.org/nomicon/exception-safety.html) | [EDGE_CASES_AND_SPECIAL_CASES](../../../docs/02_reference/02_edge_cases_and_special_cases.md) |
| **Concurrency / Send and Sync** | [send-and-sync](https://doc.rust-lang.org/nomicon/send-and-sync.html) | § 示例 3 实现 Send/Sync、[threads_concurrency_cheatsheet](../../../docs/02_reference/quick_reference/02_threads_concurrency_cheatsheet.md) |
| **Implementing Vec** | vec | § 示例 1 原始指针（Raw Pointer）、§ 示例 6 自定义智能指针（Smart Pointer） |
| **Implementing Arc** | [arc](https://doc.rust-lang.org/nomicon/arc-mutex/arc.html) | [smart_pointers_cheatsheet](../../../docs/02_reference/quick_reference/02_smart_pointers_cheatsheet.md) |
| **FFI** | [ffi](https://doc.rust-lang.org/nomicon/ffi.html) | § 示例 2 调用外部函数 |

> **官方入口**: [The Rustonomicon](https://doc.rust-lang.org/nomicon/index.html) · 与 Rust 1.93 对应见 [09_rust_1.93_compatibility_deep_dive](../../../docs/06_toolchain/06_09_rust_1_93_compatibility_deep_dive.md)
