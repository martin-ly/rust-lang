# 代码-文档-形式化完整映射

> **创建日期**: 2026-02-20
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **用途**: 建立代码模式、文档位置与形式化定义之间的完整映射关系

---

## 📋 目录 {#-目录}

- [代码-文档-形式化完整映射](#代码-文档-形式化完整映射)
  - [📋 目录 {#-目录}](#-目录--目录)
  - [1. 代码到概念的映射](#1-代码到概念的映射)
    - [1.1 所有权与移动语义](#11-所有权与移动语义)
    - [1.2 借用与引用](#12-借用与引用)
    - [1.3 生命周期](#13-生命周期)
    - [1.4 Trait 与泛型](#14-trait-与泛型)
    - [1.5 并发与同步](#15-并发与同步)
    - [1.6 错误处理](#16-错误处理)
  - [2. 代码到文档的映射](#2-代码到文档的映射)
    - [2.1 所有权系统文档映射](#21-所有权系统文档映射)
    - [2.2 生命周期文档映射](#22-生命周期文档映射)
    - [2.3 泛型与 Trait 文档映射](#23-泛型与-trait-文档映射)
    - [2.4 并发文档映射](#24-并发文档映射)
    - [2.5 标准库 API 文档映射](#25-标准库-api-文档映射)
  - [3. 代码到形式化的映射](#3-代码到形式化的映射)
    - [3.1 所有权转移的形式化](#31-所有权转移的形式化)
    - [3.2 借用的形式化](#32-借用的形式化)
    - [3.3 生命周期的形式化](#33-生命周期的形式化)
    - [3.4 类型系统的形式化](#34-类型系统的形式化)
    - [3.5 并发的形式化](#35-并发的形式化)
    - [3.6 异步的形式化](#36-异步的形式化)
  - [4. 错误代码映射](#4-错误代码映射)
    - [4.1 所有权错误 (E03xx)](#41-所有权错误-e03xx)
    - [4.2 借用错误 (E04xx, E05xx)](#42-借用错误-e04xx-e05xx)
    - [4.3 生命周期错误 (E05xx)](#43-生命周期错误-e05xx)
    - [4.4 类型系统错误 (E02xx, E03xx)](#44-类型系统错误-e02xx-e03xx)
    - [4.5 并发错误 (E0xxx)](#45-并发错误-e0xxx)
    - [4.6 错误码快速修复索引](#46-错误码快速修复索引)
  - [5. API映射](#5-api映射)
    - [5.1 所有权相关 API](#51-所有权相关-api)
    - [5.2 借用相关 API](#52-借用相关-api)
    - [5.3 集合 API](#53-集合-api)
    - [5.4 并发 API](#54-并发-api)
    - [5.5 异步 API](#55-异步-api)
    - [5.6 I/O API](#56-io-api)
  - [6. 快速查找索引](#6-快速查找索引)
    - [6.1 按代码模式查找](#61-按代码模式查找)
    - [6.2 按错误码查找](#62-按错误码查找)
    - [6.3 按文档类型查找](#63-按文档类型查找)
    - [6.4 按形式化主题查找](#64-按形式化主题查找)
  - [相关文档](#相关文档)
    - [项目内部文档](#项目内部文档)
    - [形式化文档](#形式化文档)
    - [外部资源](#外部资源)

---

## 1. 代码到概念的映射

### 1.1 所有权与移动语义

| 代码模式 | 对应概念 | 概念解释 |
| :--- | :--- | :--- |
| `let s = String::from("x");` | 所有权获取 | 值的所有权绑定到变量 |
| `let s2 = s1;` | 所有权转移 (Move) | `s1` 所有权转移到 `s2`，`s1` 失效 |
| `let s2 = s1.clone();` | 深度复制 (Clone) | 创建值的完整副本，两者独立 |
| `let x = 5; let y = x;` | Copy 语义 | 标量类型实现 `Copy`，按位复制 |
| `drop(s);` | 显式释放 | 提前释放值的所有权 |

### 1.2 借用与引用

| 代码模式 | 对应概念 | 概念解释 |
| :--- | :--- | :--- |
| `let r = &s;` | 不可变借用 | 只读引用，可同时存在多个 |
| `let r = &mut s;` | 可变借用 | 独占写引用，同一时刻只能有一个 |
| `let r: &str = &s[0..5];` | 切片借用 | 借用集合的一部分 |
| `fn foo(s: &str)` | 借用参数 | 函数接受引用而非所有权 |
| `fn foo(s: &mut String)` | 可变借用参数 | 函数可以修改传入的值 |

### 1.3 生命周期

| 代码模式 | 对应概念 | 概念解释 |
| :--- | :--- | :--- |
| `&'a str` | 显式生命周期 | 标注引用的有效范围 |
| `fn foo<'a>(x: &'a str)` | 生命周期参数 | 泛型生命周期约束 |
| `struct Foo<'a> { x: &'a str }` | 结构体生命周期 | 结构体包含引用时的生命周期标注 |
| `fn foo<'a, 'b>(x: &'a str, y: &'b str) -> &'a str` | 生命周期选择 | 返回与特定参数相同生命周期的引用 |
| `&'static str` | 静态生命周期 | 程序整个运行期间有效 |

### 1.4 Trait 与泛型

| 代码模式 | 对应概念 | 概念解释 |
| :--- | :--- | :--- |
| `fn foo<T>(x: T)` | 泛型函数 | 对任意类型 `T` 生效的函数 |
| `fn foo<T: Display>(x: T)` | Trait Bound | 约束 `T` 必须实现 `Display` |
| `fn foo<T>(x: T) where T: Clone` | Where 从句 | 更清晰的多约束写法 |
| `impl Trait for Type` | Trait 实现 | 为类型实现特定行为 |
| `dyn Trait` | 动态分发 | 运行时确定具体类型的 Trait 对象 |
| `impl Trait` | 静态分发 | 编译时确定具体类型的抽象返回 |

### 1.5 并发与同步

| 代码模式 | 对应概念 | 概念解释 |
| :--- | :--- | :--- |
| `thread::spawn(\|_\| { ... })` | 线程创建 | 创建新操作系统线程 |
| `Arc::new(data)` | 原子引用计数 | 线程间共享所有权 |
| `Mutex::new(data)` | 互斥锁 | 保护共享数据的独占访问 |
| `RwLock::new(data)` | 读写锁 | 多读单写锁 |
| `mpsc::channel()` | 消息通道 | 线程间通信 |
| `async { ... }` | 异步块 | 延迟执行的异步代码 |
| `.await` | 异步等待 | 挂起当前异步任务等待结果 |

### 1.6 错误处理

| 代码模式 | 对应概念 | 概念解释 |
| :--- | :--- | :--- |
| `Result<T, E>` | 结果类型 | 显式表示成功或失败 |
| `Option<T>` | 可选类型 | 表示可能为空的值 |
| `?` 操作符 | 错误传播 | 简化错误处理的语法糖 |
| `match result { Ok(v) => ..., Err(e) => ... }` | 结果匹配 | 显式处理两种情况 |
| `.unwrap()` | 强制解包 | 成功时返回值，失败时 panic |
| `.expect("msg")` | 带消息解包 | 失败时带自定义消息 panic |

---

## 2. 代码到文档的映射

### 2.1 所有权系统文档映射

| 代码示例 | 相关文档位置 | 快速查找关键词 |
| :--- | :--- | :--- |
| `let s = String::from("hello");` | [C01 所有权](../02_reference/quick_reference/ownership_cheatsheet.md) | 所有权获取 |
| `let s2 = s1;` | [C01 所有权](../02_reference/quick_reference/ownership_cheatsheet.md#移动语义) | move, 转移 |
| `fn take_ownership(s: String)` | [C01 函数参数](../02_reference/quick_reference/ownership_cheatsheet.md#函数参数) | 参数所有权 |
| `fn borrow(s: &String)` | [C01 借用](../02_reference/quick_reference/ownership_cheatsheet.md#引用与借用) | 引用, 借用 |

### 2.2 生命周期文档映射

| 代码示例 | 相关文档位置 | 快速查找关键词 |
| :--- | :--- | :--- |
| `fn longest<'a>(x: &'a str, y: &'a str)` | [C01 生命周期](../02_reference/quick_reference/ownership_cheatsheet.md#生命周期) | lifetime, 生命周期 |
| `struct Excerpt<'a> { part: &'a str }` | [C01 结构体生命周期](../02_reference/quick_reference/ownership_cheatsheet.md#生命周期标注) | 结构体生命周期 |
| `impl<'a> Excerpt<'a> { ... }` | [C01 生命周期省略](../02_reference/quick_reference/ownership_cheatsheet.md#生命周期省略规则) | impl 生命周期 |

### 2.3 泛型与 Trait 文档映射

| 代码示例 | 相关文档位置 | 快速查找关键词 |
| :--- | :--- | :--- |
| `fn foo<T>(x: T)` | [C04 泛型](../02_reference/quick_reference/generics_cheatsheet.md) | 泛型函数 |
| `struct Point<T> { x: T, y: T }` | [C04 泛型结构体](../02_reference/quick_reference/generics_cheatsheet.md#泛型结构体) | 泛型结构体 |
| `fn foo<T: Display + Clone>(x: T)` | [C04 Trait Bound](../02_reference/quick_reference/generics_cheatsheet.md#trait-bound) | trait bound, 约束 |
| `trait Drawable { fn draw(&self); }` | [C04 Trait 定义](../02_reference/quick_reference/generics_cheatsheet.md#定义-trait) | trait 定义 |
| `impl Drawable for Circle { ... }` | [C04 Trait 实现](../02_reference/quick_reference/generics_cheatsheet.md#实现-trait) | trait 实现 |

### 2.4 并发文档映射

| 代码示例 | 相关文档位置 | 快速查找关键词 |
| :--- | :--- | :--- |
| `thread::spawn(\|_\| { ... })` | [C05 线程](../02_reference/quick_reference/threads_concurrency_cheatsheet.md#创建线程) | spawn, 创建线程 |
| `Arc::new(Mutex::new(0))` | [C05 Arc + Mutex](../02_reference/quick_reference/threads_concurrency_cheatsheet.md#共享状态并发) | Arc, Mutex, 共享状态 |
| `let (tx, rx) = mpsc::channel();` | [C05 消息传递](../02_reference/quick_reference/threads_concurrency_cheatsheet.md#消息传递) | channel, mpsc |
| `async fn foo() { ... }` | [C06 异步](../02_reference/quick_reference/async_patterns.md#async-函数) | async, 异步函数 |
| `let handle = tokio::spawn(async { ... });` | [C06 任务调度](../02_reference/quick_reference/async_patterns.md#任务调度) | spawn, 异步任务 |

### 2.5 标准库 API 文档映射

| 代码示例 | 相关文档位置 | 快速查找关键词 |
| :--- | :--- | :--- |
| `vec![1, 2, 3]` | [C02 Vec](../02_reference/quick_reference/type_system.md#vec) | Vec, 动态数组 |
| `HashMap::new()` | [C02 HashMap](../02_reference/quick_reference/type_system.md#hashmap) | HashMap, 哈希表 |
| `String::from("hello")` | [C02 String](../02_reference/quick_reference/type_system.md#string) | String, 字符串 |
| `file.read_to_string(&mut s)?` | [C07 I/O](../02_reference/quick_reference/collections_iterators_cheatsheet.md#读取文件) | read, I/O |
| `Command::new("ls").arg("-l").output()` | [C07 进程](../02_reference/quick_reference/process_management_cheatsheet.md#运行外部命令) | Command, 进程 |

---

## 3. 代码到形式化的映射

### 3.1 所有权转移的形式化

| 代码 | 形式化定义 | 相关定理/证明 |
| :--- | :--- | :--- |
| `let s2 = s1;` | move(s1, s2) -> Omega(s1) = Moved && Omega(s2) = Owned | [定理 2 - 所有权唯一性](./formal_methods/ownership_model.md#定理-2-所有权唯一性) |
| `drop(s);` | drop(s) -> Omega(s) = Freed | [引理 1 - 资源释放](./formal_methods/ownership_model.md#引理-1-资源释放) |
| `let x = 5; let y = x;` | Copy(T) -> forall x: T, assign(x, y) => Omega(x) = Omega(y) = Owned | [定理 3 - Copy 语义](./formal_methods/ownership_model.md#定理-3-copy-语义) |

### 3.2 借用的形式化

| 代码 | 形式化定义 | 相关定理/证明 |
| :--- | :--- | :--- |
| `let r = &s;` | Borrow(r, s, Immutable) -> type(r) = &T && valid(r) subset lifetime(s) | [规则 1 - 借用规则](./formal_methods/borrow_checker_proof.md#规则-1-借用规则) |
| `let r = &mut s;` | Borrow(r, s, Mutable) -> type(r) = &mut T && forall r' != r: !aliased(r, r') | [定理 1 - 数据竞争自由](./formal_methods/borrow_checker_proof.md#定理-1-数据竞争自由) |
| `&s[0..5]` | Slice(r, s, i, j) -> r = {s_k | i <= k < j} && valid(r) subset valid(s) | [引理 2 - 切片有效性](./formal_methods/borrow_checker_proof.md#引理-2-切片有效性) |

### 3.3 生命周期的形式化

| 代码 | 形式化定义 | 相关定理/证明 |
| :--- | :--- | :--- |
| `&'a str` | Lifetime(&'a T) = a subset Scope(T) | [规则 3 - 生命周期包含](./formal_methods/lifetime_formalization.md#规则-3-生命周期包含) |
| `fn foo<'a>(x: &'a str) -> &'a str` | forall 'a. forall x: &'a T. exists y: &'a T. lft(y) = lft(x) | [定理 LF-T1 - 生命周期传递](./formal_methods/lifetime_formalization.md#定理-lf-t1-生命周期传递) |
| `'static` | Lifetime('static) = [0, infinity) | [定义 - 静态生命周期](./formal_methods/lifetime_formalization.md#定义-静态生命周期) |

### 3.4 类型系统的形式化

| 代码 | 形式化定义 | 相关定理/证明 |
| :--- | :--- | :--- |
| `fn foo<T: Display>(x: T)` | Gamma |- T: Display => forall x: T. displayable(x) | [类型规则 - Trait Bound](./type_theory/type_system_foundations.md#类型规则-trait-bound) |
| `impl Clone for MyType` | Gamma |- MyType: Clone <=> exists clone: MyType -> MyType | [类型规则 - Trait 实现](./type_theory/type_system_foundations.md#类型规则-trait-实现) |
| `dyn Trait` | dyn Trait = exists T. T: Trait && vtable(T) | [类型规则 - Trait 对象](./type_theory/type_system_foundations.md#类型规则-trait-对象) |

### 3.5 并发的形式化

| 代码 | 形式化定义 | 相关定理/证明 |
| :--- | :--- | :--- |
| `Arc::new(data)` | Arc(T) = T x AtomicUsize && Send(T) && Sync(T) | [定理 C-T1 - Arc 安全](./formal_methods/send_sync_formalization.md#定理-c-t1-arc-安全) |
| `Mutex::new(data)` | Mutex(T) = T x Lock && invariant(lock -> exclusive(T)) | [定理 C-T2 - Mutex 互斥](./formal_methods/send_sync_formalization.md#定理-c-t2-mutex-互斥) |
| `RwLock::new(data)` | RwLock(T) = T x RWLock && (n_r > 0 -> !w) && (w -> n_r = 0) | [定理 C-T3 - 读写锁](./formal_methods/send_sync_formalization.md#定理-c-t3-读写锁) |
| `Send` trait | Send(T) <=> forall t1, t2: Thread. safe_transfer(T, t1, t2) | [定义 - Send](./formal_methods/send_sync_formalization.md#定义-send) |
| `Sync` trait | Sync(T) <=> forall r: &T. Send(r) | [定义 - Sync](./formal_methods/send_sync_formalization.md#定义-sync) |

### 3.6 异步的形式化

| 代码 | 形式化定义 | 相关定理/证明 |
| :--- | :--- | :--- |
| `async fn foo() -> T` | Async(f) = Future && Output(f) = T && poll: Context -> Poll(T) | [定义 - 异步函数](./formal_methods/async_state_machine.md#定义-异步函数) |
| `f.await` | Await(f) = poll(f) until Ready(v) then v | [定理 A-T1 - Await 正确性](./formal_methods/async_state_machine.md#定理-a-t1-await-正确性) |
| `Pin<Box<dyn Future>>` | Pin(F) = F && immovable(F) && drop(F) -> cleanup | [定理 A-T2 - Pin 安全性](./formal_methods/async_state_machine.md#定理-a-t2-pin-安全性) |

---

## 4. 错误代码映射

### 4.1 所有权错误 (E03xx)

| 错误码 | 代码示例 | 概念解释 | 修复文档 | 形式化规则 |
| :--- | :--- | :--- | :--- | :--- |
| **E0382** | `let s2 = s1; println!("{}", s1);` | 使用已移动的值 | [TROUBLESHOOTING](../05_guides/TROUBLESHOOTING_GUIDE.md#1-所有权错误) | 规则 2 - 移动语义: move(x, y) -> Omega(x) = Moved |
| **E0383** | `let x = s.field; use(s);` | 部分移动 | [EDGE_CASES](../02_reference/EDGE_CASES_AND_SPECIAL_CASES.md) | 定理 2 - 所有权唯一性 |
| **E0505** | `let r = &s; drop(s);` | 在借用时移动 | [C01 借用](../02_reference/quick_reference/ownership_cheatsheet.md) | 规则 3 - 借用有效性 |
| **E0507** | `let x = *r;` (r 是借用) | 从借用内容移动 | [C01 借用检查器](../02_reference/quick_reference/ownership_cheatsheet.md) | 规则 1 - 借用规则 |

### 4.2 借用错误 (E04xx, E05xx)

| 错误码 | 代码示例 | 概念解释 | 修复文档 | 形式化规则 |
| :--- | :--- | :--- | :--- | :--- |
| **E0499** | `let r1 = &mut s; let r2 = &mut s;` | 双重可变借用 | [TROUBLESHOOTING](../05_guides/TROUBLESHOOTING_GUIDE.md) | 规则 1 - 可变借用唯一性: forall b1, b2: type(b1) = &mut T -> b1 = b2 |
| **E0502** | `let r1 = &mut s; let r2 = &s;` | 可变与不可变共存 | [TROUBLESHOOTING](../05_guides/TROUBLESHOOTING_GUIDE.md) | 规则 2 - 互斥借用 |
| **E0503** | `use(x)` after `let y = x` | 使用已移动值 | [C01 所有权](../02_reference/quick_reference/ownership_cheatsheet.md) | 定理 2 - 所有权唯一性 |
| **E0506** | `*r = value;` (while borrowed) | 给借用赋值 | [C01 借用](../02_reference/quick_reference/ownership_cheatsheet.md) | 规则 1 - 借用规则 |

### 4.3 生命周期错误 (E05xx)

| 错误码 | 代码示例 | 概念解释 | 修复文档 | 形式化规则 |
| :--- | :--- | :--- | :--- | :--- |
| **E0597** | `{ let s = "x"; r = &s; } use(r);` | 生命周期不足 | [TROUBLESHOOTING](../05_guides/TROUBLESHOOTING_GUIDE.md#2-生命周期错误) | 规则 3 - 借用有效性: Valid(b) <=> Lifetime(b) subset Scope(b) |
| **E0310** | `fn foo<T>(x: &T)` | 参数生命周期不足 | [C01 生命周期](../02_reference/quick_reference/ownership_cheatsheet.md) | 定理 LF-T2 - 引用有效性 |
| **E0373** | `move \|_\| x` in closure | 闭包生命周期 | [C06 异步](../02_reference/quick_reference/async_patterns.md) | 捕获变量生命周期约束 |

### 4.4 类型系统错误 (E02xx, E03xx)

| 错误码 | 代码示例 | 概念解释 | 修复文档 | 形式化规则 |
| :--- | :--- | :--- | :--- | :--- |
| **E0308** | `let x: i32 = "hello";` | 类型不匹配 | [TROUBLESHOOTING](../05_guides/TROUBLESHOOTING_GUIDE.md#3-类型不匹配) | 类型系统一致性: Gamma |- e : tau |
| **E0277** | `fn foo<T>(x: T) { println!("{}", x); }` | Trait Bound 不满足 | [C04 Trait](../02_reference/quick_reference/generics_cheatsheet.md) | Trait 约束: Gamma |- T: Trait |
| **E0282** | `let x = Vec::new();` | 需要类型标注 | [C02 类型推断](../02_reference/quick_reference/type_system.md) | 类型推断规则 |
| **E0283** | `x.into()` (ambiguous) | 需要更多类型信息 | [C04 泛型](../02_reference/quick_reference/generics_cheatsheet.md) | 类型推断冲突 |
| **E0325** | 递归 trait bound | 溢出求值要求 | [C04 泛型](../02_reference/quick_reference/generics_cheatsheet.md) | 类型系统一致性 |

### 4.5 并发错误 (E0xxx)

| 错误码 | 代码示例 | 概念解释 | 修复文档 | 形式化规则 |
| :--- | :--- | :--- | :--- | :--- |
| **E0378** | `Rc::new(data)` across threads | Send/Sync 相关 | [C05 线程](../02_reference/quick_reference/threads_concurrency_cheatsheet.md) | Send/Sync 约束 |
| **E0381** | 跨 await 持锁 | 异步借用错误 | [C06 异步](../05_guides/TROUBLESHOOTING_GUIDE.md) | 借用有效性跨 await |

### 4.6 错误码快速修复索引

| 错误码 | 常见原因 | 快速修复 | 形式化规则 | 相关定理 |
| :--- | :--- | :--- | :--- | :--- |
| **E0382** | 使用已移动的值 | 使用引用 `.clone()` 或重新设计 | 规则 2 - 移动语义 | 定理 2 |
| **E0499** | 双重可变借用 | 使用作用域隔离或 NLL | 规则 1 - 可变借用唯一性 | 定理 1 |
| **E0502** | 可变与不可变共存 | 分离借用作用域 | 规则 2 - 互斥借用 | 定理 1 |
| **E0597** | 生命周期不足 | 确保引用在有效期内 | 规则 3 - 借用有效性 | 定理 LF-T2 |
| **E0308** | 类型不匹配 | 类型转换或修正声明 | 类型系统一致性 | - |
| **E0277** | Trait 未实现 | 添加 Trait Bound 或实现 Trait | Trait 约束 | - |
| **E0373** | 闭包生命周期 | 使用 `move` 或 `Arc` | 捕获变量生命周期 | - |

---

## 5. API映射

### 5.1 所有权相关 API

| API | 概念 | 使用场景 | 形式化规格 |
| :--- | :--- | :--- | :--- |
| `String::from(s)` | 所有权获取 | 从字符串切片创建拥有所有权的 String | String::from: &str -> String && Omega(result) = Owned |
| `s.clone()` | 深度复制 | 需要独立副本时 | clone: T -> T && T: Clone && Omega(r) = Owned && deep_copy(r, s) |
| `mem::drop(s)` | 显式释放 | 提前释放资源 | drop: T -> () && Omega(T) = Freed |
| `mem::replace(&mut T, T)` | 替换值 | 从可变引用取出值并替换 | replace: (&mut T, T) -> T && old_value = return && new_value = *ref |
| `mem::take(&mut T)` | 取出默认值 | 取出值并用 Default 替换 | take: &mut T -> T && T: Default && old = return && *ref = default() |

### 5.2 借用相关 API

| API | 概念 | 使用场景 | 形式化规格 |
| :--- | :--- | :--- | :--- |
| `&T` | 不可变借用 | 只读访问 | borrow: T -> &T && readonly && multiple_allowed |
| `&mut T` | 可变借用 | 独占写访问 | borrow_mut: T -> &mut T && exclusive && single_allowed |
| `as_ref()` | 转为引用 | 将容器转为引用 | as_ref: T -> &U && view |
| `as_mut()` | 转为可变引用 | 将容器转为可变引用 | as_mut: T -> &mut U && mutable_view |
| `to_owned()` | 转为拥有值 | 从引用创建拥有值 | to_owned: &T -> T && Omega(result) = Owned |

### 5.3 集合 API

| API | 概念 | 使用场景 | 形式化规格 |
| :--- | :--- | :--- | :--- |
| `Vec::new()` | 创建空向量 | 动态数组 | Vec = { ptr, len, cap } && len = 0 && cap >= 0 |
| `vec.push(x)` | 添加元素 | 尾部添加 | push: (Vec<T>, T) -> () && len' = len + 1 && vec[len] = x |
| `vec.pop()` | 移除尾部 | 移除并返回尾部 | pop: Vec<T> -> Option<T> && if len > 0 then len' = len - 1 |
| `HashMap::new()` | 创建哈希表 | 键值对映射 | HashMap<K, V> = { buckets, len, load_factor } |
| `map.insert(k, v)` | 插入键值 | 插入或更新 | insert: (K, V) -> Option<V> && map[k] = v && return = old_value |
| `map.get(&k)` | 获取值 | 按键查找 | get: &K -> Option<&V> && if k in keys(map) then Some(&map[k]) |

### 5.4 并发 API

| API | 概念 | 使用场景 | 形式化规格 |
| :--- | :--- | :--- | :--- |
| `Arc::new(x)` | 原子引用计数 | 线程间共享所有权 | Arc<T> = (T, AtomicUsize) && count = 1 && T: Send + Sync |
| `Arc::clone(&arc)` | 增加引用计数 | 共享所有权 | clone: Arc<T> -> Arc<T> && count' = count + 1 |
| `Mutex::new(x)` | 互斥锁 | 保护共享数据 | Mutex<T> = (T, Lock) && lock_state in { Unlocked, Locked(ThreadId) } |
| `mutex.lock()` | 获取锁 | 独占访问 | lock: () -> LockGuard<T> && wait_if_locked && RAII_unlock |
| `RwLock::new(x)` | 读写锁 | 多读单写 | RwLock<T> = (T, State) && (n_r > 0 -> !w) && (w -> n_r = 0) |
| `channel()` | 消息通道 | 线程间通信 | Channel<T> = (Sender<T>, Receiver<T>) && queue |

### 5.5 异步 API

| API | 概念 | 使用场景 | 形式化规格 |
| :--- | :--- | :--- | :--- |
| `async fn` | 异步函数 | 定义异步操作 | AsyncFn = Future<Output = T> && state_machine |
| `.await` | 异步等待 | 等待异步结果 | await: Future<T> -> T && yield_if_pending && resume_on_ready |
| `tokio::spawn(f)` | 创建任务 | 后台执行异步任务 | spawn: Future<T> -> JoinHandle<T> && schedule_on_runtime |
| `join!(f1, f2)` | 并发等待 | 等待多个 Future | join: (F1, F2, ...) -> (T1, T2, ...) && wait_all |
| `select!` | 选择完成 | 等待任一 Future | select: {F_i} -> T_j && j = min { i | F_i ready } |

### 5.6 I/O API

| API | 概念 | 使用场景 | 形式化规格 |
| :--- | :--- | :--- | :--- |
| `File::open(p)` | 打开文件 | 读取文件 | open: Path -> Result<File> && read_mode |
| `File::create(p)` | 创建文件 | 写入文件 | create: Path -> Result<File> && write_mode && truncate |
| `read_to_string(&mut s)` | 读取全部 | 读入字符串 | read_to_string: &mut String -> Result<usize> && s = file_content |
| `write_all(&buf)` | 写入全部 | 写入数据 | write_all: &[u8] -> Result<()> && file = buf |
| `BufReader::new(f)` | 缓冲读取 | 高效读取 | BufReader = (F, buf) && reduce_syscalls |

---

## 6. 快速查找索引

### 6.1 按代码模式查找

```
所有权获取       -> 1.1, 3.1, 5.1
所有权转移       -> 1.1, 3.1, E0382
借用             -> 1.2, 3.2, 5.2
生命周期标注     -> 1.3, 3.3
泛型函数         -> 1.4, 3.4
Trait Bound      -> 1.4, E0277
错误处理         -> 1.6
线程创建         -> 1.5, 5.4
异步操作         -> 1.5, 3.6, 5.5
集合操作         -> 5.3
```

### 6.2 按错误码查找

```
所有权错误:
  E0382, E0383, E0505, E0507 -> 4.1, 4.6

借用错误:
  E0499, E0502, E0503, E0506 -> 4.2, 4.6

生命周期错误:
  E0597, E0310, E0373 -> 4.3, 4.6

类型错误:
  E0308, E0277, E0282, E0283 -> 4.4, 4.6

并发错误:
  E0378, E0381 -> 4.5
```

### 6.3 按文档类型查找

```
概念文档       -> 02_reference/quick_reference/
形式化证明     -> research_notes/formal_methods/
故障排查       -> 05_guides/TROUBLESHOOTING_GUIDE.md
错误码详解     -> 02_reference/ERROR_CODE_MAPPING.md
标准库分析     -> 02_reference/STANDARD_LIBRARY_COMPREHENSIVE_ANALYSIS_2025_12_25.md
```

### 6.4 按形式化主题查找

```
所有权模型      -> ownership_model.md
借用检查器      -> borrow_checker_proof.md
生命周期形式化  -> lifetime_formalization.md
并发模型        -> send_sync_formalization.md
异步形式化      -> async_state_machine.md
类型理论基础    -> type_system_foundations.md
```

---

## 相关文档

### 项目内部文档

- [ERROR_CODE_MAPPING.md](../02_reference/ERROR_CODE_MAPPING.md) - 编译错误码详细映射
- [STANDARD_LIBRARY_COMPREHENSIVE_ANALYSIS_2025_12_25.md](../02_reference/STANDARD_LIBRARY_COMPREHENSIVE_ANALYSIS_2025_12_25.md) - 标准库全面分析
- [TROUBLESHOOTING_GUIDE.md](../05_guides/TROUBLESHOOTING_GUIDE.md) - 故障排查指南
- [C01 所有权与借用](../02_reference/quick_reference/ownership_cheatsheet.md) - 所有权核心概念
- [C02 类型系统](../02_reference/quick_reference/type_system.md) - 类型系统详解
- [C04 泛型与 Trait](../02_reference/quick_reference/generics_cheatsheet.md) - 泛型编程

### 形式化文档

- [ownership_model.md](./formal_methods/ownership_model.md) - 所有权模型形式化
- [borrow_checker_proof.md](./formal_methods/borrow_checker_proof.md) - 借用检查器证明
- [lifetime_formalization.md](./formal_methods/lifetime_formalization.md) - 生命周期形式化
- [send_sync_formalization.md](./formal_methods/send_sync_formalization.md) - 并发模型
- [async_state_machine.md](./formal_methods/async_state_machine.md) - 异步形式化
- [type_system_foundations.md](./type_theory/type_system_foundations.md) - 类型理论基础

### 外部资源

- [Rust 官方文档](https://doc.rust-lang.org/)
- [Compiler Error Index](https://doc.rust-lang.org/error-index.html)
- [Rust 标准库 API](https://doc.rust-lang.org/std/)
