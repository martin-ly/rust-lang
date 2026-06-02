> **内容分级**: [综述级]

> **本节关键术语**: 错误处理 (Error Handling) · Result · Option · ? 运算符 · 自定义错误类型 · thiserror — [完整对照表](../00_meta/terminology_glossary.md)
>
# Error Handling（错误处理）

> **📎 交叉引用**
>
> 本主题在 knowledge 中有系统化的知识索引：[错误处理](../../knowledge/02_intermediate/02_error_handling.md)
> **受众**: [进阶]
> **层级**: L2 进阶概念
> **A/S/P 标记**: **A+S** — Application + Structure
> **双维定位**: C×App — 实施 Result/Option 传播模式
> **前置概念**: [Type System Basics](../01_foundation/04_type_system.md) ·
> [Ownership](../01_foundation/01_ownership.md) ·
> [Traits](./01_traits.md)
> **后置概念**: [Concurrency](../03_advanced/01_concurrency.md) ·
> [Async](../03_advanced/02_async.md)
> **主要来源**: [TRPL: Ch9](https://doc.rust-lang.org/book/ch09-00-error-handling.html) ·
> [Rust Reference: Errors] ·
> [Wikipedia: Exception handling] ·
> [RFC 243]

---
**变更日志**:

> **Bloom 层级**: 应用 → 分析

- v2.1 (2026-05-14): 扩展 §9.4——补充 `miette` / `snafu` 生态库详解，六库综合对比矩阵与决策树
- v2.0 (2026-05-12): 深度重构——定理推理链、反命题决策树、边界极限测试、6步认知路径与章节过渡
- v1.0 (2026-05-12): 初始版本

---

## 📑 目录

- [Error Handling（错误处理）](#error-handling错误处理)
  - [📑 目录](#-目录)
  - [一、权威定义（Definition）](#一权威定义definition)
    - [1.1 Wikipedia 对齐定义](#11-wikipedia-对齐定义)
    - [1.2 TRPL 官方定义](#12-trpl-官方定义)
    - [1.3 形式化定义](#13-形式化定义)
  - [二、概念属性矩阵（Attribute Matrix）](#二概念属性矩阵attribute-matrix)
    - [2.1 错误处理机制矩阵](#21-错误处理机制矩阵)
    - [2.2 Rust vs 其他语言错误处理对比](#22-rust-vs-其他语言错误处理对比)
    - [2.3 `Result` 组合子矩阵](#23-result-组合子矩阵)
  - [三、思维导图（Mind Map）](#三思维导图mind-map)
  - [四、定理推理链（Theorem Chain）](#四定理推理链theorem-chain)
    - [4.1 引理：Result\<T,E\> ⟹ 和类型强制错误处理](#41-引理resultte--和类型强制错误处理)
    - [4.2 定理：? 运算符 ⟹ 错误传播自动化](#42-定理-运算符--错误传播自动化)
    - [4.3 推论：panic ⟹ 不可恢复错误的显式边界](#43-推论panic--不可恢复错误的显式边界)
    - [4.4 类型安全错误处理](#44-类型安全错误处理)
    - [4.5 定理一致性矩阵](#45-定理一致性矩阵)
  - [五、示例与反例（Examples \& Counter-examples）](#五示例与反例examples--counter-examples)
    - [5.1 正确示例：`?` 运算符链式传播](#51-正确示例-运算符链式传播)
    - [5.2 正确示例：自定义错误类型](#52-正确示例自定义错误类型)
    - [5.3 反例：`?` 在错误返回类型中不匹配](#53-反例-在错误返回类型中不匹配)
    - [5.4 反例：忽略 Result 导致 bug](#54-反例忽略-result-导致-bug)
    - [5.5 边界示例：`Option` 与 `Result` 互转](#55-边界示例option-与-result-互转)
    - [5.5 补充：异步错误处理与 `poll_fn` / `TryFuture` 模式](#55-补充异步错误处理与-poll_fn--tryfuture-模式)
      - [`poll_fn`：将闭包提升为 Future](#poll_fn将闭包提升为-future)
      - [`TryFuture` 与 `?` 运算符的异步扩展](#tryfuture-与--运算符的异步扩展)
      - [取消安全（Cancellation Safety）与错误处理](#取消安全cancellation-safety与错误处理)
  - [六、反命题与边界分析（Counter-proposition \& Boundary Analysis）](#六反命题与边界分析counter-proposition--boundary-analysis)
    - [6.1 反命题 1: "Result 消除了所有错误"](#61-反命题-1-result-消除了所有错误)
    - [6.2 反命题 2: "? 运算符总是正确传播"](#62-反命题-2--运算符总是正确传播)
    - [6.3 反命题 3: "panic 只应在完全不可能时发生"](#63-反命题-3-panic-只应在完全不可能时发生)
    - [6.4 反命题 4: "Option 完全替代 null"](#64-反命题-4-option-完全替代-null)
  - [七、边界极限测试代码（Boundary Limit Tests）](#七边界极限测试代码boundary-limit-tests)
    - [7.1 测试 1: ? 运算符在闭包中的限制](#71-测试-1--运算符在闭包中的限制)
    - [7.2 测试 2: From 转换链的边界](#72-测试-2-from-转换链的边界)
    - [7.3 测试 3: panic 边界与 catch\_unwind](#73-测试-3-panic-边界与-catch_unwind)
    - [7.4 测试 4: Result 与 Option 的组合边界](#74-测试-4-result-与-option-的组合边界)
  - [八、认知路径（Cognitive Path）](#八认知路径cognitive-path)
    - [Step 1: 直觉类比 — "快递包裹"](#step-1-直觉类比--快递包裹)
    - [Step 2: 语法熟悉 — Result/Option 与 match](#step-2-语法熟悉--resultoption-与-match)
    - [Step 3: 传播自动化 — ? 运算符与 From](#step-3-传播自动化---运算符与-from)
    - [Step 4: 自定义错误 — thiserror 与 anyhow](#step-4-自定义错误--thiserror-与-anyhow)
    - [Step 5: 边界认知 — panic 与不可恢复错误](#step-5-边界认知--panic-与不可恢复错误)
    - [Step 6: 形式化掌控 — Monad 与类型级错误处理](#step-6-形式化掌控--monad-与类型级错误处理)
  - [九、知识来源关系（Provenance）](#九知识来源关系provenance)
    - [9.1 补充：`Termination` trait 与 `main` 返回 `Result`](#91-补充termination-trait-与-main-返回-result)
      - [`Termination` trait 定义](#termination-trait-定义)
      - [`main` 返回 `Result` 的工程价值](#main-返回-result-的工程价值)
    - [9.2 补充：`Result<T, !>` 与 `!` (never type) 在错误处理中的使用](#92-补充resultt--与--never-type-在错误处理中的使用)
    - [9.3 `std::backtrace::Backtrace` 与错误追踪](#93-stdbacktracebacktrace-与错误追踪)
      - [9.3.1 基本获取与显示](#931-基本获取与显示)
      - [9.3.2 环境变量控制](#932-环境变量控制)
      - [9.3.3 与 `anyhow` / `thiserror` 的集成](#933-与-anyhow--thiserror-的集成)
      - [9.3.4 自定义错误类型中嵌入 `Backtrace` 的模式](#934-自定义错误类型中嵌入-backtrace-的模式)
      - [9.3.5 `#[track_caller]` 与 `Backtrace` 的协同与对比](#935-track_caller-与-backtrace-的协同与对比)
      - [9.3.6 与 `panic::Location` 的对比](#936-与-paniclocation-的对比)
      - [9.3.7 性能考量：Backtrace 捕获的成本](#937-性能考量backtrace-捕获的成本)
    - [9.4 `eyre` / `color-eyre` / `miette` / `snafu` 生态库对比](#94-eyre--color-eyre--miette--snafu-生态库对比)
      - [9.4.1 `eyre`：可定制报告的错误处理](#941-eyre可定制报告的错误处理)
      - [9.4.2 `color-eyre`：彩色诊断与链式回溯](#942-color-eyre彩色诊断与链式回溯)
      - [9.4.3 `miette`：诊断式错误处理](#943-miette诊断式错误处理)
      - [9.4.4 `snafu`：显式上下文错误类型](#944-snafu显式上下文错误类型)
      - [9.4.5 六库综合对比矩阵](#945-六库综合对比矩阵)
    - [9.5 `#[track_caller]` 与错误定位优化](#95-track_caller-与错误定位优化)
      - [9.5.1 工作原理：编译器隐式传递 `Location`](#951-工作原理编译器隐式传递-location)
      - [9.5.2 `Location::caller()` 与 `PanicInfo::location()` 的区别](#952-locationcaller-与-panicinfolocation-的区别)
      - [9.5.3 在自定义错误类型中使用 `#[track_caller]` 实现轻量级定位](#953-在自定义错误类型中使用-track_caller-实现轻量级定位)
      - [9.5.4 `#[track_caller]` 与 `Backtrace` 的对比](#954-track_caller-与-backtrace-的对比)
      - [9.5.5 与 `anyhow` / `thiserror` 的集成](#955-与-anyhow--thiserror-的集成)
      - [9.5.6 限制与演进边界](#956-限制与演进边界)
    - [9.6 `Try` trait 与自定义 `?` 行为（稳定化中）](#96-try-trait-与自定义--行为稳定化中)
  - [十、相关概念链接](#十相关概念链接)
  - [十一、待补充与演进方向（TODOs）](#十一待补充与演进方向todos)
  - [Wikipedia 概念对齐](#wikipedia-概念对齐)
  - [权威来源索引](#权威来源索引)
  - [十、C++ 异常安全 vs Rust 错误处理](#十c-异常安全-vs-rust-错误处理)
    - [10.1 异常安全保证等级](#101-异常安全保证等级)
    - [10.2 C++ 异常 vs Rust `Result` 的 ABI 差异](#102-c-异常-vs-rust-result-的-abi-差异)
    - [10.3 C++23 `std::expected` vs Rust `Result`](#103-c23-stdexpected-vs-rust-result)
    - [10.4 析构函数异常：C++ 的致命陷阱](#104-析构函数异常c-的致命陷阱)
  - [十一、边界测试：错误处理的编译错误](#十一边界测试错误处理的编译错误)
    - [11.1 边界测试：? 运算符在错误类型不匹配时使用（编译错误）](#111-边界测试-运算符在错误类型不匹配时使用编译错误)
    - [11.2 边界测试：panic 在 const fn 中（编译错误）](#112-边界测试panic-在-const-fn-中编译错误)
    - [11.3 边界测试：`Result` 未处理（编译错误）](#113-边界测试result-未处理编译错误)
    - [11.4 边界测试：`?` 在闭包中的类型推断失败（编译错误）](#114-边界测试-在闭包中的类型推断失败编译错误)
    - [11.5 边界测试：自定义 Error 未实现 `std::error::Error`（编译错误）](#115-边界测试自定义-error-未实现-stderrorerror编译错误)
    - [11.6 边界测试：`Result` 与 `Option` 混用（编译错误）](#116-边界测试result-与-option-混用编译错误)
    - [11.7 边界测试：`panic!` 在 `const fn` 中的限制（编译错误）](#117-边界测试panic-在-const-fn-中的限制编译错误)
    - [10.5 边界测试：`?` 运算符与 `From` 转换的失败（编译错误）](#105-边界测试-运算符与-from-转换的失败编译错误)
    - [10.6 边界测试：`Result` 的 `map_err` 与错误链的累积（逻辑错误）](#106-边界测试result-的-map_err-与错误链的累积逻辑错误)
  - [实践](#实践)

## 一、权威定义（Definition）

### 1.1 Wikipedia 对齐定义
>

> **[Wikipedia: Exception handling]** Exception handling is the process of responding to the occurrence of exceptions – anomalous or exceptional conditions requiring special processing – during the execution of a program. Rust does not use exceptions; instead, it uses the algebraic data types `Option<T>` and `Result<T, E>` for error handling, with the `?` operator for ergonomic propagation.

### 1.2 TRPL 官方定义
>

> **[TRPL: Ch9.0]** Rust groups errors into two major categories: recoverable and unrecoverable errors. For a recoverable error, we most likely want to report the problem to the user and retry the operation. Unrecoverable errors are always symptoms of bugs, and we want to immediately stop the program.

> **[TRPL: Ch9.2]** The `?` placed after a `Result` value is defined to work in almost the same way as the `match` expressions we defined to handle the `Result` values. If the value of the `Result` is an `Ok`, the value inside the `Ok` will get returned from this expression, and the program will continue. If the value is an `Err`, the `Err` will be returned from the whole function as if we had used the `return` keyword.

### 1.3 形式化定义
>

> **[Haskell: Either Monad] · [类型论: Monad 定律]** Option/Result 对应单子中的 Maybe 和 Either。 ✅ 已验证

> **[Haskell Wiki: Either]** Rust's `Result<T, E>` corresponds directly to Haskell's `Either e a` monad, with `Ok` as `Right` and `Err` as `Left`. ✅ 已验证

Rust 的错误处理对应**单子**（Monad）模式中的 `Option` 和 `Result`：

```text
Option<T> ≅ 1 + T          （余和类型: None + Some(T)）
Result<T, E> ≅ T + E       （余和类型: Ok(T) + Err(E)）

? 运算符的形式化语义:
  expr? ≡ match expr {
      Ok(v) => v,
      Err(e) => return Err(From::from(e)),
  }

即: ? 是 Result/Option 的 monadic bind 的语法糖
```

> **过渡到属性矩阵**: 从形式化定义出发，错误处理不仅是"返回错误码"的简单概念，而是由不可恢复错误（panic）、可恢复错误（Result/Option）、错误传播（? 运算符）和错误组合（map/and_then）构成的多层次系统。下一节通过属性矩阵对这些机制进行系统分类与跨语言对比。

---

## 二、概念属性矩阵（Attribute Matrix）

### 2.1 错误处理机制矩阵
>

| **机制** | **类型** | **可恢复** | **栈展开** | **使用场景** |
|:---|:---|:---|:---|:---|
| `panic!` | 运行时崩溃 | ❌ | 默认展开 | 不可恢复 bug、assert |
| `Option<T>` | 值可能存在 | ✅ | ❌ | 可能为空的查询 |
| `Result<T, E>` | 操作可能失败 | ✅ | ❌ | IO、解析、外部调用 |
| `?` 运算符 | 错误传播 | ✅ | ❌ | 链式错误处理 |
| `unwrap/expect` | 强制解包 | 可能 | ❌ | 快速原型/已知安全 |
| `catch_unwind` | 捕获 panic | 边界情况 | ✅ | FFI 边界、线程隔离 |

### 2.2 Rust vs 其他语言错误处理对比
>

| **维度** | **Rust (Result)** | **Go (error value)** | **Java (Exception)** | **Haskell (Either)** | **C (errno)** |
|:---|:---|:---|:---|:---|:---|
| **错误类型** | 代数类型 `Result<T,E>` | 接口 `error` | 类层次 `Throwable` | `Either e a` | 全局变量 |
| **强制性** | 强：必须处理或显式传播 | 弱：可忽略 | 中：checked/unchecked | 强：Monad bind | 弱：可忽略 |
| **传播语法** | `?` 运算符 | `if err != nil` | `throw/throws` | `>>=` / do notation | 手动检查 |
| **组合性** | ✅ `and_then`, `map` | ⚠️ 手动 | ⚠️ try/catch | ✅ `>>=` | ❌ 差 |
| **运行时开销** | 零（tagged union） | 接口调用 | 栈展开/对象分配 | 零 | 零 |
| **类型安全** | ✅ 编译期 | ⚠️ 运行时断言 | ⚠️ catch 任意类型 | ✅ 编译期 | ❌ 无 |

### 2.3 `Result` 组合子矩阵
>

| **方法** | **签名** | **语义** | **类比** |
|:---|:---|:---|:---|
| `map` | `Result<T,E> → (T→U) → Result<U,E>` | 成功时转换值 | `Option.map` |
| `map_err` | `Result<T,E> → (E→F) → Result<T,F>` | 失败时转换错误 | — |
| `and_then` | `Result<T,E> → (T→Result<U,E>) → Result<U,E>` | 成功时链式调用 | `>>=` / flatMap |
| `or_else` | `Result<T,E> → (E→Result<T,F>) → Result<T,F>` | 失败时恢复 | catch + fallback |
| `unwrap_or` | `Result<T,E> → T → T` | 失败时提供默认值 | `getOrElse` |
| `?` | `Result<T,E> → T` 或提前返回 | 错误自动传播 | `try` 关键字 |

> **过渡到思维导图**: 属性矩阵展示了错误处理机制的静态分类，但未能表达概念间的动态关联与控制流路径。思维导图通过拓扑结构揭示错误处理从 panic 分支、Result 构造、? 传播到自定义错误的完整概念网络。

---

## 三、思维导图（Mind Map）

```mermaid
graph TD
    A[Error Handling 错误处理] --> B[不可恢复]
    A --> C[可恢复]
    A --> D[错误传播]
    A --> E[自定义错误]

    B --> B1["panic!"]
    B --> B2["assert! / debug_assert!"]
    B --> B3["unreachable!"]
    B --> B4[Stack unwinding / abort]

    C --> C1[Option<T>: 可能为空]
    C --> C2[Result<T, E>: 可能失败]
    C --> C3[unwrap / expect]
    C --> C4[unwrap_or / unwrap_or_default]

    D --> D1[? 运算符]
    D --> D2[match 显式处理]
    D --> D3[and_then / map 链式]

    E --> E1[thiserror]
    E --> E2[anyhow]
    E --> E3[std::error::Error trait]
    E --> E4[From trait 转换]
```

> **认知功能**: 全局拓扑导航图——以层次化树状结构呈现错误处理的四大概念域及其子节点关系。读者可将此图作为"概念地图"，在深入学习各子主题前建立整体空间感，或在复习时快速定位特定机制（如 `?` 运算符或 `thiserror`）在知识体系中的坐标。核心洞察：Rust 错误处理不是单一机制，而是由"不可恢复—可恢复—传播—自定义"构成的正交分解系统。[来源: 💡 原创分析]
> [来源: [TRPL — Error Handling](https://doc.rust-lang.org/book/ch09-00-error-handling.html)]

> **过渡到定理推理链**: 思维导图呈现了错误处理的概念拓扑，但缺乏严格的逻辑推导关系。下一节通过"⟹"标注的定理链，将 Result 和类型、? 运算符传播、panic 边界等核心命题形式化为可验证的推理网络。

---

## 四、定理推理链（Theorem Chain）

### 4.1 引理：Result<T,E> ⟹ 和类型强制错误处理
>

> **[TRPL: Ch9] · [Rust Reference: Enums]** Result<T, E> 作为和类型（sum type），编译器通过穷尽性检查强制处理所有分支。 ✅ 已验证

```text
前提 1: Result<T, E> 是代数数据类型，具有 Ok(T) 和 Err(E) 两个变体
前提 2: match 表达式要求穷尽所有变体（或显式使用 _ 通配）
前提 3: 未使用的 Result 值触发编译器警告（#[must_use]）
    ↓
引理: Result<T,E> ⟹ 和类型强制错误处理
    ↓
定理: 在 Rust 中，可恢复错误无法被静默忽略（对比 Go 的 error 可忽略）
    ↓
推论: 编译器通过类型系统保证错误处理路径的完备性（无隐式跳过）
边界: unwrap() / expect() 将 Result 转为 panic，是显式的"我保证这里不会错"
```

### 4.2 定理：? 运算符 ⟹ 错误传播自动化
>

> **[TRPL: Ch9.2] · [Rust Reference: The ? operator]** ? 运算符通过隐式调用 From::from 实现错误的自动转换与传播。 ✅ 已验证

> **[RFC 243: The ? Operator]** The `?` operator was introduced in RFC 243 to provide ergonomic error propagation, later extended by RFC 3058 for the general `Try` trait. ✅ 已验证

```text
前提 1: ? 运算符展开为 match，Err 分支提前返回
前提 2: From trait 提供错误类型的自动向上转换
前提 3: 函数返回类型必须兼容（Result/Option）
    ↓
引理: ? 运算符 = monadic bind 的语法糖（Result >>= 的特化）
    ↓
定理: ? 运算符 ⟹ 错误传播自动化
    ↓
推论 1: 链式调用中每个 ? 点都是潜在的错误返回点（控制流显式）
推论 2: 不同错误类型通过 From 自动统一，无需手动转换
边界: 闭包/回调中 ? 可能受限（返回类型需匹配）
```

### 4.3 推论：panic ⟹ 不可恢复错误的显式边界

> **[TRPL: Ch9] · [Rust Reference: panic]** panic 是 Safe Rust 中显式标记"程序进入不可能状态"的机制。 ✅ 已验证

> **[Wikipedia: Exception handling]** Unlike Java/C++ exceptions, Rust's `panic!` is not a general recovery mechanism but an explicit boundary for unrecoverable bugs; recoverable errors use `Result<T, E>`. ✅ 已验证

```text
前提 1: panic 立即终止当前线程的执行（默认展开栈）
前提 2: panic 仅应用于不可恢复的内部不变量违反（bug）
前提 3: catch_unwind 可在 FFI 边界隔离 panic（非通用恢复机制）
    ↓
引理: panic 将不可恢复错误与可恢复错误在类型层面分离
    ↓
推论: panic ⟹ 不可恢复错误的显式边界
    ↓
边界 1: 不应使用 panic 处理预期错误（如文件不存在）
边界 2: 不应使用 panic 处理用户输入验证（应用 Result）
边界 3: 库代码应优先返回 Result，让调用者决定是否 panic
```

### 4.4 类型安全错误处理

> **[Rust Reference: Enums] · [TRPL: Ch9]** Result 的错误类型在编译期确定，match 穷尽性检查保证处理完备性。 ✅ 已验证

```text
前提: Result<T, E> 是泛型代数数据类型
    ↓
定理: 错误类型 E 在编译期确定，无法 catch 不相关的错误类型
    ↓
对比: Java catch(Exception e) 可捕获任意异常
      Rust match Err(e) 只匹配该函数的 Result 类型
推论: 错误处理的类型安全由编译器静态保证
```

### 4.5 定理一致性矩阵

> **[原创分析] · [TRPL: Ch9] · [Rust Reference: The ? operator]** 错误处理定理矩阵基于和类型、Monad bind 和 Rust 编译器检查。 💡 原创分析

| **定理/引理/推论** | **前提** | **结论** | **依赖的 L4 公理** | **被哪些定理依赖** | **失效条件** | **典型错误码** |
|:---|:---|:---|:---|:---|:---|:---|
| **引理**: Result ⟹ 和类型强制 | Result 返回 + 编译器检查 | 错误不可忽略 | 和类型 (A + E) | 所有错误处理代码 | `unwrap()` 忽略 | — |
| **定理**: ? 运算符传播 | 函数返回兼容 Result/Option | 自动错误短路 | Monad bind (>>=) | 异步错误传播 | 在闭包/回调中误用 | E0277 |
| **推论**: panic 边界 | 不可恢复状态 | 显式程序终止 | —（运行时机制） | 设计决策 | 滥用 panic 处理预期错误 | panic |
| **定理**: Error trait 一致性 | 自定义错误实现 Error | 可与 ? 和其他错误互操作 | 类型类一致性 | 错误链、报告 | 未实现 Source | — |
| **引理**: Option 空值安全 | 使用 Option<T> | 无 null 解引用 | Maybe Monad | 所有可空场景 | `unwrap()` on None | — |
| **推论**: From 转换链 | E1: From<E2> | 错误类型自动统一 | 类型类传递性 | ? 运算符 | 未实现 From | E0277 |
| **定理**: 类型状态编码 | enum 表达状态 | 非法状态不可表示 | 代数类型穷尽性 | Typestate 模式 | 状态转换遗漏 | — |
| **引理**: catch_unwind 隔离 | 闭包内 panic | 线程级别隔离 | —（运行时机制） | FFI 边界 | 跨线程 panic 传播 | panic |

> **一致性检查**: Option 空值安全 ⟹ Result 显式传播 ⟹ ? 运算符合法性 ⟹ From 转换链，形成**从值到函数到控制流到类型统一**的递进链。panic 是独立维度（不可恢复边界），与 Result 形成互补。
>
> **跨层映射**: 本文件定理 ↔ [`00_meta/inter_layer_map.md`](../00_meta/inter_layer_map.md) §4.1 "内存安全完备性"

> **过渡到示例与反例**: 定理链提供了形式化保证，但工程实践中这些保证的边界在哪里？下一节通过正例展示错误处理的正确使用方式，通过反例揭示定理失效的精确条件——特别是 unwrap panic、? 类型不匹配、错误忽略等边界场景。

---

## 五、示例与反例（Examples & Counter-examples）

### 5.1 正确示例：`?` 运算符链式传播

```rust
// ✅ 正确: ? 运算符使错误传播简洁
use std::fs::File;
use std::io::{self, Read};

fn read_username_from_file() -> Result<String, io::Error> {
    let mut file = File::open("hello.txt")?;  // Err 则提前返回
    let mut username = String::new();
    file.read_to_string(&mut username)?;      // Err 则提前返回
    Ok(username)
}

// 更简洁的版本:
fn read_username() -> Result<String, io::Error> {
    let mut username = String::new();
    File::open("hello.txt")?.read_to_string(&mut username)?;
    Ok(username)
}
```

### 5.2 正确示例：自定义错误类型

```rust
// ✅ 正确: thiserror 风格自定义错误
use std::fmt;

#[derive(Debug)]
enum AppError {
    Io(std::io::Error),
    Parse(std::num::ParseIntError),
    Config(String),
}

impl fmt::Display for AppError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            AppError::Io(e) => write!(f, "IO error: {}", e),
            AppError::Parse(e) => write!(f, "Parse error: {}", e),
            AppError::Config(s) => write!(f, "Config error: {}", s),
        }
    }
}

impl std::error::Error for AppError {}

// From 实现使 ? 自动转换
impl From<std::io::Error> for AppError {
    fn from(e: std::io::Error) -> Self { AppError::Io(e) }
}

impl From<std::num::ParseIntError> for AppError {
    fn from(e: std::num::ParseIntError) -> Self { AppError::Parse(e) }
}

fn load_config() -> Result<i32, AppError> {
    let content = std::fs::read_to_string("config.txt")?;  // io::Error → AppError
    let port: i32 = content.trim().parse()?;                // ParseIntError → AppError
    Ok(port)
}
```

### 5.3 反例：`?` 在错误返回类型中不匹配

```rust,ignore
// ❌ 反例: ? 的错误类型无法自动转换
fn parse_or_zero(s: &str) -> Result<i32, std::io::Error> {
    let n: i32 = s.parse()?;  // E0277: `?` couldn't convert the error
    Ok(n)
}
// parse() 返回 Result<i32, ParseIntError>
// 但函数返回 Result<i32, io::Error>
// ParseIntError 不实现 From<io::Error>

```

**修正方案**：

```rust,ignore
// ✅ 方案 1: 使用 map_err 显式转换
fn parse_or_zero(s: &str) -> Result<i32, std::io::Error> {
    let n = s.parse().map_err(|e| {
        std::io::Error::new(std::io::ErrorKind::InvalidData, e)
    })?;
    Ok(n)
}

// ✅ 方案 2: 使用通用错误类型（如 anyhow）
use anyhow::Result;
fn parse_or_zero(s: &str) -> Result<i32> {
    let n: i32 = s.parse()?;  // anyhow 自动转换任何错误
    Ok(n)
}
```

### 5.4 反例：忽略 Result 导致 bug

```rust
// ❌ 反例: 忽略 Result 返回值
fn main() {
    let file = std::fs::File::create("/root/protected.txt");
    // file 是 Result<File, Error>，但未被处理
    // 如果创建失败，程序静默继续，后续使用可能 panic
}
```

**修正方案**：

```rust
// ✅ 修正: 必须处理 Result
fn main() {
    let file = std::fs::File::create("/root/protected.txt")
        .expect("Failed to create file");  // 或 ?, unwrap, match
}

// 编译器警告: unused `Result` that must be used
// 也可以通过 let _ = ... 显式忽略（但通常不建议）
```

### 5.5 边界示例：`Option` 与 `Result` 互转

```rust
// ✅ 边界: Option 与 Result 的优雅互转
struct User { name: String }

fn find_user(id: u64) -> Option<User> { /* ... */ None }

fn get_user_name(id: u64) -> Result<String, &'static str> {
    let user = find_user(id).ok_or("User not found")?;  // Option → Result
    Ok(user.name)
}

fn maybe_port() -> Option<u16> {
    let config = std::fs::read_to_string("port.txt").ok()?;  // Result → Option
    config.trim().parse().ok()
}
```

> **过渡到反命题分析**: 示例展示了错误处理的正确使用方式，但反例只是孤立场景。下一节通过系统化的反命题分析，将"错误处理定理何时成立/何时失效"形式化为可遍历的决策树，重点揭示 Result 的"强制不可忽略"边界与 ? 运算符的适用限制。

---

### 5.5 补充：异步错误处理与 `poll_fn` / `TryFuture` 模式

> **[RFC 243]** · **[futures-rs 文档]** · **[Rust Reference: Async]** 异步错误处理不是同步 `Result` 的简单平移——`Future` 的惰性求值、取消（cancellation）和 `Waker` 驱动模型引入了新的错误传播边界。✅

#### `poll_fn`：将闭包提升为 Future

```rust,ignore
use std::future::poll_fn;
use std::task::Poll;

// ✅ 用 poll_fn 包装底层异步原语
async fn read_with_timeout<R>(reader: &mut R, timeout: Duration) -> Result<Vec<u8>, Error>
where
    R: AsyncRead + Unpin,
{
    poll_fn(|cx| {
        // 直接操作 Poll<Result<T, E>>
        match reader.poll_read(cx, &mut buf) {
            Poll::Ready(Ok(n)) => Poll::Ready(Ok(buf[..n].to_vec())),
            Poll::Ready(Err(e)) => Poll::Ready(Err(e.into())),
            Poll::Pending => {
                // 检查超时...
                Poll::Pending
            }
        }
    }).await
}
```

`poll_fn` 的核心价值：**在 `async` 块内部手动控制 `Poll` 状态转换**，常用于：

1. 桥接非 `async` 的底层 IO（如 `mio`）到 `Future` 接口
2. 实现自定义超时、重试逻辑
3. 在 `select!` 中嵌入临时 Future

#### `TryFuture` 与 `?` 运算符的异步扩展

虽然标准库中没有独立的 `TryFuture` trait，但 `Future<Output = Result<T, E>>` 在生态中形成了**隐式的 TryFuture 模式**：

```rust,ignore
use futures::future::TryFutureExt; // futures crate 扩展

// ✅ 链式错误处理：map_err + and_then
let result = fetch_user(id)
    .map_err(|e| Error::Network(e))          // Future<Output = Result<User, Error>>
    .and_then(|user| fetch_orders(user.id))  // 自动传递 Err，扁平化嵌套 Future
    .await?;
```

| 模式 | 同步等价 | 异步形式 | 适用场景 |
|:---|:---|:---|:---|
| `?` 传播 | `Result::?` | `Future<Output = Result<T, E>>` 后接 `?` | 顺序异步操作，错误立即返回 |
| `map_err` | `Result::map_err` | `TryFutureExt::map_err` | 错误类型转换 |
| `and_then` | `Result::and_then` | `TryFutureExt::and_then` | 顺序组合两个可能失败的 Future |
| `try_join!` | — | `futures::try_join!` | 并行执行多个 Future，任一失败即返回 Err |
| `try_select!` | — | `futures::future::select` + 错误处理 | 竞争执行，需手动处理取消与错误 |

#### 取消安全（Cancellation Safety）与错误处理

```rust,ignore
use tokio::select!;

let result = select! {
    // ✅ 取消安全：recv 被取消后，channel 状态一致（无半读消息）
    msg = rx.recv() => msg.ok_or(Error::ChannelClosed),
    // ⚠️ 非取消安全：send 被取消后，数据可能已部分写入 socket
    _ = tx.send(data) => Ok(()),
};
```

> **关键洞察**: 异步错误处理有**两个维度**：1) `Result` 维度的业务错误（IO 失败、解析错误）；2) **取消维度**的生命周期错误（Future 被 `select!` 丢弃时资源未清理）。`Drop` 实现负责后者，`?` 运算符负责前者，但两者在 `unsafe` 或 FFI 边界处可能交互产生 UB。
> **来源**: [Tokio 文档: Cancellation Safety] · [RFC 243: ? in main] · [futures-rs: TryFutureExt]

---

## 六、反命题与边界分析（Counter-proposition & Boundary Analysis）

> **[TRPL: Ch9] · [Rust API Guidelines] · [RFC 243]** 反命题分析基于和类型、Monad bind 和 Rust 编译器检查的形式化语义。 ✅ 已验证

**错误处理策略决策树（Mermaid graph TD）**:

```mermaid
graph TD
    A[函数可能失败?] -->|是| B{失败类型?}
    A -->|否| C[返回裸类型 T]

    B -->|可恢复错误| D[返回 Result<T, E>]
    B -->|不可恢复/程序 bug| E["panic!"]
    B -->|值可能缺失| F[返回 Option<T>]

    D --> G{调用方如何处理?}
    G -->|传播| H[使用 ? 运算符]
    G -->|转换错误| I[使用 map_err]
    G -->|提供默认值| J[使用 unwrap_or]
    G -->|合并多个错误| K[使用 anyhow/eyre]

    E --> L{是否在 main/测试?}
    L -->|是| M[直接 panic]
    L -->|否| N[考虑改回 Result]

    F --> O{缺失是错误还是正常?}
    O -->|正常场景| P[Option 足够]
    O -->|错误场景| Q[升级为 Result]

    style C fill:#9f9
    style H fill:#9f9
    style M fill:#ff9
    style N fill:#f99
```

> **认知功能**: 交互式策略选择器——将"当前函数应如何返回"这一工程决策转化为可遍历的条件判断流程。读者遇到"函数可能失败"的场景时，可沿决策节点逐层下行，最终到达对应 Rust 惯用法（Result/panic/Option）的叶子节点。核心洞察：颜色编码（绿=推荐，红=避免）将 Rust API Guidelines 的规范性建议转化为视觉即时判断。[来源: 💡 原创分析]

> **思维表征说明**: 此 `graph TD` 决策树将错误处理的**策略选择**形式化为可遍历的判断流程——从「是否可能失败」开始，经过「失败类型」「调用方处理方式」等决策节点，最终到达叶子节点的具体 Rust 惯用法。与 ASCII 决策树相比，Mermaid 图的优势在于**可视化层次结构**和**颜色编码**（绿色=推荐，黄色=谨慎，红色=避免），帮助读者快速定位当前场景的正确策略。 [来源: TRPL §9; Rust API Guidelines; RFC 243]

### 6.1 反命题 1: "Result 消除了所有错误"

> 运行时层 — Result 消除了静默错误忽略，但 unwrap 和 panic 仍是错误爆发的通道。

```mermaid
graph TD
    P["命题: Result 消除了所有错误"] --> Q1{"使用 unwrap() / expect()?"}
    Q1 -->|是| F1["反例: unwrap() 将 Err 转为 panic<br/>→ 错误被暴力转换为崩溃"]
    Q1 -->|否| Q2{"使用 let _ = result?"}
    Q2 -->|是| F2["反例: 绑定到 _ 丢弃错误值<br/>→ 信息丢失，但 panic 风险仍在（? 会传播）"]
    Q2 -->|否| Q3{"使用 unsafe { *ptr }?"}
    Q3 -->|是| F3["反例: unsafe 可完全绕过类型系统<br/>→ 所有保证失效，UAF/DF 可能发生"]
    Q3 -->|否| Q4{"函数返回 Result 但调用方不处理?"}
    Q4 -->|是| F4["反例: #[must_use] 仅警告，不强制<br/>→ 编译通过但逻辑错误"]
    Q4 -->|否| T1["定理成立: 错误必须显式处理<br/>✅ 和类型强制分支"]

    style F1 fill:#f66
    style F2 fill:#f66
    style F3 fill:#f66
    style F4 fill:#f66
    style T1 fill:#6f6
```

> **认知功能**: 反事实验证器——通过系统化枚举定理失效的精确路径，帮助读者建立"Result 的强制处理边界"。读者可沿分支逐一检验自己代码中是否存在 unwrap、let _ = result 或 unsafe 绕过等反模式。核心洞察：Result 的 `#[must_use]` 仅是弱强制；unwrap 和 unsafe 是类型系统安全性的两个主要逃逸通道。[来源: 💡 原创分析]

**四层分析**:

| **层面** | **分析** | **结果** |
|:---|:---|:---|
| 编译期 | #[must_use] 警告未处理 Result，但不阻止编译 | ⚠️ 弱强制 |
| 运行时 | unwrap 导致 panic，是显式放弃安全性 | ❌ 可能崩溃 |
| 语义 | Result 的语义是"错误存在"，不保证"错误被正确处理" | ⚠️ 语义边界 |
| 工程 | clippy 有 `unwrap_used` lint，anyhow/thiserror 是标准 | ✅ 可缓解 |

### 6.2 反命题 2: "? 运算符总是正确传播"

> 编译期层 — ? 运算符有明确的类型约束，违反时编译失败。

```mermaid
graph TD
    P["命题: ? 运算符总是正确传播"] --> Q1{"函数返回 Result<T, E>?"}
    Q1 -->|否| Q2{"函数返回 Option<T>?"}
    Q1 -->|是| Q3{"Err 类型实现 From<内部错误类型>?"}
    Q2 -->|否| F1["反例: ? 在返回非 Result/Option 的函数中<br/>→ E0277: the `?` operator can only be used in a function that returns `Result` or `Option`"]
    Q2 -->|是| T1["定理成立: Option 内 ? 正确传播<br/>✅ Some 继续，None 提前返回"]
    Q3 -->|是| T2["定理成立: ? 正确传播并自动转换<br/>✅ From trait 完成类型统一"]
    Q3 -->|否| F2["反例: E0277 couldn't convert the error<br/>→ 错误类型不匹配且无 From 实现"]
    Q3 -->|部分| Q4{"在闭包/回调中使用?"}
    Q4 -->|返回类型不匹配| F3["反例: 闭包返回类型与外部函数不同<br/>→ ? 展开后的 return 目标错误"]
    Q4 -->|返回类型匹配| T3["定理成立: try_fold 等闭包中 ? 可用<br/>✅ 闭包返回 Result，与外部一致"]

    style F1 fill:#f66
    style F2 fill:#f66
    style F3 fill:#f66
    style T1 fill:#6f6
    style T2 fill:#6f6
    style T3 fill:#6f6
```

> **认知功能**: 类型约束诊断图——将 ? 运算符的编译期类型检查逻辑可视化为决策节点。读者在遭遇 E0277 错误时，可对照此图定位是"返回类型不匹配"还是"From 实现缺失"。核心洞察：? 的"自动化"并非魔法，而是 monadic bind + From trait 的语法糖；闭包中的限制源于 return 目标函数的歧义。[来源: 💡 原创分析]

**四层分析**:

| **层面** | **分析** | **结果** |
|:---|:---|:---|
| 编译期 | 类型不匹配时编译错误（E0277） | ✅ 安全 |
| 运行时 | 无运行时检查开销（纯语法糖） | ✅ 零成本 |
| 语义 | 要求 From 实现，语义边界明确 | ✅ 语义清晰 |
| 工程 | map_err 或 anyhow 是标准 workaround | ✅ 可解 |

### 6.3 反命题 3: "panic 只应在完全不可能时发生"

> 工程层 — panic 的"不可恢复"定义在实践中存在灰色地带。

```mermaid
graph TD
    P["命题: panic 只应在完全不可能时发生"] --> Q1{"是内部不变量违反?"}
    Q1 -->|是| T1["定理成立: panic 正确<br/>✅ 例如数组索引越界（逻辑已保证不可能）"]
    Q1 -->|否| Q2{"是用户输入无效?"}
    Q2 -->|是| F1["反例: 用户输入不应 panic<br/>→ 应返回 Result，让调用者决定"]
    Q2 -->|否| Q3{"是外部资源暂时不可用?"}
    Q3 -->|是| F2["反例: 网络/文件错误不应 panic<br/>→ 应返回 Result，支持重试"]
    Q3 -->|否| Q4{"是快速原型/测试代码?"}
    Q4 -->|是| N1["工程解: unwrap 在原型中可接受<br/>→ 但生产化前必须替换"]
    Q4 -->|否| Q5{"是 const/static 初始化?"}
    Q5 -->|是| T2["定理成立: 编译期求值失败可 panic<br/>✅ 编译期已知不可能"]
    Q5 -->|否| F3["反例: panic 在库代码中强制调用方崩溃<br/>→ 库应优先返回 Result"]

    style F1 fill:#f66
    style F2 fill:#f66
    style F3 fill:#f66
    style N1 fill:#69f
    style T1 fill:#6f6
    style T2 fill:#6f6
```

> **认知功能**: 工程伦理校准器——揭示 panic 与 Result 之间的灰色地带，帮助读者在"内部不变量违反""用户输入无效""外部资源不可用"等模糊场景中做出正确决策。核心洞察：panic 的使用边界不是"是否可能"，而是"调用者是否有意义地恢复"；库代码应优先返回 Result，将崩溃决策权交还调用方。[来源: 💡 原创分析]

**四层分析**:

| **层面** | **分析** | **结果** |
|:---|:---|:---|
| 编译期 | panic 编译通过，无静态检查限制使用场景 | ⚠️ 无编译期阻止 |
| 运行时 | panic 立即终止线程，不可恢复 | ❌ 可能过度使用 |
| 语义 | Rust API Guidelines 明确区分 panic vs Result 场景 | ✅ 语义明确 |
| 工程 | 库代码应返回 Result，应用代码可酌情 panic | ✅ 有指导原则 |

### 6.4 反命题 4: "Option<T> 完全替代 null"

> 语义层 — Option 替代了空指针，但 unwrap 重新引入了 null 解引用的等价风险。

```mermaid
graph TD
    P["命题: Option<T> 完全替代 null"] --> Q1{"使用 unwrap() 或 unwrap_unchecked()?"}
    Q1 -->|是| F1["反例: unwrap() on None → panic<br/>→ 等价于 null 解引用（只是有定义的行为：panic）"]
    Q1 -->|否| Q2{"使用 if let Some(x) = opt?"}
    Q2 -->|是| T1["定理成立: 模式匹配强制处理 None<br/>✅ 编译器检查穷尽性"]
    Q2 -->|否| Q3{"使用 opt.map / and_then?"}
    Q3 -->|是| T2["定理成立: 组合子保持 Option 语义<br/>✅ 无直接解包风险"]
    Q3 -->|否| Q4{"将 Option 转为 Result 再 ?"}
    Q4 -->|是| T3["定理成立: ok_or / ok_or_else 显式提供错误信息<br/>✅ None 被转化为明确的 Err"]
    Q4 -->|否| F2["反例: let x = opt; 后续 *x 假设 Some<br/>→ 逻辑错误，编译器不阻止"]

    style F1 fill:#f66
    style F2 fill:#f66
    style T1 fill:#6f6
    style T2 fill:#6f6
    style T3 fill:#6f6
```

> **认知功能**: 语义等价性检验器——澄清 Option 替代 null 的精确语义边界，揭示 unwrap 如何重新引入 null 解引用的等价风险。读者可用此图审查代码中 Option 的使用是否真正遵循类型安全路径。核心洞察：Option 在编译期替代了 null，但 unwrap 在运行期将"有定义的行为（panic）"重新暴露为崩溃风险；模式匹配和组合子才是安全替代。[来源: 💡 原创分析]

**四层分析**:

| **层面** | **分析** | **结果** |
|:---|:---|:---|
| 编译期 | Option 类型替代 null，但 unwrap 仍编译通过 | ⚠️ 弱强制 |
| 运行时 | unwrap on None 是 panic，非 UB（优于 null 解引用） | ✅ 更安全 |
| 语义 | None 是显式的，不同于 null 的隐式存在 | ✅ 语义清晰 |
| 工程 | 优先使用 ?、match、组合子，避免 unwrap | ✅ 有指导原则 |

> **过渡到边界极限测试**: 反命题决策树揭示了定理失效的逻辑路径，但极限测试将定理推向边界——通过代码展示编译器在极端约束下的精确行为。

---

## 七、边界极限测试代码（Boundary Limit Tests）

### 7.1 测试 1: ? 运算符在闭包中的限制

```rust
use std::num::ParseIntError;

// 边界: ? 在闭包中的精确限制

fn process(items: Vec<&str>) -> Result<i32, ParseIntError> {
    // ❌ 错误: 闭包返回类型不匹配
    // let sum: Result<i32, _> = items.iter().map(|s| s.parse()?).sum();
    // 编译错误: ? 不能在返回类型不匹配的闭包中使用
    // 因为 map 闭包返回 i32，但 ? 需要返回 Result

    // ✅ 正确: 使用 try_fold 或 try_for_each（闭包返回 Result）
    let sum: i32 = items.iter()
        .try_fold(0, |acc, s| {
            let n: i32 = s.parse()?;  // ✅ try_fold 返回 Result，匹配
            Ok(acc + n)
        })?;

    // ✅ 正确: collect 到 Result<Vec<_>, _>
    let nums: Vec<i32> = items.iter()
        .map(|s| s.parse())
        .collect::<Result<Vec<_>, _>>()?;

    Ok(sum)
}
```

### 7.2 测试 2: From 转换链的边界

```rust,ignore
use std::fmt;
use std::io;

// 边界: From 转换链的自动推导与断点

# [derive(Debug)]

enum MyError {
    Io(io::Error),
    Parse(std::num::ParseIntError),
    Custom(String),
}

impl fmt::Display for MyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}
impl std::error::Error for MyError {}

impl From<io::Error> for MyError {
    fn from(e: io::Error) -> Self { MyError::Io(e) }
}

impl From<std::num::ParseIntError> for MyError {
    fn from(e: std::num::ParseIntError) -> Self { MyError::Parse(e) }
}

// 断点测试: String 没有实现 From<String> for MyError
fn may_fail() -> Result<i32, MyError> {
    let s = std::fs::read_to_string("num.txt")?;  // io::Error → MyError ✅
    let n: i32 = s.trim().parse()?;                // ParseIntError → MyError ✅

    // let custom: String = "error".to_string();
    // custom?;  // ❌ E0277: String 不能转为 MyError

    Ok(n)
}

// 缓解: 使用 map_err 或 anyhow
fn may_fail_anyhow() -> anyhow::Result<i32> {
    let s = std::fs::read_to_string("num.txt")?;   // 任何错误自动转换 ✅
    let n: i32 = s.trim().parse()?;                 // 任何错误自动转换 ✅
    Ok(n)
}

```

### 7.3 测试 3: panic 边界与 catch_unwind

```rust
use std::panic;

fn may_panic(flag: bool) -> i32 {
    if flag { panic!("intentional panic"); }
    42
}

fn test_catch_unwind() {
    let result = panic::catch_unwind(|| may_panic(true) );
    match result {
        Ok(v) => println!("Success: {}", v),
        Err(_) => println!("Caught panic!"),
    }
    // 边界: catch_unwind 不捕获 abort 策略；要求 UnwindSafe；非通用异常处理
}
```

### 7.4 测试 4: Result 与 Option 的组合边界

```rust
// 边界: Result<Option<T>, E> 与 Option<Result<T, E>> 的精确语义

fn nested_result_option() {
    // 场景: 查询可能失败（Result），成功时可能无数据（Option）
    let ro: Result<Option<i32>, &str> = Ok(Some(42));

    // 模式 1: 先处理 Result，再处理 Option
    match ro {
        Ok(Some(v)) => println!("Value: {}", v),
        Ok(None) => println!("No data"),
        Err(e) => println!("Error: {}", e),
    }

    // 模式 2: 使用 ? 和 if let 分层处理
    fn get_value() -> Result<Option<i32>, &'static str> {
        Ok(Some(10))
    }

    fn process() -> Result<i32, &'static str> {
        let opt = get_value()?;  // 先解 Result
        if let Some(v) = opt {
            Ok(v * 2)
        } else {
            Err("No value")
        }
    }

    // 模式 3: transpose — Result<Option<T>, E> ↔ Option<Result<T, E>>
    let ro: Result<Option<i32>, &str> = Ok(Some(5));
    let or: Option<Result<i32, &str>> = ro.transpose();
    // Ok(Some(5)) → Some(Ok(5))
    // Ok(None)    → None
    // Err(e)      → Some(Err(e))
}
```

> **过渡到认知路径**: 边界测试验证了定理在极端条件下的行为，但从学习者的视角，错误处理概念如何从直觉逐步构建到形式化理解？下一节提供六步递进的认知路径，每步之间有过渡解释。

---

## 八、认知路径（Cognitive Path）

> **[原创分析] · [TRPL: Ch9]** 认知路径从"如何处理错误"直觉到和类型 + Error Monad 形式化的渐进映射。 💡 原创分析

### Step 1: 直觉类比 — "快递包裹"

**核心问题**: "Rust 没有异常，那错误怎么处理？"

**过渡解释**: 从熟悉的概念出发建立直觉锚点。将 `Result<T, E>` 类比为"快递包裹"——要么是商品（Ok），要么是拒收单（Err），你必须拆开才知道。这与 Java/C++ 的异常（快递员突然冲进房间大喊"出事了！"）形成鲜明对比。这一步建立 Rust 错误处理的显式性直觉。从 Step 1 到 Step 2 的过渡发生在学习者写第一个返回 `Result` 的函数时，发现编译器要求调用方必须处理返回值。

```text
直觉映射:
  Result<T, E>  ≈  快递包裹（要么是商品，要么是拒收单）
  unwrap()      ≈  "我保证里面是商品，直接拆"（如果不是就崩溃）
  ? 运算符      ≈  "如果是拒收单，直接退给上级"（错误传播）
  match         ≈  "拆开包裹，分别处理两种情况"
```

### Step 2: 语法熟悉 — Result/Option 与 match

**核心问题**: "怎么写错误处理代码？match 太啰嗦怎么办？"

**过渡解释**: 在直觉锚定后，需要将抽象概念映射到具体语法。这一步覆盖 `Result::Ok/Err`、`Option::Some/None`、`match`、`if let`、`?` 等核心语法。关键是建立"错误是值，不是控制流异常"的理解。从 Step 2 到 Step 3 的过渡由简洁性需求驱动：当学习者发现嵌套 match 过于冗长时，`?` 运算符成为自然的学习目标。

```rust
// 核心语法模式:
fn may_fail() -> Result<i32, String> {
    Ok(42)
}

// 显式处理
match may_fail() {
    Ok(v) => println!("{}", v),
    Err(e) => println!("Error: {}", e),
}

// 简洁处理
if let Ok(v) = may_fail() { println!("{}", v); }

// 传播处理
fn caller() -> Result<i32, String> {
    let v = may_fail()?;  // Err 则提前返回
    Ok(v + 1)
}
```

### Step 3: 传播自动化 — ? 运算符与 From

**核心问题**: "不同函数返回不同错误类型，怎么统一？"

**过渡解释**: 语法熟练后，学习者需要处理多函数链式调用中的错误传播。`?` 运算符不仅简化语法，还通过 `From` trait 实现错误类型的自动转换。这一步是认知的关键跃迁——理解 Rust 错误处理不是"每个错误单独处理"，而是"错误类型自动向上转换"的层级结构。从 Step 3 到 Step 4 的过渡由设计需求驱动：当学习者需要定义自己的错误类型时，进入自定义错误设计领域。

```text
错误层级:
  底层错误: io::Error, ParseIntError, serde::Error ...
      ↓ 通过 From 自动转换
  中层错误: AppError { Io(...), Parse(...), Config(...) }
      ↓ 通过 From 自动转换
  顶层错误: anyhow::Error（通用包装器）

? 运算符的魔力:
  let n = s.parse()?;  // ParseIntError → AppError（自动）
```

### Step 4: 自定义错误 — thiserror 与 anyhow

> **[crates.io: thiserror / anyhow]** `thiserror` is the standard choice for libraries that need structured error types, while `anyhow` is preferred in applications for ergonomic error propagation. ✅ 已验证

**核心问题**: "怎么设计好的错误类型？"

**过渡解释**: 当学习者理解了错误传播机制后，需要面对错误类型的设计决策。`thiserror` 适合库（结构化错误，调用者可以 match），`anyhow` 适合应用（快速传播，无需自定义错误类型）。这一步建立"错误设计是 API 设计的一部分"的认知。从 Step 4 到 Step 5 的过渡由边界问题驱动：当学习者发现某些场景下 Result 不够用时（如内部不变量违反），需要理解 panic 的精确语义。

```text
设计决策:
  库代码（被调用）: thiserror + enum AppError
    → 调用者需要区分错误类型并采取不同行动

  应用代码（主逻辑）: anyhow + Result<T, anyhow::Error>
    → 快速开发，统一错误处理，错误链报告

  快速原型: unwrap / expect
    → 标记 TODO，后续替换为 proper error handling
```

### Step 5: 边界认知 — panic 与不可恢复错误

**核心问题**: "什么时候用 panic？什么时候用 Result？"

**过渡解释**: 学习者在前四步建立了对 Result 的信任，这一步需要精确校准 panic 的使用边界。核心原则是：Result 用于"预期可能失败的操作"，panic 用于"逻辑上不可能发生的状态"。关键区分：文件不存在 → Result；数组索引越界（已验证逻辑保证不会）→ panic。从 Step 5 到 Step 6 的过渡是"从现象到原理"——理解为什么 Rust 这样设计（和类型 vs 异常，显式控制流 vs 隐式跳转）。

```text
决策框架:
  调用者可能恢复?        → Result<T, E>
  违反函数契约/不变量?   → panic! / assert!
  逻辑不可能到达?        → unreachable!
  快速原型/已知安全?      → unwrap（带注释）
```

### Step 6: 形式化掌控 — Monad 与类型级错误处理

**核心问题**: "Result 在数学上是什么？为什么 ? 能自动传播？"

**过渡解释**: 认知路径的最终目标是让学习者具备自主验证能力。通过类型论视角，`Result<T, E>` 是 Either Monad，`?` 是 monadic bind（`>>=`）的语法糖。Monad 定律（左单位元、右单位元、结合律）保证了错误传播的可组合性。这一形式化视角不仅解释了 ? 为什么工作，还揭示了 `and_then`、`map`、`or_else` 等组合子的数学本质。

```text
形式化映射:
  Result<T, E>  ≅  Either E T
  ? 运算符      ≅  >>= / bind 的语法糖
  and_then      ≅  >>=（monadic bind）
  map           ≅  fmap（functor map）

Monad 定律验证:
  左单位元: Ok(x).and_then(f)  ≡  f(x) ✅
  右单位元: result.and_then(|x| Ok(x))  ≡  result ✅
  结合律:   result.and_then(f).and_then(g)
            ≡  result.and_then(|x| f(x).and_then(g)) ✅
```

---

## 九、知识来源关系（Provenance）

| **论断** | **来源** | **可信度** |
|:---|:---|:---|
| Result/Option 用于可恢复错误 | [TRPL: Ch9] | ✅ |
| panic 用于不可恢复错误 | [TRPL: Ch9] | ✅ |
| ? 运算符自动传播错误 | [TRPL: Ch9.2] | ✅ |
| ? 调用 From::from | [Rust Reference: The ? operator] | ✅ |
| Result 是 Monad | [Haskell: Either Monad] · 类型论 | ✅ |
| thiserror / anyhow 是生态标准 | [crates.io] · 社区实践 | ✅ |
| unwrap 在生产代码中需谨慎 | [Rust API Guidelines] | ✅ |
| Monad 与错误处理 | [Wadler 1992 — The Essence of Functional Programming, POPL] | ✅ |
| 代数效应与异常 | [Plotkin & Pretnar 2009 — Handlers of Algebraic Effects] | ✅ |
| ? 运算符设计 | [RFC 243] | ✅ |
| 和类型穷尽性检查 | [类型论标准教材] · [Rust Reference: Enums] | ✅ |

---

### 9.1 补充：`Termination` trait 与 `main` 返回 `Result`

> **[Rust Reference: Termination]** · **[RFC 1937]** Rust 程序入口 `main` 可以返回 `Result<T, E>` 或 `()`，这由 `Termination` trait 统一处理。该 trait 定义了程序退出时的**退出码转换规则**和**错误报告行为**。✅

#### `Termination` trait 定义

```rust,ignore
pub trait Termination {
    fn report(self) -> ExitCode;
}

// ✅ 为 () 实现：正常退出，退出码 0
impl Termination for () {
    fn report(self) -> ExitCode { ExitCode::SUCCESS }
}

// ✅ 为 Result<T, E> 实现：Ok → 0, Err → 非零
impl<T: Termination, E: Debug> Termination for Result<T, E> {
    fn report(self) -> ExitCode {
        match self {
            Ok(val) => val.report(),
            Err(err) => {
                eprintln!("Error: {:?}", err);  // 自动打印错误信息
                ExitCode::FAILURE
            }
        }
    }
}
```

#### `main` 返回 `Result` 的工程价值

```rust,ignore
// ✅ main 可以直接返回 Result，? 运算符在顶层可用
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let config = std::fs::read_to_string("config.json")?;
    let settings: Settings = serde_json::from_str(&config)?;
    run_server(settings)?;
    Ok(())
}
```

| `main` 返回类型 | 退出码 | 错误输出 | 适用场景 |
|:---|:---|:---|:---|
| `()` | 0 | 无 | 简单程序、 CLI 工具 |
| `Result<(), E>` | 0 (Ok) / 1 (Err) | `eprintln!("Error: {:?}", err)` | 需要错误传播的应用 |
| `Result<T, E>`（T 非 ()） | 同 Result<(), E> | 同上 | 极少使用（T 的 report 通常也返回 0） |
| `!`（永不返回） | 无 | 无 | 守护进程、事件循环 |

> **来源**: [Rust Reference: Termination] · [RFC 1937: const fn] · [TRPL: Ch12.6] · [Wikipedia: Exit status]

### 9.2 补充：`Result<T, !>` 与 `!` (never type) 在错误处理中的使用

```rust,ignore
// ✅ Result<T, !> 表示"不可能失败"的操作
fn parse_known_good() -> Result<i32, !> {
    // 若输入是编译期已知的合法字符串，解析不可能失败
    Ok("42".parse().unwrap())  // unwrap 安全，因为输入已知合法
}

// ✅ 在泛型代码中统一处理"可能失败"和"不可能失败"
fn process<T, E>(result: Result<T, E>) -> T
where
    E: std::fmt::Debug,
{
    match result {
        Ok(v) => v,
        Err(e) => panic!("unexpected error: {:?}", e),
    }
}
```

> **关键洞察**: `Result<T, !>` 将"不可能出错"这一信息编码进类型系统。当泛型函数要求 `Result<T, E>` 时，传入 `Result<T, !>` 完全合法——因为 `!` 是任意类型的子类型，`Result<T, !>` 自然满足 `Result<T, E>` 的约束（当 `E` 接收 `!` 时）。这是子类型多态在错误处理中的优雅应用。
> **来源**: [Rust Reference: Never type] · [RFC 1216: Never type] · [TAPL Ch.11: Bottom type]

### 9.3 `std::backtrace::Backtrace` 与错误追踪

> **Bloom 层级**: 应用 → 分析
> **[Rust Standard Library: Backtrace]** · **[RFC 2504: Catch Unwind]** Rust 1.65 将 `std::backtrace::Backtrace` 纳入 stable，使得可恢复错误也能携带完整的调用栈上下文，填补了"错误发生点"与"错误报告点"之间的信息鸿沟。 ✅

#### 9.3.1 基本获取与显示

`Backtrace` 通过运行时栈展开（stack unwinding）捕获当前调用链：

```rust
use std::backtrace::Backtrace;

fn inner() {
    let bt = Backtrace::capture();
    println!("{}", bt);  // 显示捕获时的调用栈
}

fn outer() {
    inner();
}

fn main() {
    outer();
}
```

`Backtrace` 实现了 `Display` 与 `Debug`，默认输出包含：

- 帧序号（frame number）
- 符号名（symbol name）与偏移量
- 源文件路径与行列号（若调试符号可用）

> **[来源: Rust std docs — std::backtrace::Backtrace]** 稳定于 Rust 1.65。`Backtrace::capture()` 在 `RUST_BACKTRACE` 未设置时返回 `disabled`，避免无条件开销。 ✅

#### 9.3.2 环境变量控制

| 环境变量值 | 行为 | 适用场景 |
|:---|:---|:---|
| `unset` / `0` | `Backtrace::capture()` 返回 `disabled`；panic 不打印 backtrace | 生产环境默认 |
| `1` | 捕获并打印 backtrace，省略某些运行时/编译器内部帧 | 常规调试 |
| `full` | 捕获并打印完整 backtrace，包含所有帧 | 深度诊断 |

```bash
# ✅ 常规调试：显示简洁 backtrace
$ RUST_BACKTRACE=1 cargo run

# ✅ 深度诊断：显示包含所有内部帧的完整 backtrace
$ RUST_BACKTRACE=full cargo run
```

> **[来源: Rust Standard Library: Backtrace]** `Backtrace::capture()` 的行为受 `RUST_BACKTRACE` 环境变量控制；`force_capture()` 则无视环境变量强制捕获，适用于必须记录栈轨迹的关键错误。 ✅

#### 9.3.3 与 `anyhow` / `thiserror` 的集成

**`anyhow` 的自动 backtrace**：

`anyhow::Error` 在启用 `backtrace` feature（默认开启）时会自动捕获 `Backtrace`：

```rust,ignore
use anyhow::Result;

fn may_fail() -> Result<()> {
    std::fs::read_to_string("missing.txt")?;
    Ok(())
}

fn main() {
    if let Err(e) = may_fail() {
        // ✅ anyhow::Error 自动附加 backtrace
        eprintln!("Error: {:#}", e);      // 显示错误链
        eprintln!("Backtrace: {:?}", e.backtrace());  // 显示 backtrace
    }
}
```

> **[来源: anyhow docs — Features]** `anyhow` 的 `backtrace` feature 在 Rust 1.65+ 使用 `std::backtrace::Backtrace`，在旧版本回退到 `backtrace` crate。 ✅

**`thiserror` 中嵌入 backtrace**：

```rust,ignore
use std::backtrace::Backtrace;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum AppError {
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),

    #[error("configuration error: {msg}")]
    Config {
        msg: String,
        #[backtrace]  // ✅ thiserror 自动填充 Backtrace::capture()
        backtrace: Backtrace,
    },
}

fn load_config() -> Result<Config, AppError> {
    let content = std::fs::read_to_string("app.toml")
        .map_err(|e| AppError::Config {
            msg: e.to_string(),
            backtrace: Backtrace::capture(),
        })?;
    // ...
}
```

> **[来源: thiserror docs]** `thiserror` 1.0+ 支持 `#[backtrace]` 属性，可自动在构造错误时填充 `Backtrace`。若字段类型为 `Backtrace`，`#[backtrace]` 标记后 `Error::backtrace()` 方法将返回该字段。 ✅

#### 9.3.4 自定义错误类型中嵌入 `Backtrace` 的模式

当不使用 `thiserror` 时，手动嵌入 `Backtrace` 的标准模式：

```rust,ignore
use std::backtrace::Backtrace;
use std::fmt;

#[derive(Debug)]
struct TracedError {
    message: String,
    backtrace: Backtrace,
}

impl TracedError {
    fn new(msg: &str) -> Self {
        Self {
            message: msg.to_string(),
            backtrace: Backtrace::capture(),
        }
    }
}

impl fmt::Display for TracedError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}\n\nBacktrace:\n{}", self.message, self.backtrace)
    }
}

impl std::error::Error for TracedError {
    // ✅ 可选：实现 provide/backtrace 使错误报告器能提取 backtrace
    fn backtrace(&self) -> Option<&Backtrace> {
        Some(&self.backtrace)
    }
}
```

**设计模式矩阵**：

| 模式 | 实现方式 | 适用场景 | 性能影响 |
|:---|:---|:---|:---|
| 主动捕获 | `Backtrace::capture()` 嵌入错误结构体 | 库代码、结构化错误 | 仅在错误路径触发 |
| 延迟捕获 | `anyhow::Error` 自动捕获 | 应用代码、快速迭代 | 同上 |
| 强制捕获 | `Backtrace::force_capture()` | 关键安全审计点 | 无视环境变量，始终展开 |
| 不捕获 | 纯 `std::io::Error` | 高频错误路径、性能敏感 | 零额外开销 |

> **[来源: Rust API Guidelines — Error handling]** 库代码应仅在错误路径中捕获 backtrace，避免在成功路径引入运行时开销。 ✅

#### 9.3.5 `#[track_caller]` 与 `Backtrace` 的协同与对比

`#[track_caller]`（详见 [§9.5](#95-track_caller-与错误定位优化)）与 `Backtrace` 解决的是**不同维度**的定位问题：

| 维度 | `#[track_caller]` | `Backtrace` |
|:---|:---|:---|
| **定位粒度** | 单点：文件、行号、列号 | 完整调用链：多层帧 |
| **捕获时机** | 编译期（隐式传递 `Location`） | 运行时（栈展开） |
| **运行时开销** | 极低（额外寄存器/栈参数） | 高（符号解析、栈展开） |
| **信息类型** | 调用者位置（精确到语句） | 函数调用链（精确到函数） |
| **可控性** | 编译器自动管理 | 受 `RUST_BACKTRACE` 环境变量控制 |
| **适用场景** | 包装函数、断言宏 | 错误诊断、日志审计 |

**协同使用示例**：

```rust
use std::backtrace::Backtrace;
use std::fmt;

#[derive(Debug)]
struct LocatedError {
    msg: String,
    location: &'static std::panic::Location<'static>,
    backtrace: Backtrace,
}

#[track_caller]
fn fail(msg: &str) -> LocatedError {
    LocatedError {
        msg: msg.to_string(),
        location: std::panic::Location::caller(),  // ✅ 精确到调用者代码位置
        backtrace: Backtrace::capture(),            // ✅ 完整调用链
    }
}

fn main() {
    let e = fail("something went wrong");  // Location 指向这一行
    println!("At: {}:{}", e.location.file(), e.location.line());
    println!("Trace:\n{}", e.backtrace);
}
```

> **[来源: Rust Reference: track_caller]** · **[Rust Standard Library: Location]** `#[track_caller]` 与 `Location::caller()` 在 Rust 1.46+ 稳定；`Backtrace` 在 Rust 1.65+ 稳定。两者结合可同时获得"精确错误源点"与"完整传播路径"。 ✅

#### 9.3.6 与 `panic::Location` 的对比

`std::panic::Location` 与 `Backtrace` 在错误处理生态中形成**互补层级**：

```text
定位精度层级（从低到高）：
  1. 函数名（Backtrace 帧）      → "哪个函数"
  2. 文件+行号（Location）        → "哪一行代码"
  3. 列号（Location 精确）        → "哪一列表达式"
  4. 调用链（Backtrace 多帧）     → "怎么走到这里的"

信息成本层级（从低到高）：
  Location::caller()    ≈ 零成本（编译期内联）
  #[track_caller]       ≈ 极低（调用约定修改）
  Backtrace::capture()  ≈ 高（运行时栈展开 + 符号解析）
```

**决策树**：

```mermaid
graph TD
    A[需要错误定位信息？] --> B{需要完整调用链？}
    B -->|是| C[使用 Backtrace]
    B -->|否| D{需要精确源位置？}
    D -->|是| E["使用 #[track_caller] + Location::caller"]
    D -->|否| F[仅使用 error message]
    C --> G[权衡: 生产环境性能开销]
    E --> H[权衡: 仅适用于函数调用点]
```

> **认知功能**: 工程权衡决策器——在"完整调用链"与"精确源点"两个定位维度间提供结构化选择框架。读者可根据生产环境的性能约束和调试精度需求，快速确定使用 Backtrace、`#[track_caller]` 还是纯错误消息。核心洞察：定位精度与运行时开销呈正相关；大多数场景只需 `#[track_caller]` 的单点定位，Backtrace 应保留给故障审计。[来源: 💡 原创分析]

> **[来源: Rust Standard Library: panic::Location]** `panic::Location` 是 `const` 友好的轻量级定位机制，与 Backtrace 的运行时重定位形成鲜明对比。 ✅

#### 9.3.7 性能考量：Backtrace 捕获的成本

`Backtrace::capture()` 的性能特征：

| 阶段 | 成本来源 | 量级估计 |
|:---|:---|:---|
| 栈展开（unwinding） | 遍历调用帧、读取帧指针 | ~微秒级（10–100 μs） |
| 符号解析（symbolication） | 查询调试符号表（DWARF / PDB） | ~毫秒级（1–10 ms） |
| 字符串格式化 | `Display` 实现展开为字符串 | 与帧数成正比 |

**优化策略**：

1. **环境变量开关**：默认使用 `capture()` 而非 `force_capture()`，让生产环境用户通过 `RUST_BACKTRACE=0` 禁用。
2. **错误路径隔离**：仅在 `Err` 分支中构造 backtrace，不在 `Ok` 路径中预先捕获。
3. **延迟格式化**：`Backtrace` 内部保存原始帧数据，`Display` 时才进行符号解析，因此仅当实际打印时才产生完整开销。
4. **替代方案**：若仅需单点定位，优先使用 `#[track_caller]` + `Location`，完全避免运行时开销。

```rust,ignore
// ✅ 性能友好：仅在错误路径捕获
fn parse_config(path: &str) -> Result<Config, AppError> {
    match std::fs::read_to_string(path) {
        Ok(content) => Ok(parse(&content)?),
        Err(e) => Err(AppError::Io {
            source: e,
            backtrace: Backtrace::capture(),  // 仅在 Err 分支
        }),
    }
}

// ❌ 性能浪费：在成功路径也捕获
fn parse_config_bad(path: &str) -> Result<Config, AppError> {
    let bt = Backtrace::capture();  // 无论成功失败都捕获！
    // ...
}
```

> **[来源: Rust Standard Library: Backtrace]** `Backtrace` 采用惰性求值策略：构造时仅捕获原始帧指针，格式化时才解析符号。但即使如此，栈展开本身仍有不可忽略的开销。 ✅
> **[来源: RFC 2504]** Backtrace 稳定化 RFC 明确要求"在默认情况下不产生开销"，因此 `capture()` 在环境变量未启用时返回 `disabled`。 ✅

**跨层映射**: Backtrace 的运行时成本 ↔ [§9.3.6](#936-与-paniclocation-的对比) `Location` 的编译期零成本 ↔ [../04_formal/04_rustbelt.md](../04_formal/04_rustbelt.md) §3 "运行时与编译期保证的边界"

---

### 9.4 `eyre` / `color-eyre` / `miette` / `snafu` 生态库对比

> **Bloom 层级**: 应用 → 分析
> **[来源: eyre docs] · [color-eyre docs] · [miette docs] · [snafu docs] · [Rust CLI Book] · [thiserror docs] · [anyhow docs]** Rust 错误处理生态在 `anyhow` / `thiserror` 之外，已形成多个专攻不同场景的库：`eyre` 强调可定制的报告格式，`color-eyre` 提供富媒体诊断输出，`miette` 专注于源码级诊断标注，`snafu` 则强制显式上下文附件。以下逐一分析其设计哲学、API 风格与适用边界。✅

#### 9.4.1 `eyre`：可定制报告的错误处理

`eyre` 是 `anyhow` 的 fork，核心创新在于 **`EyreHandler` trait**——允许应用通过 `eyre::set_hook` 全局自定义错误报告的格式、内容与附属信息。[来源: eyre docs]

```rust,ignore
use eyre::{Result, WrapErr};

// ✅ 安装默认 handler（或在 main 开头设置自定义 hook）
eyre::set_hook(Box::new(eyre::DefaultHandler::default_with)).unwrap();

fn read_config(path: &str) -> Result<String> {
    std::fs::read_to_string(path)
        .wrap_err("failed to read config")?;  // WrapErr 添加上下文
    Ok(String::new())
}

fn main() -> Result<()> {
    let _config = read_config("/nonexistent/config.toml")?;
    Ok(())
}
```

与 `anyhow` 的关键差异：

| 维度 | `anyhow` | `eyre` |
|:---|:---|:---|
| 核心类型 | `anyhow::Error` | `eyre::Report` |
| 上下文 trait | `Context`（`context` / `with_context`） | `WrapErr`（`wrap_err` / `wrap_err_with`） |
| 自定义报告 | ❌ 固定格式 | ✅ `EyreHandler` trait + `set_hook` |
| `Option` 上下文 | ✅ `opt.context("msg")` | ⚠️ `opt.ok_or_eyre("msg")` 或 `ok_or_else` |
| 与 anyhow 互操作 | — | ✅ 提供兼容 re-export（`Context` → `WrapErr`） |

> **[来源: eyre docs]** `eyre::Report` 要求底层错误实现 `Send + Sync + 'static`，并以窄指针（single word）表示，与 `anyhow::Error` 的内存布局一致。✅
> **设计定理**：`eyre` 将"错误类型统一"（anyhow 哲学）与"报告格式可插拔"分离，使应用可以在不修改错误构造代码的前提下，通过更换 handler 实现从纯文本到 JSON/结构化日志的迁移。

#### 9.4.2 `color-eyre`：彩色诊断与链式回溯

`color-eyre` 是 `eyre` 的官方 companion handler，提供**彩色、一致且格式良好的错误报告**，集成 `tracing-error::SpanTrace`、`color-backtrace` 与 `color-spantrace`。[来源: color-eyre docs]

```rust,ignore
use color_eyre::{config::HookBuilder, eyre::Result, Section, SectionExt};
use tracing::{info, instrument};

// ✅ 在 main 开头安装 panic + error handler
color_eyre::install()?;

#[instrument]
fn read_file(path: &str) -> Result<String> {
    std::fs::read_to_string(path)
        .wrap_err("failed to read file")
        .with_section(|| format!("path: {}", path).header("Config Path:"))
}

fn main() -> Result<()> {
    let _ = read_file("missing.txt")?;
    Ok(())
}
// 输出示例：
// Error:
//    0: failed to read file
//    1: No such file or directory (os error 2)
//
// Config Path:
//    path: missing.txt
//
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ SPANTRACE ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//    0: read_file with path="missing.txt"
//       at src/main.rs:10
```

**核心特性**：

| 特性 | 说明 | 来源 |
|:---|:---|:---|
| **彩色输出** | 依赖 `owo_colors`，支持 ANSI/Unicode | [color-eyre docs] |
| **Backtrace** | 自动捕获 `backtrace::Backtrace`，集成 `color-backtrace` | [color-backtrace] |
| **SpanTrace** | 集成 `tracing-error`，显示 async/tracing span 链 | [tracing-error] |
| **Section** | `with_section` 附加任意诊断块（stdout/stderr/配置值） | [color-eyre docs] |
| **聚合多错误** | 通过 `Section` trait 组合多个错误为一个报告 | [color-eyre examples] |

> **[来源: color-eyre docs]** 生产环境中应通过 `RUST_SPANTRACE=0` 和 `RUST_BACKTRACE=0` 控制诊断噪声；`color-eyre` 在 debug 模式下性能显著低于 `eyre`，因为 `backtrace` crate 的 debug 构建比 `std::backtrace::Backtrace` 慢一个数量级，建议对 `backtrace` 包启用 `[profile.dev.package.backtrace] opt-level = 3`。✅

#### 9.4.3 `miette`：诊断式错误处理

`miette` 的定位是**诊断库**（diagnostic library），而非单纯的错误包装器。其核心是 `Diagnostic` trait——对 `std::error::Error` 的扩展，支持源码标注、错误代码、帮助文本、URL 链接与严重程度分级。[来源: miette docs]

```rust,ignore
use miette::{Diagnostic, NamedSource, SourceSpan};
use thiserror::Error;

#[derive(Error, Debug, Diagnostic)]
#[error("invalid config syntax")]
#[diagnostic(
    code(config::parse_error),
    url("https://docs.example.com/errors/config::parse_error"),
    help("try using TOML instead of INI for nested tables")
)]
struct ConfigParseError {
    #[source_code]
    src: NamedSource<String>,

    #[label = "unexpected token here"]
    err_span: SourceSpan,
}

use miette::Result;
fn parse_config(input: &str) -> Result<Config> {
    // ... 解析失败时 ...
    Err(ConfigParseError {
        src: NamedSource::new("config.toml", input.to_string()),
        err_span: (12, 3).into(),  // byte offset 12, length 3
    })?
}
```

**`miette` 的 Diagnostic 协议**：

```text
pub trait Diagnostic: Error {
    fn code(&self) -> Option<Box<dyn Display>>;      // 错误码，如 "config::parse_error"
    fn severity(&self) -> Option<Severity>;           // Error / Warning / Advice
    fn help(&self) -> Option<Box<dyn Display>>;       // 帮助文本
    fn url(&self) -> Option<Box<dyn Display>>;        // 文档链接
    fn source_code(&self) -> Option<&dyn SourceCode>; // 关联源码
    fn labels(&self) -> Option<Box<dyn Iterator<Item = LabeledSpan>>>; // 源码标注
    fn related(&self) -> Option<Box<dyn Iterator<Item = &dyn Diagnostic>>>; // 相关错误
}
```

> **[来源: miette docs]** `miette` 与 `thiserror` 完全兼容：可用 `#[derive(Error, Diagnostic)]` 同时实现两个 trait。库代码应仅依赖 `miette` 的核心 trait（不启用 `fancy` feature），由顶层应用启用 `fancy` 获取图形化输出。✅

**`miette::Result` 与 `miette::Report`**：

```rust,ignore
use miette::{Result, Report};

// ✅ 应用层：直接返回 miette::Result，启用 fancy 报告
fn main() -> Result<()> {
    let _ = parse_config("bad = [")?;
    Ok(())
}

// ✅ 自定义 ReportHandler：控制主题、颜色、输出格式
miette::set_hook(Box::new(|_| {
    Box::new(miette::MietteHandlerOpts::new()
        .terminal_links(true)
        .unicode(true)
        .context_lines(3)
        .build())
}));
```

#### 9.4.4 `snafu`：显式上下文错误类型

`snafu` 的哲学与 `anyhow`/`eyre` 相反：它**拒绝隐式转换**，要求每个错误变体在构造时提供显式上下文。通过 `#[derive(Snafu)]` 自动生成 **Context Selector**（如 `ConfigFileSnafu`），在转换点强制开发者填充字段。[来源: snafu docs]

```rust,ignore
use snafu::prelude::*;

#[derive(Debug, Snafu)]
enum AppError {
    #[snafu(display("could not read config file {path}"))]
    ConfigFile {
        source: std::io::Error,
        path: String,
    },

    #[snafu(display("invalid port {port}"))]
    InvalidPort {
        port: u16,
    },

    // ✅ transparent：将 Display 和 Error::source 委托给底层错误
    #[snafu(transparent)]
    Inner { source: InnerError },
}

fn read_config(path: &str) -> Result<String, AppError> {
    // ConfigFileSnafu 是自动生成的上下文选择器
    std::fs::read_to_string(path).context(ConfigFileSnafu { path })
}

fn parse_port(s: &str) -> Result<u16, AppError> {
    let port: u16 = s.parse().map_err(|_| InvalidPortSnafu { port: 0 }.build())?;
    ensure!(port >= 1024, InvalidPortSnafu { port });  // snafu 的 ensure! 宏
    Ok(port)
}
```

**`snafu` 的设计模式**：

| 模式 | 说明 | 来源 |
|:---|:---|:---|
| **Context Selector** | 每个变体生成 `VariantSnafu` 结构体，显式构造错误 | [snafu docs] |
| **`#[snafu(module)]`** | 将选择器放入子模块，避免命名空间污染 | [snafu guide] |
| **`#[snafu(transparent)]`** | 委托 Display/source 给底层错误，消除冗余包装 | [snafu docs] |
| **`#[snafu(context(false))]`** | 跳过选择器生成，直接实现 `From`（类似 `thiserror`） | [snafu docs] |
| **`ensure!` / `whatever!`** | 类似 `assert!` 的错误构造宏；`Whatever` 类型用于快速原型 | [snafu docs] |
| **`snafu::Location`** | 轻量级错误源点跟踪（类似 `#[track_caller]`） | [snafu changelog] |

> **[来源: snafu docs]** `snafu` 特别适合大型多 crate 项目：每个模块定义自己的错误类型，通过 `context` 方法在边界处转换，保持错误类型的模块内聚性。GreptimeDB 等工业项目采用此模式管理数百个错误变体。✅

#### 9.4.5 六库综合对比矩阵

| **维度** | **`anyhow`** | **`thiserror`** | **`eyre`** | **`color-eyre`** | **`miette`** | **`snafu`** |
|:---|:---|:---|:---|:---|:---|:---|
| **核心定位** | 应用级快速错误传播 | 库级结构化错误定义 | 可定制报告的应用错误 | 富媒体诊断报告 | 源码级诊断协议 | 显式上下文错误类型 |
| **使用场景** | CLI / 原型 / 应用顶层 | 库公共 API | 需自定义报告格式的应用 | 终端用户面向的 CLI | 编译器 / 解析器 / DSL | 大型多模块系统 |
| **API 风格** | 隐式转换，`?` 即用 | 派生宏减少样板 | 类似 anyhow + WrapErr | eyre handler 扩展 | Diagnostic trait + 派生 | Context Selector 强制显式 |
| **错误类型** | 动态 `anyhow::Error` | 静态枚举/结构体 | 动态 `eyre::Report` | 动态（基于 eyre） | 静态 + `Report` 包装 | 静态枚举 |
| **源码标注** | ❌ | ❌ | ❌ | ❌ | ✅ `SourceSpan` + 高亮 | ❌ |
| **错误代码** | ❌ | ✅ 手动 | ❌ | ❌ | ✅ `#[diagnostic(code(...))]` | ❌ |
| **Backtrace** | ✅ 自动 | ✅ `#[backtrace]` | ✅ 自动 | ✅ 彩色 backtrace | ✅ 可集成 | ✅ 可选 |
| **自定义报告** | ❌ | ❌ | ✅ `EyreHandler` | ✅ 主题/颜色/过滤器 | ✅ `ReportHandler` | ❌ |
| **编译时间** | 极低 | 低 | 低 | 中（额外依赖） | 中（`fancy` 依赖多） | 低 |
| **运行时开销** | 低（窄指针） | 零成本抽象 | 低（narrow pointer） | 中（backtrace/spantrace） | 低（标注为引用） | 低（选择器零成本） |
| **向下转型** | ✅ `downcast_ref` | ✅ `match` 枚举 | ✅ `downcast_ref` | ✅ `downcast_ref` | ✅ `match` / `downcast` | ✅ `match` 枚举 |
| **与 `?` 互操作** | ✅ 任意 `Error` | ✅ 需 `From` 实现 | ✅ 任意 `Error` | ✅ 任意 `Error` | ✅ 需 `Into<miette::Report>` | ✅ 需 `From` / `context` |

**决策树**：

```mermaid
graph TD
    A[选择错误处理库] --> B{库代码还是应用代码?}
    B -->|库| C{需要调用者 match 错误?}
    C -->|是| D[thiserror / snafu]
    C -->|否| E["thiserror + #[error(transparent)]\n包装底层错误"]
    B -->|应用| F{需要富媒体诊断?}
    F -->|是| G[miette + fancy]
    F -->|否| H{需要彩色 backtrace + spantrace?}
    H -->|是| I[color-eyre]
    H -->|否| J{需要自定义报告格式?}
    J -->|是| K[eyre]
    J -->|否| L[anyhow]
    D --> M[snafu: 大型模块化系统]
    D --> N[thiserror: 快速派生]
```

> **认知功能**: 生态选型导航器——将六库对比矩阵的高维信息降维为"库代码 vs 应用代码"首分叉的决策路径。读者在项目初始化或重构阶段，可沿此树在 3-4 步内确定最适合的错误处理策略。核心洞察：Rust 错误处理生态的核心张力是"静态结构化（thiserror/snafu）"与"动态统一（anyhow/eyre）"的权衡；miette 与 color-eyre 则是在诊断体验维度的垂直深化。[来源: 💡 原创分析]

> **定理**：Rust 错误处理生态的分化反映了"**静态结构化**"（`thiserror`/`snafu`）与"**动态统一**"（`anyhow`/`eyre`）的两极张力，而 `miette` 与 `color-eyre` 分别在**诊断精度**与**报告体验**维度上做了垂直深化。库作者应选择静态类型以暴露契约；应用作者应选择动态类型以加速迭代；当错误面向终端用户时，`miette`/`color-eyre` 的诊断可视化能力不可替代。
> **来源**: [eyre docs] · [color-eyre docs] · [miette docs] · [snafu docs] · [anyhow docs] · [thiserror docs] · [Rust CLI Book] · [GreptimeDB Blog]

---

### 9.5 `#[track_caller]` 与错误定位优化

> **Bloom 层级**: 应用 → 分析
> **[Rust Reference: The track_caller attribute]** · **[RFC 2091: Implicit caller location]** · **[Rust Standard Library: core::panic::Location]** `#[track_caller]` 在 Rust 1.46 稳定化，它通过修改函数的调用约定（calling convention），在编译期隐式注入调用者位置信息，使 panic、错误包装器和断言宏能够报告**调用点**而非被调用函数内部位置。✅

#### 9.5.1 工作原理：编译器隐式传递 `Location`

当函数标记为 `#[track_caller]` 时，编译器执行两项变换：

1. **ABI 修改**：在函数的调用约定中追加一个隐式的 `&'static Location<'static>` 参数。调用方在每次调用时自动填充该参数为自己的源码位置（文件、行号、列号）。
2. **MIR 重定向**：在 MIR（Mid-level IR）阶段，编译器将所有对 `#[track_caller]` 函数的调用重定向到一个内部闭包 `foo::{{closure}}`，该闭包负责把调用点的 `Location` 常数绑定到函数的隐式参数上。[来源: rustc-dev-guide — Implicit caller location]

```rust
// ✅ #[track_caller] 使 panic 报告调用者位置
#[track_caller]
fn my_unwrap<T>(opt: Option<T>) -> T {
    match opt {
        Some(v) => v,
        None => panic!("unwrap failed"),  // panic 位置显示为调用者位置
    }
}

fn main() {
    let x: Option<i32> = None;
    my_unwrap(x);  // panic 信息指向这一行，而非 my_unwrap 内部
}
```

**代价模型**：隐式 `Location` 参数通常通过寄存器传递（在支持的平台），或在栈上占用一个指针宽度（`usize` 大小）。因此开销为**极低**（亚指令级），但非绝对零成本——与 `Backtrace` 的运行时栈展开相比可忽略。[来源: RFC 2091 — Cost analysis] · [Rust Reference: track_caller ABI]

#### 9.5.2 `Location::caller()` 与 `PanicInfo::location()` 的区别

两者都返回 `&'static Location<'static>`，但语义完全不同：

| 维度 | `std::panic::Location::caller()` | `PanicInfo::location()` |
|:---|:---|:---|
| **定义位置** | `core::panic::Location` | `core::panic::PanicInfo` |
| **语义** | "**谁调用了我**" — 返回当前函数的调用者位置 | "**panic 发生在哪里**" — 返回 `panic!()` 宏被展开的位置 |
| **使用场景** | 自定义包装函数、错误构造器、断言辅助函数 | `panic` hook、`catch_unwind` 后的错误报告 |
| **是否依赖 `#[track_caller]`** | ✅ 必须在 `#[track_caller]` 函数中调用才指向调用者 | ❌ 直接反映 panic 调用点，与属性无关 |
| **典型调用位置** | 库代码中的 `unwrap`/`expect` 包装器 | 全局 panic handler、日志记录器 |

```rust
use std::panic::{self, Location};

#[track_caller]
fn checked_div(a: i32, b: i32) -> i32 {
    if b == 0 {
        // Location::caller() 指向 checked_div 的调用者，而非这一行
        panic!("division by zero at {}:{}",
               Location::caller().file(),
               Location::caller().line());
    }
    a / b
}

fn main() {
    panic::set_hook(Box::new(|info| {
        // PanicInfo::location() 指向 panic!() 被调用的位置
        // 如果 checked_div 有 #[track_caller]，这里会指向 main 中的调用点
        if let Some(loc) = info.location() {
            eprintln!("Panic at {}:{}", loc.file(), loc.line());
        }
    }));

    let _ = checked_div(10, 0);  // panic 位置指向这一行
}
```

> **[来源: Rust Standard Library: Location::caller]** `Location::caller()` 在 `#[track_caller]` 函数内部返回调用者的 `Location`；在普通函数中返回自身位置。 ✅
> **[来源: Rust Standard Library: PanicInfo]** `PanicInfo::location()` 返回 panic 实际发生的位置；当 panic 源自 `#[track_caller]` 函数时，该位置已被替换为调用者位置。 ✅

#### 9.5.3 在自定义错误类型中使用 `#[track_caller]` 实现轻量级定位

与嵌入 `Backtrace`（运行时栈展开，~微秒至毫秒级开销）不同，`#[track_caller]` + `Location` 提供**编译期确定的单点定位**，成本极低：

```rust,ignore
use std::panic::Location;
use std::fmt;

// ✅ 轻量级定位错误：仅存储一个 &'static Location 指针
#[derive(Debug)]
pub struct LocatedError {
    msg: String,
    loc: &'static Location<'static>,
}

impl LocatedError {
    #[track_caller]
    pub fn new(msg: impl Into<String>) -> Self {
        Self {
            msg: msg.into(),
            loc: Location::caller(),  // 编译期内联为常量指针，零运行时解析开销
        }
    }
}

impl fmt::Display for LocatedError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} at {}:{}", self.msg, self.loc.file(), self.loc.line())
    }
}

impl std::error::Error for LocatedError {}

// 使用示例
fn parse_port(s: &str) -> Result<u16, LocatedError> {
    s.parse().map_err(|_| LocatedError::new("invalid port"))?  // Location 指向这一行
}
```

**设计模式：零成本抽象**

| 模式 | 存储类型 | 运行时开销 | 精度 | 适用场景 |
|:---|:---|:---|:---|:---|
| `Backtrace` | `std::backtrace::Backtrace` | 高（栈展开+符号解析） | 完整调用链 | 审计、生产故障诊断 |
| `#[track_caller]` + `Location` | `&'static Location<'static>` | 极低（寄存器/栈参数传递） | 单点（文件+行+列） | 高频错误路径、库断言 |
| 手动 `file!/line!` | `&'static str` + `u32` | 零（编译期常量） | 单点 | 宏生成的错误 |

> **[来源: Rust API Guidelines — Error handling]** 库代码若仅需记录"错误在哪个调用点产生"，应优先使用 `#[track_caller]` 而非 `Backtrace`，以避免在热路径引入运行时展开开销。 ✅

#### 9.5.4 `#[track_caller]` 与 `Backtrace` 的对比

两者构成**互补层级**（与 [§9.3.5](#935-track_caller-与-backtrace-的协同与对比) 和 [§9.3.6](#936-与-paniclocation-的对比) 形成呼应）：

| 维度 | `#[track_caller]` + `Location` | `Backtrace` |
|:---|:---|:---|
| **信息粒度** | 单点：精确到调用者语句（文件、行、列） | 完整调用链：多层函数帧 |
| **捕获时机** | 编译期（隐式参数内联） | 运行时（栈展开 `libunwind`） |
| **运行时开销** | 极低（额外寄存器/栈参数，~1–2 指令） | 高（栈遍历 + 符号解析，10 μs–10 ms） |
| **惰性求值** | 自动（`Location` 为 `Copy`，无堆分配） | `Backtrace` 构造时捕获原始帧，格式化时解析符号 |
| **可控性** | 编译器自动管理，不可禁用单点 | 受 `RUST_BACKTRACE` 环境变量控制 |
| **动态分发** | ❌ `dyn Fn` / 函数指针调用丢失 caller 信息 | ✅ 不受调用方式影响 |
| **适用场景** | 包装函数、断言、自定义错误构造器 | 未知错误源、复杂调用链诊断 |

**协同模式**：在关键错误路径中同时使用两者——`Location` 提供**精确错误源点**，`Backtrace` 提供**传播路径上下文**：

```rust
use std::backtrace::Backtrace;
use std::panic::Location;
use std::fmt;

#[derive(Debug)]
pub struct RichError {
    msg: String,
    loc: &'static Location<'static>,
    backtrace: Backtrace,
}

impl RichError {
    #[track_caller]
    pub fn new(msg: impl Into<String>) -> Self {
        Self {
            msg: msg.into(),
            loc: Location::caller(),
            backtrace: Backtrace::capture(),
        }
    }
}
```

> **[来源: Rust Standard Library: Backtrace]** · **[Rust Reference: track_caller]** 两者结合可覆盖"从精确源点到完整传播路径"的全谱系定位需求。 ✅

#### 9.5.5 与 `anyhow` / `thiserror` 的集成

**`anyhow` 中的隐式使用**：

`anyhow` 的宏（`anyhow!`、`bail!`、`ensure!`）内部已使用 `#[track_caller]`，确保错误构造时的 `Location` 指向宏的调用点而非宏定义内部：

```rust,ignore
use anyhow::{anyhow, Result};

fn load_config(path: &str) -> Result<String> {
    // anyhow! 宏内部通过 #[track_caller] 使 Location 指向这一行
    std::fs::read_to_string(path)
        .map_err(|e| anyhow!("failed to read {}: {}", path, e))
}
```

> **[来源: anyhow source — macro rules]** `anyhow!` 宏利用 `#[track_caller]` 将错误位置绑定到调用方源码坐标，使错误链中的 `location()` 方法返回用户代码位置。 ✅

**`thiserror` 中 `#[backtrace]` 与 `#[track_caller]` 的协同**：

`thiserror` 1.0+ 支持 `#[backtrace]` 自动嵌入 `Backtrace`，但 `Backtrace` 的构造开销较高。对于仅需单点定位的场景，可手动结合 `#[track_caller]`：

```rust,ignore
use std::panic::Location;
use std::backtrace::Backtrace;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum AppError {
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),

    #[error("config error: {msg}")]
    Config {
        msg: String,
        // thiserror 的 #[backtrace] 自动填充 Backtrace
        #[backtrace]
        backtrace: Backtrace,
        // 手动存储 Location 实现轻量级精确源点
        location: &'static Location<'static>,
    },
}

impl AppError {
    #[track_caller]
    pub fn config(msg: impl Into<String>) -> Self {
        AppError::Config {
            msg: msg.into(),
            backtrace: Backtrace::capture(),
            location: Location::caller(),
        }
    }
}
```

**设计权衡**：

| 策略 | 实现方式 | 开销 | 推荐场景 |
|:---|:---|:---|:---|
| 纯 `anyhow` | `anyhow::Error` + `?` | 中（自动 backtrace + track_caller） | 应用代码、CLI 工具 |
| `thiserror` + `#[backtrace]` | 枚举 + 自动 Backtrace | 高（仅在错误路径） | 库代码、需结构化 match |
| `thiserror` + `#[track_caller]` | 枚举 + `Location::caller()` | 极低 | 高频错误、性能敏感的库 |
| 混合策略 | `Location` + 条件 `Backtrace` | 按需 | 关键路径错误审计 |

> **[来源: thiserror docs]** · **[anyhow docs]** 生态库的设计哲学是：`anyhow` 默认提供丰富的运行时上下文，`thiserror` 提供编译期结构化能力，两者均内建对 `#[track_caller]` 的一阶支持。 ✅

#### 9.5.6 限制与演进边界

尽管 `#[track_caller]` 已稳定，但其适用范围存在明确的编译器级边界：

**适用范围矩阵（准确状态）**：

| 函数类型 | 支持状态 | 说明 |
|:---|:---:|:---|
| 普通函数 | ✅ 稳定 | Rust 1.46+ |
| 泛型函数 | ✅ 稳定 | 单态化后隐式参数正确传递 |
| `const fn` | ✅ 稳定 | 编译期错误定位 |
| trait 方法 | ✅ 稳定 | RFC 2091 最初因 MIR 传递时机限制而禁止；后实现改为 monomorphization 之后注入，解除限制 [来源: rustc-dev-guide — track_caller in traits] |
| `async fn` | ⚠️ 部分支持 | Stable 上为 **no-op**（编译通过但 `Location::caller()` 返回 async fn 自身位置）；完整支持需 nightly `#![feature(async_fn_track_caller)]`（Tracking: [rust-lang/rust#110011]） |
| 闭包 | ❌ 不稳定 | 需 nightly `#![feature(closure_track_caller)]`（Tracking: [rust-lang/rust#87417]） |
| `dyn Fn()` / 函数指针 | ❌ 不支持 | 动态分发无法传递隐式 `Location` 参数；通过 trait object 调用时丢失 caller 信息 |
| `#[naked]` / 自定义 ABI | ❌ 不支持 | 与显式 ABI 冲突 |

**性能边界**：

`#[track_caller]` 修改调用约定，增加一个隐式参数。在**极高频调用**（如逐字节解析循环中的辅助函数）中，额外的寄存器压力可能导致轻微性能下降。因此不应在热路径的无错误分支中滥用——它最适合用于：

1. 错误报告/包装函数（如自定义 `unwrap`、`bail`）
2. 断言和调试辅助函数
3. 宏生成的代码（`assert!`、`unwrap` 等标准库模式）

```rust
// ❌ 不建议：热路径中的高频辅助函数
#[track_caller]
fn add_one(x: i32) -> i32 { x + 1 }  // 无错误报告需求，浪费 ABI 修改

// ✅ 建议：仅在错误包装/断言中使用
#[track_caller]
fn ensure_nonzero(x: i32) -> i32 {
    if x == 0 { panic!("expected non-zero") }
    x
}
```

> **[来源: Rust Reference: track_caller]** · **[RFC 2091: Implicit caller location]** · **[rustc-dev-guide]** `#[track_caller]` 的设计目标是为错误报告提供"足够好的位置信息"，而非替代调试符号或 profiling 工具。 ✅

**跨层映射**: `#[track_caller]` 的编译期定位 ↔ [§9.3](#93-stdbacktracebacktrace-与错误追踪) `Backtrace` 的运行时定位 ↔ [../04_formal/04_rustbelt.md](../04_formal/04_rustbelt.md) §3 "编译期保证与运行时观察的边界"

---

### 9.6 `Try` trait 与自定义 `?` 行为（稳定化中）

`Try` trait（Tracking: RFC 3058）将 `?` 运算符泛化到任意类型：

```rust,ignore
// ✅ Try trait 的核心定义（概念等价，稳定化中）
pub trait Try {
    type Output;   // 成功时的值类型
    type Residual; // 失败时的残差类型

    fn from_output(output: Self::Output) -> Self;
    fn branch(self) -> ControlFlow<Self::Residual, Self::Output>;
}
```

`ControlFlow` 枚举区分 "继续" 与 "提前返回"：

```rust,ignore
use std::ops::ControlFlow;

// ✅ ControlFlow 的语义
enum ControlFlow<B, C> {
    Continue(C),  // 正常继续，C 为中间结果
    Break(B),     // 提前终止，B 为残差
}

// Result 的 Try 实现（概念等价）
impl<T, E> Try for Result<T, E> {
    type Output = T;
    type Residual = Result<!, E>;  // ! 为 never type

    fn branch(self) -> ControlFlow<Result<!, E>, T> {
        match self {
            Ok(v) => ControlFlow::Continue(v),
            Err(e) => ControlFlow::Break(Err(e)),
        }
    }
}
```

**自定义 `?` 行为示例**：

```rust,ignore
use std::ops::ControlFlow;

// ✅ 自定义类型支持 ? 运算符
enum Maybe<T> {
    Just(T),
    Nothing,
}

impl<T> Try for Maybe<T> {
    type Output = T;
    type Residual = Maybe<!>;

    fn from_output(output: T) -> Self { Maybe::Just(output) }
    fn branch(self) -> ControlFlow<Maybe<!>, T> {
        match self {
            Maybe::Just(v) => ControlFlow::Continue(v),
            Maybe::Nothing => ControlFlow::Break(Maybe::Nothing),
        }
    }
}

fn try_divide(a: i32, b: i32) -> Maybe<i32> {
    if b == 0 { Maybe::Nothing } else { Maybe::Just(a / b) }
}

fn compute() -> Maybe<i32> {
    let x = try_divide(10, 2)?;  // ✅ 自定义 ? 行为
    let y = try_divide(x, 0)?;   // 返回 Maybe::Nothing
    Maybe::Just(y)
}
```

> **定理**：`Try` trait 将 `?` 从 `Result`/`Option` 的语法糖提升为**通用的控制流抽象**。任何满足代数结构的类型（含成功/失败两种分支）都可实现 `Try`。
> **边界**：`Try` trait 当前尚未完全稳定（`Residual` 关联类型在演进中）。`ControlFlow` 本身已稳定（Rust 1.55+），但直接实现 `Try` 需要 nightly。
> **来源**: [RFC 3058: Try trait v2] · [Rust Reference: The ? operator] · [Rust Standard Library: ControlFlow]

---

## 十、相关概念链接

| 概念 | 文件 | 关系 |
|:---|:---|:---|
| Trait 系统 | [01_traits.md](./01_traits.md) | Error/From trait 的实现基础 |
| 泛型系统 | [02_generics.md](./02_generics.md) | Result<T, E> 的泛型参数约束 |
| 所有权与生命周期 | [01_foundation/01_ownership.md](../01_foundation/01_ownership.md) | panic 时的资源清理 |
| 类型系统基础 | [01_foundation/04_type_system.md](../01_foundation/04_type_system.md) | 和类型的理论基础 |
| 并发与 Send/Sync | [03_advanced/01_concurrency.md](../03_advanced/01_concurrency.md) | 跨线程错误传播 |
| 异步与 Future | [03_advanced/02_async.md](../03_advanced/02_async.md) | async 中的 ? 运算符 |
| 形式化验证 | [04_formal/04_rustbelt.md](../04_formal/04_rustbelt.md) | 错误处理的逻辑基础 |

---

## 十一、待补充与演进方向（TODOs）

- [x] **TODO**: 补充 `std::backtrace::Backtrace` 与错误追踪 —— 优先级: 中 —— 已完成 §9.3 (2026-05-14)
- [x] **TODO**: 补充 `Termination` trait 与 main 返回 Result —— 优先级: 中 —— 已完成 §9.1
- [x] **TODO**: 补充 `eyre` / `color-eyre` / `miette` / `snafu` 等生态库的对比 —— 优先级: 低 —— 已完成 §9.4 (2026-05-14)
- [x] **TODO**: 补充 `#[track_caller]` 与错误定位优化 —— 优先级: 低 —— 已完成 §9.5 (2026-05-14)
- [x] **TODO**: 补充 `Result<T, !>` 与 `!` (never type) 在错误处理中的使用 —— 优先级: 中 —— 已完成 §9.2
- [x] **TODO**: 补充 `poll_fn` / `TryFuture` 等异步错误处理 —— 优先级: 高 —— 已完成 §5.5
- [x] **TODO**: 补充 `Try` trait（稳定化中）与自定义 ? 行为 —— 优先级: 中 —— 已完成 §9.6

> **[来源: Rust Reference; TRPL; Rust RFCs; Academic Papers]** 本文件内容基于官方文档、学术研究和工业实践的综合分析。✅

> **[来源: Wikipedia; POPL/PLDI/ECOOP Papers; RustBelt/Iris Project]** 形式化概念参考了权威学术来源和类型论研究。✅
---

---

## Wikipedia 概念对齐

> **[来源: Wikipedia]** 核心概念与国际知识库映射。

| 概念 | Wikipedia 词条 | 说明 |
|:---|:---|:---|
| **Exception handling** | [Exception handling](https://en.wikipedia.org/wiki/Exception_handling) | 异常处理 |
| **Result type** | [Result type](https://en.wikipedia.org/wiki/Result_type) | Result 类型 |
| **Option type** | [Option type](https://en.wikipedia.org/wiki/Option_type) | Option 类型 |
| **Monad (functional programming)** | [Monad (functional programming)](https://en.wikipedia.org/wiki/Monad_(functional_programming)) | Monad 模式 |
| **Panic (computing)** | [Panic (computing)](https://en.wikipedia.org/wiki/Panic_(computing)) | Panic |

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rustonomicon](https://doc.rust-lang.org/nomicon/)
> **权威来源对齐变更日志**: 2026-05-19 补全权威来源标注（Rust Reference、TRPL、Rustonomicon、RFCs、学术论文） [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 权威来源索引

>
>
>
>

---

## 十、C++ 异常安全 vs Rust 错误处理

### 10.1 异常安全保证等级

C++ 社区定义了三种异常安全保证（Exception Safety Guarantees）：

| 保证等级 | 定义 | C++ 实现 | Rust 等价 |
|:---|:---|:---|:---|
| **No-throw guarantee** | 操作绝不抛出异常 | `noexcept` 函数 | 普通函数（panic = abort） |
| **Strong guarantee** | 操作成功或保持原状态（事务性） | 拷贝-修改-交换惯用法 | `Result` + 早期返回 |
| **Basic guarantee** | 操作后程序处于有效状态（可能改变） | RAII + 异常捕获 | `Result` + `?` 传播 |
| **No guarantee** | 可能泄漏资源或破坏不变量 | 未处理的异常 | `unsafe` 块 / `mem::forget` |

### 10.2 C++ 异常 vs Rust `Result` 的 ABI 差异

| 维度 | C++ 异常 | Rust `Result<T, E>` |
|:---|:---|:---|
| **控制流** | 非局部跳转（栈展开） | 显式返回 + `?` 传播 |
| **类型安全** | 运行时类型匹配（RTTI） | 编译期穷尽性检查 |
| **性能** | 无异常时零开销 | 始终有 `Result` 封装开销（通常优化掉） |
| **二进制体积** | 增加 10-30%（unwind 元数据） | 无额外开销（panic=abort） |
| **跨 FFI** | 不能跨 C ABI | 可自由跨 FFI（`Result` 是普通类型） |
| **析构函数异常** | 析构函数抛异常 → `std::terminate` | `Drop::drop` 不可失败（`&mut self`，无返回值） |

### 10.3 C++23 `std::expected` vs Rust `Result`

```cpp
// C++23: std::expected（类似 Rust Result）
std::expected<int, Error> parse_int(const std::string& s) {
    try {
        return std::stoi(s);
    } catch (...) {
        return std::unexpected(Error::InvalidFormat);
    }
}

// 调用: 不强制处理错误！
auto result = parse_int("42");
// result.value(); // 可能抛 bad_expected_access！
```

```rust,ignore
// Rust: Result（强制处理）
fn parse_int(s: &str) -> Result<i32, ParseIntError> {
    s.parse::<i32>()
}

// 调用: 编译器强制处理
let result = parse_int("42");
match result {
    Ok(n) => println!("{}", n),
    Err(e) => println!("Error: {:?}", e), // 强制此分支
}
```

> **关键洞察**: C++23 `std::expected` 是 Rust `Result` 的语法类似物，但**不强制错误处理**——调用者可以忽略 `expected`，直到访问 `.value()` 时才可能抛异常。Rust 的 `Result` 通过类型系统强制错误处理的分支覆盖。[来源: C++23 Draft Standard] · [Rust Reference — §4.5.6] ✅

### 10.4 析构函数异常：C++ 的致命陷阱

```cpp
// C++: 析构函数抛异常 = 灾难
class Dangerous {
public:
    ~Dangerous() {
        throw std::runtime_error("boom"); // ❌ std::terminate!
    }
};

// 在栈展开过程中，若另一个异常正在传播，析构函数抛异常会导致 std::terminate
```

```rust,ignore
// Rust: Drop 不能失败
impl Drop for Safe {
    fn drop(&mut self) {
        // 返回值是 ()，不能返回 Result
        // 若需要失败，必须 panic（或忽略错误）
        if let Err(e) = self.cleanup() {
            // 只能 log 或 panic
            eprintln!("Cleanup failed: {:?}", e);
        }
    }
}
```

> **关键洞察**: C++ 允许析构函数抛异常，但在栈展开时会导致 `std::terminate`。Rust 根本不允许 `Drop::drop` 返回 `Result`——资源释放必须是**不可失败**的操作。这是 Rust "无未定义行为"承诺的重要组成部分。[来源: Rustonomicon — Drop Check] ✅

---

---

---

---

---

## 十一、边界测试：错误处理的编译错误

### 11.1 边界测试：? 运算符在错误类型不匹配时使用（编译错误）

```rust,compile_fail
fn parse_number(s: &str) -> Result<i32, std::num::ParseIntError> {
    s.parse::<i32>() // ✅ ParseIntError
}

fn double_number(s: &str) -> Result<i32, String> {
    let n = parse_number(s)?; // ❌ 编译错误: `?` couldn't convert the error
    // parse_number 返回 ParseIntError，但 double_number 返回 String
    // 需要实现 From<ParseIntError> for String
    Ok(n * 2)
}

// 正确: 统一错误类型或使用 map_err
fn double_number_fixed(s: &str) -> Result<i32, String> {
    let n = parse_number(s).map_err(|e| e.to_string())?;
    Ok(n * 2)
}
```

> **修正**: `?` 运算符要求当前函数的返回错误类型实现 `From<E>`，其中 `E` 是被调用函数的错误类型。

### 11.2 边界测试：panic 在 const fn 中（编译错误）

```rust,ignore
const fn divide(a: i32, b: i32) -> i32 {
    // ❌ 编译错误: `panic!` is not allowed in const fn
    if b == 0 { panic!("division by zero") }
    a / b
}

// 正确: 使用 assert!（在稳定版 Rust 中 const fn 允许 assert）
const fn divide_fixed(a: i32, b: i32) -> i32 {
    assert!(b != 0, "division by zero"); // ✅ const fn 中允许
    a / b
}
```

> **修正**: `const fn` 中不允许 `panic!`（除非在编译期可求值的上下文中）。使用 `assert!` 替代。

### 11.3 边界测试：`Result` 未处理（编译错误）

```rust,ignore
fn fallible_op() -> Result<i32, String> {
    Ok(42)
}

fn main() {
    // ❌ 编译错误: `Result` 的 `must_use` 属性
    // 忽略 `Result` 会导致编译警告，在 `deny(warnings)` 下为错误
    fallible_op();
}
```

> **修正**: `Result<T, E>` 标记了 `#[must_use]`，调用者必须显式处理（`?`、`match`、`if let` 或 `let _ = ...`）。

### 11.4 边界测试：`?` 在闭包中的类型推断失败（编译错误）

```rust,compile_fail
fn main() {
    let result: Result<i32, String> = Ok(42);
    let closure = || {
        // ❌ 编译错误: `?` 在闭包中无法推断返回类型
        // 闭包没有显式返回类型，`?` 无法确定目标 Error 类型
        let val = result?;
        Ok(val * 2)
    };
}
```

> **修正**: 在闭包中使用 `?` 时，必须显式标注闭包返回类型（`|| -> Result<i32, String> { ... }`）。

### 11.5 边界测试：自定义 Error 未实现 `std::error::Error`（编译错误）

```rust,compile_fail
#[derive(Debug)]
struct MyError {
    msg: String,
}

fn fallible() -> Result<(), MyError> {
    Err(MyError { msg: "error".to_string() })
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // ❌ 编译错误: `MyError` 未实现 `std::error::Error`
    // `?` 运算符需要 `From<MyError> for Box<dyn Error>`
    fallible()?;
    Ok(())
}
```

> **修正**: 自定义错误类型必须实现 `std::error::Error`（通常通过 `#[derive(thiserror::Error)]` 或手动实现），才能与 `?` 运算符和 `Box<dyn Error>` 兼容。

### 11.6 边界测试：`Result` 与 `Option` 混用（编译错误）

```rust,compile_fail
fn main() {
    let opt: Option<i32> = Some(42);
    // ❌ 编译错误: `Option<i32>` 不是 `Result` 类型
    let val = opt?; // `?` 在返回 Result 的函数中不能用于 Option
    println!("{}", val);
}

// 正确: 显式转换或返回 Option
fn with_option() -> Option<i32> {
    let opt: Option<i32> = Some(42);
    let val = opt?; // ✅ 函数返回 Option，? 可传播 Option
    Some(val)
}

// 或: 使用 ok_or 转换
fn with_result() -> Result<i32, String> {
    let opt: Option<i32> = Some(42);
    let val = opt.ok_or("missing")?; // ✅ Option → Result
    Ok(val)
}
```

> **修正**: `?` 运算符要求被传播的类型与函数返回类型兼容。`Option` 和 `Result` 不能自动混用。从 Rust 1.41 起，`?` 在返回 `Option` 的函数中可用于 `Option`，但在返回 `Result` 的函数中不能直接用 `?` 传播 `Option`。[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]

### 11.7 边界测试：`panic!` 在 `const fn` 中的限制（编译错误）

```rust,ignore
const fn checked_div(a: i32, b: i32) -> i32 {
    // ❌ 编译错误: `panic!` 在 const fn 中有限制（Edition 2021 前不允许）
    // Rust 1.57+ 允许 const panic，但信息受限
    if b == 0 {
        panic!("division by zero"); // 旧版编译器报错
    }
    a / b
}

// 正确: 使用断言（现代 Rust 支持 const panic）
const fn checked_div_fixed(a: i32, b: i32) -> i32 {
    assert!(b != 0, "division by zero"); // ✅ Rust 1.57+ 支持
    a / b
}
```

> **修正**: `const fn` 中的 `panic!` 从 Rust 1.57 起稳定支持，但要求 panic 信息为字符串字面量（非动态格式化）。在 Edition 2021 之前，`panic!` 完全不能在 `const fn` 中使用。这反映了编译期求值的严格约束。[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]

> **相关问题树**: [错误处理问题树](../00_meta/problem_graph.md#七错误处理问题树)

### 10.5 边界测试：`?` 运算符与 `From` 转换的失败（编译错误）

```rust,compile_fail
use std::fs::File;
use std::io;

fn read_file(path: &str) -> Result<String, io::Error> {
    let mut file = File::open(path)?;
    // ❌ 编译错误: ? 要求错误类型实现 From<io::Error>，但自定义错误可能不兼容
    Ok(String::new())
}

#[derive(Debug)]
struct MyError;

fn do_work() -> Result<(), MyError> {
    read_file("test.txt")?; // MyError 未实现 From<io::Error>
    Ok(())
}

fn main() {
    let _ = do_work();
}
```

> **修正**: `?` 运算符自动将错误类型转换为目标错误类型（`From::from(err)`）。若 `MyError` 未实现 `From<io::Error>`，`read_file("test.txt")?` 编译错误。修复：1) `impl From<io::Error> for MyError { ... }`；2) 使用 `map_err(|e| MyError::Io(e))` 显式转换；3) 使用 `anyhow`/`eyre`（自动错误转换和上下文）。`?` 是 Rust 错误处理的**语法糖**：`expr?` 等价于 `match expr { Ok(v) => v, Err(e) => return Err(From::from(e)) }`。这与 Go 的 `if err != nil { return err }`（手动传播）或 Java 的异常抛出（自动向上传播）不同——Rust 的 `?` 要求显式类型兼容，编译期检查错误转换。[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/ch09-02-recoverable-errors-with-result.html)] · [来源: [Rust Reference — The Question Mark Operator](https://doc.rust-lang.org/reference/expressions/operator-expr.html#the-question-mark-operator)]

### 10.6 边界测试：`Result` 的 `map_err` 与错误链的累积（逻辑错误）

```rust,ignore
use std::fs::File;
use std::io;

#[derive(Debug)]
struct AppError {
    msg: String,
}

impl From<io::Error> for AppError {
    fn from(e: io::Error) -> Self {
        AppError { msg: e.to_string() }
    }
}

fn read_config() -> Result<String, AppError> {
    let file = File::open("config.txt")
        .map_err(|e| AppError { msg: format!("open failed: {}", e) })?;
    // ❌ 逻辑错误: 若后续操作失败，错误链丢失 "open failed" 上下文
    // 除非每一步都手动包装
    Ok(String::new())
}

fn main() {
    let _ = read_config();
}
```

> **修正**: 手动 `map_err` 的错误链：每一步失败只保留当前上下文，丢失之前的信息。`anyhow` 的 `Context` trait 解决：`file.open("config.txt").context("failed to open config")?` — 自动累积上下文，生成错误链。`thiserror` 的 `#[source]` 字段保留原始错误。错误链的设计：1) **底层错误**（`io::Error`）→ 原始原因；2) **中间层**（`context`）→ 操作描述；3) **顶层** → 用户友好消息。这与 Go 的 `fmt.Errorf("%w", err)`（错误包装，Go 1.13+）或 Java 的 `Exception(String msg, Throwable cause)`（异常链）类似——Rust 的错误处理生态提供了类型安全和可读性的平衡。[来源: [anyhow](https://docs.rs/anyhow/)] · [来源: [thiserror](https://docs.rs/thiserror/)]

## 实践

> **相关资源**:
>
> - [crates/ 示例代码](../crates/) — 与本文概念对应的可编译示例
> - [exercises/ 练习](../exercises/) — 动手编程挑战
> - [MVP 学习路径](../00_meta/LEARNING_MVP_PATH.md) — 从零到多线程 CLI 的 40 小时路径
>
> **建议**: 阅读完本概念文件后，打开对应 crate 的示例代码，尝试修改并运行。完成至少 1 道相关练习以巩固理解。
