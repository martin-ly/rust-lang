> **内容分级**: [综述级]
>
> **本节关键术语**: 类型系统 (Type System) · 结构体 (Struct) · 枚举 (Enum) · 模式匹配 (Pattern Matching) · 泛型 (Generic) · Trait — [完整对照表](../00_meta/terminology_glossary.md)

# Type System Basics（类型系统基础）
>
> **EN**: Type System
> **Summary**: Rust's static type system combines scalar and compound types with algebraic data types, pattern matching, generics, and trait bounds. This chapter covers structs, enums, the match expression, type inference, and the path from everyday types toward formal type theory, giving learners the vocabulary needed for generic and trait-based design.
>
> **📎 交叉引用（Reference）**
>
> 本主题在 knowledge 中有系统化的知识索引：[类型系统（Type System）](04_type_system.md)
>
> **受众**: [初学者]
>
> **层级**: L1 基础概念
> **A/S/P 标记**: **S** — Structure（心智模型）
> **双维定位**: C×Und — 理解 ADT 的代数结构
> **前置概念**: [Ownership](01_ownership.md)
> **后置概念**:
>
> [Traits](../02_intermediate/01_traits.md) ·
> [Generics](../02_intermediate/02_generics.md) ·
> [Algebraic Data Types](../02_intermediate/01_traits.md)
>
> **主要来源**:
>
> [TRPL: Ch3](https://doc.rust-lang.org/book/ch03-00-common-programming-concepts.html) ·
> [TRPL: Ch6](https://doc.rust-lang.org/book/ch06-00-enums.html) ·
> [Wikipedia: Type system](https://en.wikipedia.org/wiki/Type_system) ·
> [Rust Reference: Types](https://doc.rust-lang.org/reference/types.html)
>

---

> ⚠️ **不稳定特性警告**: 本文件包含 `#![feature(...)]` 标注的代码示例，需要 **nightly 工具链** 编译。
>
> **使用方式**: `rustup run nightly rustc ...` 或 `cargo +nightly ...`
> **状态查询**: <https://doc.rust-lang.org/nightly/unstable-book/index.html>
> **注意**: 不稳定特性可能在后续版本中变更或移除，生产代码应避免依赖。

---
> **Bloom 层级**: 理解 → 分析 → 评价
**变更日志**:

- v1.0 (2026-05-12): 初始版本，完成权威定义、类型分类矩阵、ADT 分析、形式化视角、思维导图、示例反例
- v2.0 (2026-05-12): 深度重构，补充引理-定理-推论 ⟹ 链条、四层反命题分析、六步认知路径、章节过渡、相关概念链接

---

## 📑 目录

- [Type System Basics（类型系统基础）](#type-system-basics类型系统基础)
  - [📑 目录](#-目录)
  - [一、权威定义（Definition）](#一权威定义definition)
    - [1.1 Wikipedia 定义](#11-wikipedia-定义)
    - [1.2 TRPL 官方定义](#12-trpl-官方定义)
    - [1.3 形式化定义](#13-形式化定义)
  - [二、概念属性矩阵（Attribute Matrix）](#二概念属性矩阵attribute-matrix)
    - [2.1 类型分类矩阵](#21-类型分类矩阵)
    - [2.2 Rust 类型系统特征矩阵](#22-rust-类型系统特征矩阵)
  - [三、思维导图（Mind Map）](#三思维导图mind-map)
  - [四、定理推理链（Theorem Chain）](#四定理推理链theorem-chain)
    - [4.1 引理：ADT（枚举 + 结构体）⟹ 代数数据类型完备性](#41-引理adt枚举--结构体-代数数据类型完备性)
    - [4.2 引理：NPO 零成本空值优化 ⟹ Option\<\&T\> 的内存同构于 \&T](#42-引理npo-零成本空值优化--optiont-的内存同构于-t)
    - [4.3 定理：match 穷尽性检查 ⟹ 无未处理变体](#43-定理match-穷尽性检查--无未处理变体)
    - [4.4 定理：类型推断完备性 ⟹ Principal type property](#44-定理类型推断完备性--principal-type-property)
    - [4.5 定理：类型一致性（Progress + Preservation）⟹ 运行时无类型错误](#45-定理类型一致性progress--preservation-运行时无类型错误)
    - [4.6 推论：`Option<T>` ⟹ 空指针在类型层面消除](#46-推论optiont--空指针在类型层面消除)
    - [4.7 推论：Result\<T, E\> ⟹ 错误在类型层面强制处理](#47-推论resultt-e--错误在类型层面强制处理)
    - [4.8 推论：! (Never type) ⟹ 发散类型的逻辑完备性](#48-推论-never-type--发散类型的逻辑完备性)
    - [4.9 定理一致性矩阵](#49-定理一致性矩阵)
  - [五、示例与反例（Examples \& Counter-examples）](#五示例与反例examples--counter-examples)
    - [5.1 正确示例：ADT + Pattern Matching](#51-正确示例adt--pattern-matching)
    - [5.2 正确示例：Option 消除空值](#52-正确示例option-消除空值)
    - [5.3 反例：未覆盖的 match 分支（E0004）](#53-反例未覆盖的-match-分支e0004)
    - [5.4 反例：递归类型需要间接层（E0072）](#54-反例递归类型需要间接层e0072)
  - [六、反命题与边界分析（Inverse Propositions \& Boundary Analysis）](#六反命题与边界分析inverse-propositions--boundary-analysis)
    - [6.1 命题: "Rust 类型系统总是安全的"](#61-命题-rust-类型系统总是安全的)
    - [6.2 命题: "enum match 强制穷尽"](#62-命题-enum-match-强制穷尽)
    - [6.3 命题: "类型推断总是完备的"](#63-命题-类型推断总是完备的)
  - [七、边界极限测试代码（Boundary Stress Tests）](#七边界极限测试代码boundary-stress-tests)
    - [7.1 边界：unsafe 绕过类型系统后的行为](#71-边界unsafe-绕过类型系统后的行为)
    - [7.2 边界：#\[non\_exhaustive\] 对穷尽性的削弱](#72-边界non_exhaustive-对穷尽性的削弱)
    - [7.3 边界：NPO 与 Option\<\&T\> 的内存同构验证](#73-边界npo-与-optiont-的内存同构验证)
  - [八、认知路径（Cognitive Path）](#八认知路径cognitive-path)
    - [Step 1: 直觉困惑（Intuitive Confusion）](#step-1-直觉困惑intuitive-confusion)
    - [Step 2: 具体场景（Concrete Scenario）](#step-2-具体场景concrete-scenario)
    - [Step 3: 模式抽象（Pattern Abstraction）](#step-3-模式抽象pattern-abstraction)
    - [Step 4: 形式规则（Formal Rules）](#step-4-形式规则formal-rules)
    - [Step 5: 代码验证（Code Verification）](#step-5-代码验证code-verification)
    - [Step 6: 边界测试（Boundary Testing）](#step-6-边界测试boundary-testing)
  - [九、国际课程与论文对齐](#九国际课程与论文对齐)
  - [十、知识来源关系（Provenance）](#十知识来源关系provenance)
  - [十一、相关概念链接](#十一相关概念链接)
    - [补充章节：`impl Trait` 与 `dyn Trait` 的类型论差异](#补充章节impl-trait-与-dyn-trait-的类型论差异)
      - [存在类型 vs 全称类型](#存在类型-vs-全称类型)
      - [单态化 vs 动态分发：性能对比](#单态化-vs-动态分发性能对比)
      - [vtable 内存开销](#vtable-内存开销)
      - [选择决策树](#选择决策树)
    - [11.1 补充：`!` (Never type) 的形式化分析](#111-补充-never-type-的形式化分析)
      - [形式化定义](#形式化定义)
      - [控制流交互：`!` 作为统一分支类型](#控制流交互-作为统一分支类型)
      - [`Result<T, !>`：表示"不可能出错"](#resultt-表示不可能出错)
    - [11.2 补充：Zero-Sized Types (ZST) 与 `PhantomData`](#112-补充zero-sized-types-zst-与-phantomdata)
      - [ZST 的类型论意义](#zst-的类型论意义)
      - [`PhantomData<T>` 的工程用途](#phantomdatat-的工程用途)
      - [`PhantomData` 与 variance](#phantomdata-与-variance)
    - [11.3 Const Generics（常量泛型）](#113-const-generics常量泛型)
    - [11.4 Type Inference：HM 算法完整规则](#114-type-inferencehm-算法完整规则)
      - [11.4.1 HM 核心规则（Var、App、Abs、Let）](#1141-hm-核心规则varappabslet)
      - [11.4.2 统一（Unification）过程](#1142-统一unification过程)
      - [11.4.3 Rust 对 HM 算法的扩展](#1143-rust-对-hm-算法的扩展)
      - [11.4.4 `let` 多态性（let-polymorphism）与 Rust 的 `let` 绑定](#1144-let-多态性let-polymorphism与-rust-的-let-绑定)
      - [11.4.5 类型推断的边界（何时需要显式标注）](#1145-类型推断的边界何时需要显式标注)
      - [11.4.6 与 Haskell、ML 的类型推断对比](#1146-与-haskellml-的类型推断对比)
    - [11.5 Discriminant 与 Enum 内存布局](#115-discriminant-与-enum-内存布局)
      - [11.5.1 Discriminant 的基本概念与 `std::mem::discriminant`](#1151-discriminant-的基本概念与-stdmemdiscriminant)
      - [11.5.2 枚举的内存布局：Tagged Union 模型](#1152-枚举的内存布局tagged-union-模型)
      - [11.5.3 Niche Optimization 与 Null Pointer Optimization（NPO）](#1153-niche-optimization-与-null-pointer-optimizationnpo)
      - [11.5.4 `#[repr]` 对 Discriminant 与布局的影响](#1154-repr-对-discriminant-与布局的影响)
      - [11.5.5 `std::mem::Discriminant<T>` 与 `DiscriminantKind`](#1155-stdmemdiscriminantt-与-discriminantkind)
      - [11.5.6 `mem::size_of` 与 `mem::align_of` 的对比分析](#1156-memsize_of-与-memalign_of-的对比分析)
      - [11.5.7 边界极限测试：用 unsafe 窥探原始字节](#1157-边界极限测试用-unsafe-窥探原始字节)
    - [11.6 `union` 的类型安全边界](#116-union-的类型安全边界)
    - [11.7 名义类型与结构类型（Nominal vs Structural Typing）](#117-名义类型与结构类型nominal-vs-structural-typing)
      - [11.7.1 定义与形式化区分](#1171-定义与形式化区分)
      - [11.7.2 Rust 的类型二元性：名义与结构并存](#1172-rust-的类型二元性名义与结构并存)
      - [11.7.3 内部二元性：生命周期子类型化的结构本质](#1173-内部二元性生命周期子类型化的结构本质)
      - [11.7.4 幻影类型与新类型惯用法：名义类型的零成本抽象](#1174-幻影类型与新类型惯用法名义类型的零成本抽象)
      - [11.7.5 一致性规则与名义类型的深层绑定](#1175-一致性规则与名义类型的深层绑定)
      - [11.7.6 FFI 翻译中的类型范式冲突](#1176-ffi-翻译中的类型范式冲突)
      - [11.7.7 跨语言对比表](#1177-跨语言对比表)
      - [11.7.8 反命题与边界分析](#1178-反命题与边界分析)
        - [命题 1: "名义类型阻止了所有非预期的类型等价"](#命题-1-名义类型阻止了所有非预期的类型等价)
        - [命题 2: "结构类型系统可以解决孤儿规则（Orphan Rule）的问题"](#命题-2-结构类型系统可以解决孤儿规则orphan-rule的问题)
        - [命题 3: "新类型模式（Newtype）具有零运行时成本"](#命题-3-新类型模式newtype具有零运行时成本)
      - [11.7.9 认知路径：何时名义、何时结构](#1179-认知路径何时名义何时结构)
    - [11.7.10 与多级引用语义的交叉：引用的名义与结构行为](#11710-与多级引用语义的交叉引用的名义与结构行为)
  - [十二、待补充与演进方向（TODOs）](#十二待补充与演进方向todos)
  - [Wikipedia 概念对齐](#wikipedia-概念对齐)
  - [权威来源索引](#权威来源索引)
  - [十二、边界测试：类型系统的编译错误](#十二边界测试类型系统的编译错误)
    - [12.1 边界测试：类型不匹配（编译错误）](#121-边界测试类型不匹配编译错误)
    - [12.2 边界测试：泛型约束不满足（编译错误）](#122-边界测试泛型约束不满足编译错误)
    - [12.3 边界测试：match 非穷尽（编译错误）](#123-边界测试match-非穷尽编译错误)
    - [12.4 边界测试：impl Trait 在参数位置与返回位置的差异（编译错误）](#124-边界测试impl-trait-在参数位置与返回位置的差异编译错误)
    - [12.5 边界测试：生命周期省略规则失效（编译错误）](#125-边界测试生命周期省略规则失效编译错误)
    - [10.1 边界测试：类型不匹配的基础错误](#101-边界测试类型不匹配的基础错误)
  - [实践](#实践)
  - [逆向推理链（Backward Reasoning）](#逆向推理链backward-reasoning)
  - [参考来源](#参考来源)
  - [Never 类型元组强制（Rust 1.96）](#never-类型元组强制rust-196)
  - [嵌入式测验（Embedded Quiz）](#嵌入式测验embedded-quiz)
    - [测验 1：结构体与元组结构体（理解层）](#测验-1结构体与元组结构体理解层)
    - [测验 2：枚举与模式匹配穷尽性（应用层）](#测验-2枚举与模式匹配穷尽性应用层)
    - [测验 3：Option 与 unwrap（分析层）](#测验-3option-与-unwrap分析层)
    - [测验 4：类型推断边界（应用层）](#测验-4类型推断边界应用层)
    - [测验 5：类型转换与 as（分析层）](#测验-5类型转换与-as分析层)
  - [十二、补充：运算符重载（Operator Overloading）](#十二补充运算符重载operator-overloading)
    - [12.1 核心命题](#121-核心命题)
    - [12.2 C++ 自由运算符重载](#122-c-自由运算符重载)
    - [12.3 Rust 的 `std::ops` Trait 约束](#123-rust-的-stdops-trait-约束)
    - [12.4 常用 `std::ops` trait](#124-常用-stdops-trait)
    - [12.5 形式化视角](#125-形式化视角)
    - [12.6 边界与反例](#126-边界与反例)
    - [12.7 权威来源](#127-权威来源)

## 一、权威定义（Definition）

### 1.1 Wikipedia 定义

> **[Wikipedia: Type system](https://en.wikipedia.org/wiki/Type_system)** In computer programming, a type system is a logical system comprising a set of rules that assigns a property called a type to every term.
> A type system constrains the operations that can be performed on values of different types, preventing errors in programs.
> **[Wikipedia: Rust](https://en.wikipedia.org/wiki/Rust)** Rust has a strong, static type system with type inference.
> The type system supports algebraic data types, generics, and traits (type classes) but does not use garbage collection.

### 1.2 TRPL 官方定义

> **[TRPL Ch3.2](https://doc.rust-lang.org/book/ch03-02-data-types.html)** Rust is a statically typed language, which means that it must know the types of all variables at compile time.
> The compiler can usually infer what type we want to use based on the value and how we use it.
> **[TRPL Ch6](https://doc.rust-lang.org/book/ch06-00-enums.html)** Rust's enums are most similar to algebraic data types in functional languages, such as Haskell, F#, OCaml, and others. They allow you to define a type by enumerating its possible variants.

### 1.3 形式化定义

Rust 的类型系统（Type System）可以形式化为一个**带所有权（Ownership）约束的 Hindley-Milner 类型系统扩展**：

```text
类型推断规则（简化）:
─────────────────────────────────────────
  Γ ⊢ x : τ           （变量）
  Γ ⊢ c : τ           （常量）
  Γ, x:τ₁ ⊢ e : τ₂    （lambda 抽象）
  ─────────────────────
  Γ ⊢ λx.e : τ₁ → τ₂

Rust 扩展:
  Γ ⊢ e : τ₁    τ₁ implements Trait
  ──────────────────────────────────
  Γ ⊢ e : impl Trait

所有权约束:
  Γ; Σ ⊢ e : τ {Σ'}   （Σ = 堆状态，Σ' = 执行后的堆状态）
```

> **[来源: Pierce "Types and Programming Languages"]** Hindley-Milner 类型推断（Type Inference）算法及其扩展是 Rust 类型系统的基础。✅
> **[来源: COR: ETH Zurich]** Γ; Σ ⊢ e : τ {Σ'} 的所有权（Ownership）约束形式化表示 Rust 的堆状态演化。✅
> **过渡**: 权威定义从逻辑和官方来源确立了类型系统的语义——静态约束与代数数据类型。
> 而概念属性矩阵则将这些语义转化为可操作的分类——Rust 的类型类别、系统特征与内存布局的系统性对比。

---

## 二、概念属性矩阵（Attribute Matrix）

理解类型系统需要同时把握其静态分类能力与动态内存特征。
以下矩阵从类型分类、系统特征与内存布局三个维度建立完整的属性空间。

### 2.1 类型分类矩阵

| **类别** | **子类别** | **Rust 类型** | **内存位置** | **Copy?** | **Size** |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **标量** | 整数 | `i8`-`i128`, `u8`-`u128`, `isize`, `usize` | 栈 | ✅ | 固定 |
| | 浮点 | `f32`, `f64` | 栈 | ✅ | 固定 |
| | 布尔 | `bool` | 栈 | ✅ | 1 byte |
| | 字符 | `char` | 栈 | ✅ | 4 bytes |
| **复合** | 元组 | `(T, U, ...)` | 栈（若成员全栈） | 若成员全 Copy | 成员和 |
| | 数组 | `[T; N]` | 栈（通常） | 若 T: Copy | N × size(T) |
| | 结构体（Struct） | `struct` | 视成员而定 | 若成员全 Copy | 成员和 + padding |
| **引用（Reference）** | 共享 | `&T` | 栈（指针大小） | ✅ | ptr 大小 |
| | 可变 | `&mut T` | 栈（指针大小） | ✅ | ptr 大小 |
| | 裸指针 | `*const T`, `*mut T` | 栈 | ✅ | ptr 大小 |
| **ADT** | 枚举（Enum） | `enum` | 标签 + 最大变体 | 若变体全 Copy | tag + max variant |
| | Option | `Option<T>` | 同 `enum` | 若 T: Copy | 优化: 零成本空值 |
| | Result | `Result<T, E>` | 同 `enum` | 若 T,E: Copy | tag + max(T, E) |
| **函数** | 函数指针 | `fn(T) -> U` | 栈 | ✅ | ptr 大小 |
| | 闭包（Closures） | `impl Fn/FnMut/FnOnce` | 视捕获而定 | 通常 ❌ | 捕获变量和 |
| **动态** | Trait Object | `dyn Trait` | 栈（胖指针） | ❌ | 2 × ptr |
| | Slice | `[T]` | 无法直接拥有 | N/A | 动态 |

### 2.2 Rust 类型系统特征矩阵
>

| **特征** | **Rust** | **Haskell** | **C++** | **Java** | **Go** |
|:---|:---|:---|:---|:---|:---|
| **类型检查时机** | 静态 + 编译期 | 静态 | 静态 | 静态 + 运行时（Runtime）擦除 | 静态 |
| **类型推断（Type Inference）** | ✅ HM 扩展 | ✅ HM | ⚠️ `auto` | ❌（需显式） | ✅ 局部 |
| **代数数据类型** | ✅ `enum` | ✅ `data` | ⚠️ `variant` (C++17) | ❌ | ❌ |
| **空安全** | ✅ `Option<T>` | ✅ `Maybe` | ❌ `nullptr` | ⚠️ `Optional` | ❌ `nil` |
| **错误处理（Error Handling）类型** | ✅ `Result<T,E>` | ✅ `Either` | ❌ 异常 | ⚠️ 异常/Optional | ⚠️ 多返回值 |
| **泛型（Generics）** | ✅ 单态化（Monomorphization） | ✅ | ✅ 模板 | ⚠️ 类型擦除 | ✅ 无约束 |
| **Trait/类型类** | ✅ | ✅ 类型类 | ⚠️ Concepts (C++20) | ✅ 接口 | ✅ 接口 |
| **线性/所有权（Ownership）类型** | ✅ | ⚠️ 线性类型扩展 | ❌ | ❌ | ❌ |

---

> **过渡**: 属性矩阵展示了类型系统的静态分类能力，接下来需要建立概念之间的关联网络——类型如何与所有权（Ownership）、借用（Borrowing）、生命周期（Lifetimes）、Trait 等机制交织，形成完整的类型安全体系。

## 三、思维导图（Mind Map）

Rust 类型系统的全部知识可以组织为"标量—复合—ADT—引用（Reference）—特殊类型"五个维度，其中 ADT 是 Rust 区别于传统命令式语言的核心表达工具。

**Rust 类型层次图（Mermaid classDiagram）**:

```mermaid
classDiagram
    class Any {
        +size_of_val()
        +type_id()
    }
    class Sized {
        +编译期已知大小
    }
    class Copy {
        +按位复制语义
    }
    class Clone {
        +显式克隆接口
    }
    class Send {
        +可跨线程转移
    }
    class Sync {
        +可跨线程共享引用
    }
    class Default {
        +默认构造接口
    }
    class Display {
        +格式化输出接口
    }
    class Debug {
        +调试输出接口
    }

    Any <|-- Sized : 子类型约束
    Sized <|-- Copy : 子类型约束
    Sized <|-- Clone : 子类型约束
    Sized <|-- Send : auto trait
    Sized <|-- Sync : auto trait
    Clone <|-- Copy : Copy 继承 Clone

    note for Any "所有 Rust 类型的根\n（除 dyn Trait 外均实现）"
    note for Sized "99% 类型自动实现\n（dyn Trait / [T] 除外）"
    note for Copy "i32, bool, &T 等\n（堆分配类型除外）"
    note for Send "Arc<T>, Mutex<T> 等\n（Rc<T>, Cell<T> 除外）"
```

> **认知功能**:
> 此 classDiagram 建立了 Rust 核心 trait 的**能力层次结构**。
> 读者可直观理解 trait 之间的依赖关系：
> Copy 是 Clone 的「子集」（所有 Copy 类型都可 Clone，但反之不成立）；
> Sized 是 Send/Sync 的「前提」（auto trait 默认基于 Sized）。
> 图中的 note 标注了典型实现者和例外，帮助读者快速判断「我的类型是否自动实现了某 trait」。
> 建议将此图作为「trait 实现推断」的参考——看到 `T: Copy` 约束时，知道它也满足 `T: Clone + Sized`。
> 来源: [Rust Reference §11; TRPL §10; UML Class Diagram Standard](https://doc.rust-lang.org/reference/)
> [来源: [TRPL — Types](https://doc.rust-lang.org/book/title-page.html)]
> **类型分类层次（另一视角——数据导向）**:

```mermaid
graph TD
    A[类型系统] --> B[标量类型]
    A --> C[复合类型]
    A --> D[ADT]
    A --> E[引用类型]
    A --> F[特殊类型]

    B --> B1[整数 i/u]
    B --> B2[浮点 f]
    B --> B3[bool]
    B --> B4[char]

    C --> C1["数组 [T; N]"]
    C --> C2["元组 (A, B)"]
    C --> C3["切片 [T]"]

    D --> D1[struct]
    D --> D2[enum]
    D --> D3[union]

    E --> E1[&T]
    E --> E2[&mut T]
    E --> E3[*const T]
    E --> E4[*mut T]

    F --> F1["! Never"]
    F --> F2["() Unit"]
    F --> F3[dyn Trait]
    F --> F4[impl Trait]
    F --> F5[Fn/FnMut/FnOnce]
```

> **认知功能**:
> 此层次图从**数据构造**视角（而非 trait 能力视角）组织 Rust 全部类型。
> 读者面对一个不熟悉的类型时，可按图定位它属于哪一类——标量（简单值）、复合（多值组合）、ADT（代数构造）、引用（Reference）（内存别名）、特殊（类型系统元机制）。
> 关键认知：Rust 的类型系统不是平铺的清单，而是有层次的taxonomy（分类学）。
> enum/struct 对应「和类型/积类型」的代数结构，impl Trait/dyn Trait 对应「存在类型/动态分发」的类型论概念。
> 建议将此图与上方的 classDiagram 对照阅读，建立「数据构造 × 能力接口」的二维认知模型。
> 来源: [Rust Reference §3, §6; TRPL §3](https://doc.rust-lang.org/reference/)

```mermaid
graph TD
    A[Type System 类型系统] --> B[标量类型]
    A --> C[复合类型]
    A --> D[代数数据类型 ADT]
    A --> E[引用类型]
    A --> F[特殊类型]

    B --> B1[整数: i8..i128, u8..u128, isize, usize]
    B --> B2[浮点: f32, f64]
    B --> B3[bool, char]

    C --> C1["元组: (T, U)"]
    C --> C2["数组: [T; N]"]
    C --> C3[结构体: struct]
    C --> C4["切片: [T]"]

    D --> D1[枚举: enum = Sum Type]
    D --> D2[Option<T> = 1 + T]
    D --> D3[Result<T, E> = T + E]
    D --> D4["Never: ! = 空类型"]

    E --> E1[&T: 共享引用]
    E --> E2[&mut T: 可变引用]
    E --> E3[*const/*mut T: 裸指针]

    F --> F1[impl Trait: 存在类型]
    F --> F2[dyn Trait: 动态分发]
    F --> F3["!: Never 类型"]
    F --> F4[元类型: type/const 泛型]
```

> **认知功能**: 此图是前两张类型层次图的**教学强化版**，在 D 分支中显式标注了代数类型论对应（enum = Sum Type、Option = 1 + T、Result = T + E、! = ⊥）。
> 关键认知：Rust 的 enum 不只是「带标签的 union」，而是**和类型（Sum Type）**——它是类型论中「要么 A 要么 B」的构造子。
> `Option<T>` = 1 + T 的标注揭示了 None 对应单元类型 1（大小为 1 的集合），Some(T) 对应 T。
> 这种代数视角是理解 match 穷尽性、NPO 优化、以及 Rust 类型系统表达力的关键。 [来源: 💡 原创分析]

---

> **过渡**: 思维导图呈现了类型系统的静态知识结构，而定理推理链则回答"为什么类型检查能保证安全"——通过代数类型、模式匹配（Pattern Matching）穷尽性、类型一致性（Coherence）的层层演绎，建立类型系统的形式化保证。

## 四、定理推理链（Theorem Chain）

Rust 类型系统的安全性保障同样由引理、定理与推论构成严密的推理链条。
以下链条从代数结构的完备性出发，一直延伸到运行时安全保证。

### 4.1 引理：ADT（枚举 + 结构体）⟹ 代数数据类型完备性

```text
引理 L1: ADT 代数完备性
  前提: struct 对应积类型（Product Type / ×）
  前提: enum  对应余积类型（Sum Type / Coproduct / +）
    ↓
  结论: Rust ADT 在范畴论意义上封闭于积与余积
    ↓
  ⟹ 任何可计算数据结构都可由 struct + enum 组合表达
```

> **[来源: Category Theory for Programmers]** enum 对应余积（Coproduct / Sum Type），struct 对应积（Product Type）。✅
> **[来源: Pierce "Types and Programming Languages"]** 积与余积的组合构成代数数据类型的完备基。✅

### 4.2 引理：NPO 零成本空值优化 ⟹ Option<&T> 的内存同构于 &T
>

```text
引理 L2: Null Pointer Optimization
  前提: Rust 引用 `&T` 永不为 null（内存安全公理）
  前提: `Option<&T>` 是余积类型 `1 + &T`
    ↓
  结论: 编译器可用 `&T` 的 0x0 编码 `None`，消除 tag
    ↓
  ⟹ Option<&T> 的内存布局与 &T 完全相同，空值检查零成本
```

> **[来源: [Rust Reference: Enums](https://doc.rust-lang.org/reference/items/enumerations.html)]** NPO 利用引用永不为 null 的特性将 Option<&T> 压缩为单个指针。✅

### 4.3 定理：match 穷尽性检查 ⟹ 无未处理变体
>

```text
定理 T1: Match 穷尽性
  前提: enum 定义封闭集合（所有变体编译期已知）
  前提: 引理 L1（ADT 完备性确保所有数据结构可枚举）
    ↓
  结论: 编译器验证 match 覆盖 enum 的所有变体
    ↓
  ⟹ Safe Rust 中对 enum 的 match 不会遗漏 case，无需默认分支即可保证穷尽性
```

> **[来源: [Rust Reference: Patterns](https://doc.rust-lang.org/reference/patterns.html)]** match 穷尽性检查由编译器验证，确保 enum 的所有变体都被处理。✅
> **来源: [TRPL Ch6.1](https://doc.rust-lang.org/book/title-page.html)** `Option<T>` 强制处理 None 情况，消除空指针错误。✅

### 4.4 定理：类型推断完备性 ⟹ Principal type property

```text
定理 T2: 类型推断完备性
  前提: Rust 类型推断基于 Hindley-Milner 算法的扩展
  前提: 无显式泛型约束的表达式
    ↓
  结论: 存在唯一的最一般类型（Principal Type）可被编译器推断
    ↓
  ⟹ 程序员在绝大多数局部场景无需显式标注类型，同时保持静态检查的严格性
```

> **[来源: Pierce "Types and Programming Languages"]** Hindley-Milner 类型推断对无显式约束的表达式是完备的（Principal type property）。✅

### 4.5 定理：类型一致性（Progress + Preservation）⟹ 运行时无类型错误

```text
定理 T3: 类型安全定理
  前提: 程序通过 Rust 类型检查（含 borrow check）
  前提: 不使用 unsafe 绕过类型系统
    ↓
  结论: Progress（良类型程序不会卡住）+ Preservation（归约保持类型）
    ↓
  ⟹ Safe Rust 运行时不会发生类型不匹配导致的未定义行为
```

> **[来源: Wright & Felleisen 1994]** 类型安全定理（Progress + Preservation）是类型系统的标准元定理。✅

### 4.6 推论：`Option<T>` ⟹ 空指针在类型层面消除

```text
推论 C1: 空指针消除
  前提: 定理 T1（match 穷尽性）
  前提: 引理 L2（NPO 零成本）
    ↓
  结论: `T` 与 `None` 被强制分离为不同变体，必须显式处理
    ↓
  ⟹ Tony Hoare 的"十亿美元错误"（null pointer）在 Rust 类型层面被消除，且无需运行时开销
```

> **来源: [Wikipedia: Null pointer](https://en.wikipedia.org/wiki/Null_pointer)** Tony Hoare 将 null 引入 ALGOL W 称为"十亿美元错误"。✅

### 4.7 推论：Result<T, E> ⟹ 错误在类型层面强制处理

```text
推论 C2: 错误强制处理
  前提: 定理 T1（match 穷尽性）
  前提: 引理 L1（ADT 完备性）
    ↓
  结论: `Ok(T)` 与 `Err(E)` 作为 enum 变体，match 必须同时处理
    ↓
  ⟹ 异常隐藏控制流的问题被消除，所有错误路径在类型上显式且不可遗漏
```

> **来源: TRPL Ch9** Result<T, E> 强制显式错误处理（Error Handling），避免异常带来的隐藏控制流。✅

### 4.8 推论：! (Never type) ⟹ 发散类型的逻辑完备性

```text
推论 C3: Never 类型完备性
  前提: 引理 L1（ADT 完备性）
  前提: 类型系统中需要表达"永不返回"的函数语义
    ↓
  结论: `!` 作为空类型（Bottom Type），可与任何类型统一
    ↓
  ⟹ `panic!()`、`loop {}`、`exit()` 等发散函数可安全参与任意控制流，类型系统逻辑闭合
```

> **[来源: [Rust Reference: Never type](https://doc.rust-lang.org/reference/types.html#never-type)(https://doc.rust-lang.org/reference/types.html#never-type)]** `!` 是 Rust 的空类型，可与任意类型统一（coerce）。✅

### 4.9 定理一致性矩阵

| **定理/引理/推论** | **前提** | **结论** | **依赖的 L4 公理** | **被哪些定理依赖** | **失效条件** | **典型错误码** |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| L1: ADT 代数完备性 | struct = 积, enum = 余积 | 所有数据结构可组合表达 | 范畴论（积/余积） | T1, C2, C3 | 无法表达开放变体（需 dyn Trait） | — |
| L2: NPO 零成本优化 | `&T` 永不为 null | Option<&T> ≅ &T 内存布局 | 内存安全（Memory Safety）公理 | C1 | 非引用类型无 NPO | — |
| T1: Match 穷尽性 | enum 封闭 + match 全覆盖 | 无遗漏 case | 代数类型论（和类型） | C1, C2 | `#[non_exhaustive]` 跨 crate | E0004 |
| T2: 类型推断完备性 | 无显式泛型（Generics）约束 | 唯一最一般类型可推断 | HM 类型推断 | — | 多态场景需标注 | E0282 |
| T3: 类型安全定理 | 类型检查通过 + 无 unsafe | Progress + Preservation | 类型论元定理 | — | `std::mem::transmute` | — |
| C1: 空指针消除 | T1 + L2 | null 在类型层面不可达 | 和类型 + NPO | — | `unsafe` 构造 null &T | — |
| C2: 错误强制处理 | T1 + L1 | 错误路径不可遗漏 | 和类型穷尽性 | — | `unwrap()` 运行时（Runtime） panic | — |
| C3: Never 类型完备性 | L1 | 发散函数参与任意控制流 | 空类型 (⊥) | — | 不稳定特性需 nightly | — |

> **一致性检查**: L1 ⟹ L2 ⟹ T1/T2/T3 ⟹ C1/C2/C3，形成**从代数结构到运行时安全**的递进链。T1 是连接 ADT 结构与程序正确性的枢纽定理。
> **跨层映射**: 本文件定理 ↔ [`00_meta/inter_layer_map.md`](../00_meta/inter_layer_map.md) §4.2 "类型系统一致性"

---

## 五、示例与反例（Examples & Counter-examples）

定理链条的正确性需要通过代码实例来验证。以下示例覆盖正确用法、编译期反例与运行时边界。

### 5.1 正确示例：ADT + Pattern Matching

```rust
// ✅ 正确: enum 表示可能的状态，match 穷尽处理
enum Message {
    Quit,
    Move { x: i32, y: i32 },
    Write(String),
    ChangeColor(i32, i32, i32),
}

fn process(msg: Message) {
    match msg {
        Message::Quit => println!("Quit"),
        Message::Move { x, y } => println!("Move to ({}, {})", x, y),
        Message::Write(text) => println!("Text: {}", text),
        Message::ChangeColor(r, g, b) => println!("RGB({}, {}, {})", r, g, b),
    } // ✅ 编译器验证：所有变体都被处理
}
```

### 5.2 正确示例：Option 消除空值

```rust
// ✅ 正确: Option 强制处理空值情况
fn divide(numerator: f64, denominator: f64) -> Option<f64> {
    if denominator == 0.0 {
        None
    } else {
        Some(numerator / denominator)
    }
}

fn main() {
    let result = divide(10.0, 2.0);
    match result {
        Some(x) => println!("Result: {}", x),
        None => println!("Cannot divide by zero"),
    }
    // 不能直接使用 result + 1（Option<f64> 不实现 Add）
    // 必须先 unwrap 或 match
}
```

### 5.3 反例：未覆盖的 match 分支（E0004）

```rust,compile_fail
// ❌ 反例: non-exhaustive pattern
enum Color {
    Red,
    Green,
    Blue,
}

fn print_color(c: Color) {
    match c {
        Color::Red => println!("Red"),
        Color::Green => println!("Green"),
        // E0004: non-exhaustive patterns: `Blue` not covered
    }
}
```

**错误分析**：

- `Color` 是封闭 enum，编译器已知三个变体
- match 仅覆盖两个变体，违反定理 T1
- 编译器在编译期拦截，而非运行时抛出异常

**修正方案**：

```rust,ignore
// ✅ 修正: 覆盖所有变体或使用通配符
fn print_color(c: Color) {
    match c {
        Color::Red => println!("Red"),
        Color::Green => println!("Green"),
        Color::Blue => println!("Blue"),
    }
}

// 或
fn print_color(c: Color) {
    match c {
        Color::Red => println!("Red"),
        Color::Green => println!("Green"),
        _ => println!("Other"),  // ✅ 通配符覆盖剩余变体
    }
}
```

### 5.4 反例：递归类型需要间接层（E0072）

```rust,compile_fail
// ❌ 反例: 递归类型直接自包含
enum List<T> {
    Cons(T, List<T>),  // E0072: recursive type has infinite size
    Nil,
}
```

**错误分析**：

- `List<T>` 的大小 = `tag + max(size(T), size(List<T>))`
- `size(List<T>)` 出现在等式右侧，导致无限递归
- 这是 ADT 代数完备性在内存布局层面的边界：无限类型需要递归锚点

**修正方案**：

```rust
// ✅ 修正: 使用 Box 提供间接层（指针大小固定，终止递归）
enum List<T> {
    Cons(T, Box<List<T>>),
    Nil,
}
```

---

## 六、反命题与边界分析（Inverse Propositions & Boundary Analysis）

任何定理都有成立边界。以下通过决策树系统分析三个核心命题的成立条件与反例分布。

### 6.1 命题: "Rust 类型系统总是安全的"

```mermaid
graph TD
    P["命题: Rust 类型系统总是安全的"] --> Q1{"使用 unsafe 块?"}
    Q1 -->|是| F1["反例: transmute 将位模式 reinterpret<br/>→ 任意类型错误（编译期层绕过）"]
    Q1 -->|否| Q2{"使用 dyn Any downcast?"}
    Q2 -->|是| F2["反例: downcast_ref 可能返回 None<br/>→ 运行时类型不匹配（安全但需处理）"]
    Q2 -->|否| Q3{"使用 union?"}
    Q3 -->|是| F3["反例: union 字段访问需 unsafe<br/>→ 可能读取错误变体（语义层）"]
    Q3 -->|否| Q4{"使用 std::mem::forget 或循环引用?"}
    Q4 -->|是| F4["反例: 内存泄漏或逻辑错误<br/>→ 非类型错误，但属工程层安全边界"]
    Q4 -->|否| T["定理成立: Safe Rust 无未定义行为<br/>✅ 类型安全定理（T3）保证"]

    style F1 fill:#f66
    style F2 fill:#f96
    style F3 fill:#f66
    style F4 fill:#f96
    style T fill:#6f6
```

> **认知功能**:
> 此图按**绕过类型系统的手段**分类安全边界，颜色编码了危险程度：深红色（unsafe/union，可导致 UB）vs 橙色（downcast/forget，安全但需处理）。
> 关键认知：Safe Rust 的「安全」不是「不会出错」，而是「不会出现未定义行为」。
> dyn Any::downcast_ref 返回 None 是「安全地失败」，std::mem::forget 导致泄漏是「安全但不理想」。
> 这帮助读者建立 Rust 安全模型的精确理解：类型系统保证的是 UB 不可达，而非逻辑正确性。 [来源: 💡 原创分析]

**四层分类**：

| **层次** | **反例** | **性质** |
|:---|:---|:---|
| 编译期 | `unsafe` 块、`transmute`、`union` | 显式绕过类型系统 |
| 运行时（Runtime） | `dyn Any::downcast_ref` 返回 `None` | 安全，但逻辑可能错误 |
| 语义 | `union` 字段误读、类型双关 | 需 unsafe，编译器不保证 |
| 工程 | `std::mem::forget`、Rc 循环引用 | 内存泄漏，非 UB，但属安全边界 |

### 6.2 命题: "enum match 强制穷尽"

```mermaid
graph TD
    P["命题: enum match 强制穷尽"] --> Q1{"标准 enum（同 crate）?"}
    Q1 -->|是| T1["定理成立: 编译器强制全覆盖<br/>✅ 遗漏则 E0004"]
    Q1 -->|否| Q2{"标记 #[non_exhaustive]?"}
    Q2 -->|是| F1["反例: 跨 crate 兼容性要求 _ =><br/>→ 编译器不强制穷尽（工程层设计）"]
    Q2 -->|否| Q3{"使用 if let / while let?"}
    Q3 -->|是| F2["反例: 语法糖不检查穷尽<br/>→ 可能遗漏变体（工程层）"]
    Q3 -->|否| Q4{"使用 unsafe + 裸指针读 tag?"}
    Q4 -->|是| F3["反例: 直接绕过模式匹配<br/>→ 未定义行为（编译期层绕过）"]
    Q4 -->|否| T2["定理成立: match 穷尽性保证<br/>✅ 类型论保证（T1）"]

    style T1 fill:#6f6
    style F1 fill:#f96
    style F2 fill:#f96
    style F3 fill:#f66
    style T2 fill:#6f6
```

> **认知功能**:
> 此图展示了 match 穷尽性的**完整保证谱系**。
> 两个绿色节点覆盖了「编译器强制检查穷尽」的场景（同 crate 的标准 enum、跨 crate 无 non_exhaustive 且用 match），三个反例展示了「看似可穷尽但实际不检查」的陷阱。
> 关键认知：if let 是 match 的语法糖，但故意不检查穷尽——这是设计上的「便利与安全的权衡」；#[non_exhaustive] 是 API 演化的兼容性设计，而非安全漏洞。
> 读者应建立「match = 强制穷尽，if let = 选择性处理」的精确区分。 [来源: 💡 原创分析]

**核心洞察**：`#[non_exhaustive]` 和 `if let` 是编译器故意提供的"逃生舱"，它们在工程层面削弱了穷尽性，但仍在 Safe Rust 的边界内。

### 6.3 命题: "类型推断总是完备的"

```mermaid
graph TD
    P["命题: 类型推断总是完备的"] --> Q1{"纯局部表达式（let x = vec![1,2,3]）?"}
    Q1 -->|是| T1["定理成立: HM 推断完备<br/>✅ 自动推导 Vec<i32>"]
    Q1 -->|否| Q2{"函数签名（公共 API）?"}
    Q2 -->|是| F1["反例: 必须显式标注类型<br/>→ 文档与接口契约需求（工程层）"]
    Q2 -->|否| Q3{"泛型约束场景（collect）?"}
    Q3 -->|是| F2["反例: collect::<Vec<_>>() 需标注目标类型<br/>→ 多态歧义（编译期层）"]
    Q3 -->|否| Q4{"数值字面量歧义（42 vs 42.0）?"}
    Q4 -->|是| F3["反例: 需后缀或上下文确定 i32/f64<br/>→ 文字多义（编译期层）"]
    Q4 -->|否| T2["定理成立: 类型推断成功<br/>✅ HM Principal Type"]

    style T1 fill:#6f6
    style F1 fill:#f96
    style F2 fill:#f96
    style F3 fill:#f96
    style T2 fill:#6f6
```

> **认知功能**:
> 此图将类型推断的「边界情况」系统化。
> 关键认知：HM 推断在「纯局部、无歧义」场景是完备的（两个绿色节点），但在三种场景下需要人工干预——公共 API（工程契约，非推断不能）、泛型（Generics）多态（信息不足，需显式消歧）、字面量歧义（语法层面的多重解释）。
> 这帮助读者理解「为什么有时编译器要求我写类型标注」——不是因为推断算法弱，而是因为**信息论上的不可能**（多解）或**工程上的需求**（文档契约）。 [来源: 💡 原创分析]

---

## 七、边界极限测试代码（Boundary Stress Tests）

边界测试是验证定理在极限场景下是否仍然成立的关键手段。以下三个测试分别挑战类型一致性、穷尽性边界与 NPO 优化。

### 7.1 边界：unsafe 绕过类型系统后的行为

```rust
// 测试: transmute 破坏类型安全（unsafe 边界）
fn type_safety_boundary() {
    let i: u32 = 0x0041_0000;  // 'A' 的 ASCII 码放在高 16 位
    let f: f32 = unsafe { std::mem::transmute(i) };
    println!("transmute u32 -> f32: {}", f);  // 非预期数值，非 panic

    // 更危险的: 将整数转引用（仅在测试环境中展示概念）
    // let ptr: &u32 = unsafe { std::mem::transmute(0x1usize) };
    // 解引用 ptr → 立即段错误 / 未定义行为
}

fn main() {
    type_safety_boundary();
}
```

### 7.2 边界：#[non_exhaustive] 对穷尽性的削弱

```rust
// 测试: 跨 crate 的 non_exhaustive enum 需要通配符
mod external {
    #[non_exhaustive]
    pub enum Status {
        Ok,
        Err,
    }
}

fn handle_status(s: external::Status) {
    match s {
        external::Status::Ok => println!("ok"),
        external::Status::Err => println!("err"),
        // 若省略 _ =>，在当前 crate 编译通过（因为只有两个变体）
        // 但若 external crate 新增变体，当前 crate 不会因此编译失败
        // 这正是 #[non_exhaustive] 的设计意图
        _ => println!("unknown"),
    }
}

fn main() {
    handle_status(external::Status::Ok);
}
```

### 7.3 边界：NPO 与 Option<&T> 的内存同构验证

```rust
// 测试: 验证 Option<&T> 与 &T 大小相同（NPO）
use std::mem::size_of;

fn npo_boundary() {
    assert_eq!(size_of::<&u32>(), size_of::<Option<&u32>>());
    assert_eq!(size_of::<Box<u32>>(), size_of::<Option<Box<u32>>>());

    // 对比: 无 NPO 的类型（tag 无法消除）
    assert!(size_of::<Option<u32>>() > size_of::<u32>());

    println!("NPO verified: Option<&u32> = {} bytes", size_of::<Option<&u32>>());
}

fn main() {
    npo_boundary();
}
```

---

## 八、认知路径（Cognitive Path）

从直觉到形式化的过渡需要六步递进的认知脚手架。每一步不仅提供新知识，还解释"为什么这一步必须接在上一步之后"。

### Step 1: 直觉困惑（Intuitive Confusion）

> **核心困惑**: "为什么 enum 比 null 好？"
> 大多数命令式语言程序员习惯于 `T` 可能就是 `null`，并用 `if (x != null)` 防御。Rust 要求写成 `Option<T>` 并强制 match，初看像是"多余的语法噪音"。困惑的根源在于将"类型的存在性"视为默认，而未意识到**null 实际上是一种隐式的、不可追踪的类型状态**。

### Step 2: 具体场景（Concrete Scenario）

> **过渡**: 抽象辩论无法说服习惯 null 的程序员，必须先看到具体的崩溃场景。
> 想象一个函数返回 `User`，调用方直接访问 `user.name`，但数据库查询实际返回了空结果。在 null 语言中，这是运行时 `NullPointerException`。Rust 的 `Option<User>` 强制调用方在编译期处理 `None`，**将运行时崩溃转化为编译期错误**。具体场景让"显式空值"获得了动机——它不是噪音，而是保险。
> **锚点示例**: `fn find_user(id: u64) -> Option<User>` 的调用方必须写 `if let Some(u) = ...` 或 `match`。

### Step 3: 模式抽象（Pattern Abstraction）

> **过渡**: 单个场景不足以指导系统设计，需要提炼为可复用的模式。
> 从"Option 强制处理空值"抽象出**通用模式**：Rust 用 enum 将"可能的状态"编码为**和类型（Sum Type）**。`Option<T> = Some(T) | None`，`Result<T, E> = Ok(T) | Err(E)`。每一种状态都是显式变体，不存在隐式的"第三种可能"。这引出了引理 L1 的直觉版本：enum 让我们可以**枚举所有可能并强制处理每一种**。
> **模式提炼**: 所有"或"关系都应由 enum 表达，所有"与"关系都应由 struct 表达。

### Step 4: 形式规则（Formal Rules）

> **过渡**: 模式在简单场景有效，但递归类型、泛型（Generics） ADT、与 trait 的交互需要更精确的工具。
> 引入**代数数据类型（ADT）**的形式框架：struct 是**积类型** `A × B`（同时拥有 A 和 B），enum 是**余积类型** `A + B`（要么是 A 要么是 B）。`Option<T> ≅ 1 + T`，其中 `1` 是单元类型（None）。match 的穷尽性检查对应于**和类型的消除规则**——你必须处理所有注入（injection）。这正是定理 T1 的形式化根基。
> **形式公理**: 若类型 `T` 是封闭 enum，则对 `T` 的 match 必须覆盖其所有构造子（constructors）。

### Step 5: 代码验证（Code Verification）

> **过渡**: 形式规则必须落回代码，否则只是代数游戏。
> 用编译错误 E0004 验证形式规则：当你遗漏一个 enum 变体时，编译器不仅报错，还会列出未覆盖的变体。这不是简单的语法检查——它是在执行**和类型的穷尽性证明**。尝试添加 `#[non_exhaustive]`，观察通配符 `_ =>` 如何成为编译器认可的"穷尽策略"，从而理解定理的边界。
> **验证实验**: 故意遗漏 match 分支，阅读错误信息；再添加 `_ =>`，观察编译通过，思考"安全"与"完备"的权衡。

### Step 6: 边界测试（Boundary Testing）

> **过渡**: 理解规则的正常运作只是起点，掌握其失效边界才能写出健壮的系统代码。
> 边界测试回答：unsafe transmute 能破坏类型安全吗？`#[non_exhaustive]` 如何削弱穷尽性？NPO 对所有类型都生效吗？通过刻意构造极限代码，验证定理在极端条件下的行为，完成从"学习类型系统"到"驾驭类型系统"的跃迁。
> **终极边界**: `std::mem::transmute`、`#[non_exhaustive]` 跨 crate 演化、`Option<bool>` 与 `Option<&T>` 的内存布局差异。

```text
直觉困惑 ──→ 具体场景 ──→ 模式抽象 ──→ 形式规则 ──→ 代码验证 ──→ 边界测试
    │           │           │           │           │           │
    ▼           ▼           ▼           ▼           ▼           ▼
"为什么 Rust     "null 指针    "Option<T> =    "和类型:       "编译器强制    "unwrap()
没有 null？"   导致崩溃      显式空值"      Some/None     match 处理"    运行时 panic"
              怎么避免？"                  代数完备"                    "non_exhaustive
                                                                      削弱穷尽"

"怎么实现        "不同类型需要   "Trait = 共享    "Type Class /  "impl / dyn    "对象安全
多态？"        相同接口"      行为接口"      存在类型"      分发"        限制"

"编译器怎么      "let x =       "类型推断 =     "HM 算法:      "rustc 自动    "collect()
知道变量        vec![1,2,3]    约束求解"       统一算法"      推导"        需标注"
类型？"        不需要写类型？"
```

**认知脚手架**：

- **类比**: enum 像"单选按钮"——必须且只能选一个；struct 像"表单"——每个字段都必须填写。
- **反直觉点**: 很多语言有隐式 null，Rust 用 `Option<T>` 强制显式处理。
- **形式化过渡**: 从"不能为空" → `Option<T>` 类型 → "和类型 (A + 1)" → "代数类型论" → "范畴论余积".

---

## 九、国际课程与论文对齐

| 来源 | 核心内容 | 与本文件对应 |
|:---|:---|:---|
| **[CMU 17-363: Programming Language Pragmatics]** | 类型系统（Type System）、ADT、模式匹配（Pattern Matching） | L1 类型系统 |
| **[CMU 17-350: Safe Systems Programming]** | 类型安全与内存安全（Memory Safety）的关系 | T3 类型安全定理 |
| **[Wikipedia: Type system](https://en.wikipedia.org/wiki/Type_system)** | 类型系统的通用定义 | 权威定义 §1.1 |
| **[Wikipedia: Algebraic data type](https://en.wikipedia.org/wiki/Algebraic_data_type)** | 积类型与余积类型 | 引理 L1 |
| **[Pierce "Types and Programming Languages"]** | Hindley-Milner、类型推断、子类型 | T2、形式化定义 |
| **[Wright & Felleisen 1994]** | Progress + Preservation | T3 类型安全定理 |
| **[Category Theory for Programmers]** | 积、余积、初始对象、终对象 | L1 ADT 完备性 |
| **[TRPL Ch3.2](https://doc.rust-lang.org/book/ch03-02-data-types.html)** | 静态类型与类型推断 | 权威定义 §1.2 |
| **[TRPL Ch6](https://doc.rust-lang.org/book/ch06-00-enums.html)** | enum 与模式匹配（Pattern Matching） | T1 match 穷尽性 |
| **[TRPL Ch9](https://doc.rust-lang.org/book/ch09-00-error-handling.html)** | Result<T, E> 错误处理（Error Handling） | 推论 C2 |

---

## 十、知识来源关系（Provenance）

| **论断** | **来源** | **可信度** |
|:---|:---|:---|
| Rust 是静态类型语言 | [TRPL Ch3.2](https://doc.rust-lang.org/book/ch03-02-data-types.html) | ✅ |
| 编译器通常可推断类型 | [TRPL Ch3.2](https://doc.rust-lang.org/book/ch03-02-data-types.html) | ✅ |
| enum 类似函数式语言的 ADT | [TRPL Ch6](https://doc.rust-lang.org/book/ch06-00-enums.html) | ✅ |
| `Option<T>` 消除空指针 | [TRPL Ch6.1](https://doc.rust-lang.org/book/title-page.html) · [Wikipedia: Null pointer](https://en.wikipedia.org/wiki/Null_pointer) | ✅ |
| `Result<T, E>` 强制错误处理（Error Handling） | [TRPL Ch9](https://doc.rust-lang.org/book/ch09-00-error-handling.html) | ✅ |
| NPO 优化 Option<&T> | [Rust Reference: Enums](https://doc.rust-lang.org/reference/items/enumerations.html) | ✅ |
| ADT 对应积与余积 | [Category Theory for Programmers] | ✅ |
| match 穷尽性检查 | [Rust Reference: Patterns](https://doc.rust-lang.org/reference/patterns.html) | ✅ |
| 类型系统理论基础 | [Pierce 2002 — Types and Programming Languages] | ✅ |
| 类型安全定理 (Progress + Preservation) | [Wright & Felleisen 1994 — JFP] | ✅ |
| 子类型理论基础 | [Cardelli 1996 — Type Systems, ACM Computing Surveys] | ✅ |
| Never 类型语义 | [Rust Reference: Never type](https://doc.rust-lang.org/reference/types.html#never-type) | ✅ |

---

## 十一、相关概念链接

- [Ownership](01_ownership.md) — 类型系统与所有权规则共同构成 Safe Rust 的内存安全（Memory Safety）基础
- [Borrowing](02_borrowing.md) — 引用类型 `&T`、`&mut T` 是类型系统对内存别名的约束表达
- [Lifetimes](03_lifetimes.md) — 生命周期（Lifetimes）是类型系统的参数化扩展，将时间维度引入类型
- [Traits](../02_intermediate/01_traits.md) — Trait 将行为抽象引入类型系统，对应 Haskell Type Class
- [Generics](../02_intermediate/02_generics.md) — 泛型参数化使 ADT 具备多态表达能力
- [00_meta/inter_layer_map.md](../00_meta/inter_layer_map.md) — 跨层定理映射 §4.2 "类型系统一致性"

---

### 补充章节：`impl Trait` 与 `dyn Trait` 的类型论差异

> **[Rust Reference: Impl Trait](https://doc.rust-lang.org/reference/types/impl-trait.html)** `impl Trait` 是**存在类型**（existential type）：调用方知道值满足某 Trait，但不知道具体类型。✅ 已验证
> **[Rust Reference: Trait Objects](https://doc.rust-lang.org/reference/types/trait-object.html)** `dyn Trait` 是**动态分发**（dynamic dispatch）：通过胖指针（数据指针 + vtable 指针）在运行时解析方法调用。✅ 已验证

#### 存在类型 vs 全称类型

```text
类型论视角:
  impl Trait  ≈  ∃T. Trait(T)   （存在类型：某个满足 Trait 的类型）
  <T: Trait>  ≈  ∀T. Trait(T)   （全称类型：所有满足 Trait 的类型）
  dyn Trait   ≈  ∃T. Trait(T) + 运行时擦除  （存在类型 + 延迟解析）
```

| **维度** | `impl Trait`（返回位置） | `dyn Trait` | `<T: Trait>`（泛型） |
|:---|:---|:---|:---|
| **类型论** | 存在类型 ∃T | 存在类型 + 运行时擦除 | 全称类型 ∀T |
| **分发方式** | 静态分发（单态化） | 动态分发（vtable） | 静态分发（单态化） |
| **大小信息** | 编译期已知（单态化后） | 编译期未知（胖指针） | 编译期已知 |
| **vtable 开销** | ❌ 无 | ✅ 双指针 + 间接调用 | ❌ 无 |
| **异构集合** | ❌ 不支持 `Vec<impl Trait>` | ✅ `Vec<Box<dyn Trait>>` | ❌ 单一类型 |
| **trait object** | ❌ 不能构造 `dyn` | ✅ 本身就是 `dyn` | ❌ 不能构造 `dyn` |
| **隐藏实现** | ✅ 返回类型抽象 | ❌ 暴露为动态分发 | ❌ 编译期实例化 |

#### 单态化 vs 动态分发：性能对比

| **指标** | `impl Trait` / `<T: Trait>` | `dyn Trait` |
|:---|:---|:---|
| **调用开销** | 零成本（直接调用） | vtable 间接调用（1 次指针解引用） |
| **内联优化** | ✅ 编译器可内联 | ❌ 通常无法内联 |
| **二进制体积** | 每个实例化膨胀一份代码 | 一份代码，运行时分发 |
| **缓存友好性** | 高（单一类型连续内存） | 低（vtable 指针跳跃访问） |
| **编译时间** | 较长（单态化） | 较短 |

#### vtable 内存开销

```text
dyn Trait 的胖指针布局:
  胖指针 = [数据指针 | vtable 指针]
         16 bytes（64 位系统）

vtable 内容:
  [drop_in_place | size | align | method_1 | method_2 | ...]

开销分析:
  - 每个 dyn Trait 值：额外 8 bytes（vtable 指针）
  - 每个 vtable：每 Trait + 每类型 一份，方法数 × 8 bytes
  - 间接调用：CPU 分支预测失败率更高
```

#### 选择决策树

```mermaid
graph TD
    Q1[需要返回具体类型且隐藏实现细节?] -->|是| A1[返回 impl Trait]
    Q1 -->|否| Q2[需要异构集合或运行时多态?]
    Q2 -->|是| Q3[Trait 满足对象安全?]
    Q3 -->|是| A2[使用 dyn Trait / Box<dyn Trait>]
    Q3 -->|否| A3[拆分为对象安全子 Trait + Sized 方法]
    Q2 -->|否| Q4[性能敏感且类型编译期已知?]
    Q4 -->|是| A4[使用 <T: Trait> 泛型约束]
    Q4 -->|否| A1

    A1[impl Trait<br/>零成本 + 抽象]
    A2[dyn Trait<br/>运行时灵活 + vtable 开销]
    A3[重构 Trait 设计]
    A4[泛型约束<br/>零成本 + 类型参数暴露]
```

> **认知功能**:
> 此决策树是「多态机制选择」的**工程决策器**。
> Rust 提供三种多态方式（impl Trait、dyn Trait、泛型约束），初学者常困惑该选哪个。
> 此图通过三个问题引导选择：是否需要隐藏实现？是否需要异构集合？是否性能敏感？每个叶节点标注了「收益 + 代价」，帮助读者做出知情权衡。
> 关键认知：没有「最佳」选择，只有「最适合当前约束」的选择——impl Trait 是默认值（零成本 + 隐藏实现），dyn Trait 是灵活性需求时的备选（vtable 开销），泛型约束是调用方需要知道具体类型时的选择。 [来源: 💡 原创分析]

```rust,ignore
// ✅ impl Trait: 隐藏实现，零成本
fn make_iter() -> impl Iterator<Item = u32> {
    vec![1, 2, 3].into_iter()
}

// ✅ dyn Trait: 异构集合
fn process_all(items: &[Box<dyn Drawable>]) {
    for item in items { item.draw(); }
}

// ✅ 泛型：性能敏感路径
fn max<T: Ord>(a: T, b: T) -> T { if a > b { a } else { b } }
```

> **[TRPL Ch10.2](https://doc.rust-lang.org/book/ch10-02-traits.html)** `impl Trait` 适用于"返回某种 Iterator/Display，但不想暴露具体类型"；`dyn Trait` 适用于"需要运行时异构集合"。✅ 已验证

---

### 11.1 补充：`!` (Never type) 的形式化分析

> **[Rust Reference: Never type](https://doc.rust-lang.org/reference/types.html#never-type)** ·
> **[Wikipedia: Bottom type](https://en.wikipedia.org/wiki/Bottom_type)** ·
> **[TAPL Ch.11]** `!` 是 Rust 的 **bottom type**（底类型），表示"永无返回"。
> 它在类型论中是**所有类型的子类型**（`! <: T` 对任意 `T`），在控制流分析中扮演关键角色。✅

#### 形式化定义

```text
语法:  fn diverges() -> ! { loop {} }
语义:  diverges() 不终止 ⟹ 不存在值属于类型 !
类型论: ! 是空集 ∅，是任意类型 T 的子类型（! <: T）
```

#### 控制流交互：`!` 作为统一分支类型

```rust,ignore
fn main() -> Result<(), String> {
    let value = match maybe_error() {
        Ok(v) => v,           // v: i32
        Err(e) => return Err(e.into()),  // return 表达式类型为 !
    };
    // ✅ 编译器知道：若 Err 分支执行，则不会到达此处
    //    因此 value 的类型 = Ok 分支的 i32
    println!("{}", value);
    Ok(())
}
```

#### `Result<T, !>`：表示"不可能出错"

```rust,ignore
// ✅ Result<T, !> 表示操作总是成功，Err 变体不可构造
fn infallible_op() -> Result<String, !> {
    Ok(String::from("always success"))
}

let s = infallible_op()?;  // ? 不会返回，因为 Err(!) 无法构造
// s 的类型直接为 String，无需 unwrap
```

| 用法 | 类型签名 | 含义 |
|:---|:---|:---|
| `fn foo() -> !` | 返回底类型 | 函数永不返回（panic/loop/exit） |
| `Result<T, !>` | 成功类型 T，错误类型 ! | 操作不可能失败 |
| `Option<!>` | 无值类型 | 等价于 `()`，但语义更精确 |
| `match` 统一 | `!` 作为缺失分支的类型 | 允许 match 分支类型不一致时通过子类型统一 |

> **来源**:
> [Rust Reference: Diverging functions](https://doc.rust-lang.org/reference/) ·
> [Wikipedia: Bottom type](https://en.wikipedia.org/wiki/Bottom_type) ·
> [TAPL Ch.11: Subtyping] ·
> [RFC 1216: Never type](https://github.com/rust-lang/rfcs/pull/1216)

### 11.2 补充：Zero-Sized Types (ZST) 与 `PhantomData`

> **[Rust Reference: Zero-sized types](https://doc.rust-lang.org/reference/)** ·
> **[Rust Reference: PhantomData](https://doc.rust-lang.org/reference/special-types-and-traits.html)**
> ZST 是**运行时大小为 0 字节**的类型，在类型论中是**单元类型（unit type）**的泛化。
> `PhantomData<T>` 是 ZST 的代表，用于**在类型系统中携带编译期信息**，而不产生运行时开销。✅

#### ZST 的类型论意义

```rust
// ✅ 所有 ZST 在运行时占 0 字节
struct Unit;           // 单元结构体
enum Void {}          // 空枚举（无变体）
struct Wrapper<T>(std::marker::PhantomData<T>);  // 泛型但零大小

assert_eq!(std::mem::size_of::<Unit>(), 0);
assert_eq!(std::mem::size_of::<Wrapper<String>>(), 0);
```

| ZST | 大小 | 类型论语义 | 典型用途 |
|:---|:---|:---|:---|
| `()` | 0 | 单元类型（terminal object） | 无返回值、无副作用 |
| `!` | 0 | 底类型（initial object） | 永不返回 |
| `Void`（空 enum） | 0 | 空类型（无 inhabitant） | 不可达分支标记 |
| `PhantomData<T>` | 0 | 类型标记（type token） | 编译期携带泛型参数信息 |

#### `PhantomData<T>` 的工程用途

```rust
use std::marker::PhantomData;

// ✅ 用 PhantomData 在类型系统中编码"所有权"
struct Handle<T> {
    raw: *mut T,
    _marker: PhantomData<T>,  // 告诉编译器：这个 handle 逻辑上拥有 T
}

impl<T> Drop for Handle<T> {
    fn drop(&mut self) {
        unsafe { drop(Box::from_raw(self.raw)); }
    }
}

// ✅ 自动实现 Send/Sync 基于 T
// 若没有 PhantomData<T>，编译器不知道 Handle 与 T 的关系
// 可能错误实现 Send（即使 T: !Send）
```

#### `PhantomData` 与 variance

```rust,ignore
// ✅ 用 PhantomData 控制泛型参数的 variance
struct Covariant<T>(PhantomData<T>);        // T 协变
struct Contravariant<T>(PhantomData<fn(T)>); // T 逆变
struct Invariant<T>(PhantomData<*mut T>);    // T 不变
```

| `PhantomData` 形式 | Variance |
|:---|:---|
| `PhantomData<T>` | 协变（covariant） |
| `PhantomData<fn(T)>` | 逆变（contravariant） |
| `PhantomData<*mut T>` | 不变（invariant） |
| `PhantomData<fn() -> T>` | 协变（covariant） |

> **关键洞察**:
>
> `PhantomData` 是 Rust 类型系统的"幽灵字段"——它在运行时完全不存在，但在编译期决定了：
>
> 1) 类型的自动 trait 推导（Send/Sync）；
> 2) 泛型参数的 variance；
> 3) drop check 的行为。
> 这是"零成本抽象（Zero-Cost Abstraction）"的极致体现。
>
> **来源**: [Rust Reference: PhantomData](https://doc.rust-lang.org/reference/special-types-and-traits.html) ·
> [Rust Reference: Variance](https://doc.rust-lang.org/reference/) ·
> [Rustonomicon: PhantomData](https://doc.rust-lang.org/nomicon/) ·
> [Wikipedia: Unit type](https://en.wikipedia.org/wiki/Unit_type)

---

### 11.3 Const Generics（常量泛型）

**定义**：Const Generics 允许类型参数中包含**编译期常量值**（如 `N: usize`），使数组长度等值成为类型系统的一部分：

```rust
// ✅ Const Generics：数组长度作为类型参数
struct Array<T, const N: usize> {
    data: [T; N],  // N 是编译期已知的常量
}

// 不同类型（长度不同）
let a: Array<i32, 3> = Array { data: [1, 2, 3] };
let b: Array<i32, 5> = Array { data: [1, 2, 3, 4, 5] };
// a 和 b 是不同类型！
```

**与 Dependent Type 的关系**：Const Generics 是**受限的依赖类型**（Dependent Type）——值（`N`）可以出现在类型中，但值的计算必须是编译期可求值的常量表达式。

> **来源**:
>
> [RFC 2000: Const Generics](https://rust-lang.github.io/rfcs/2000-const-generics.html) ·
> [Rust Reference: Const Generics](https://doc.rust-lang.org/reference/items/generics.html#const-generics) ·
> [Wikipedia: Dependent type](https://en.wikipedia.org/wiki/Dependent_type)

### 11.4 Type Inference：HM 算法完整规则

> **Bloom 层级**: 分析 → 评价
> Rust 的类型推断基于 **Hindley-Milner (HM) 算法**，这是函数式编程语言（ML、Haskell）的基石。
> HM 算法的核心特性是 **Principal Type Property**：对无显式类型约束的表达式，存在唯一的最一般类型（principal type），编译器可自动推导。
> 本节从 HM 核心规则出发，逐步扩展到 Rust 的 trait bounds、生命周期与关联类型，建立类型推断的完整形式化图景。
>
> **交叉链接**:
>
> [L1 生命周期: Elision 规则](03_lifetimes.md) ·
> [L2 泛型: 约束推导](../02_intermediate/02_generics.md) ·
> [L4 类型论: 系统 F](../04_formal/02_type_theory.md)

#### 11.4.1 HM 核心规则（Var、App、Abs、Let）

HM 算法的形式化基础是 **Damas-Milner 类型系统**。以下四条规则覆盖 λ-演算的全部语法构造：

```text
─────────────────────────────────────────  [Var]
  Γ, x:σ ⊢ x : σ

  Γ ⊢ e₀ : τ → τ'    Γ ⊢ e₁ : τ
─────────────────────────────────────────  [App]
  Γ ⊢ e₀ e₁ : τ'

  Γ, x:τ ⊢ e : τ'
─────────────────────────────────────────  [Abs]
  Γ ⊢ λx.e : τ → τ'

  Γ ⊢ e₀ : σ    Γ, x:σ ⊢ e₁ : τ
─────────────────────────────────────────  [Let]
  Γ ⊢ let x = e₀ in e₁ : τ
```

**规则语义**:

| **规则** | **名称** | **直觉** |
|:---|:---|:---|
| **Var** | 变量 | 从类型环境 Γ 中查找变量的类型方案 σ |
| **App** | 应用 | 若函数 `e₀` 的类型为 `τ → τ'`，且参数 `e₁` 的类型为 `τ`，则结果的类型为 `τ'` |
| **Abs** | 抽象 | lambda `λx.e` 的类型是 `τ → τ'`，其中 `τ` 是参数 `x` 的类型，`τ'` 是体 `e` 的类型 |
| **Let** | 绑定 | `let x = e₀ in e₁` 的类型为 `τ`，其中 `x` 获得 `e₀` 的泛化类型方案 `σ`，再在 `e₁` 中使用 |

> **[来源: Damas & Milner 1982, *Principal Type-Schemes for Functional Programs*]** HM 算法的四条规则构成完整的类型推导系统，支持 let-多态性（let-polymorphism）。✅
> **[来源: Pierce, *Types and Programming Languages*, Ch.22]** HM 算法是 ML 家族语言类型推断的理论基础，Var/App/Abs/Let 规则对应 λ-演算的四类语法节点。✅

#### 11.4.2 统一（Unification）过程

**统一**是 HM 算法的计算核心：给定两个类型项，找出使它们相等的**最一般替换（most general unifier, MGU）**。

```text
统一算法（Robinson 1965）:

  unify(τ, τ) = ∅                         （恒等）
  unify(α, τ) = {α ↦ τ}  若 α ∉ fv(τ)    （变量替换，需 occur check）
  unify(τ, α) = {α ↦ τ}  若 α ∉ fv(τ)
  unify(τ₁→τ₂, τ₁'→τ₂') = unify(τ₁,τ₁') ∪ unify(τ₂,τ₂')  （结构递归）
  unify 失败 → 类型错误
```

**Occur Check**：禁止将类型变量 `α` 统一为包含自身的类型（如 `α = Vec<α>`），否则会导致无限类型。

```text
示例: 统一 `α → β` 与 `i32 → γ`
  unify(α → β, i32 → γ)
  = unify(α, i32) ∪ unify(β, γ)
  = {α ↦ i32, β ↦ γ}
```

> **[来源: Robinson 1965, *A Machine-Oriented Logic Based on the Resolution Principle*]** 统一算法是自动定理证明与类型推断的共同基础，Robinson 证明了 MGU 的存在唯一性（若存在）。✅

#### 11.4.3 Rust 对 HM 算法的扩展

Rust 的类型推断不是纯 HM——它在 HM 骨架上增加了多个扩展，使问题从多项式时间变为更复杂的约束求解：

| **扩展** | **HM 原始形式** | **Rust 扩展** | **影响** |
|:---|:---|:---|:---|
| **Trait Bounds** | 无 | `T: Display + Clone` | 统一后需额外求解 trait 约束（非 HM 标准部分） |
| **Lifetime 参数** | 无 | `'a`, `'static` | 生命周期作为类型参数参与统一，但约束是偏序而非等式 |
| **Associated Types** | 无 | `<T as Trait>::Output` | 统一涉及类型投影归一化（normalization） |
| **数值字面量** | 无 | `42` 可为 `i32/u32/i64/...` | 引入浮动类型变量（fallback 到 `i32`） |
| **闭包（Closures）捕获** | 无 | `Fn/FnMut/FnOnce` | 闭包类型由捕获集推断，无显式语法 |

```text
Rust 类型推断的两阶段模型:

  阶段 1: HM 风格局部推断
    - 为表达式生成类型变量和等式约束
    - 统一求解大部分变量绑定

  阶段 2: Trait / 生命周期约束求解
    - trait bound: 在类型已部分确定后，搜索满足约束的实现
    - lifetime: 生成 outlives 约束图，求解最小满足区域
    - associated type: 归一化投影类型为具体类型
```

> **来源: [Rust Reference: Type Inference](https://doc.rust-lang.org/reference/statements.html)** Rust 的类型推断基于 HM 算法，但 trait bound 求解和生命周期推断是独立的扩展。✅
> **[来源: rustc dev guide: Type inference]** rustc 的类型推断器将 HM 统一与 trait solver 分离：先统一类型变量，再求解 trait 约束。✅

**关联类型推断示例**:

```rust
trait Add<RHS = Self> {
    type Output;
    fn add(self, rhs: RHS) -> Self::Output;
}

fn sum<T>(a: T, b: T) -> T::Output
where
    T: Add,
{
    a.add(b)
}

// 调用时编译器推断:
// sum(1i32, 2i32) → T = i32, T::Output = i32（通过 Add<i32> 的 impl 归一化）
```

#### 11.4.4 `let` 多态性（let-polymorphism）与 Rust 的 `let` 绑定

**let-多态性**是 HM 算法的标志性特征：在 `let x = e₀ in e₁` 中，`x` 的类型被**泛化（generalize）**为多态类型方案（type scheme），允许在 `e₁` 中以不同具体类型使用 `x`。

```text
泛化规则:
  Γ ⊢ e₀ : τ    α₁,...,αₙ 不在 Γ 中自由出现
  ─────────────────────────────────────────
  Γ ⊢ let x = e₀ in e₁ : ∀α₁...αₙ.τ

示例:
  let id = λx.x in (id 5, id true)
  id 的类型 = ∀α. α → α
  id 5 中 α = Int, id true 中 α = Bool
```

**Rust 中的 let-多态性**:

```rust,compile_fail
// ✅ 正确: Rust 的 let 绑定支持 HM 风格的类型推断
let id = |x| x;  // 推断为 id<T>(x: T) -> T
let a = id(5i32);    // T = i32
let b = id("hello"); // T = &str
// id 在不同调用点实例化为不同类型（单态化）
```

**Rust 的限制**:

| **场景** | **HM/ML** | **Rust** | **原因** |
|:---|:---|:---|:---|
| 泛型函数递归 | 自动推断 | ❌ 需显式标注 | 递归调用点无足够约束 |
| 高阶类型多态 | `map : ∀a,b. (a→b) → [a] → [b]` | 需显式泛型参数 | Rust 无 ML 风格的隐式泛型函数 |
| 值级别多态 | `let f = id in (f 1, f true)` | 闭包（Closures）可做到 | 但单态化后生成两份代码 |

> **[来源: Damas & Milner 1982]** let-多态性是 HM 算法的核心创新：它将 `let` 绑定的右侧类型泛化，使多态性在不增加显式标注的情况下可用。✅
> **来源: [Rust Reference: Type Inference](https://doc.rust-lang.org/reference/statements.html)** Rust 函数签名中的泛型参数必须显式声明（`fn id<T>(x: T) -> T`），但函数体内部和 `let` 绑定的局部推断遵循 HM 原则。✅

#### 11.4.5 类型推断的边界（何时需要显式标注）

尽管 HM 算法在局部表达式上是完备的，Rust 的工程实践在多个场景下要求显式标注：

```mermaid
graph TD
    P["何时需要显式类型标注?"] --> Q1{"函数签名公共 API?"}
    Q1 -->|是| F1["必须显式标注<br/>→ 文档契约与编译期接口稳定性"]
    Q1 -->|否| Q2{"泛型方法链 collect?"}
    Q2 -->|是| F2["collect::<Vec<_>><br/>→ 目标容器类型歧义"]
    Q2 -->|否| Q3{"数值字面量无上下文?"}
    Q3 -->|是| F3["42 → i32? u32? i64?<br/>→ fallback 到 i32 但可能非预期"]
    Q3 -->|否| Q4{"递归函数?"}
    Q4 -->|是| F4["递归调用点无足够约束<br/>→ 需显式签名锚定"]
    Q4 -->|否| Q5{"关联类型歧义?"}
    Q5 -->|是| F5["T::Output 可能多解<br/>→ 需显式 where 约束"]
    Q5 -->|否| T1["类型推断成功<br/>✅ HM Principal Type"]

    style F1 fill:#f96
    style F2 fill:#f96
    style F3 fill:#f96
    style F4 fill:#f96
    style F5 fill:#f96
    style T1 fill:#6f6
```

> **认知功能**: 此决策树是「类型推断失败场景」的**系统排查指南**。
> 当编译器报错 E0282（类型标注 needed）时，读者可按图快速定位原因：
> 是函数签名缺失？
> 还是 collect 链歧义？
> 还是字面量 fallback 非预期？
> 五个橙色节点覆盖了 Rust 类型推断需要人工干预的几乎全部场景，绿色节点确认「推断成功」的常规路径。
> 关键认知：HM 推断本身是完备的，但 Rust 的工程设计（显式函数签名、整数 fallback 规则、关联类型）在特定边界处要求人工标注
> ——这不是推断算法的缺陷，而是「理论完备性」与「工程实用性」的权衡。 [来源: 💡 原创分析]

**边界矩阵**:

| **场景** | **错误码** | **说明** |
| :--- | :--- | :--- |
| `let v = vec![];` | E0282 | 无法推断 Vec 元素类型 |
| `let c = items.collect();` | E0282 | 无法推断目标容器类型 |
| `fn foo(x: _) -> _` | E0121 | 函数签名不允许 `_` 类型占位 |
| `let x = 42; x as _` | E0283 | `as` 转换目标类型不明确 |
| `impl Trait` 返回递归 | E0720 | 递归调用点无法推断存在类型 |

> **来源: [Rust Reference: Type Inference](https://doc.rust-lang.org/reference/statements.html)** 类型推断的边界是工程设计与理论完备性的权衡：显式标注提供接口契约，推断减少局部冗余。✅

#### 11.4.6 与 Haskell、ML 的类型推断对比

| **维度** | **ML (OCaml/SML)** | **Haskell** | **Rust** |
|:---|:---|:---|:---|
| **核心算法** | HM | HM + 类型类（Type Classes） | HM + Trait Bounds |
| **多态性** | let-多态性 | let-多态性 + 高阶类型 | 参数多态性（显式泛型） |
| **显式标注** | 极少 | 类型类实例需声明 | 函数签名必须显式 |
| **约束求解** | 等式统一 | 等式统一 + 类型类上下文 | 统一 + trait solver + 生命周期（Lifetimes） |
| **高阶类型** | ❌ 不支持 | ✅ 支持（HKT） | ⚠️ GATs 提供受限 HKT |
| **数值字面量** | 默认 `int`/`float` | `Num a => a`（多态字面量） | fallback 到 `i32`/`f64` |
| **类型推断失败** | 精确错误定位 | 类型类歧义提示 | trait bound 不满足提示 |

**关键差异分析**:

```text
Haskell 的多态字面量:
  let x = 42      -- x :: Num a => a（任意数值类型）
  let y = x + 3.5 -- y :: Fractional a => a

Rust 的数值 fallback:
  let x = 42;     // x: i32（默认 fallback）
  let y = x + 3.5; // 错误: i32 + f64 不匹配
```

> **[来源: Peyton Jones et al., *Haskell 98 Report*]** Haskell 的类型推断通过类型类扩展 HM，允许数值字面量保持多态直到使用上下文确定具体类型。✅
> **来源: [Rust Reference: Type Inference](https://doc.rust-lang.org/reference/statements.html)** Rust 选择显式性优先：函数签名必须标注类型参数，数值字面量无上下文时 fallback 到 `i32`/`f64`，避免隐式多态带来的意外。✅

**形式化对比**:

```text
ML 类型推断:      HM 算法，多项式时间 O(n³)
Haskell 类型推断: HM + 类型类约束求解，指数级最坏情况（但实践中高效）
Rust 类型推断:    HM + Trait 求解 + 生命周期约束，NP-hard 最坏情况

工程权衡:
  ML/Haskell 追求"不写类型"的极致推断
  Rust 追求"接口显式、局部推断"的工程可维护性
```

> **[来源: Kfoury et al., *Typability and Type Checking in System F*]** System F（含显式 ∀ 类型）的类型推断是不可判定的；Rust 的显式泛型参数将类型推断限制在 HM 可判定片段内，确保编译终止。✅

### 11.5 Discriminant 与 Enum 内存布局

> **Bloom 层级**: 分析 → 评价
> 本节从工程直觉深入到内存表示的精确分析，建立 enum 作为 **tagged union** 的完整心智模型。内容覆盖 discriminant 的工作原理、编译器 niche optimization 的数学条件、`#[repr]` 的强制布局语义，以及通过 `unsafe` 对原始字节的验证实验。
> **交叉链接**: [L4 类型论: ADT 代数语义](../04_formal/02_type_theory.md) · [L3 unsafe: 无效枚举值](../03_advanced/03_unsafe.md) · [00_meta/inter_layer_map.md](../00_meta/inter_layer_map.md) §4.2 "类型系统一致性"

#### 11.5.1 Discriminant 的基本概念与 `std::mem::discriminant`

**Discriminant** 是编译器为 enum 每个变体分配的唯一整数标签，用于在运行时识别当前激活的变体。

```rust
enum Message {
    Quit,                    // discriminant = 0（默认）
    Move { x: i32, y: i32 }, // discriminant = 1
    Write(String),           // discriminant = 2
}

// 显式指定 discriminant（常用于 C 兼容或位标志场景）
enum HttpStatus {
    Ok = 200,
    NotFound = 404,
    ServerError = 500,
}
```

> **[来源: [Rust Reference: Enums](https://doc.rust-lang.org/reference/items/enumerations.html)]** 若未显式指定，discriminant 从 0 开始按定义顺序递增，类型为编译器内部选择的整数类型。✅

`std::mem::discriminant` 提供了一种**仅比较变体身份、忽略 payload** 的安全方式：

```rust,ignore
use std::mem;

let msg1 = Message::Quit;
let msg2 = Message::Write(String::from("hello"));
let msg3 = Message::Write(String::from("world"));

assert_ne!(mem::discriminant(&msg1), mem::discriminant(&msg2)); // 不同变体
assert_eq!(mem::discriminant(&msg2), mem::discriminant(&msg3)); // 同一变体（payload 不同）
```

**工作原理**：`discriminant(&value)` 返回 `Discriminant<T>`——一个 opaque 的编译器内省句柄，其底层通常直接读取 enum 的 tag 字段。`Discriminant<T>` 仅实现 `Clone`、`Copy`、`PartialEq`、`Eq`、`Hash`、`Debug`，**不暴露具体整数值**，这保证了即使编译器对 tag 进行压缩或重排，语义仍然稳定。

> **来源: [Rust Reference: std::mem::discriminant](https://doc.rust-lang.org/reference/)** `Discriminant<T>` 的比较等价于判断两个值是否属于同一变体，不触及变体携带的数据。✅

#### 11.5.2 枚举的内存布局：Tagged Union 模型

Rust enum 的抽象内存模型是 **tagged union**（标签联合体）：

```text
内存布局（概念模型）:
┌─────────────────────────────────────────────────┐
│  discriminant (tag)  │  payload (union of variants) │
└─────────────────────────────────────────────────┘
> [来源: [The Rust Programming Language](https://doc.rust-lang.org/book/title-page.html)]
```

| 组件 | 语义 | 大小决定因素 |
|:---|:---|:---|
| **Discriminant** | 标识激活变体的整数标签 | 变体数量的对数：⌈log₂(N)⌉ bits，向上取整到 u8/u16/u32/u64 |
| **Payload** | 当前变体携带的数据 | `max(size_of(V₁), size_of(V₂), ..., size_of(Vₙ))` |
| **Padding** | 对齐填充 | 使总大小满足 `align_of(E)` 的整数倍 |

总大小的近似公式：

```text
size_of(E) ≈ align_to(max(size_of(discriminant) + max_variant_size,
                           max_variant_size_with_discriminant_inlined),
                       align_of(E))
```

> **[来源: Unsafe Code Guidelines: Enum Layout]** Rust 无 `#[repr]` 的 enum 布局未指定（unspecified），编译器可自由重排字段、压缩 tag、合并 niche。✅
> **来源: [Rust Reference: Type Layout](https://doc.rust-lang.org/reference/type-layout.html)** `align_of::<E>()` 等于所有变体对齐要求的最大值（discriminant 通常对齐为 1）。✅

**关键洞察**：无 `#[repr]` 时，编译器可能将 discriminant 嵌入到 payload 的 padding 中（称为 "tag packing"），甚至完全消除 tag（见 §11.5.3 Niche Optimization）。因此程序员**不能**对默认 enum 的内存布局做任何假设。

#### 11.5.3 Niche Optimization 与 Null Pointer Optimization（NPO）

**Niche** 指某个类型中**非法的位模式集合**。编译器利用这些非法值来编码 enum 的某个无 payload 变体（通常是 `None`），从而**完全消除 discriminant 的显式存储**。

| 类型 | 合法位模式 | Niche（非法值） | 可被 NPO 优化的外层 Enum |
|:---|:---|:---|:---|
| `&T` | 所有非 0 地址 | `0x0`（null） | `Option<&T>` |
| `Box<T>` | 所有非 0 地址 | `0x0` | `Option<Box<T>>` |
| `NonNull<T>` | 所有非 0 地址 | `0x0` | `Option<NonNull<T>>` |
| `fn()` | 所有非 0 地址 | `0x0` | `Option<fn()>` |
| `NonZeroU32` | 1..=u32::MAX | `0` | `Option<NonZeroU32>` |
| `bool` | `0x00`, `0x01` | `0x02`..=`0xFF`（共 254 个） | `Option<bool>` |
| `char` | 合法 Unicode scalar | `0xD800`..=`0xDFFF` 等 | `Option<char>` |

> **[来源: [Rust Reference: Enums](https://doc.rust-lang.org/reference/items/enumerations.html)]** Niche value optimization 是编译器保证的优化：`Option<&T>` 的内存布局与 `&T` 完全相同。✅
> **来源: [The Rustonomicon: Exotic Sizes](https://doc.rust-lang.org/nomicon/)** NPO 是 Rust "零成本抽象（Zero-Cost Abstraction）" 的核心体现之一。✅

**`Option<&T>` 的 NPO 详解**：

```rust
use std::mem;

assert_eq!(mem::size_of::<&u32>(), 8);           // 64 位系统指针大小
assert_eq!(mem::size_of::<Option<&u32>>(), 8);   // ✅ NPO：tag 被消除
assert_eq!(mem::size_of::<Box<u32>>(), 8);
assert_eq!(mem::size_of::<Option<Box<u32>>>(), 8); // ✅ NPO 同样生效
```

内存层面的编码规则：

```text
Option<&T>:
  0x0000_0000_0000_0000  → None
  任何非 0 地址           → Some(&T)
```

这意味着 `Option<&T>` 的空值检查在汇编层面**不需要额外的比较指令**——解引用前检查是否为 null 的代价与 C 指针检查完全相同。

**NPO 的递归边界**：Niche 被消耗后不可复用。

```rust
use std::mem;

assert_eq!(mem::size_of::<Option<bool>>(), 1);           // ✅ bool 有 254 个 niche 值
assert_eq!(mem::size_of::<Option<Option<bool>>>(), 1);    // ✅ 仍有足够 niche
assert_eq!(mem::size_of::<Option<Option<&u32>>>(), 16);   // ❌ &u32 仅有 1 个 niche，已被内层 Option 消耗
```

| 类型 | 大小 | 原因 |
|:---|:---:|:---|
| `Option<&u32>` | 8 | `&u32` 的 null 编码 `None` |
| `Option<Option<&u32>>` | 16 | `Option<&u32>` 的所有 2⁶⁴ 位模式均被合法占用（0=None，非0=Some），外层需额外 tag |
| `Option<bool>` | 1 | bool 仅需 2 个值，`0x02` 编码 `None` |
| `Option<Option<bool>>` | 1 | `Option<bool>` 仅用 3 个值，`0x03` 编码外层的 `None` |

> **[来源: Unsafe Code Guidelines: Values]** 类型的 "invalid value" 集合是 niche optimization 的形式化基础。编译器在布局计算时枚举类型的有效值范围，寻找可用于编码 enum 变体的非法位模式。✅

#### 11.5.4 `#[repr]` 对 Discriminant 与布局的影响

`#[repr]` 属性强制改变 enum 的布局策略，使其满足 FFI 或特定硬件对齐需求，但**牺牲编译器优化空间**。

| `repr` 属性 | 适用场景 | Discriminant 类型 | Payload 布局 | Niche Optimization |
|:---|:---|:---|:---|:---:|
| （无） | 通用 Rust 代码 | 编译器自选 | 编译器优化 | ✅ 允许 |
| `#[repr(u8)]` | 强制 tag 为 u8 | `u8` | 类似 C union | ❌ 禁用 |
| `#[repr(u16)]` | 强制 tag 为 u16 | `u16` | 类似 C union | ❌ 禁用 |
| `#[repr(u32)]` | 兼容 32 位系统/协议 | `u32` | 类似 C union | ❌ 禁用 |
| `#[repr(u64)]` | 兼容 64 位协议 | `u64` | 类似 C union | ❌ 禁用 |
| `#[repr(i8/i16/i32/i64)]` | 有符号整数标签 | 对应有符号类型 | 类似 C union | ❌ 禁用 |
| `#[repr(C)]` | C FFI 兼容 | `c_int` 或更大 | `repr(C)` 结构 | ❌ 禁用 |
| `#[repr(packed)]` | 无对齐填充 | — | 无 padding | ❌ 禁用 |
| `#[repr(align(N))]` | 强制对齐边界 | — | 按 N 对齐 | 视情况而定 |

> **来源: [Rust Reference: repr Attribute](https://doc.rust-lang.org/reference/)** `repr(u8)` 等整型参数强制 enum 的 discriminant 类型为对应整数类型，布局变为 "tag + union" 的固定结构。✅
> **来源: [Rust Reference: Type Layout](https://doc.rust-lang.org/reference/type-layout.html)** `repr(C)` 应用于有数据 enum 时，其布局遵循与 C 兼容的 tagged union 规则，但 C 语言本身无原生 sum type，需谨慎用于 FFI。✅

**`repr(u8)` 与默认布局的对比**：

```rust
enum DefaultEnum {
    A(u8),
    B(u32),
}

#[repr(u8)]
enum ReprEnum {
    A(u8),
    B(u32),
}

use std::mem;

// 默认布局：编译器可能将 tag 嵌入 padding，总大小可能为 8
// repr(u8)：tag 明确占 1 byte，padding 显式存在，总大小通常为 8
println!("DefaultEnum: size={}, align={}", mem::size_of::<DefaultEnum>(), mem::align_of::<DefaultEnum>());
println!("ReprEnum:    size={}, align={}", mem::size_of::<ReprEnum>(), mem::align_of::<ReprEnum>());
```

> **评价**: `#[repr]` 在 FFI 边界是必需的，但在纯 Rust 代码中应谨慎使用——它禁用了编译器的 niche optimization 和 tag packing，可能导致内存膨胀。例如 `Option<&T>` 在 `#[repr(C)]` 下将膨胀为 16 字节（tag + 指针 + padding），而非优化的 8 字节。

#### 11.5.5 `std::mem::Discriminant<T>` 与 `DiscriminantKind`

`Discriminant<T>` 除了通过 `mem::discriminant` 构造外，还可用于**泛型场景**中按 enum 变体做哈希键或集合成员：

```rust,ignore
use std::collections::HashMap;
use std::mem;

// ✅ 按 Message 的变体统计频次（不关心 payload）
let mut counts: HashMap<mem::Discriminant<Message>, usize> = HashMap::new();
let msgs = vec![Message::Quit, Message::Write(String::from("a")), Message::Quit];

for msg in &msgs {
    *counts.entry(mem::discriminant(msg)).or_insert(0) += 1;
}
// counts[discriminant(Message::Quit)] == 2
```

**`DiscriminantKind` trait**（unstable，需 nightly）提供了在泛型上下文中获取类型的 "discriminant 类型" 的能力：

```rust
#![feature(discriminant_kind)]
use std::marker::DiscriminantKind;

// <T as DiscriminantKind>::Discriminant 表示 T 的 discriminant 底层整数类型
// 对 enum 而言，这是编译器用于 tag 的类型；对非 enum 类型通常是 ()
```

> **来源: [Rust Reference: DiscriminantKind](https://doc.rust-lang.org/reference/)** `DiscriminantKind` 是编译器内建 trait，用于支持泛型代码中对 enum 变体类型的元编程。当前仍为 unstable 特性。✅

#### 11.5.6 `mem::size_of` 与 `mem::align_of` 的对比分析

| 函数 | 返回值 | 对 enum 的语义 | 典型用途 |
|:---|:---|:---|:---|
| `size_of::<T>()` | 类型占用的字节数 | tag + payload union + padding 的总和 | 分配内存、FFI 缓冲区大小计算 |
| `align_of::<T>()` | 类型的对齐要求（字节） | `max(align_of(discriminant), align_of(各变体))` | 手动内存对齐、裸指针算术 |
| `size_of_val(&T)` | 具体值的字节数 | 与 `size_of::<T>()` 相同（enum 为 Sized） | 动态分发场景 |
| `align_of_val(&T)` | 具体值的对齐要求 | 与 `align_of::<T>()` 相同 | trait object 等动态场景 |

**枚举（Enum）布局的计算示例**：

```rust
#[repr(u8)]
enum Example {
    A(u8),      // variant size = 1, align = 1
    B(u32),     // variant size = 4, align = 4
    C,          // variant size = 0, align = 1
}

// 计算过程:
// discriminant (u8) = 1 byte, align = 1
// max payload = 4 bytes (B 的 u32), align = 4
// 总对齐 = max(1, 4) = 4
// 原始排列: [tag: 1] + [B: 4] = 5 bytes → 对齐到 4 的倍数 = 8 bytes
// 实际布局: [tag: 1][pad: 3][B: 4] 或编译器可能将 tag 放在尾部

assert_eq!(std::mem::size_of::<Example>(), 8);
assert_eq!(std::mem::align_of::<Example>(), 4);
```

> **来源: [Rust Reference: Type Layout](https://doc.rust-lang.org/reference/type-layout.html)** 类型的对齐要求是其大小必须是该值的整数倍；`align_of::<T>()` 是满足该条件的最小 2 的幂（对大多数基础类型）。✅

**关键差异**：`size_of` 回答"分配多少字节"，`align_of` 回答"起始地址必须是几的倍数"。在 `unsafe` 代码中，两者缺一不可——分配未对齐的内存并构造 enum 属于未定义行为（UB）。

#### 11.5.7 边界极限测试：用 unsafe 窥探原始字节

以下实验通过 `std::mem::transmute` 和裸指针将 enum 解构为字节切片（Slice），直接观察编译器的布局决策。这些代码**仅用于教学目的**，生产代码中不应依赖具体布局。

```rust
use std::mem;

unsafe fn inspect_bytes<T>(name: &str, value: &T) {
    let bytes = std::slice::from_raw_parts(
        value as *const T as *const u8,
        mem::size_of::<T>()
    );
    println!("{} (size={}, align={}): {:02x?}", name, mem::size_of::<T>(), mem::align_of::<T>(), bytes);
}

#[repr(u8)]
enum SmallEnum {
    A = 1,
    B(u16) = 2,
}

fn main() {
    // 测试 1: repr(u8) enum 的显式 tag
    let a = SmallEnum::A;
    let b = SmallEnum::B(0xABCD);
    unsafe {
        inspect_bytes("SmallEnum::A", &a); // 预期: tag=01, 其余为 0 或未初始化
        inspect_bytes("SmallEnum::B(0xABCD)", &b); // 预期: tag=02, payload=cd ab（小端）
    }

    // 测试 2: Option<bool> 的 niche optimization（size = 1）
    let some_true: Option<bool> = Some(true);
    let some_false: Option<bool> = Some(false);
    let none_bool: Option<bool> = None;
    unsafe {
        inspect_bytes("Option<bool>::Some(true)", &some_true);   // 预期: [01]
        inspect_bytes("Option<bool>::Some(false)", &some_false); // 预期: [00]
        inspect_bytes("Option<bool>::None", &none_bool);         // 预期: [02]（或编译器选择的 niche）
    }

    // 测试 3: Option<&u32> 的 NPO（size = 8，无显式 tag）
    let x = 42u32;
    let some_ref: Option<&u32> = Some(&x);
    let none_ref: Option<&u32> = None;
    unsafe {
        inspect_bytes("Option<&u32>::Some", &some_ref); // 预期: 8 字节有效地址（非 0）
        inspect_bytes("Option<&u32>::None", &none_ref); // 预期: [00, 00, 00, 00, 00, 00, 00, 00]
    }

    // 测试 4: Option<Option<&u32>> 无 NPO（size = 16）
    let some_some: Option<Option<&u32>> = Some(Some(&x));
    let some_none: Option<Option<&u32>> = Some(None);
    let none_outer: Option<Option<&u32>> = None;
    unsafe {
        inspect_bytes("Some(Some(&x))", &some_some);
        inspect_bytes("Some(None)", &some_none);
        inspect_bytes("None", &none_outer);
    }
}
```

**预期输出分析**：

| 值 | 预期字节模式 | 说明 |
|:---|:---|:---|
| `SmallEnum::A` | `[01, 00, 00]`（或 `[01, ??, ??]`） | `repr(u8)` 强制 tag=0x01；payload 未初始化区域可能为任意值 |
| `SmallEnum::B(0xABCD)` | `[02, cd, ab]`（小端） | tag=0x02；`u16` payload 按小端存储 |
| `Option<bool>::None` | `[02]` | 编译器选择 `0x02` 作为 `None` 的 niche |
| `Option<&u32>::None` | 全 0 | 64 位 null 指针 |
| `Option<Option<&u32>>::None` | `[00, ..., 00, 01, 00, ..., 00]` | 需显式 tag 区分 `None` 与 `Some(None)`，大小为 16 |

> **来源: [The Rustonomicon: Transmute](https://doc.rust-lang.org/nomicon/)** `std::mem::transmute` 和裸指针转换是观察内存布局的终极工具，但任何对布局的依赖都属于 `unsafe` 合约——编译器版本升级可能改变无 `#[repr]` 类型的布局。✅
> **一致性检查**: §11.5.2 的形式化布局公式与 §11.5.7 的实验代码形成 "理论—实践" 闭环。`#[repr]` 的介入是两者之间的控制变量：无 repr 时理论仅能给出上界，有 repr 时布局精确可预测。
> **来源汇总**:
> [Rust Reference: Enums](https://doc.rust-lang.org/reference/items/enumerations.html) · [Rust Reference: Type Layout](https://doc.rust-lang.org/reference/type-layout.html) · [Rust Reference: repr Attribute](https://doc.rust-lang.org/reference/type-layout.html#representations) ·
> [Rust Reference: std::mem::discriminant](https://doc.rust-lang.org/reference/) · [Rust Reference: DiscriminantKind](https://doc.rust-lang.org/reference/) ·
> [Unsafe Code Guidelines: Enum Layout] · [Unsafe Code Guidelines: Values] ·
> [The Rustonomicon: Exotic Sizes](https://doc.rust-lang.org/nomicon/) · [The Rustonomicon: Transmute](https://doc.rust-lang.org/nomicon/) · [Wikipedia: Tagged union](https://en.wikipedia.org/wiki/Tagged_union)

### 11.6 `union` 的类型安全边界

`union` 允许在同一内存位置存储不同类型（C 兼容），但**所有访问都必须 unsafe**：

```rust
union IntOrFloat {
    i: i32,
    f: f32,
}

let mut u = IntOrFloat { i: 42 };
unsafe {
    assert_eq!(u.i, 42);
    // u.f 也指向同一块内存，但按 f32 解释
}
```

> **边界**：`union` 不自动 drop 未激活的变体，需使用 `ManuallyDrop` 避免双重释放。
> **来源**: [Rust Reference: Unions](https://doc.rust-lang.org/reference/items/unions.html) · [The Rustonomicon: Unions](https://doc.rust-lang.org/nomicon/other-reprs.html)

---

### 11.7 名义类型与结构类型（Nominal vs Structural Typing）

> **Bloom 层级**: 理解 → 分析 → 评价
> 类型等价（type equivalence）是类型系统的核心问题：
> 两个类型"相同"意味着什么？名义类型系统（Nominal Typing）以**显式声明的名称**作为类型身份的判据；
> 结构类型系统（Structural Typing）以**内存布局与成员结构**作为类型身份的判据。
> Rust 并非纯粹的名义或结构系统，而是在不同构造上呈现独特的**类型二元性**——理解这种二元性，是掌握 Rust 类型系统设计哲学、一致性（coherence）规则与 FFI 边界的关键。
> **交叉链接**:
> [L2 Trait: 一致性规则](../02_intermediate/01_traits.md) ·
> [L2 泛型: Variance](../02_intermediate/02_generics.md) ·
> [L3 Unsafe: 裸指针与类型双关](../03_advanced/03_unsafe.md) ·
> [L4 形式化: 子类型关系](../04_formal/02_type_theory.md)

#### 11.7.1 定义与形式化区分

> **来源: [Wikipedia — Nominal type system](https://en.wikipedia.org/wiki/Nominal_type_system)**
> 在名义类型系统中，两种类型相等当且仅当它们具有相同的显式名称（name）；子类型关系也必须显式声明（如 `class A extends B`）。✅
> **来源: [Wikipedia — Structural type system](https://en.wikipedia.org/wiki/Structural_type_system)**
> 在结构类型系统中，两种类型相等当且仅当它们具有兼容的结构（structure）；子类型关系由成员集合的包含关系自动推导。✅
> **[来源: Pierce, *Types and Programming Languages* (TAPL), Ch.15]**
> "Nominal type systems associate types with names; structural type systems associate types with shapes." 名义系统将类型与名称绑定，结构系统将类型与形状绑定。✅
> **[来源: TypeScript Handbook — Structural Type System]**
> TypeScript 使用结构类型系统："The basic rule for TypeScript's structural type system is that `x` is compatible with `y` if `y` has at least the same members as `x`." ✅

形式化区分：

```text
名义类型等价（Nominal Equivalence）:
  Γ ⊢ type A = ...
  Γ ⊢ type B = ...
  ─────────────────────────────
  A ≡ B  ⟺  name(A) = name(B)

结构类型等价（Structural Equivalence）:
  struct(A) = { f₁: T₁, f₂: T₂, ... }
  struct(B) = { f₁: T₁, f₂: T₂, ... }
  ─────────────────────────────
  A ≡ B  ⟺  struct(A) = struct(B)   （成员名称与类型均匹配）
```

**关键差异**：
名义类型的身份由**声明位置**决定；结构类型的身份由**成员集合**决定。
在名义系统中，即使两个类型的内存布局完全相同，只要名称不同，它们就是不兼容的；在结构系统中，只要布局相同，无论名称如何，它们就是兼容的。

> **[来源: Cardelli & Wegner 1985, *On Understanding Types, Data Abstraction, and Polymorphism*]** 名义类型与结构类型的区分是类型系统设计的首要决策之一，它深刻影响语言的模块（Module）化、演化能力与类型检查算法。✅

---

#### 11.7.2 Rust 的类型二元性：名义与结构并存

Rust 并非纯粹的名义类型系统，也非纯粹的结构类型系统。
它在不同语法构造上呈现**不对称的二元性**：

| **构造** | **类型判别方式** | **说明** |
| :--- | :--- | :--- |
| `struct S { ... }` | **名义** | 必须显式声明名称，`S` 的身份由名称决定 |
| `enum E { ... }` | **名义** | 变体名称是类型的身份标识 |
| `trait Tr { ... }` | **名义** | 必须显式 `impl Tr for T`，无法自动推导 |
| `(T, U)` 元组 | **结构** | 身份由成员类型序列决定，无名称约束 |
| `[T; N]` 数组 | **结构** | 身份由元素类型与长度决定 |
| `fn(T) -> U` | **结构** | 函数指针类型由参数与返回类型决定 |
| 生命周期 `'a` | **结构** | 子类型关系由生命周期区域的包含关系决定 |

> **来源: Rust Reference: Types** Rust 的 `struct`、`enum`、`trait` 均为名义类型构造；元组、数组、函数指针、切片（Slice）为结构类型构造。✅

**不对称性：名义包装与结构原型的共存**:

Rust 中存在一组有趣的"名义—结构配对"：

```rust
// ✅ 名义版本：单元结构体
struct UnitA;
struct UnitB;

// 结构版本：单元类型
let unit: () = ();

// ✅ 名义版本：元组结构体
struct Point(f64, f64);
struct Vector(f64, f64);

// 结构版本：匿名元组
let tuple: (f64, f64) = (1.0, 2.0);

// ✅ 名义版本：记录结构体
struct Point2D { x: f64, y: f64 }
struct Vector2D { x: f64, y: f64 }

// ❌ 结构版本：记录结构体**没有**对应的匿名结构类型
// Rust 不支持 { x: f64, y: f64 } 作为独立类型
```

> **[来源: [RFC 2584](https://github.com/rust-lang/rfcs/pull/2584): Structural Records (closed)]**
> Centril 提出的 Structural Records RFC 试图为 Rust 引入匿名记录类型 `{ x: f64, y: f64 }`，但该 RFC 已被关闭（postponed/closed）。
> 这意味着 Rust 设计者**刻意保留了记录结构体（Struct）的名义性**——记录字段的命名是类型身份的一部分，不可通过结构等价绕过。✅

**关键洞察**：单元类型 `()` 和元组类型 `(T, U)` 既有名义包装（`struct Unit;`、`struct T(A, B)`）又有结构原型（`()`、`(A, B)`），但**记录结构体 `struct T { a: A }` 只有名义形式**。这种不对称性反映了 Rust 的设计哲学：

- **简单组合**（元组、数组）使用结构类型，降低语法开销；
- **语义命名**（记录字段）使用名义类型，强制显式契约；
- **行为抽象**（trait）使用名义类型，确保一致性（coherence）可判定。

```mermaid
graph TD
    A[Rust 类型构造] --> B[名义类型]
    A --> C[结构类型]

    B --> B1["struct S { a: A }<br/>记录结构体：无结构对应"]
    B --> B2["struct S(T, U)<br/>元组结构体：有结构对应"]
    B --> B3[struct S;<br/>单元结构体：有结构对应]
    B --> B4["enum E { ... }<br/>枚举：无结构对应"]
    B --> B5["trait Tr { ... }<br/>Trait：无结构对应"]

    C --> C1["(T, U)<br/>元组"]
    C --> C2["[T; N]<br/>数组"]
    C --> C3["fn(T) -> U<br/>函数指针"]
    C --> C4['a, 'static<br/>生命周期]

    B1 -.-> D["不对称性<br/>记录无结构 counterpart"]
    C1 -.-> D
```

> **认知功能**: 此图揭示了 Rust 类型系统的"分裂性格"。关键认知：**不是所有构造都有名义/结构双版本**。
> 记录结构体的纯粹名义性是有意的设计——它防止了"意外类型等价"（accidental type equivalence），确保 API 契约的显式性。
> 元组结构体虽然可以模拟结构类型（`(f64, f64)` 与 `Point(f64, f64)` 布局相同），但 `Point` 和 `Vector` 因名称不同而互不兼容，这正是名义类型的保护作用。 [来源: 💡 原创分析]

---

#### 11.7.3 内部二元性：生命周期子类型化的结构本质

Rust 的类型系统中最容易被忽视的二元性体现在**生命周期子类型化**中：

```text
生命周期子类型规则（结构子类型）:
  'long <: 'short  ⟺  lifetime('long) ⊇ lifetime('short)

即：生命周期 'a 是 'b 的子类型，当且仅当 'a 的存活区域包含 'b 的存活区域。
```

> **来源: [Rust Reference: Subtyping](https://doc.rust-lang.org/reference/subtyping.html)** "Lifetime parameters are covariant: `'long` is a subtype of `'short` if `'long` outlives `'short`." 生命周期参数具有协变性，子类型关系由区域的包含关系（结构特征）决定。✅
> **来源: [The Rustonomicon: Variance](https://doc.rust-lang.org/nomicon/)** Rust 的 variance 系统决定了泛型参数在何种方向上保持子类型关系。生命周期是唯一在 Rust 中显式展示结构子类型的机制。✅

这种**内部二元性**意味着：

- `struct`、`enum`、`trait` 的等价与实现关系是**名义的**（必须显式声明）；
- 生命周期的包含关系是**结构的**（由区域集合的数学关系自动推导）。

**定理：Rust 是混合型类型系统**:

```text
定理 T4: Rust 的类型判别机制是名义—结构混合体
  前提: struct/enum/trait 使用名义等价（由名称决定）
  前提: tuple/array/fn pointer 使用结构等价（由形状决定）
  前提: lifetime 使用结构子类型（由区域包含关系决定）
    ↓
  结论: Rust 不是纯粹的名义系统，也不是纯粹的结构系统
    ↓
  ⟹ 编程者必须在不同构造上切换"名义思维"与"结构思维"
```

```rust
// 结构子类型的体现：生命周期协变
fn borrow_long<'long>(s: &'long str) {
    // 'long 可以自动降级为 'short
    fn inner<'short>(t: &'short str) {}
    inner(s);  // ✅ 'long <: 'short，自动协变
}

// 名义类型的体现：struct 不自动等价
struct Meters(f64);
struct Feet(f64);

fn use_meters(m: Meters) {}

let f = Feet(3.28);
// use_meters(f);  // ❌ 编译错误：Meters 与 Feet 不兼容
```

> **关键洞察**: 生命周期子类型化的结构性是 Rust 借用（Borrowing）检查器的数学基础——它不需要程序员显式声明 `'long extends 'short`，编译器自动从代码的作用域结构中推导区域包含关系。这与 `trait` 实现形成鲜明对比：你必须写 `impl Trait for T`，编译器不会自动"发现"某个类型满足某个 trait。

---

#### 11.7.4 幻影类型与新类型惯用法：名义类型的零成本抽象

Rust 的名义类型系统被刻意用于**零成本抽象（Zero-Cost Abstraction）**——通过新类型（Newtype）模式为相同底层结构赋予不同的语义身份：

```rust
// ✅ 新类型模式：相同结构，不同身份
struct Kilometers(f64);
struct Miles(f64);

// 两者在内存中完全相同（大小 = 8 bytes，对齐 = 8），但类型不兼容
fn distance_km(d: Kilometers) -> f64 { d.0 }
fn distance_mi(d: Miles) -> f64 { d.0 }

let k = Kilometers(5.0);
let m = Miles(3.1);

distance_km(k);  // ✅
// distance_km(m);  // ❌ 编译错误：类型不匹配
```

> **来源: [TRPL Ch19.3](https://doc.rust-lang.org/book/title-page.html)** "The newtype pattern is useful for tasks like ensuring type safety and encapsulation... A tuple struct with a single field is a newtype pattern." ✅

**幻影数据（PhantomData）与方差控制**:

`PhantomData<T>` 是名义类型系统的极致应用——它在运行时不占任何空间，但在编译期携带类型信息，控制泛型参数的 variance：

```rust
use std::marker::PhantomData;

// ✅ 名义标记：Vec<T> 的所有权句柄，零运行时开销
struct VecHandle<T> {
    ptr: *mut T,
    len: usize,
    cap: usize,
    _marker: PhantomData<T>,  // 告诉编译器：此结构逻辑上拥有 T
}

// PhantomData<T> 使 VecHandle<T> 对 T 协变
// 这允许 VecHandle<&'static str> 作为 VecHandle<&'a str> 使用
```

> **来源: [Rust Reference: PhantomData](https://doc.rust-lang.org/reference/)** `PhantomData<T>` 是零大小类型（ZST），用于影响编译期的类型检查行为（如 drop check、auto trait 推导、variance）。✅

**定理：新类型模式的零成本性**:

```text
定理 T5: 新类型模式（Newtype）具有零运行时成本
  前提: struct Kilometers(f64) 与 f64 的内存布局完全相同
  前提: PhantomData<T> 的大小为 0
    ↓
  结论: 名义区分在编译后完全消除
    ↓
  ⟹ 程序员获得类型安全的同时不支付运行时代价
```

> **来源: [Rust Reference: Type Layout](https://doc.rust-lang.org/reference/type-layout.html)** 单字段元组结构体的布局与其字段类型相同（`#[repr(Rust)]` 下的当前保证）。✅
> **来源: [The Rustonomicon: PhantomData](https://doc.rust-lang.org/nomicon/)** PhantomData 是"名义类型系统的幽灵杠杆"——它不产生代码，但改变编译器的类型推导路径。✅

---

#### 11.7.5 一致性规则与名义类型的深层绑定

Rust 的**一致性规则（Orphan Rules）**从根本上依赖于名义类型：

```text
一致性规则（简化）:
  可以写 impl Trait for Type 当且仅当：
    - 当前 crate 定义了 Trait，或
    - 当前 crate 定义了 Type

即：不能为"别人的 trait"和"别人的类型"同时写实现。
```

> **来源: [Rust Reference: Orphan Rules](https://doc.rust-lang.org/reference/)** "An impl is valid only if either the trait or the type is local to the current crate." ✅
> **[来源: [RFC 1023](https://rust-lang.github.io/rfcs//1023-rebalancing-coherence.html): Rebalancing Coherence]** 一致性规则的设计目标是防止「重叠实现（overlapping impls）」，确保 trait 解析在编译期是确定性的。✅

为什么一致性规则**必须**依赖名义类型？

```text
反事实推理：假设 Rust 使用纯结构类型系统
  - 在结构系统中，类型由成员集合唯一确定
  - 两个 crate 可以独立定义「成员相同但名称不同」的结构类型
  - 如果允许为「结构等价」的外部类型写 impl，则两个 crate 可能为同一结构写重叠 impl
  - 结果：trait 解析出现歧义，编译器无法确定使用哪个实现
  - 结论：结构类型系统与全局一致性（global coherence）不兼容
```

**推论：名义身份是全局一致性的前提**:

```text
推论 C1: 一致性规则要求类型具有全局唯一的名义身份
  前提: 结构等价允许「不同名称、相同结构」的类型被视为等价
  前提: trait 解析需要全局无歧义（coherence）
    ↓
  结论: 若 Rust 使用纯结构类型系统，则 coherence 无法保证
    ↓
  ⟹ Rust 对 struct/enum/trait 采用名义类型是 coherence 的必然要求
```

```rust
// 一致性规则的实际影响
// Crate A 定义了 trait Display（标准库）
// Crate B 定义了 struct MyInt(i32)
// Crate C 可以为 MyInt 实现 Display（拥有 MyInt）
// Crate C 不能为 i32 实现 Display（都不拥有）

// 这是名义系统的保护：i32 的身份是全局固定的（标准库所有）
// 若 i32 的结构等价于 "相同位模式的自定义类型"，
// 则 coherence 将因「谁有权实现 trait」而崩溃
```

> **[来源: Rust Internals — Blog: "Coherence in Rust"]** 名义类型的全局唯一身份使得编译器可以在 crate 边界上做出「是否存在重叠 impl」的确定性判断。✅ 二级来源

---

#### 11.7.6 FFI 翻译中的类型范式冲突

从 C 翻译到 Rust 时，名义类型与结构类型的冲突产生深刻的工程影响。C 的 `struct` 在语义上更接近**结构类型**（C 编译器允许隐式类型转换和类型双关），而 Rust 的 `struct` 是**名义类型**。

> **[来源: arXiv:2412.15042 — *Compiling C to Safe Rust, Formalized*]**
> "Nominal typing 'sets in stone' representation and mutability, causing 'contamination' when translating from C structs.
> A C struct with mixed read/write fields becomes a Rust struct where mutability is fixed at declaration." ✅

**C 到 Rust 的翻译困境**：

```c
// C: 结构类型思维——内存块可以按需读写
typedef struct {
    int x;      // 有时只读
    int y;      // 有时读写
} Point;

void read_only(const Point* p) { /* 只读访问 p->x, p->y */ }
void read_write(Point* p) { p->x = 0; p->y = 0; }
```

```rust
// Rust 翻译：名义类型思维——mutability 固定在声明处
// 方案 A: 全部不可变（丢失写能力）
struct PointImm { x: i32, y: i32 }

// 方案 B: 全部可变（丢失只读保证）
struct PointMut { x: i32, y: i32 }

// 方案 C: 拆分结构（增加 API 复杂度）
struct PointRead { x: i32, y: i32 }
struct PointWrite { x: i32, y: i32 }
```

> **[来源: arXiv:2412.15042]** C 的 `const Point*` 是「调用时决定的只读视图」，Rust 的 `&Point` vs `&mut Point` 是「类型声明时固定的所有权状态」。这种差异导致 C→Rust 自动化翻译必须做「污染性选择」——要么保守地全部标记为 mutable，要么激进地拆分类型，两者都有代价。✅

**形式化表达**：

```text
C 结构类型的灵活性:
  const Point* p  ≡  p 指向的内存是只读的（调用时决定）
  Point* p        ≡  p 指向的内存是可写的（调用时决定）

Rust 名义类型的刚性:
  &Point          ≡  Point 本身在声明时就是不可变的借用它
  &mut Point      ≡  Point 本身在声明时就是通过可变引用借用它

关键差异: C 的 const 是「视图属性」；Rust 的 &/&mut 是「类型身份的一部分」
```

---

#### 11.7.7 跨语言对比表

| **维度** | **Rust** | **TypeScript** | **Go** | **Haskell** | **C++ (Concepts)** |
|:---|:---|:---|:---|:---|:---|
| **基本对象类型** | 名义（`struct`） | 结构（shape） | 名义（`struct`） | 名义（`data`） | 名义（`class`/`struct`） |
| **接口/行为抽象** | 名义（`trait`，需显式 `impl`） | 结构（duck typing） | **结构**（interface 自动满足） | 名义（Type Class，需显式 `instance`） | 结构（Concepts / SFINAE） |
| **函数类型** | 结构（`fn(T) -> U`） | 结构 | 无独立函数类型 | 结构（`a -> b`） | 结构（函数指针） |
| **元组/数组** | 结构 | 结构 | 结构（slice 接口） | 结构 | 结构（`std::tuple`） |
| **生命周期/子类型** | **结构**（区域包含） | N/A | N/A | N/A | N/A |
| **新类型支持** | ✅ 原生（tuple struct） | ⚠️ 需 branded type | ❌ 无 | ✅ `newtype` | ✅ 强类型别名 / wrapper |
| **一致性保证** | ✅ 全局 coherence | ❌ 无（运行时才知） | ⚠️ 运行时 panic | ✅ 全局 coherence | ⚠️ 模板实例化歧义 |
| **FFI 友好性** | ⚠️ 名义刚性导致翻译困难 | N/A | ⚠️ 名义 + 结构混合 | ⚠️ 名义 | ⚠️ 名义 |

> **[来源: TypeScript Handbook]** TypeScript 的接口是纯粹结构的——只要对象满足接口的 shape，就自动兼容，无需显式声明 `implements`。✅ 三级来源
> **[来源: Go Language Specification]** Go 的 interface 是结构类型的典型代表：类型自动满足 interface，只要它实现了所有方法。✅ 三级来源
> **[来源: Haskell 2010 Report]** Haskell 的 Type Class 需要显式 `instance` 声明，与 Rust trait 同为名义系统。✅ 一级来源
> **[来源: C++20 Concepts]** C++20 Concepts 是结构类型的回归：模板约束由「类型是否满足 expression 要求」自动判定，无需显式「实现」某个 concept。✅ 一级来源

**关键观察**：

- **TypeScript 与 Go** 在接口/行为层使用结构类型，降低了「适配成本」，但牺牲了编译期一致性保证；
- **Haskell 与 Rust** 在行为抽象层使用名义类型（Type Class / Trait），确保了全局 coherence，但增加了「为外部类型实现接口」的摩擦；
- **Rust 的独特性**：它是唯一在**生命周期子类型化**中使用结构类型、同时在**trait 实现**中使用名义类型的语言。这种二元性是 Rust 类型系统的核心张力。

---

#### 11.7.8 反命题与边界分析

> **Bloom 层级**: 评价

##### 命题 1: "名义类型阻止了所有非预期的类型等价"

```mermaid
graph TD
    P["命题: 名义类型阻止所有非预期等价"] --> Q1{"涉及 struct/enum/trait?"}
    Q1 -->|是| T1["定理成立: 名称不同 ⟹ 不兼容<br/>✅ 新类型模式保护"]
    Q1 -->|否| Q2{"涉及 tuple/array/fn pointer?"}
    Q2 -->|是| F1["反例: (i32, i32) 与 Point(i32, i32) 名义不同<br/>但可通过 .0/.1 结构兼容（非自动，但可转换）"]
    Q2 -->|否| Q3{"涉及生命周期?"}
    Q3 -->|是| F2["反例: 'static 与 'a 名义不同<br/>但 'static <: 'a 自动成立（结构子类型）"]
    Q3 -->|否| T2["超出 Rust 类型系统范围"]

    style T1 fill:#6f6
    style F1 fill:#f96
    style F2 fill:#f96
    style T2 fill:#6f6
```

> **认知功能**: 此命题的 falsification 揭示了 Rust 类型二元性的本质。关键认知：**名义类型并非无处不在**。在 tuple、array、function pointer 和 lifetime 领域，结构等价仍然发挥作用。程序员不能简单地认为"只要名字不同就一定安全"——必须区分当前操作的是名义构造还是结构构造。 [来源: 💡 原创分析]

**判定**: **FALSE**（假）。名义类型仅覆盖 `struct`/`enum`/`trait`，元组、数组、函数指针和生命周期仍遵循结构规则。

##### 命题 2: "结构类型系统可以解决孤儿规则（Orphan Rule）的问题"

```mermaid
graph TD
    P["命题: 结构类型解决孤儿规则问题"] --> Q1{"保留全局 coherence?"}
    Q1 -->|是| F1["反例: 两个 crate 独立为结构等价的类型写 impl<br/>→ 重叠 impl 无法避免（coherence 崩溃）"]
    Q1 -->|否| Q2{"允许运行时歧义解析?"}
    Q2 -->|是| F2["反例: 类型检查不再静态确定<br/>→ 失去 Rust 核心保证（编译期解析）"]
    Q2 -->|否| T1["放弃 trait 系统，改用其他机制<br/>→ 不再是 Rust"]

    style F1 fill:#f66
    style F2 fill:#f66
    style T1 fill:#f96
```

> **认知功能**:
> 此命题是对「结构类型更灵活」直觉的形式化检验。关键认知：孤儿规则（Orphan Rule）的约束**不是实现上的偶然**，而是**名义类型与全局 coherence 之间的逻辑必然**。
> 结构类型允许「不同名称、相同结构」的类型存在，这使得「谁有权为类型实现 trait」成为不可判定问题。
> TypeScript 放弃全局 coherence（接口兼容是运行时的），Go 通过运行时 panic 处理歧义——Rust 选择名义类型来保持编译期确定性。
> [来源: 💡 原创分析]

**判定**: **FALSE**（假）。结构类型与全局 coherence 不兼容；若采用结构类型，要么放弃 coherence（TypeScript 模式），要么引入运行时歧义（Go 模式）。

##### 命题 3: "新类型模式（Newtype）具有零运行时成本"

```mermaid
graph TD
    P["命题: 新类型模式零运行时成本"] --> Q1{"单字段元组结构体?"}
    Q1 -->|是| Q2{"#[repr(Rust)] 默认布局?"}
    Q2 -->|是| T1["定理成立: 布局同构于底层类型<br/>✅ size_of::<Newtype>() == size_of::<Inner>()"]
    Q2 -->|否| F1["反例: #[repr(C)] 可能引入不同 ABI 要求<br/>→ 需显式保证"]
    Q1 -->|否| Q3{"多字段新类型?"}
    Q3 -->|是| F2["反例: 多字段 struct 有独立布局<br/>→ 非零成本（但非新类型模式本意）"]

    style T1 fill:#6f6
    style F1 fill:#f96
    style F2 fill:#f96
```

**判定**: **TRUE**（真），在 `#[repr(Rust)]` 单字段元组结构体的条件下。

```rust
use std::mem;

struct Kilometers(f64);
struct Miles(f64);

fn main() {
    assert_eq!(mem::size_of::<Kilometers>(), mem::size_of::<f64>());
    assert_eq!(mem::size_of::<Miles>(), mem::size_of::<f64>());
    assert_eq!(mem::align_of::<Kilometers>(), mem::align_of::<f64>());
    // ✅ 零成本验证：新类型在内存中完全等同于底层类型
}
```

> **来源: [Rust Reference: Type Layout](https://doc.rust-lang.org/reference/type-layout.html)** "A tuple struct with a single field has the same layout as its field." ✅

---

#### 11.7.9 认知路径：何时名义、何时结构

> **Bloom 层级**: 理解 → 分析

Rust 编程者需要建立**双模式认知框架**，在不同场景下切换名义思维与结构思维：

| **场景** | **思维模型** | **检查清单** |
|:---|:---|:---|
| 定义 `struct` / `enum` | **名义思维** | 「这个名字是否准确表达了语义？」 |
| 实现 `trait` | **名义思维** | 「我是否有权为这个类型实现这个 trait？（一致性规则）」 |
| 编写泛型约束 `<T: Trait>` | **名义思维** | 「Trait bound 是否足够精确，避免意外类型满足？」 |
| 使用元组 `(T, U)` | **结构思维** | 「成员的顺序和类型是否匹配？」 |
| 传递函数指针 `fn(T) -> U` | **结构思维** | 「参数和返回类型的签名是否兼容？」 |
| 标注生命周期 `&'a T` | **结构思维** | 「引用存活区域是否包含被引用的数据区域？」 |
| FFI 翻译 C `struct` | **范式冲突** | 「C 的灵活 mutability 如何在 Rust 的名义 rigid 中表达？」 |

**六步认知路径**：

**Step 1: 直觉困惑** — "为什么我不能把 `Feet` 传给需要 `Meters` 的函数？它们都是 `f64`！"
> 困惑根源：将类型视为「内存布局」，而非「语义契约」。名义类型强制你认识到：**类型的身份独立于其表示**。

**Step 2: 具体场景** — 混合使用 `Meters` 和 `Feet` 导致火星气候轨道器（Mars Climate Orbiter）式的单位灾难。新类型模式在编译期消除了这种错误。

**Step 3: 模式抽象** — 「名义 = 语义契约 + 编译期强制」；「结构 = 形状兼容 + 自动推导」。Rust 在「需要强制契约」处使用名义，在「需要便捷组合」处使用结构。

**Step 4: 形式规则** — 名义类型的等价规则：`S₁ ≡ S₂ ⟺ name(S₁) = name(S₂)`。结构类型的等价规则：`T₁ ≡ T₂ ⟺ fields(T₁) = fields(T₂)`。Rust 的混合规则：不同构造使用不同的等价判据。

**Step 5: 代码验证** — 尝试为外部类型实现外部 trait（违反孤儿规则（Orphan Rule）），观察编译器错误 E0117/E0210；尝试将 `Kilometers` 传给 `Miles` 参数，观察类型不匹配错误。这些错误不是限制，而是「名义身份保护」的证据。

**Step 6: 边界测试** — 在 FFI 边界测试 `#[repr(C)] struct` 与 C 结构体的布局兼容性；测试 `PhantomData<T>` 对 Send/Sync 推导的影响；测试生命周期协变在嵌套泛型中的传播行为。

> **来源**:
> [Rust Reference: Subtyping](https://doc.rust-lang.org/reference/subtyping.html) ·
> [Rust Reference: Variance](https://doc.rust-lang.org/reference/) ·
> [Rust Reference: PhantomData](https://doc.rust-lang.org/reference/special-types-and-traits.html) ·
> [Rustonomicon: PhantomData](https://doc.rust-lang.org/nomicon/) ·
> [RFC 2584: Structural Records](https://github.com/rust-lang/rfcs/pull/2584) ·
> [RFC 1023: Rebalancing Coherence](https://rust-lang.github.io/rfcs/1023-rebalancing-coherence.html) ·
> [arXiv:2412.15042] ·
> [Pierce, TAPL, Ch.15] ·
> [Wikipedia: Nominal type system](https://en.wikipedia.org/wiki/Nominal_type_system) ·
> [Wikipedia: Structural type system](https://en.wikipedia.org/wiki/Structural_type_system) ·
> [TypeScript Handbook: Structural Type System]

---

### 11.7.10 与多级引用语义的交叉：引用的名义与结构行为

> **Bloom 层级**: 分析

引用类型 `&T` 和 `&mut T` 本身是**结构构造**（structural construction）——它们由引用构造子 `&` / `&mut` 与目标类型 `T` 组合而成，不依赖类型名称。然而，引用类型的**等价性**却同时受名义与结构两股力量的支配：

**结构行为（引用构造层面）**：

```rust,compile_fail
let r1: &i32 = &42;
let r2: &&i32 = &r1;   // ✅ 结构组合：& 构造子嵌套
let r3: &mut &i32 = &mut r1; // ❌ 错误：r1 不是 mut 绑定
```

- `&` 和 `&mut` 作为类型构造子是**结构的**：`&T` 的兼容性由 "是否是引用" 决定，不由名称决定。
- 引用弱化 `&mut T → &T` 也是**结构的**：这是引用构造子自身的性质，与 `T` 是否名义无关。
- 生命周期子类型化 `&'a T <: &'b T`（当 `'a: 'b`）同样是**结构的**：由生命周期区域的包含关系决定。

**名义行为（目标类型层面）**：

```rust
struct Meters(f64);
struct Feet(f64);

let m: &Meters = &Meters(3.0);
// let f: &Feet = m;           // ❌ 错误：&Meters 与 &Feet 不等价
// 即使 Meters 和 Feet 内部都是 f64，名称不同导致 &Meters ≠ &Feet
```

- `&T` 的等价性**继承** `T` 的等价性：若 `T` 是名义类型（如 `struct Meters(f64)`），则 `&T` 也是名义区分的。
- 这意味着：**引用构造是结构的，但引用的身份是名义的**——当目标类型具有名义身份时，引用也随之获得名义身份。

**交叉边界定理**：

> **定理 T6（引用的混合等价性）**：在 Rust 中，`&T₁ ≡ &T₂` 当且仅当 `T₁ ≡ T₂` **且** 生命周期约束相容。其中 `T₁ ≡ T₂` 的判定取决于 `T` 自身的类型系统类别（名义或结构）。引用构造子 `&` 本身不引入额外的名义约束，但也不消除目标类型的名义约束。
> **推论 C2**：`&mut T → &T` 的弱化在所有 `T` 上成立，无论 `T` 是名义还是结构类型。这是因为弱化是引用构造子的结构性质，与目标类型无关。
> **推论 C3**：多级引用 `&&T` 的自动解引用链深度由**结构规则**控制（编译期确定），但每一层解引用后的类型等价性仍受**目标类型的名义/结构性质**约束。

```rust
// 结构行为示例：元组引用可以跨名称兼容
let t: &(i32, i32) = &(1, 2);
let u: &(i32, i32) = t;  // ✅ 结构等价

// 名义行为示例：新类型引用不兼容
struct Point(i32, i32);
let p: &Point = &Point(1, 2);
// let q: &(i32, i32) = p;  // ❌ 名义不等价
```

> **分析**: 这一交叉点揭示了 Rust 类型系统的**层次化设计**：外层构造（引用、生命周期、泛型参数）倾向于结构规则以提供灵活性；内层原子类型（struct、enum、trait）倾向于名义规则以提供安全性与一致性。
> [来源: [Rust Reference: Types](https://doc.rust-lang.org/reference/types.html) · [Rust Reference: Subtyping](https://doc.rust-lang.org/reference/subtyping.html) · [Rust Reference: Type Coercions](https://doc.rust-lang.org/reference/)]（一级来源）
> **与多级引用语义的关联**: 详见 `05_reference_semantics.md` §七 对 `&mut &T`、`&&mut T` 及 partial reborrow 的深度分析——其中外层引用的可变性遵循结构规则，而内层引用的目标类型遵循名义或结构规则，两者的交互决定了复杂借用（Borrowing）场景的类型检查行为。

---

## 十二、待补充与演进方向（TODOs）

- [x] **TODO**: 补充 `impl Trait` 与 `dyn Trait` 的类型论差异 —— 优先级: 高 —— 已完成 v1.2
- [x] **TODO**: 补充 `!` (Never type) 的完整形式化分析与控制流图交互 —— 优先级: 中 —— 已完成 §11.1
- [x] **TODO**: 补充 Const Generics（常量泛型）的类型系统扩展 —— 优先级: 中 —— 已完成 §11.3
- [x] **TODO**: 补充 Type Inference 的 HM 算法完整规则与 Rust 扩展 —— 优先级: 低 —— 已完成 §11.4 —— 2026-05-14
- [x] **TODO**: 补充 Zero-sized types (ZST) 和 PhantomData 的类型论意义 —— 优先级: 中 —— 已完成 §11.2
- [x] **TODO**: 补充 Discriminant 和内存布局的底层分析 —— 优先级: 低 —— 已完成 §11.5 —— 2026-05-14
- [x] **TODO**: 补充 `union` 的类型安全边界与使用模式 —— 优先级: 低 —— 已完成 §11.6
- [x] **TODO**: 补充名义类型与结构类型（Nominal vs Structural Typing）的完整分析 —— 优先级: 高 —— 已完成 §11.7 —— 2026-05-22

---

---

## Wikipedia 概念对齐

> **来源: [Wikipedia](https://en.wikipedia.org/wiki/Main_Page)** 核心概念与国际知识库映射。

| 概念 | Wikipedia 词条 | 说明 |
|:---|:---|:---|
| **Type system** | [Type system](https://en.wikipedia.org/wiki/Type_system) | 类型系统 |
| **Hindley–Milner type system** | [Hindley–Milner type system](https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system) | HM 类型推断 |
| **Algebraic data type** | [Algebraic data type](https://en.wikipedia.org/wiki/Algebraic_data_type) | 代数数据类型 |
| **Pattern matching** | [Pattern matching](https://en.wikipedia.org/wiki/Pattern_matching) | 模式匹配 |
| **Trait (computer programming)** | [Trait (computer programming)](https://en.wikipedia.org/wiki/Trait_(computer_programming)) | Trait 系统 |
| **Structural type system** | [Structural type system](https://en.wikipedia.org/wiki/Structural_type_system) | 结构类型 |
| **Nominal type system** | [Nominal type system](https://en.wikipedia.org/wiki/Nominal_type_system) | 名义类型 |

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/title-page.html), [Rustonomicon](https://doc.rust-lang.org/nomicon/)
> **权威来源对齐变更日志**: 2026-05-19 补全权威来源标注（Rust Reference、TRPL、Rustonomicon、RFCs、学术论文） [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 权威来源索引

## 十二、边界测试：类型系统的编译错误

### 12.1 边界测试：类型不匹配（编译错误）

```rust,compile_fail
fn main() {
    let x: i32 = 42;
    let y: f64 = x; // ❌ 编译错误: expected `f64`, found `i32`
    // Rust 不允许隐式类型转换
}

// 正确: 显式转换
fn main_fixed() {
    let x: i32 = 42;
    let y: f64 = x as f64; // ✅ 显式 cast
}
```

> **修正**: Rust 禁止隐式类型转换，必须显式使用 `as` 或 `From`/`Into` trait。

### 12.2 边界测试：泛型约束不满足（编译错误）

```rust,compile_fail
fn print_debug<T>(x: T) {
    // ❌ 编译错误: `T` doesn't implement `Debug`
    println!("{:?}", x); // 需要 T: Debug
}

// 正确: 添加 trait bound
fn print_debug_fixed<T: std::fmt::Debug>(x: T) {
    println!("{:?}", x); // ✅ T 满足 Debug bound
}
```

> **修正**: 泛型函数使用 trait 方法时，必须在泛型参数上声明对应的 trait bound。

### 12.3 边界测试：match 非穷尽（编译错误）

```rust,compile_fail
enum Color { Red, Green, Blue }

fn color_name(c: Color) -> &'static str {
    match c {
        Color::Red => "red",
        Color::Green => "green",
        // ❌ 编译错误: non-exhaustive patterns: `Blue` not covered
    }
}

// 正确: 穷尽所有变体
fn color_name_fixed(c: Color) -> &'static str {
    match c {
        Color::Red => "red",
        Color::Green => "green",
        Color::Blue => "blue",
    }
}
```

> **修正**: Rust 的 `match` 必须覆盖所有可能变体。使用 `_ =>` 作为通配分支（但可能隐藏 bug）。

### 12.4 边界测试：impl Trait 在参数位置与返回位置的差异（编译错误）

```rust,compile_fail
// ❌ 编译错误: `impl Trait` 只能用于函数参数和返回类型，不能用于变量/字段类型
struct Container {
    items: impl Iterator<Item = i32>, // ❌ 结构体字段不允许 impl Trait
}

// 正确: 使用泛型参数
struct GoodContainer<T: Iterator<Item = i32>> {
    items: T,
}

// 或: 使用 trait 对象
struct DynContainer {
    items: Box<dyn Iterator<Item = i32>>,
}
```

> **修正**: `impl Trait` 在参数位置等价于匿名泛型参数，每个 `impl Trait` 参数独立。这意味着两个 `impl Iterator` 参数是**不同类型**，不能假设它们相同。返回位置的 `impl Trait` 则表示"某个实现该 trait 的具体类型"。[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]

### 12.5 边界测试：生命周期省略规则失效（编译错误）

```rust,compile_fail
fn longest(x: &str, y: &str) -> &str {
    // ❌ 编译错误: missing lifetime specifier
    if x.len() > y.len() { x } else { y }
    // 编译器无法推断返回的生命周期与哪个参数关联
}

// 正确: 显式标注生命周期
fn longest_fixed<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y } // ✅ 返回生命周期 'a 覆盖两个参数
}
```

> **修正**: 生命周期省略规则（lifetime elision）仅适用于简单模式（单个输入引用 → 输出引用与其相同）。当存在多个输入引用且输出引用需要与其中某个关联时，必须显式标注生命周期。省略规则不适用于复杂签名。[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/title-page.html)]
> **相关判定树**: [泛型判定树](../00_meta/concept_definition_decision_forest.md#六泛型判定树) · [Trait 判定树](../00_meta/concept_definition_decision_forest.md#五trait-判定树)
> **相关 FTA**: [类型系统失效树](../00_meta/fault_tree_analysis_collection.md#四类型系统失效树)

### 10.1 边界测试：类型不匹配的基础错误

```rust,compile_fail
fn main() {
    // ❌ 编译错误: 类型不匹配
    let x: i32 = "hello";
}
```

> **修正**: **类型不匹配**是 Rust 最常见的编译错误：1) `let x: i32 = "hello"` — `&str` 不能隐式转为 `i32`；2) Rust 无隐式类型转换（C/Java 的自动转换）；3) 需显式转换：`"42".parse::<i32>().unwrap()` 或 `42i32.to_string()`。

## 实践

> **对应 Crate**: [`c02_type_system`](../crates/c02_type_system)
> **对应练习**: [`exercises/src/type_system/`](../exercises/src/type_system)
>
> **建议**: 阅读完本概念文件后，打开对应 crate 的示例代码，尝试修改并运行。

## 逆向推理链（Backward Reasoning）

> **从类型错误反推定理链**：
>
> ```text
> C1(Option<T> 空指针消除) ⟸ T1(match 穷尽性) + L2(NPO)
> T3(类型一致性 / Progress + Preservation) ⟸ L1(ADT 代数完备性) + L2(NPO)
> ```
>
> **诊断方法**：
>
> - E0004 (non-exhaustive patterns) → T1(match 穷尽性) 违反 → 补全 match 分支或添加 `_`
> - E0308 (mismatched types) → T3(类型一致性) 违反 → 检查类型转换或添加显式转换
> - E0277 (the trait bound is not satisfied) → L1(ADT 完备性) + Trait 约束不满足

## 参考来源

> [来源: [RFC 0401 — Coercions](https://rust-lang.github.io/rfcs//0401-coercions.html)]
> [来源: [RFC 1214 — WF](https://rust-lang.github.io/rfcs//1214-projections-lifetimes-and-wf.html)]
> [来源: [The Rust Programming Language, Ch. 3.2](https://doc.rust-lang.org/book/ch03-02-data-types.html)]

## Never 类型元组强制（Rust 1.96）

Rust 1.96 稳定了 never 类型 (`!`) 的元组元素强制转换（tuple coercion），允许空类型自动转换为任意类型的元组元素：

```rust
// Rust 1.96+: never 类型可强制为任意类型的元组元素
fn diverge() -> ! { panic!("never returns") }

let pair: (i32, String) = (42, diverge());  // ! 强制为 String
```

> **语义**: 这是 never 类型子类型化的自然延伸。由于 `!` 是任意类型的子类型，`(!, T)` 可以强制为 `(U, T)`。
> 此特性填补了类型系统一致性的一块拼图，尤其在宏（Macro）生成代码和泛型抽象中减少显式转换。
> [来源: [Rust 1.96 Release Notes](https://releases.rs/docs/1.96.0/)] ·
> [来源: [RFC 1216 — `!` type](https://rust-lang.github.io/rfcs//1216-bang-type.html)]

---

## 嵌入式测验（Embedded Quiz）

### 测验 1：结构体与元组结构体（理解层）

以下代码能否编译？

```rust
struct Point(i32, i32);
struct Point2D { x: i32, y: i32 }

fn main() {
    let p1 = Point(1, 2);
    let p2 = Point2D { x: 1, y: 2 };
    println!("{}", p1.0);
    println!("{}", p2.x);
}
```

- A. 编译通过
- B. 编译失败：`Point` 不能按 `.0` 访问
- C. 编译失败：`Point2D` 不能按 `.x` 访问

<details>
<summary>✅ 答案</summary>

**A. 编译通过**。

- 元组结构体 `Point` 通过索引 `.0`、`.1` 访问字段
- 命名字段结构体 `Point2D` 通过字段名 `.x`、`.y` 访问
- 两者都是合法的结构体变体

</details>

---

### 测验 2：枚举与模式匹配穷尽性（应用层）

以下代码为什么编译失败？

```rust,compile_fail
enum Direction {
    North,
    South,
    East,
    West,
}

fn main() {
    let d = Direction::North;
    match d {
        Direction::North => println!("N"),
        Direction::South => println!("S"),
    }
}
```

<details>
<summary>✅ 答案</summary>

**编译错误：非穷尽模式匹配**。

Rust 要求 `match` 表达式覆盖枚举的所有变体。此处缺少 `East` 和 `West` 的处理。

修复方案：

```rust,ignore
match d {
    Direction::North => println!("N"),
    Direction::South => println!("S"),
    Direction::East => println!("E"),
    Direction::West => println!("W"),
}
// 或使用通配符: _ => println!("Other"),
```

</details>

---

### 测验 3：Option 与 unwrap（分析层）

以下代码在运行时会发生什么？

```rust
fn main() {
    let x: Option<i32> = None;
    println!("{}", x.unwrap());
}
```

- A. 打印 `0`
- B. 打印 `None`
- C. 编译错误
- D. 运行时 panic

<details>
<summary>✅ 答案</summary>

**D. 运行时 panic**。

`Option::unwrap()` 在 `None` 时会触发 panic：`"called`Option::unwrap()` on a `None`value"`。

安全替代方案：

```rust,ignore
if let Some(v) = x {
    println!("{}", v);
} else {
    println!("no value");
}
// 或: println!("{}", x.unwrap_or(0));
```

</details>

---

### 测验 4：类型推断边界（应用层）

以下代码中，编译器能否推断出 `v` 的类型？

```rust,compile_fail
let v = Vec::new();
v.push(42);
```

- A. 能，`Vec<i32>`
- B. 能，`Vec<{integer}>`
- C. 不能，需要显式标注类型

<details>
<summary>✅ 答案</summary>

**A. 能，`Vec<i32>`**。

Rust 编译器通过后续使用推断类型。`v.push(42)` 中的 `42` 是 `i32` 字面量，因此编译器推断 `v: Vec<i32>`。

如果后续没有使用，则必须显式标注：`let v: Vec<i32> = Vec::new();`
</details>

---

### 测验 5：类型转换与 as（分析层）

以下代码的输出是什么？

```rust
fn main() {
    let x: i32 = 256;
    let y: i8 = x as i8;
    println!("{}", y);
}
```

- A. 256
- B. 0
- C. 编译错误

<details>
<summary>✅ 答案</summary>

**B. 0**。

`i8` 的范围是 `-128..=127`。`256` 超出范围，`as` 执行**截断转换**（wrapping/truncating）。

`256` 的二进制是 `1_0000_0000`，取低 8 位得到 `0000_0000` = 0。

> **警告**: `as` 转换在溢出时不报错，是潜在 bug 来源。Rust 1.45+ 推荐使用 `TryInto` 进行可失败转换。
</details>

---

## 十二、补充：运算符重载（Operator Overloading）

### 12.1 核心命题

> **运算符重载不是语法糖，而是类型系统能力的显式化。
> C++ 允许为任意类型自由重载 `+`、`-`、`*`、`/` 等运算符；Rust 将运算符重载限制在 `std::ops` trait 体系内，从而保证：
>
> 1. 重载行为必须显式实现；
> 2. 编译器可以静态检查运算符两侧类型是否匹配；
> 3. 不会出现 C++ 中"意外重载导致语义漂移"的问题。**

### 12.2 C++ 自由运算符重载

```cpp
// C++: 可以为任意类型重载任意运算符
struct Vector2 {
    double x, y;
};

Vector2 operator+(const Vector2& a, const Vector2& b) {
    return Vector2{a.x + b.x, a.y + b.y};
}

// 甚至可以重载 &、->、[]、() 等
```

**C++ 的问题**：

- 运算符语义完全由程序员定义，可能与自然直觉相悖。
- 无法静态保证 `a + b` 的两边类型兼容。
- 重载决策可能涉及隐式转换，导致意外行为。

### 12.3 Rust 的 `std::ops` Trait 约束

Rust 中，`a + b` 是 `a.add(b)` 的语法糖，而 `add` 来自 `std::ops::Add` trait：

```rust
use std::ops::Add;

#[derive(Debug, Clone, Copy)]
struct Vector2 {
    x: f64,
    y: f64,
}

impl Add for Vector2 {
    type Output = Self;
    fn add(self, other: Self) -> Self {
        Self {
            x: self.x + other.x,
            y: self.y + other.y,
        }
    }
}

fn main() {
    let a = Vector2 { x: 1.0, y: 2.0 };
    let b = Vector2 { x: 3.0, y: 4.0 };
    println!("{:?}", a + b); // 必须实现 Add
}
```

**关键差异**：

| 维度 | C++ | Rust |
|:---|:---|:---|
| 重载机制 | 自由函数 `operator+` | `std::ops::Add` trait impl |
| 类型检查 | 运行时/重载决议 | 编译期 trait bound 检查 |
| 可重载运算符 | 几乎所有运算符 | 仅限于 `std::ops` 中定义的 trait |
| 隐式转换 | 可参与重载决议 | 不参与；必须类型完全匹配或显式 `Into` |
| 错误信息 | 复杂，涉及候选函数列表 | 直接提示未实现 `Add` trait |

### 12.4 常用 `std::ops` trait

| 运算符 | Trait | 说明 |
|:---|:---|:---|
| `+` | `std::ops::Add` | 加法 |
| `-` | `std::ops::Sub` | 减法 |
| `*` | `std::ops::Mul` | 乘法 |
| `/` | `std::ops::Div` | 除法 |
| `%` | `std::ops::Rem` | 取模 |
| `-x` | `std::ops::Neg` | 取负 |
| `!x` | `std::ops::Not` | 逻辑非/按位非 |
| `a += b` | `std::ops::AddAssign` | 复合赋值 |
| `a[b]` | `std::ops::Index` / `IndexMut` | 索引 |
| `()` | `Fn` / `FnMut` / `FnOnce` | 函数调用（闭包） |
| `?` | `Try` | 错误传播 |

### 12.5 形式化视角

C++ 的运算符重载是**特设多态（ad-hoc polymorphism）**的语法扩展：编译器根据操作数类型选择重载函数。Rust 的运算符重载是**参数化多态 + trait bound**的语法扩展：`a + b` 等价于 `Add::add(a, b)`，类型系统保证只有实现了 `Add<Output=Self>` 的类型才能使用 `+`。

> **关键洞察**：Rust 没有"重载决议"，只有"trait 求解"。这消除了 C++ 中因隐式转换和重载优先级导致的许多歧义。

### 12.6 边界与反例

```rust,compile_fail
struct Foo;

fn main() {
    let a = Foo;
    let b = Foo;
    let _ = a + b; // ❌ 错误: cannot add `Foo` to `Foo`
}
```

错误信息直接指出 `Foo` 未实现 `Add`：

```text
error[E0369]: cannot add `Foo` to `Foo`
  --> src/main.rs:7:15
   |
7  |     let _ = a + b;
   |               ^ no implementation for `Foo + Foo`
```

### 12.7 权威来源

- [Rust Reference — Operator Expressions](https://doc.rust-lang.org/reference/expressions/operator-expr.html)
- [Rust Reference — Trait Implementations](https://doc.rust-lang.org/reference/items/implementations.html#trait-implementations)
- [std::ops](https://doc.rust-lang.org/std/ops/index.html)
- [TRPL — Advanced Features](https://doc.rust-lang.org/book/ch19-00-advanced-features.html)
- [cppreference — Operator overloading](https://en.cppreference.com/w/cpp/language/operators)
- [Stroustrup — The C++ Programming Language, 4th ed.](https://www.stroustrup.com/4th.html)
