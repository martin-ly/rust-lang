# 🔧 Rust编译器内部机制完整指南（2025版）

> **版本**: v2.0  
> **创建日期**: 2025-10-20  
> **适用rustc版本**: 1.90+  
> **难度**: 🔴 高级到专家级

---

## 📊 目录

- [🔧 Rust编译器内部机制完整指南（2025版）](#-rust编译器内部机制完整指南2025版)
  - [📊 目录](#-目录)
  - [📋 目录](#-目录-1)
  - [简介](#简介)
  - [1. 编译器整体架构](#1-编译器整体架构)
    - [1.1 宏观架构图](#11-宏观架构图)
    - [1.2 核心数据结构](#12-核心数据结构)
    - [1.3 编译流程时间线](#13-编译流程时间线)
  - [2. 前端：从源码到HIR](#2-前端从源码到hir)
    - [2.1 词法分析（Lexing）](#21-词法分析lexing)
      - [实现位置](#实现位置)
      - [Token类型](#token类型)
      - [示例：词法分析过程](#示例词法分析过程)
    - [2.2 语法分析（Parsing）](#22-语法分析parsing)
      - [2.2.1 实现位置](#221-实现位置)
      - [AST节点示例](#ast节点示例)
      - [解析示例](#解析示例)
    - [2.3 宏展开](#23-宏展开)
      - [宏类型](#宏类型)
      - [展开过程](#展开过程)
    - [2.4 HIR降级](#24-hir降级)
      - [HIR vs AST](#hir-vs-ast)
      - [HIR示例](#hir示例)
      - [完整示例：从源码到HIR](#完整示例从源码到hir)
  - [3. 类型系统与Trait求解](#3-类型系统与trait求解)
    - [3.1 类型检查流程](#31-类型检查流程)
    - [3.2 类型推断算法](#32-类型推断算法)
      - [类型变量和约束](#类型变量和约束)
      - [统一算法（Unification）](#统一算法unification)
    - [3.3 Trait求解](#33-trait求解)
      - [Trait求解器架构](#trait求解器架构)
      - [Trait求解示例](#trait求解示例)
      - [复杂Trait求解](#复杂trait求解)
  - [4. 借用检查器深度解析](#4-借用检查器深度解析)
    - [4.1 借用检查器的三大支柱](#41-借用检查器的三大支柱)
    - [4.2 NLL（Non-Lexical Lifetimes）](#42-nllnon-lexical-lifetimes)
      - [NLL之前 vs NLL之后](#nll之前-vs-nll之后)
    - [4.3 借用检查算法](#43-借用检查算法)
      - [数据流分析](#数据流分析)
      - [三地规则（Two-Phase Borrows）](#三地规则two-phase-borrows)
    - [4.4 借用检查器MIR分析](#44-借用检查器mir分析)
      - [MIR表示](#mir表示)
      - [借用检查分析](#借用检查分析)
  - [5. MIR：中间表示详解](#5-mir中间表示详解)
    - [5.1 MIR概述](#51-mir概述)
    - [5.2 MIR结构](#52-mir结构)
      - [MIR组成要素](#mir组成要素)
    - [5.3 MIR示例](#53-mir示例)
      - [简单函数](#简单函数)
      - [控制流](#控制流)
      - [循环](#循环)
    - [5.4 查看MIR的方法](#54-查看mir的方法)
      - [命令行标志](#命令行标志)
      - [cargo-show-mir工具](#cargo-show-mir工具)
  - [6. 优化Pass详解](#6-优化pass详解)
    - [6.1 MIR优化Pass列表](#61-mir优化pass列表)
    - [6.2 常量传播示例](#62-常量传播示例)
    - [6.3 内联优化](#63-内联优化)
    - [6.4 死代码消除](#64-死代码消除)
  - [7. LLVM后端集成](#7-llvm后端集成)
    - [7.1 LLVM架构](#71-llvm架构)
    - [7.2 MIR到LLVM IR的转换](#72-mir到llvm-ir的转换)
    - [7.3 复杂示例](#73-复杂示例)
    - [7.4 查看LLVM IR](#74-查看llvm-ir)
  - [8. 代码生成与ABI](#8-代码生成与abi)
    - [8.1 调用约定（Calling Convention）](#81-调用约定calling-convention)
    - [8.2 ABI布局](#82-abi布局)
    - [8.3 零成本抽象实现](#83-零成本抽象实现)
  - [9. 增量编译机制](#9-增量编译机制)
    - [9.1 增量编译原理](#91-增量编译原理)
    - [9.2 查询系统](#92-查询系统)
  - [10. 实践：探索编译器内部](#10-实践探索编译器内部)
    - [10.1 查看编译器输出](#101-查看编译器输出)
    - [10.2 查看MIR](#102-查看mir)
    - [10.3 查看LLVM IR](#103-查看llvm-ir)
    - [10.4 查看汇编](#104-查看汇编)
    - [10.5 性能分析](#105-性能分析)
    - [10.6 调试编译器](#106-调试编译器)
  - [附录](#附录)
    - [A. 常用rustc标志](#a-常用rustc标志)
    - [B. 编译器组件索引](#b-编译器组件索引)
    - [C. 学习资源](#c-学习资源)
    - [D. 练习题](#d-练习题)
      - [初级练习](#初级练习)
      - [中级练习](#中级练习)
      - [高级练习](#高级练习)

## 📋 目录

- [🔧 Rust编译器内部机制完整指南（2025版）](#-rust编译器内部机制完整指南2025版)
  - [📊 目录](#-目录)
  - [📋 目录](#-目录-1)
  - [简介](#简介)
  - [1. 编译器整体架构](#1-编译器整体架构)
    - [1.1 宏观架构图](#11-宏观架构图)
    - [1.2 核心数据结构](#12-核心数据结构)
    - [1.3 编译流程时间线](#13-编译流程时间线)
  - [2. 前端：从源码到HIR](#2-前端从源码到hir)
    - [2.1 词法分析（Lexing）](#21-词法分析lexing)
      - [实现位置](#实现位置)
      - [Token类型](#token类型)
      - [示例：词法分析过程](#示例词法分析过程)
    - [2.2 语法分析（Parsing）](#22-语法分析parsing)
      - [2.2.1 实现位置](#221-实现位置)
      - [AST节点示例](#ast节点示例)
      - [解析示例](#解析示例)
    - [2.3 宏展开](#23-宏展开)
      - [宏类型](#宏类型)
      - [展开过程](#展开过程)
    - [2.4 HIR降级](#24-hir降级)
      - [HIR vs AST](#hir-vs-ast)
      - [HIR示例](#hir示例)
      - [完整示例：从源码到HIR](#完整示例从源码到hir)
  - [3. 类型系统与Trait求解](#3-类型系统与trait求解)
    - [3.1 类型检查流程](#31-类型检查流程)
    - [3.2 类型推断算法](#32-类型推断算法)
      - [类型变量和约束](#类型变量和约束)
      - [统一算法（Unification）](#统一算法unification)
    - [3.3 Trait求解](#33-trait求解)
      - [Trait求解器架构](#trait求解器架构)
      - [Trait求解示例](#trait求解示例)
      - [复杂Trait求解](#复杂trait求解)
  - [4. 借用检查器深度解析](#4-借用检查器深度解析)
    - [4.1 借用检查器的三大支柱](#41-借用检查器的三大支柱)
    - [4.2 NLL（Non-Lexical Lifetimes）](#42-nllnon-lexical-lifetimes)
      - [NLL之前 vs NLL之后](#nll之前-vs-nll之后)
    - [4.3 借用检查算法](#43-借用检查算法)
      - [数据流分析](#数据流分析)
      - [三地规则（Two-Phase Borrows）](#三地规则two-phase-borrows)
    - [4.4 借用检查器MIR分析](#44-借用检查器mir分析)
      - [MIR表示](#mir表示)
      - [借用检查分析](#借用检查分析)
  - [5. MIR：中间表示详解](#5-mir中间表示详解)
    - [5.1 MIR概述](#51-mir概述)
    - [5.2 MIR结构](#52-mir结构)
      - [MIR组成要素](#mir组成要素)
    - [5.3 MIR示例](#53-mir示例)
      - [简单函数](#简单函数)
      - [控制流](#控制流)
      - [循环](#循环)
    - [5.4 查看MIR的方法](#54-查看mir的方法)
      - [命令行标志](#命令行标志)
      - [cargo-show-mir工具](#cargo-show-mir工具)
  - [6. 优化Pass详解](#6-优化pass详解)
    - [6.1 MIR优化Pass列表](#61-mir优化pass列表)
    - [6.2 常量传播示例](#62-常量传播示例)
    - [6.3 内联优化](#63-内联优化)
    - [6.4 死代码消除](#64-死代码消除)
  - [7. LLVM后端集成](#7-llvm后端集成)
    - [7.1 LLVM架构](#71-llvm架构)
    - [7.2 MIR到LLVM IR的转换](#72-mir到llvm-ir的转换)
    - [7.3 复杂示例](#73-复杂示例)
    - [7.4 查看LLVM IR](#74-查看llvm-ir)
  - [8. 代码生成与ABI](#8-代码生成与abi)
    - [8.1 调用约定（Calling Convention）](#81-调用约定calling-convention)
    - [8.2 ABI布局](#82-abi布局)
    - [8.3 零成本抽象实现](#83-零成本抽象实现)
  - [9. 增量编译机制](#9-增量编译机制)
    - [9.1 增量编译原理](#91-增量编译原理)
    - [9.2 查询系统](#92-查询系统)
  - [10. 实践：探索编译器内部](#10-实践探索编译器内部)
    - [10.1 查看编译器输出](#101-查看编译器输出)
    - [10.2 查看MIR](#102-查看mir)
    - [10.3 查看LLVM IR](#103-查看llvm-ir)
    - [10.4 查看汇编](#104-查看汇编)
    - [10.5 性能分析](#105-性能分析)
    - [10.6 调试编译器](#106-调试编译器)
  - [附录](#附录)
    - [A. 常用rustc标志](#a-常用rustc标志)
    - [B. 编译器组件索引](#b-编译器组件索引)
    - [C. 学习资源](#c-学习资源)
    - [D. 练习题](#d-练习题)
      - [初级练习](#初级练习)
      - [中级练习](#中级练习)
      - [高级练习](#高级练习)

---

## 简介

Rust编译器（rustc）是一个高度复杂的工程系统，负责将Rust源代码转换为高效的机器码。
本指南深入剖析rustc的内部机制，帮助你理解：

- 🏗️ **编译器架构**：多阶段编译流水线
- 🔍 **静态分析**：类型检查、借用检查
- 🎯 **中间表示**：AST → HIR → MIR → LLVM IR
- ⚡ **优化策略**：死代码消除、内联、循环优化
- 🔧 **代码生成**：LLVM集成、ABI约定

**为什么要学习编译器内部？**

1. 💡 **理解错误消息**：知道编译器在检查什么
2. 🚀 **性能优化**：了解编译器如何优化代码
3. 🛠️ **工具开发**：开发linter、宏、IDE插件
4. 📚 **深入理解Rust**：从实现层面理解语言特性
5. 🔬 **编译器贡献**：为rustc做贡献

---

## 1. 编译器整体架构

### 1.1 宏观架构图

```text
┌────────────────────────────────────────────────────────────────┐
│                      Rust编译器架构                             │
├────────────────────────────────────────────────────────────────┤
│                                                                │
│  源码 (.rs)                                                    │
│      ↓                                                         │
│  ┌────────────────┐                                            │
│  │  词法分析器    │  Token流                                    │
│  │  (Lexer)      │  ---→  [fn, main, (, ), {, ...}             │
│  └────────────────┘                                            │
│      ↓                                                         │
│  ┌────────────────┐                                            │
│  │  语法分析器    │  抽象语法树 (AST)                            │
│  │  (Parser)     │  ---→  Fn(main) { Block {...} }             │
│  └────────────────┘                                            │
│      ↓                                                         │
│  ┌────────────────┐                                            │
│  │  宏展开        │  展开后的AST                                │
│  │  (Macro Exp)  │  ---→  扩展的语法树                          │
│  └────────────────┘                                            │
│      ↓                                                         │
│  ┌────────────────┐                                            │
│  │  HIR降级       │  高级中间表示 (HIR)                         │
│  │  (HIR Lower)  │  ---→  去糖后的表示                         │
│  └────────────────┘                                           │
│      ↓                                                        │
│  ┌────────────────┐                                           │
│  │  类型检查      │  添加类型信息                               │
│  │  (Type Check) │  ---→  类型标注的HIR                        │
│  └────────────────┘                                           │
│      ↓                                                        │
│  ┌────────────────┐                                           │
│  │  借用检查      │  验证所有权规则                             │
│  │  (Borrow Check│  ---→  安全验证                             │
│  └────────────────┘                                           │
│      ↓                                                        │
│  ┌────────────────┐                                           │
│  │  MIR构建       │  中级中间表示 (MIR)                        │
│  │  (MIR Build)  │  ---→  基于CFG的表示                        │
│  └────────────────┘                                           │
│      ↓                                                        │
│  ┌────────────────┐                                           │
│  │  MIR优化       │  优化的MIR                                 │
│  │  (MIR Opt)    │  ---→  常量传播、内联等                     │
│  └────────────────┘                                           │
│      ↓                                                        │
│  ┌────────────────┐                                           │
│  │  代码生成      │  LLVM IR                                   │
│  │  (Codegen)    │  ---→  LLVM中间表示                         │
│  └────────────────┘                                           │
│      ↓                                                         │
│  ┌────────────────┐                                            │
│  │  LLVM后端      │  机器码                                    │
│  │  (LLVM)       │  ---→  目标平台可执行文件                    │
│  └────────────────┘                                           │
│      ↓                                                         │
│  可执行文件 / 库                                                │
│                                                                │
└────────────────────────────────────────────────────────────────┘
```

### 1.2 核心数据结构

```rust
// rustc_driver/src/lib.rs (简化版)
pub struct Compiler {
    pub session: Session,              // 编译会话
    pub global_ctxt: GlobalCtxt,       // 全局上下文
    pub queries: Queries,              // 查询系统
}

// 编译会话
pub struct Session {
    pub target: Target,                // 目标平台
    pub opts: Options,                 // 编译选项
    pub parse_sess: ParseSess,         // 解析会话
    pub source_map: SourceMap,         // 源文件映射
}

// 全局上下文 (包含所有类型信息)
pub struct GlobalCtxt<'tcx> {
    pub hir: Hir<'tcx>,               // HIR数据
    pub types: Types<'tcx>,           // 类型信息
    pub arena: Arena<'tcx>,           // 内存arena
}
```

### 1.3 编译流程时间线

```text
编译时间分布（典型1000行项目）:
┌─────────────────────────────────────────────────────────────┐
│ 词法&语法分析:  ████░░░░░░░░░░░░░░░░░░  10%  (~50ms)      │
│ 宏展开:        ██░░░░░░░░░░░░░░░░░░░░   5%  (~25ms)      │
│ HIR构建:       ███░░░░░░░░░░░░░░░░░░░   8%  (~40ms)      │
│ 类型检查:      ████████░░░░░░░░░░░░░░  20%  (~100ms)     │
│ 借用检查:      ██████░░░░░░░░░░░░░░░░  15%  (~75ms)      │
│ MIR优化:       ████░░░░░░░░░░░░░░░░░░  10%  (~50ms)      │
│ LLVM优化:      ████████████░░░░░░░░░░  25%  (~125ms)     │
│ 代码生成:      ███░░░░░░░░░░░░░░░░░░░   7%  (~35ms)      │
└─────────────────────────────────────────────────────────────┘
总计: ~500ms (debug模式)
```

---

## 2. 前端：从源码到HIR

### 2.1 词法分析（Lexing）

**目标**：将字符流转换为Token流

#### 实现位置

- `rustc_lexer` crate
- 使用手写的DFA（确定性有限自动机）

#### Token类型

```rust
// rustc_lexer/src/lib.rs
pub enum TokenKind {
    // 字面量
    Literal { kind: LiteralKind },
    
    // 标识符和关键字
    Ident,
    
    // 操作符和符号
    Semi,           // ;
    Comma,          // ,
    Dot,            // .
    OpenParen,      // (
    CloseParen,     // )
    OpenBrace,      // {
    CloseBrace,     // }
    
    // 注释和空白
    LineComment,
    BlockComment { terminated: bool },
    Whitespace,
    
    // 生命周期和标签
    Lifetime { starts_with_number: bool },
}

pub enum LiteralKind {
    Int { base: Base, empty_int: bool },
    Float { base: Base, empty_exponent: bool },
    Char { terminated: bool },
    Byte { terminated: bool },
    Str { terminated: bool },
    RawStr { n_hashes: u16 },
    // ...
}
```

#### 示例：词法分析过程

```rust
// 输入源码
let x = 42;

// Token流
[
    Token { kind: Ident("let"), span: 0..3 },
    Token { kind: Whitespace, span: 3..4 },
    Token { kind: Ident("x"), span: 4..5 },
    Token { kind: Whitespace, span: 5..6 },
    Token { kind: Eq, span: 6..7 },
    Token { kind: Whitespace, span: 7..8 },
    Token { kind: Literal(Int { base: Dec }), span: 8..10 },
    Token { kind: Semi, span: 10..11 },
]
```

### 2.2 语法分析（Parsing）

**目标**：将Token流转换为抽象语法树（AST）

#### 2.2.1 实现位置

- `rustc_parse` crate
- 递归下降解析器

#### AST节点示例

```rust
// rustc_ast/src/ast.rs (简化)
pub struct Crate {
    pub module: Mod,
    pub attrs: Vec<Attribute>,
    pub span: Span,
}

pub struct Item {
    pub ident: Ident,
    pub kind: ItemKind,
    pub span: Span,
    pub attrs: Vec<Attribute>,
}

pub enum ItemKind {
    Fn(Box<Fn>),
    Struct(Variant),
    Enum(EnumDef),
    Impl(Box<Impl>),
    Trait(Box<Trait>),
    // ...
}

pub struct Fn {
    pub defaultness: Defaultness,
    pub generics: Generics,
    pub sig: FnSig,
    pub body: Option<Block>,
}
```

#### 解析示例

```rust
// 输入
fn add(a: i32, b: i32) -> i32 {
    a + b
}

// AST表示
Item {
    ident: "add",
    kind: Fn(Box<Fn> {
        sig: FnSig {
            decl: FnDecl {
                inputs: [
                    Param { ident: "a", ty: Path("i32") },
                    Param { ident: "b", ty: Path("i32") },
                ],
                output: Ty::Path("i32"),
            },
        },
        body: Some(Block {
            stmts: [
                Stmt::Expr(
                    Expr::Binary {
                        op: Add,
                        left: Expr::Path("a"),
                        right: Expr::Path("b"),
                    }
                ),
            ],
        }),
    }),
}
```

### 2.3 宏展开

**目标**：展开宏调用，生成新的AST节点

#### 宏类型

```rust
// 声明式宏 (macro_rules!)
macro_rules! vec {
    ( $( $x:expr ),* ) => {
        {
            let mut temp_vec = Vec::new();
            $(
                temp_vec.push($x);
            )*
            temp_vec
        }
    };
}

// 过程宏 (Procedural Macros)
// 1. 函数式过程宏
#[proc_macro]
pub fn my_macro(input: TokenStream) -> TokenStream { }

// 2. 派生宏
#[proc_macro_derive(MyDerive)]
pub fn my_derive(input: TokenStream) -> TokenStream { }

// 3. 属性宏
#[proc_macro_attribute]
pub fn my_attr(attr: TokenStream, item: TokenStream) -> TokenStream { }
```

#### 展开过程

```text
展开前:
vec![1, 2, 3]

展开后:
{
    let mut temp_vec = Vec::new();
    temp_vec.push(1);
    temp_vec.push(2);
    temp_vec.push(3);
    temp_vec
}
```

### 2.4 HIR降级

**目标**：将AST转换为HIR（去糖、规范化）

#### HIR vs AST

| 特性 | AST | HIR |
|------|-----|-----|
| **语法糖** | 保留 | 去除 |
| **for循环** | 语法糖 | 转换为loop+match |
| **if let** | 语法糖 | 转换为match |
| **?操作符** | 语法糖 | 转换为match |
| **作用域** | 词法 | 规范化 |
| **生命周期** | 显式+推断 | 完全显式 |

#### HIR示例

```rust
// 源码
for item in vec {
    println!("{}", item);
}

// HIR (伪代码)
{
    let mut iter = IntoIterator::into_iter(vec);
    loop {
        match Iterator::next(&mut iter) {
            Some(item) => {
                println!("{}", item);
            }
            None => break,
        }
    }
}
```

#### 完整示例：从源码到HIR

```rust
// 源码
fn example() -> Result<i32, Error> {
    let x = read_number()?;
    Ok(x + 1)
}

// AST (简化)
Fn {
    sig: "() -> Result<i32, Error>",
    body: Block {
        stmts: [
            Let { pat: "x", init: Try(Call("read_number")) },
            Expr(Call("Ok", [Binary(Add, "x", 1)])),
        ],
    },
}

// HIR (伪代码，展开?和Ok)
Fn {
    sig: "() -> Result<i32, Error>",
    body: Block {
        stmts: [
            Let { 
                pat: "x", 
                init: Match(Call("read_number")) {
                    Ok(val) => val,
                    Err(e) => return Err(From::from(e)),
                },
            },
            Return(
                Call("Result::Ok", [Binary(Add, "x", 1)])
            ),
        ],
    },
}
```

---

## 3. 类型系统与Trait求解

### 3.1 类型检查流程

```text
┌─────────────────────────────────────────────────────────┐
│              类型检查流程                               │
├─────────────────────────────────────────────────────────┤
│                                                         │
│  1. 收集项定义                                          │
│     ├─ 收集所有fn、struct、enum、trait定义            │
│     └─ 建立def_id到类型的映射                          │
│                                                         │
│  2. 类型推断                                            │
│     ├─ 自底向上推断表达式类型                          │
│     ├─ 生成类型约束                                    │
│     └─ 统一（Unification）解决约束                     │
│                                                         │
│  3. Trait求解                                           │
│     ├─ 收集trait bounds                                │
│     ├─ 检查impl块                                      │
│     └─ 解决trait对象和dyn调用                         │
│                                                         │
│  4. 生命周期推断                                        │
│     ├─ 收集生命周期约束                                │
│     ├─ 生命周期子类型关系                              │
│     └─ 检查生命周期有效性                              │
│                                                         │
│  5. 完整性检查                                          │
│     ├─ 检查孤儿规则                                    │
│     ├─ 检查一致性                                      │
│     └─ 检查特化规则                                    │
│                                                         │
└─────────────────────────────────────────────────────────┘
```

### 3.2 类型推断算法

Rust使用**Hindley-Milner类型推断**的扩展版本。

#### 类型变量和约束

```rust
// 源码
fn example() {
    let x = vec![];    // x的类型未知
    x.push(42);        // 推断出x: Vec<i32>
}

// 类型推断过程
// 1. 初始状态
x: ?T0              // x是类型变量T0
vec![]: Vec<?T1>    // vec![]返回Vec<T1>

// 2. 生成约束
?T0 = Vec<?T1>      // let x = vec![]

// 3. push调用生成约束
Vec<?T1>::push(&mut Vec<?T1>, ?T2)
?T2 = i32           // 字面量42

// 4. 统一约束
?T1 = i32
?T0 = Vec<i32>
```

#### 统一算法（Unification）

```rust
// rustc_infer/src/infer/unify.rs (简化)
impl<'tcx> TypeUnifier<'tcx> {
    fn unify(&mut self, a: Ty<'tcx>, b: Ty<'tcx>) -> Result<(), TypeError> {
        match (a.kind(), b.kind()) {
            // 两个类型变量
            (TyKind::Infer(a_var), TyKind::Infer(b_var)) => {
                self.unify_vars(a_var, b_var)
            }
            
            // 一个类型变量，一个具体类型
            (TyKind::Infer(var), ty) | (ty, TyKind::Infer(var)) => {
                self.instantiate(var, ty)
            }
            
            // 两个具体类型
            (TyKind::Adt(a_def, a_substs), TyKind::Adt(b_def, b_substs)) => {
                if a_def == b_def {
                    self.unify_substs(a_substs, b_substs)
                } else {
                    Err(TypeError::Mismatch)
                }
            }
            
            _ => Err(TypeError::Mismatch),
        }
    }
}
```

### 3.3 Trait求解

#### Trait求解器架构

```text
┌────────────────────────────────────────────────────┐
│            Trait求解器（Chalk）                    │
├────────────────────────────────────────────────────┤
│                                                    │
│  查询: T: Display                                  │
│     ↓                                              │
│  ┌──────────────────────┐                         │
│  │  搜索impl块          │                         │
│  │  impl Display for T  │                         │
│  └──────────────────────┘                         │
│     ↓                                              │
│  ┌──────────────────────┐                         │
│  │  检查约束            │                         │
│  │  where T: Debug      │                         │
│  └──────────────────────┘                         │
│     ↓                                              │
│  ┌──────────────────────┐                         │
│  │  递归求解            │                         │
│  │  solve(T: Debug)     │                         │
│  └──────────────────────┘                         │
│     ↓                                              │
│  成功 / 失败 / 模糊                                │
│                                                    │
└────────────────────────────────────────────────────┘
```

#### Trait求解示例

```rust
// 源码
fn print_vec<T: Display>(vec: Vec<T>) {
    for item in vec {
        println!("{}", item);
    }
}

// Trait约束
T: Display

// Trait求解过程
1. 查找: impl Display for T?
2. 检查泛型约束: T: Display ✓
3. 验证: println!宏需要Display ✓
4. 结果: 满足约束
```

#### 复杂Trait求解

```rust
// 源码
fn complex<T>(x: T)
where
    T: Iterator,
    T::Item: Display + Clone,
{
    // ...
}

// 约束求解
1. T: Iterator
2. <T as Iterator>::Item: Display
3. <T as Iterator>::Item: Clone

// 求解步骤
Step 1: 查找T实现Iterator
Step 2: 获取关联类型Item
Step 3: 验证Item实现Display和Clone
Step 4: 全部满足 → 通过
```

---

## 4. 借用检查器深度解析

### 4.1 借用检查器的三大支柱

1. **所有权追踪**：谁拥有值
2. **借用追踪**：谁在借用值
3. **生命周期验证**：借用是否有效

### 4.2 NLL（Non-Lexical Lifetimes）

#### NLL之前 vs NLL之后

```rust
// 示例代码
fn example() {
    let mut x = 5;
    let y = &x;        // 不可变借用开始
    
    if false {
        println!("{}", y);
    }
    // 旧版: y的生命周期延续到作用域结束
    // NLL: y的生命周期在这里结束（最后使用点）
    
    x = 10;            // 旧版: ❌ 错误
                       // NLL:  ✅ 通过
}
```

### 4.3 借用检查算法

#### 数据流分析

```text
┌─────────────────────────────────────────────────────┐
│         借用检查数据流分析                          │
├─────────────────────────────────────────────────────┤
│                                                     │
│  fn example(flag: bool) {                          │
│      let mut x = 5;       // Point 0               │
│                                                     │
│      let r1 = &x;         // Point 1: Borrow(x)    │
│                           // Loan L1 starts        │
│                                                     │
│      if flag {            // Point 2               │
│          println!("{}", r1); // Point 3: Use(L1)   │
│      }                    // Point 4: L1 ends      │
│                                                     │
│      x = 10;              // Point 5: Write(x)     │
│  }                                                  │
│                                                     │
│  数据流:                                            │
│  Point 0: Loans = {}                               │
│  Point 1: Loans = {L1}                             │
│  Point 2: Loans = {L1}                             │
│  Point 3: Loans = {L1}     (使用L1)                │
│  Point 4: Loans = {}       (L1结束)                │
│  Point 5: Loans = {}       (可以写x)  ✓            │
│                                                     │
└─────────────────────────────────────────────────────┘
```

#### 三地规则（Two-Phase Borrows）

```rust
// 示例：vec.push(vec.len())
let mut vec = vec![1, 2, 3];

// 展开过程
Vec::push(&mut vec, Vec::len(&vec));
//         ^^^^^^^^  借用1: &mut
//                   ^^^^^^^^ 借用2: &

// 两阶段借用
// Phase 1 (Reserve): &mut vec预留，但未激活
// Phase 2 (Activate): 计算len(&vec)后激活&mut
```

### 4.4 借用检查器MIR分析

#### MIR表示

```rust
// 源码
fn borrow_example() {
    let mut x = 5;
    let y = &x;
    println!("{}", y);
}

// MIR (简化)
fn borrow_example() -> () {
    let mut _0: ();
    let mut _1: i32;     // x
    let _2: &i32;        // y
    
    bb0: {
        _1 = const 5_i32;               // x = 5
        _2 = &_1;                       // y = &x  (Loan L1 starts)
        _0 = println!("{}", move _2);   // use y   (Use L1)
        return;                         // L1 ends
    }
}
```

#### 借用检查分析

```rust
// 借用检查器分析MIR
// 1. 构建CFG
// 2. 计算活跃性
// 3. 追踪借用
// 4. 检测冲突

// 伪代码
fn check_borrows(mir: &Mir) {
    let cfg = build_cfg(mir);
    let liveness = compute_liveness(&cfg);
    let loans = track_loans(&cfg);
    
    for (point, loans) in &loans {
        // 检查是否有冲突的借用
        check_for_conflicts(point, loans)?;
    }
}
```

---

## 5. MIR：中间表示详解

### 5.1 MIR概述

MIR（Mid-level Intermediate Representation）是Rust编译器的核心中间表示，介于HIR和LLVM IR之间。

**MIR的优势**：

- 🎯 **简单明确**：基于CFG（控制流图）
- 🔍 **易于分析**：适合数据流分析
- ⚡ **优化友好**：支持多种优化pass
- 🛡️ **类型安全**：保留类型信息

### 5.2 MIR结构

#### MIR组成要素

```rust
// rustc_middle/src/mir/mod.rs (简化)
pub struct Body<'tcx> {
    pub basic_blocks: IndexVec<BasicBlock, BasicBlockData<'tcx>>,
    pub local_decls: IndexVec<Local, LocalDecl<'tcx>>,
    pub arg_count: usize,
    pub source_scopes: IndexVec<SourceScope, SourceScopeData>,
}

pub struct BasicBlockData<'tcx> {
    pub statements: Vec<Statement<'tcx>>,
    pub terminator: Option<Terminator<'tcx>>,
}

pub enum Statement<'tcx> {
    Assign(Box<(Place<'tcx>, Rvalue<'tcx>)>),
    SetDiscriminant { place: Place<'tcx>, variant_index: VariantIdx },
    StorageLive(Local),
    StorageDead(Local),
    Nop,
}

pub enum Terminator<'tcx> {
    Goto { target: BasicBlock },
    SwitchInt { discr: Operand<'tcx>, targets: SwitchTargets },
    Return,
    Unreachable,
    Drop { place: Place<'tcx>, target: BasicBlock, unwind: Option<BasicBlock> },
    Call { func: Operand<'tcx>, args: Vec<Operand<'tcx>>, destination: Place<'tcx>, target: Option<BasicBlock> },
}
```

### 5.3 MIR示例

#### 简单函数

```rust
// 源码
fn add(a: i32, b: i32) -> i32 {
    a + b
}

// MIR
fn add(_1: i32, _2: i32) -> i32 {
    let mut _0: i32;                     // 返回值
    
    bb0: {
        _0 = Add(move _1, move _2);     // _0 = _1 + _2
        return;                          // 返回_0
    }
}
```

#### 控制流

```rust
// 源码
fn max(a: i32, b: i32) -> i32 {
    if a > b {
        a
    } else {
        b
    }
}

// MIR
fn max(_1: i32, _2: i32) -> i32 {
    let mut _0: i32;                    // 返回值
    let mut _3: bool;                   // 条件
    
    bb0: {
        _3 = Gt(move _1, move _2);     // _3 = _1 > _2
        switchInt(move _3) -> [0: bb2, otherwise: bb1];
    }
    
    bb1: {                              // if分支
        _0 = move _1;
        goto -> bb3;
    }
    
    bb2: {                              // else分支
        _0 = move _2;
        goto -> bb3;
    }
    
    bb3: {                              // 合并点
        return;
    }
}
```

#### 循环

```rust
// 源码
fn sum_to(n: i32) -> i32 {
    let mut sum = 0;
    let mut i = 1;
    while i <= n {
        sum += i;
        i += 1;
    }
    sum
}

// MIR
fn sum_to(_1: i32) -> i32 {
    let mut _0: i32;                    // 返回值
    let mut _2: i32;                    // sum
    let mut _3: i32;                    // i
    let mut _4: bool;                   // 条件
    
    bb0: {
        _2 = const 0_i32;               // sum = 0
        _3 = const 1_i32;               // i = 1
        goto -> bb1;
    }
    
    bb1: {                              // 循环头
        _4 = Le(move _3, move _1);      // i <= n
        switchInt(move _4) -> [0: bb3, otherwise: bb2];
    }
    
    bb2: {                              // 循环体
        _2 = Add(move _2, move _3);     // sum += i
        _3 = Add(move _3, const 1_i32); // i += 1
        goto -> bb1;
    }
    
    bb3: {                              // 循环后
        _0 = move _2;
        return;
    }
}
```

### 5.4 查看MIR的方法

#### 命令行标志

```bash
# 查看MIR
rustc +nightly -Z unpretty=mir main.rs

# 查看特定函数的MIR
rustc +nightly -Z dump-mir=all main.rs

# 查看MIR图形化（需要graphviz）
rustc +nightly -Z dump-mir-graphviz main.rs
```

#### cargo-show-mir工具

```bash
# 安装
cargo install cargo-show-mir

# 使用
cargo show-mir --fn add
```

---

## 6. 优化Pass详解

### 6.1 MIR优化Pass列表

```text
┌─────────────────────────────────────────────────────────┐
│                  MIR优化Pass                            │
├─────────────────────────────────────────────────────────┤
│                                                         │
│  1. SimplifyCfg             - CFG简化                   │
│  2. ConstProp               - 常量传播                  │
│  3. CopyProp                - 复制传播                  │
│  4. DeadStoreElimination    - 死存储消除                │
│  5. Inline                  - 函数内联                  │
│  6. InstCombine             - 指令合并                  │
│  7. SimplifyBranches        - 分支简化                  │
│  8. RemoveDeadBlocks        - 死代码块消除              │
│  9. UnreachableCodeRemoval  - 不可达代码消除            │
│ 10. SimplifyLocals          - 局部变量简化              │
│ 11. RemoveZsts              - 零大小类型消除            │
│ 12. AddRetag                - 添加重新标记（Stacked     │
│                               Borrows）                 │
│                                                         │
└─────────────────────────────────────────────────────────┘
```

### 6.2 常量传播示例

```rust
// 优化前
fn example() -> i32 {
    let x = 10;
    let y = 20;
    let z = x + y;
    z
}

// MIR (优化前)
fn example() -> i32 {
    let mut _0: i32;
    let _1: i32;  // x
    let _2: i32;  // y
    let _3: i32;  // z
    
    bb0: {
        _1 = const 10_i32;
        _2 = const 20_i32;
        _3 = Add(move _1, move _2);
        _0 = move _3;
        return;
    }
}

// MIR (常量传播后)
fn example() -> i32 {
    let mut _0: i32;
    
    bb0: {
        _0 = const 30_i32;  // 直接计算结果
        return;
    }
}
```

### 6.3 内联优化

```rust
// 源码
#[inline]
fn square(x: i32) -> i32 {
    x * x
}

fn main() {
    let result = square(5);
    println!("{}", result);
}

// 内联前MIR
fn main() {
    bb0: {
        _1 = square(const 5_i32);  // 函数调用
        println!("{}", move _1);
        return;
    }
}

// 内联后MIR
fn main() {
    bb0: {
        _1 = Mul(const 5_i32, const 5_i32);  // 直接计算
        println!("{}", move _1);
        return;
    }
}
```

### 6.4 死代码消除

```rust
// 源码
fn example(flag: bool) -> i32 {
    let x = 10;
    let y = 20;  // 未使用
    if flag {
        x
    } else {
        0
    }
}

// 优化后（消除y）
fn example(flag: bool) -> i32 {
    let x = 10;
    if flag {
        x
    } else {
        0
    }
}
```

---

## 7. LLVM后端集成

### 7.1 LLVM架构

```text
┌────────────────────────────────────────────────────────┐
│                 LLVM编译流程                           │
├────────────────────────────────────────────────────────┤
│                                                        │
│  MIR                                                   │
│   ↓                                                    │
│  ┌──────────────────┐                                 │
│  │  MIR → LLVM IR   │  代码生成                        │
│  │  (Codegen)       │  rustc_codegen_llvm             │
│  └──────────────────┘                                 │
│   ↓                                                    │
│  LLVM IR                                               │
│   ↓                                                    │
│  ┌──────────────────┐                                 │
│  │  LLVM优化Pass    │  -O1, -O2, -O3优化              │
│  │  (Optimizer)     │  llvm-opt                       │
│  └──────────────────┘                                 │
│   ↓                                                    │
│  优化的LLVM IR                                         │
│   ↓                                                    │
│  ┌──────────────────┐                                 │
│  │  机器码生成      │  目标特定代码生成                │
│  │  (CodeGen)       │  llc                            │
│  └──────────────────┘                                 │
│   ↓                                                    │
│  汇编/目标文件                                         │
│   ↓                                                    │
│  ┌──────────────────┐                                 │
│  │  链接            │  链接器（ld, lld）               │
│  │  (Linker)        │                                 │
│  └──────────────────┘                                 │
│   ↓                                                    │
│  可执行文件                                            │
│                                                        │
└────────────────────────────────────────────────────────┘
```

### 7.2 MIR到LLVM IR的转换

```rust
// Rust源码
fn add(a: i32, b: i32) -> i32 {
    a + b
}

// LLVM IR
define i32 @add(i32 %a, i32 %b) {
entry:
  %0 = add nsw i32 %a, %b
  ret i32 %0
}
```

### 7.3 复杂示例

```rust
// Rust源码
fn factorial(n: u32) -> u32 {
    if n == 0 {
        1
    } else {
        n * factorial(n - 1)
    }
}

// LLVM IR
define i32 @factorial(i32 %n) {
entry:
  %0 = icmp eq i32 %n, 0
  br i1 %0, label %then, label %else

then:
  ret i32 1

else:
  %1 = sub i32 %n, 1
  %2 = call i32 @factorial(i32 %1)
  %3 = mul i32 %n, %2
  ret i32 %3
}
```

### 7.4 查看LLVM IR

```bash
# 生成LLVM IR
rustc --emit=llvm-ir main.rs

# 生成优化的LLVM IR
rustc --emit=llvm-ir -C opt-level=3 main.rs

# 查看汇编
rustc --emit=asm main.rs
```

---

## 8. 代码生成与ABI

### 8.1 调用约定（Calling Convention）

```rust
// 不同的调用约定
extern "C" fn c_function() { }       // C调用约定
extern "system" fn sys_function() { } // 系统调用约定
extern "Rust" fn rust_function() { }  // Rust调用约定（默认）
```

### 8.2 ABI布局

```rust
// 结构体布局
#[repr(C)]
struct CLayout {
    a: u8,
    b: u32,
    c: u16,
}
// C布局: 顺序排列，带对齐

#[repr(Rust)]
struct RustLayout {
    a: u8,
    b: u32,
    c: u16,
}
// Rust布局: 可能重排序以最小化大小
```

### 8.3 零成本抽象实现

```rust
// 高级抽象
let sum: i32 = vec![1, 2, 3, 4, 5]
    .iter()
    .filter(|&&x| x % 2 == 0)
    .map(|&x| x * 2)
    .sum();

// 编译后等价于手写循环（零成本）
let mut sum = 0;
for x in &[1, 2, 3, 4, 5] {
    if x % 2 == 0 {
        sum += x * 2;
    }
}
```

---

## 9. 增量编译机制

### 9.1 增量编译原理

```text
┌─────────────────────────────────────────────────────┐
│            增量编译系统                             │
├─────────────────────────────────────────────────────┤
│                                                     │
│  1. 依赖图构建                                      │
│     ├─ 追踪每个定义的依赖                          │
│     └─ 建立细粒度依赖关系                          │
│                                                     │
│  2. 指纹计算（Fingerprinting）                      │
│     ├─ 为每个编译单元计算哈希                      │
│     └─ 检测变化                                    │
│                                                     │
│  3. 查询系统（Query System）                        │
│     ├─ 缓存查询结果                                │
│     ├─ 跟踪查询依赖                                │
│     └─ 按需重新计算                                │
│                                                     │
│  4. 增量缓存                                        │
│     ├─ target/debug/incremental/                   │
│     └─ 持久化中间结果                              │
│                                                     │
└─────────────────────────────────────────────────────┘
```

### 9.2 查询系统

```rust
// rustc查询系统示例
query type_of(key: DefId) -> Ty {
    desc { |tcx| "computing type of `{}`", tcx.def_path_str(key) }
    cache_on_disk_if { key.is_local() }
}

query mir_built(key: ty::WithOptConstParam<LocalDefId>) -> &'tcx Steal<mir::Body<'tcx>> {
    storage(ArenaCacheSelector<'tcx>)
    desc { |tcx| "building MIR for `{}`", tcx.def_path_str(key.did.to_def_id()) }
}
```

---

## 10. 实践：探索编译器内部

### 10.1 查看编译器输出

```bash
# 查看完整编译过程
cargo build -v

# 查看时间统计
cargo build -Z time-passes

# 查看各阶段详细信息
RUSTFLAGS="-Z time-passes" cargo build
```

### 10.2 查看MIR

```rust
// main.rs
fn factorial(n: u32) -> u32 {
    if n == 0 {
        1
    } else {
        n * factorial(n - 1)
    }
}

fn main() {
    println!("{}", factorial(5));
}
```

```bash
# 查看MIR
rustc +nightly -Z unpretty=mir main.rs > mir.txt
```

### 10.3 查看LLVM IR

```bash
# 生成LLVM IR
rustc --emit=llvm-ir main.rs -o main.ll

# 查看优化的LLVM IR
rustc --emit=llvm-ir -C opt-level=3 main.rs -o main_opt.ll
```

### 10.4 查看汇编

```bash
# 生成汇编
rustc --emit=asm main.rs -o main.s

# 使用cargo-asm
cargo install cargo-asm
cargo asm crate_name::function_name
```

### 10.5 性能分析

```bash
# 编译时间分析
cargo build --timings

# 生成HTML报告
# 查看target/cargo-timings/cargo-timing.html
```

### 10.6 调试编译器

```bash
# 设置RUST_BACKTRACE
RUST_BACKTRACE=1 cargo build

# 更详细的回溯
RUST_BACKTRACE=full cargo build

# 编译器内部日志
RUSTC_LOG=debug cargo build
```

---

## 附录

### A. 常用rustc标志

```bash
# 编译选项
-C opt-level=N        # 优化级别 (0, 1, 2, 3, s, z)
-C debuginfo=N        # 调试信息 (0, 1, 2)
-C lto                # 链接时优化
-C codegen-units=N    # 代码生成并行度

# 输出选项
--emit=TYPE           # 输出类型 (asm, llvm-ir, mir, link)
--crate-type=TYPE     # crate类型 (bin, lib, dylib, staticlib)

# 调试选项
-Z unpretty=TYPE      # 打印内部表示
-Z dump-mir=PASS      # 转储MIR
-Z time-passes        # 显示编译时间
-Z print-type-sizes   # 打印类型大小
```

### B. 编译器组件索引

| 组件 | Crate | 功能 |
|------|-------|------|
| 词法分析 | `rustc_lexer` | Token化 |
| 语法分析 | `rustc_parse` | AST构建 |
| HIR | `rustc_hir` | 高级IR |
| 类型检查 | `rustc_typeck` | 类型推断 |
| 借用检查 | `rustc_borrowck` | 所有权验证 |
| MIR | `rustc_mir_build` | MIR构建 |
| 优化 | `rustc_mir_transform` | MIR优化 |
| 代码生成 | `rustc_codegen_llvm` | LLVM后端 |

### C. 学习资源

- 📚 [Rust编译器开发指南](https://rustc-dev-guide.rust-lang.org/)
- 📚 [MIR文档](https://rust-lang.github.io/rustc-guide/mir/index.html)
- 📚 [LLVM文档](https://llvm.org/docs/)
- 📹 [RustConf编译器演讲](https://www.youtube.com/c/RustVideos)

### D. 练习题

#### 初级练习

1. 使用`-Z unpretty=mir`查看简单函数的MIR
2. 比较debug和release模式的LLVM IR差异
3. 查看不同优化级别的汇编输出

#### 中级练习

1. 分析一个包含泛型的函数的单态化过程
2. 观察内联优化对代码的影响
3. 使用`cargo-expand`查看宏展开结果

#### 高级练习

1. 为自定义数据结构分析内存布局
2. 调试一个复杂的借用检查错误
3. 分析增量编译的依赖图

---

**文档版本**: v2.0  
**最后更新**: 2025-10-20  
**维护者**: Rust Learning Community

🔧 **深入理解编译器，掌握Rust的灵魂！** ✨
