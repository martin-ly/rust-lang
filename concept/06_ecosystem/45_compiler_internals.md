# Compiler Internals（Rust 编译器内部原理）

> **Bloom 层级**: 分析 → 评价
> **A/S/P 标记**: **S+P** — Structure + Procedure
> **双维定位**: C×Eva — 评价 rustc 编译管线的架构设计与实现权衡
> **前置依赖**: [类型系统](../01_foundation/04_type_system.md) · [泛型](../02_intermediate/02_generics.md) · [生命周期](../01_foundation/03_lifetimes.md) · [Trait](../02_intermediate/01_traits.md) · [Unsafe](../03_advanced/03_unsafe.md)
> **后置延伸**: [Async/Await](../03_advanced/02_async.md) · [宏系统](../03_advanced/07_proc_macro.md) · [形式化验证](../04_formal/05_verification_toolchain.md)

---

> **来源**: [Rustc Development Guide](https://rustc-dev-guide.rust-lang.org/) · [Rust Reference](https://doc.rust-lang.org/reference/) · [Niko Matsakis — Rust Blog](https://smallcultfollowing.com/babysteps/) · [Polonius — OOPSLA 2018](https://hal.inria.fr/hal-03827702/) · [Chalk — Rust PL](https://rust-lang.github.io/chalk/book/) · [LLVM](https://llvm.org/docs/) · [rustc_driver API](https://doc.rust-lang.org/nightly/nightly-rustc/rustc_driver/)

## 📑 目录
>
>

- [Compiler Internals（Rust 编译器内部原理）](#compiler-internalsrust-编译器内部原理)
  - [📑 目录](#-目录)
  - [一、权威定义（Definition）](#一权威定义definition)
    - [1.1 rustc 架构概览](#11-rustc-架构概览)
    - [1.2 编译管线](#12-编译管线)
  - [二、概念属性矩阵](#二概念属性矩阵)
  - [三、前端：解析与 AST](#三前端解析与-ast)
    - [3.1 词法与语法分析](#31-词法与语法分析)
    - [3.2 宏展开](#32-宏展开)
  - [四、HIR：高级中间表示](#四hir高级中间表示)
    - [4.1 HIR 的设计目标](#41-hir-的设计目标)
    - [4.2 类型检查](#42-类型检查)
  - [五、类型系统实现](#五类型系统实现)
    - [5.1 Trait 解析与 Chalk](#51-trait-解析与-chalk)
    - [5.2 类型推断](#52-类型推断)
  - [六、MIR：中级中间表示](#六mir中级中间表示)
    - [6.1 MIR 的结构](#61-mir-的结构)
    - [6.2 MIR 优化](#62-mir-优化)
    - [6.3 常量求值（MIRI / Const Eval）](#63-常量求值miri--const-eval)
  - [七、借用检查器](#七借用检查器)
    - [7.1 NLL（Non-Lexical Lifetimes）](#71-nllnon-lexical-lifetimes)
    - [7.2 Polonius：基于逻辑的借用检查](#72-polonius基于逻辑的借用检查)
    - [7.3 别名模型：Tree Borrows](#73-别名模型tree-borrows)
  - [八、后端：代码生成](#八后端代码生成)
    - [8.1 LLVM IR 生成](#81-llvm-ir-生成)
    - [8.2 增量编译](#82-增量编译)
  - [九、查询系统](#九查询系统)
  - [十、反命题与边界](#十反命题与边界)
    - [10.1 反命题树](#101-反命题树)
    - [10.2 边界极限](#102-边界极限)
  - [十一、边界测试](#十一边界测试)
    - [11.1 边界测试：递归宏展开导致栈溢出（编译错误）](#111-边界测试递归宏展开导致栈溢出编译错误)
    - [11.2 边界测试：泛型单态化导致二进制膨胀（编译/链接错误）](#112-边界测试泛型单态化导致二进制膨胀编译链接错误)
    - [11.3 边界测试：unsafe 代码在 Miri 中触发 UB（运行时错误）](#113-边界测试unsafe-代码在-miri-中触发-ub运行时错误)
  - [相关概念文件](#相关概念文件)

> **Bloom 层级**: 分析 → 评价
**变更日志**:

- v1.0 (2026-05-25): 初始创建——rustc 编译管线、HIR/MIR、类型系统实现、借用检查器（NLL/Polonius/Tree Borrows）、LLVM 后端、查询系统

---

## 一、权威定义（Definition）
>

### 1.1 rustc 架构概览
>

> **[Rustc Development Guide](https://rustc-dev-guide.rust-lang.org/compiler-src.html)** rustc 是 Rust 的官方编译器，采用**多阶段编译管线**（Multi-pass Pipeline）架构，核心设计原则：**增量编译**、**延迟计算**（Demand-driven）、**查询系统**（Query System）。

```text
rustc 核心架构:
┌─────────────────────────────────────────────────────────────┐
│                     rustc_driver                             │
│                  (命令行解析 + 会话管理)                       │
└──────────────────────┬──────────────────────────────────────┘
                       │
┌──────────────────────▼──────────────────────────────────────┐
│                    查询系统 (Query System)                    │
│         ┌─────────┐  ┌─────────┐  ┌─────────┐             │
│         │ 解析    │  │ 类型检查 │  │ 借用检查 │             │
│         │ parse   │  │ typeck  │  │ borrowck │             │
│         └────┬────┘  └────┬────┘  └────┬────┘             │
│              │            │            │                   │
│         ┌────▼────────────▼────────────▼────┐             │
│         │           TyCtxt                  │             │
│         │    (类型上下文 + 全局状态)          │             │
│         └───────────────────────────────────┘             │
└──────────────────────────┬──────────────────────────────────┘
                           │
┌──────────────────────────▼──────────────────────────────────┐
│                    代码生成后端                               │
│              LLVM IR → 机器代码 / Cranelift                  │
└─────────────────────────────────────────────────────────────┘
```

> **关键设计决策**:
>
> - **查询系统**: 编译步骤表示为可缓存的查询（`tcx.type_of(def_id)`），天然支持增量编译
> - **TyCtxt**: 编译期间的只读全局上下文，包含所有类型信息、解析结果、中间表示
> - **多阶段降级**: Source → TokenStream → AST → HIR → MIR → LLVM IR → Machine Code
>
> **来源**: [Rustc Dev Guide — Overview](https://rustc-dev-guide.rust-lang.org/overview.html) · [rustc_driver](https://doc.rust-lang.org/nightly/nightly-rustc/rustc_driver/)

### 1.2 编译管线
>

```text
Rust 编译管线（六阶段降级）:

Phase 1 — 源文件 (Source)
  .rs 文件 → 字符串

Phase 2 — 词法分析 (Lexing)
  字符串 → TokenStream（词法单元序列）
  例: "fn main() {}" → [Fn, Ident("main"), OpenParen, CloseParen, OpenBrace, CloseBrace]

Phase 3 — 语法分析 (Parsing) + 宏展开
  TokenStream → AST（抽象语法树）
  宏在 AST 层级展开

Phase 4 — HIR 降级 + 类型检查
  AST → HIR（高级中间表示）
  名称解析、类型推断、Trait 解析

Phase 5 — MIR 降级 + 借用检查 + 优化
  HIR → MIR（中级中间表示）
  NLL/Polonius 借用检查、MIR 优化、常量求值

Phase 6 — 代码生成
  MIR → LLVM IR（或 Cranelift IR）
  LLVM 优化、机器代码生成
```

| **阶段** | **输入** | **输出** | **核心 crate** | **关键操作** |
|:---|:---|:---|:---|:---|
| 词法分析 | `.rs` 源码 | `TokenStream` | `rustc_lexer` | Unicode 识别、注释剥离 |
| 语法分析 | `TokenStream` | `AST` | `rustc_parse` | 递归下降解析、错误恢复 |
| 宏展开 | `AST` | 展开后的 `AST` | `rustc_expand` | 声明宏/过程宏求值 |
| HIR 构建 | `AST` | `HIR` | `rustc_hir` | 去语法糖、名称解析 |
| 类型检查 | `HIR` | 类型化 `HIR` | `rustc_typeck` | Trait 解析、类型推断 |
| MIR 构建 | `HIR` | `MIR` | `rustc_mir_build` | 控制流图、基本块 |
| 借用检查 | `MIR` | 验证后的 `MIR` | `rustc_borrowck` | NLL/Polonius/Tree Borrows |
| 代码生成 | `MIR` | `LLVM IR` | `rustc_codegen_llvm` | LLVM 优化、目标代码生成 |

> **来源**: [Rustc Dev Guide — Compilation](https://rustc-dev-guide.rust-lang.org/compiler-src.html) · [Rust Reference — Compilation Model](https://doc.rust-lang.org/reference/linkage.html)

---

## 二、概念属性矩阵

| **维度** | **rustc** | **GCC** | **Clang** | **Cranelift** |
|:---|:---|:---|:---|:---|
| **前端语言** | Rust | C/C++/Fortran... | C/C++/Obj-C | IR（任何前端）|
| **中间表示** | HIR → MIR | GIMPLE | AST → LLVM IR | CLIF |
| **类型系统** | 强类型 + Trait | C 弱类型 / C++ 模板 | C++ 模板 | 无（前端负责）|
| **借用检查** | ✅ NLL/Polonius | ❌ 手动 | ❌ 手动 | ❌ |
| **增量编译** | ✅ 查询系统 | ⚠️ PCH | ⚠️ Modules | ❌ |
| **后端** | LLVM / Cranelift | RTL | LLVM | 自研 |
| **宏系统** | 声明 + 过程宏 | C 预处理器 | 预处理器 | 无 |
| **编译速度** | 中（优化后慢）| 快 | 中 | 快 |

> **来源**: [Rustc Dev Guide](https://rustc-dev-guide.rust-lang.org/) · [LLVM](https://llvm.org/docs/) · [Cranelift](https://github.com/bytecodealliance/wasmtime/blob/main/cranelift/docs/ir.md)

---

## 三、前端：解析与 AST

### 3.1 词法与语法分析
>

```text
Rust 语法分析的特点:
  - 递归下降 + 操作符优先级解析（Pratt Parser）
  - 错误恢复：遇到语法错误后继续解析，报告多个错误
  - 宏友好：TokenStream 保留原始 token 信息，支持宏的卫生性（hygiene）
```

```rust,ignore
// rustc 中的 AST 节点示例（简化）
pub enum ExprKind {
    Binary(BinOp, P<Expr>, P<Expr>),      // a + b
    Unary(UnOp, P<Expr>),                 // !a
    Call(P<Expr>, Vec<P<Expr>>),          // foo(a, b)
    MethodCall(PathSegment, P<Expr>, Vec<P<Expr>>), // obj.method(a)
    Lit(token::Lit),                       // 42, "hello"
    Block(P<Block>),                       // { ... }
    Async(Async, CaptureBy, P<Block>),     // async { ... }
    Await(P<Expr>),                        // expr.await
    // ...
}
```

> **来源**: [Rustc Dev Guide — Parsing](https://rustc-dev-guide.rust-lang.org/the-parser.html)

### 3.2 宏展开
>

宏在 **AST 层级**展开，而非文本替换（与 C 预处理器不同）。

```text
宏展开顺序:
  1. 声明宏（macro_rules!）: 模式匹配 + token 替换
  2. 过程宏（Proc Macro）: 编译器调用外部 crate 的函数，传入 TokenStream，返回新 TokenStream
     ├── Derive宏: #[derive(Debug)] → 自动生成 impl Debug
     ├── Attribute宏: #[test] → 标记测试函数
     └── Function-like宏: sql!("SELECT * FROM users")

  卫生性（Hygiene）: 宏生成的标识符与调用者作用域隔离
    macro_rules! make_var {
        ($name:ident) => { let $name = 42; }
    }
    make_var!(x);  // x 只在宏展开的作用域内可见
```

> **来源**: [Rust Reference — Macros](https://doc.rust-lang.org/reference/macros.html) · [Rustc Dev Guide — Macro Expansion](https://rustc-dev-guide.rust-lang.org/macro-expansion.html)

---

## 四、HIR：高级中间表示

### 4.1 HIR 的设计目标
>

HIR（High-level IR）是 AST 的**去语法糖**版本，设计目标：

1. **简化后续分析**: 消除语法糖（如 `?` 运算符、`for` 循环、`if let`）
2. **名称解析完成**: 所有标识符已解析为 `DefId`
3. **类型无关**: HIR 本身不包含类型信息（类型检查在 HIR 上进行）

```text
AST → HIR 的降级示例:

for i in 0..10 { println!("{}", i); }
  ↓
{
    let mut iter = IntoIterator::into_iter(0..10);
    loop {
        match Iterator::next(&mut iter) {
            Some(i) => { println!("{}", i); }
            None => break,
        }
    }
}
```

> **来源**: [Rustc Dev Guide — HIR](https://rustc-dev-guide.rust-lang.org/hir.html)

### 4.2 类型检查
>

类型检查在 HIR 上进行，核心组件：

- **类型推断**: Hindley-Milner 风格的约束求解（但 Rust 比 HM 更复杂，因为有子类型、Trait）
- **Trait 解析**: 判断 `impl Trait for Type` 是否满足某个 bound
- **方法解析**: 根据参数类型选择正确的方法实现（包括自动解引用 `Deref`）

```rust,ignore
// 类型推断的简化示例
fn infer_example() {
    let x = vec![1, 2, 3];        // x: Vec<i32>（从元素推断）
    let y = x.iter().sum();        // y: i32（sum() 要求 Numeric）
    let z: f64 = y.into();         // z: f64（显式标注，验证 i32: Into<f64>）
}

// Trait 解析
fn use_debug<T: Debug>(t: T) { println!("{:?}", t); }
use_debug(42);  // 检查 i32: Debug → 是（标准库实现）
```

> **来源**: [Rustc Dev Guide — Type Checking](https://rustc-dev-guide.rust-lang.org/type-checking.html) · [Chalk Book](https://rust-lang.github.io/chalk/book/)

---

## 五、类型系统实现

### 5.1 Trait 解析与 Chalk
>

> **[Chalk — Rust PL](https://rust-lang.github.io/chalk/book/)** Chalk 是 Rust 的实验性 Trait 求解器，基于 **Datalog 风格的逻辑编程**。rustc 的传统 Trait 求解器是专用算法（Fulfilment / Selection），而 Chalk 的目标是统一和形式化 Trait 解析。

```text
Trait 求解的核心问题:
  给定约束 "T: Debug"，判断是否存在满足条件的实现。

Chalk 的方法:
  将 Trait 系统编码为逻辑规则（Horn 子句）：
    Vec<T>: Debug :- T: Debug.        // 若 T: Debug，则 Vec<T>: Debug
    i32: Debug.                        // i32 直接实现 Debug

  查询 "Vec<i32>: Debug" 的求解:
    Vec<i32>: Debug ?
    → 应用规则 Vec<T>: Debug :- T: Debug，T = i32
    → 子目标: i32: Debug ?
    → 事实: i32: Debug.
    → ✅ 满足

Chalk vs rustc 传统求解器:
  ┌─────────────────┬─────────────────┬─────────────────────────────┐
  │     特性        │  rustc 传统     │         Chalk              │
  ├─────────────────┼─────────────────┼─────────────────────────────┤
  │ 算法            │ 专用（SLG-like）│ Datalog + 逻辑求解          │
  │ 形式化验证      │ 困难            │ 更容易（基于逻辑编程）       │
  │ 性能            │ 优化过，生产可用 │ 较慢（实验性）              │
  │ 递归 Trait      │ 有限支持        │ 更自然（co-induction）       │
  │ GAT / 高阶类型   │ 部分支持        │ 设计目标                    │
  └─────────────────┴─────────────────┴─────────────────────────────┘
```

> **来源**: [Chalk Book](https://rust-lang.github.io/chalk/book/) · [Niko Matsakis — Chalk](https://smallcultfollowing.com/babysteps/blog/2017/01/26/lowering-rust-traits-to-logic/)

### 5.2 类型推断
>

Rust 的类型推断基于 **约束生成 + 统一**（Constraint Generation + Unification），但比 Hindley-Milner 更复杂：

```text
Rust 类型推断的特点:
  1. 双向推断（Bidirectional）: 期望类型（Expected type）与实际类型（Actual type）同时考虑
  2. 子类型关系: 生命周期子类型（'a: 'b）参与推断
  3. Trait bound: 类型变量可受 Trait bound 约束（T: Iterator）
  4. 闭包捕获: 推断闭包捕获哪些变量（`move` 或引用）

类型推断的限制:
  - 函数签名必须显式标注（除闭包参数外）
  - 泛型参数必须可推断（通常通过函数参数）
  - `collect()` 需要显式类型标注（因为多个类型可实现 `FromIterator`）
```

> **来源**: [Rust Reference — Type Inference](https://doc.rust-lang.org/reference/type-inference.html) · [Rustc Dev Guide — Type Checking](https://rustc-dev-guide.rust-lang.org/type-checking.html)

---

## 六、MIR：中级中间表示

### 6.1 MIR 的结构
>

MIR（Mid-level IR）是 rustc 的核心中间表示，设计目标：**简化借用检查、支持优化、统一控制流**。

```text
MIR 结构:
  - 函数体 = 控制流图（CFG）
  - 节点 = 基本块（Basic Block）
  - 边 = 跳转（Goto / SwitchInt / Return / Unwind）
  - 语句（Statement）: 无副作用的赋值（Assign、StorageLive、StorageDead）
  - 终止符（Terminator）: 控制流转移（Goto、Call、SwitchInt、Return）

MIR 语句示例:
  bb0: {
      _1 = 5;                    // 赋值语句
      _2 = _1;                   // 复制
      _3 = std::option::Option<i32>::Some(_2);  // 构造枚举
      goto -> bb1;               // 终止符: 跳转到 bb1
  }

  bb1: {
      switchInt(move _3) -> [0: bb2, otherwise: bb3];  // match 分支
  }
```

```rust,ignore
// Rust 源代码
fn example(x: Option<i32>) -> i32 {
    match x {
        Some(v) => v * 2,
        None => 0,
    }
}

// 对应的 MIR（概念等价）
fn example(_1: Option<i32>) -> i32 {
    let mut _0: i32;              // 返回值
    let mut _2: i32;

    bb0: {
        switchInt(move _1) -> [0: bb1, 1: bb2, otherwise: bb3];
    }

    bb1: {  // None
        _0 = const 0_i32;
        goto -> bb4;
    }

    bb2: {  // Some
        _2 = ((_1 as Some).0: i32);
        _0 = Mul(_2, const 2_i32);
        goto -> bb4;
    }

    bb3: {  // unreachable
        unreachable;
    }

    bb4: {
        return;
    }
}
```

> **来源**: [Rustc Dev Guide — MIR](https://rustc-dev-guide.rust-lang.org/mir/index.html)

### 6.2 MIR 优化
>

```text
MIR 优化阶段（在 borrowck 之后、codegen 之前）:
  1. ConstProp: 常量传播
  2. SimplifyCfg: 简化控制流图（删除死代码、合并基本块）
  3. Inline: 函数内联
  4. InstCombine: 指令组合（如 x * 1 → x）
  5. CopyProp: 复制传播
  6. DeadStoreElimination: 死存储消除

优化级别:
  - -C opt-level=0: 无优化（默认 debug）
  - -C opt-level=1: 基本优化
  - -C opt-level=2: 标准优化（默认 release）
  - -C opt-level=3: 激进优化
  - -C opt-level=s: 优化代码大小
  - -C opt-level=z: 极致代码大小优化
```

> **来源**: [Rustc Dev Guide — Optimizations](https://rustc-dev-guide.rust-lang.org/optimizations.html)

### 6.3 常量求值（MIRI / Const Eval）
>

```text
常量求值在编译期执行 MIR:
  - const fn: 编译期可执行的函数
  - const 值: 编译期计算的常量
  - static 值: 编译期初始化的静态变量

常量求值的限制:
  - 不能有副作用（I/O、堆分配）
  - 不能有循环（早期限制，现已放宽）
  - 不能有 panic（早期限制，现已部分放宽）
  - 不能有浮点运算（早期限制，现已放宽）

MIRI（MIR Interpreter）:
  - 编译器内部的 MIR 解释器
  - 用于常量求值和编译期检查
  - 独立工具 miri 用于运行时 UB 检测
```

> **来源**: [Rustc Dev Guide — Const Evaluation](https://rustc-dev-guide.rust-lang.org/const-eval/interpretation.html) · [MIRI](https://github.com/rust-lang/miri)

---

## 七、借用检查器

### 7.1 NLL（Non-Lexical Lifetimes）
>

> **[Niko Matsakis — Rust Blog](https://smallcultfollowing.com/babysteps/blog/2016/04/27/non-lexical-lifetimes-introduction/)** NLL 是 Rust 2018 Edition 引入的借用检查改进，核心洞察：**引用的有效性应基于实际使用位置，而非词法作用域**。

```text
NLL 之前的词法生命周期:
  {
      let x = &mut data;  // x 的生命周期 = 整个块
      x.push(1);
      // 即使不再使用 x，借用仍"活跃"
      data.len();  // ❌ 编译错误: x 仍借用 data
  }

NLL 之后的非词法生命周期:
  {
      let x = &mut data;  // x 的生命周期 = 最后一次使用
      x.push(1);
      // x 的最后一次使用在此结束
      data.len();  // ✅ NLL 允许: x 的借用已结束
  }

NLL 的实现:
  - 基于 MIR 的控制流图分析
  - 计算每个引用的"实际使用范围"（live range）
  - 检查借用在整个 live range 内不冲突
```

> **来源**: [Rust RFC 2094 — NLL](https://rust-lang.github.io/rfcs/2094-nll.html) · [Niko Matsakis — NLL](https://smallcultfollowing.com/babysteps/blog/2016/04/27/non-lexical-lifetimes-introduction/)

### 7.2 Polonius：基于逻辑的借用检查
>

> **[Polonius — OOPSLA 2018](https://hal.inria.fr/hal-03827702/)** Polonius 是下一代 Rust 借用检查器，基于 **Datalog 风格的逻辑编程**（与 Chalk 类似），目标是解决 NLL 的**位置敏感性**（Location Sensitivity）问题。

```text
Polonius 的核心问题:
  NLL 无法处理 "基于路径的条件借用":
    let mut data = vec![1, 2, 3];
    if condition {
        let x = &mut data;
        x.push(4);
    } else {
        data.push(5);  // ❌ NLL 错误: data 仍被借用
    }
    // Polonius 分析: 两个分支互斥，不会同时活跃

Polonius 的方法:
  1. 将借用检查编码为 Datalog 规则
  2. 计算 "出借点"（loan origin）和 "使用点"（use site）
  3. 检查是否存在从出借点到使用点的有效路径

Polonius 状态（2025）:
  - Alpha 版本已进入 nightly（-Zpolonius）
  - 2026 目标: 稳定化（替代 NLL 成为默认）
  - 解决了 NLL problem case #3（lending iterator）
```

> **来源**: [Polonius Paper — OOPSLA 2018](https://hal.inria.fr/hal-03827702/) · [Rustc Dev Guide — Polonius](https://rustc-dev-guide.rust-lang.org/borrow_check/polonius.html) · [Niko Matsakis — Polonius](https://smallcultfollowing.com/babysteps/blog/2019/01/21/polonius-and-region-errors/)

### 7.3 别名模型：Tree Borrows
>

> **[Tree Borrows — PLDI 2025 Distinguished Paper](https://perso.crans.org/vanille/treebor/)** Tree Borrows 是 Miri 的实验性别名模型，目标是替代 Stacked Borrows，提供更精确、更宽容的引用行为分析。

```text
Stacked Borrows vs Tree Borrows:
  ┌─────────────────┬─────────────────┬─────────────────────────────┐
  │     特性        │ Stacked Borrows │      Tree Borrows           │
  ├─────────────────┼─────────────────┼─────────────────────────────┤
  │ 模型            │ 栈（LIFO）      │ 树（父子关系）              │
  │ 共享借用转独占   │ ❌ 通常禁止     │ ✅ 某些条件下允许           │
  │ _interior_mut    │ 严格            │ 更宽松                     │
  │ 与 unsafe 兼容   │ 较严格          │ 更兼容实际 unsafe 代码      │
  │ Miri 默认        │ 曾经是          │ 现在是默认                 │
  └─────────────────┴─────────────────┴─────────────────────────────┘

Tree Borrows 的核心规则:
  - 每次创建引用时，在"借用树"中添加一个节点
  - 父节点（原始指针）可以访问子节点（引用）允许的内存
  - 子节点不能访问父节点不允许的内存
  - 读取操作向下传播（父 → 子），写入操作向上验证（子 → 父）
```

> **来源**: [Tree Borrows Paper — PLDI 2025](https://perso.crans.org/vanille/treebor/) · [Rustc Dev Guide — Tree Borrows](https://rustc-dev-guide.rust-lang.org/mir/index.html) · [Miri Book — Tree Borrows](https://github.com/rust-lang/miri/blob/master/borrow_tracker/tree_borrows.md)

---

## 八、后端：代码生成

### 8.1 LLVM IR 生成
>

rustc 的默认后端是 LLVM，MIR 被翻译为 LLVM IR，然后由 LLVM 优化和代码生成。

```text
MIR → LLVM IR 的映射:
  - MIR 基本块 → LLVM basic block
  - MIR 类型 → LLVM type
  - MIR 调用约定 → LLVM calling convention
  - Rust 的 enum → LLVM struct + discriminant
  - Rust 的 trait object → LLVM struct { vtable*, data* }
  - Rust 的闭包 → LLVM struct { 环境字段..., 函数指针 }

LLVM 优化管道:
  - rustc 在 LLVM IR 上运行标准优化（-C opt-level=2 时）
  - 关键优化: 内联、常量传播、死代码消除、循环优化、向量化
  - Rust 特有的优化: 单态化后的函数去重、panic 路径优化
```

> **来源**: [LLVM Documentation](https://llvm.org/docs/) · [Rustc Dev Guide — Code Generation](https://rustc-dev-guide.rust-lang.org/backend/index.html)

### 8.2 增量编译
>

```text
增量编译原理:
  - 编译步骤表示为查询（Query），每个查询有唯一标识（基于输入的 hash）
  - 查询结果缓存到磁盘（`target/incremental/`）
  - 第二次编译时，只有变更的查询重新执行

查询系统示例:
  tcx.type_of(def_id)          // 获取某定义的类型
  tcx.mir_borrowck(def_id)     // 对某函数执行借用检查
  tcx.optimized_mir(def_id)    // 获取优化后的 MIR

增量编译的限制:
  - 泛型单态化: 每个单态化实例是独立的，修改泛型函数可能影响大量调用点
  -  crate 边界: 跨 crate 的 inline 函数修改需要重新编译所有调用者
  -  配置变更: Cargo.toml 或 feature flag 变更通常触发全量编译
```

> **来源**: [Rustc Dev Guide — Queries](https://rustc-dev-guide.rust-lang.org/query.html) · [Rustc Dev Guide — Incremental Compilation](https://rustc-dev-guide.rust-lang.org/queries/incremental-compilation.html)

---

## 九、查询系统

```text
rustc 查询系统的核心设计:

查询 = 纯函数: Input → Output
  - 无副作用（只读访问 TyCtxt）
  - 确定性（相同输入总是产生相同输出）
  - 可缓存（输出写入磁盘，下次直接读取）

查询依赖图:
  type_check(fn_main)
    ├── resolve_name("foo") → DefId(42)
    ├── type_of(DefId(42)) → fn(i32) -> i32
    └── trait_bound_check(i32: Debug)
          └── impl_debug_for_i32 → ✅

优势:
  - 增量编译天然支持
  - 并行化: 无依赖的查询可并行执行
  - 调试: 查询追踪（-Z self-profile）精确显示编译时间分布
```

> **来源**: [Rustc Dev Guide — Query System](https://rustc-dev-guide.rust-lang.org/query.html)

---

## 十、反命题与边界

### 10.1 反命题树
>

```text
反命题 1: "Rust 编译器比 C++ 编译器慢是因为借用检查器"
├── 前提: 借用检查是 rustc 的主要性能瓶颈
├── 反驳:
│   ├── LLVM 优化通常占编译时间的 50-70%
│   ├── 单态化（Monomorphization）导致代码膨胀，增加 LLVM 工作量
│   ├── 宏展开和过程宏可能生成大量代码
│   └── 借用检查器（NLL）已高度优化，通常 < 10% 编译时间
└── 根结论: ❌ 编译速度的主要瓶颈是 LLVM 优化和单态化，不是借用检查器。

反命题 2: "MIRI 可以检测所有 UB"
├── 前提: Miri 是 Rust 的完备 UB 检测器
├── 反驳:
│   ├── Miri 不能检测并发数据竞争（需要 special 的 -Zmiri-disable-isolation）
│   ├── Miri 不能检测平台相关的 UB（如未对齐访问在某些平台合法）
│   ├── Miri 不能检测常量时间的违反（侧信道）
│   └── Miri 的 Tree Borrows 是实验性模型，可能与最终内存模型不同
└── 根结论: ❌ Miri 是强大的 UB 检测工具，但不是完备的。它是"尽可能检测"而非"保证检测所有"。

反命题 3: "Polonius 稳定后将完全解决所有借用检查痛点"
├── 前提: Polonius 比 NLL 更精确，因此没有限制
├── 反驳:
│   ├── Polonius 仍然基于 ownership + borrowing 模型，不支持共享可变
│   ├── 某些复杂的自引用结构仍然难以表达（需要 Pin 或 unsafe）
│   ├── Polonius 的计算复杂度高于 NLL，极端情况下编译时间增加
│   └── 语言的根本限制（线性逻辑）不会因为求解器改进而消失
└── 根结论: ❌ Polonius 显著改进借用检查，但不会消除所有权系统的所有限制。
```

### 10.2 边界极限
>

| **边界** | **现状** | **理论极限** | **工程影响** |
|:---|:---|:---|:---|
| **编译时间** | 中项目 10-60s | LLVM 优化是下限 | Cranelift 后端可加速 debug 构建 |
| **单态化膨胀** | 典型 2-5x | 无上限 | 动态分发（dyn Trait）替代 |
| **增量编译粒度** | 查询级 | 语句级（理论上）| 磁盘 I/O 开销 |
| **借用检查精度** | NLL / Polonius Alpha | 完整流敏感分析 | 编译时间指数增长 |
| **常量求值深度** | 有限（循环/递归限制）| 停机问题不可判定 | 超时保护 |

> **来源**: [Rustc Dev Guide — Performance](https://rustc-dev-guide.rust-lang.org/profiling.html) · [Polonius Paper](https://hal.inria.fr/hal-03827702/)

---

## 十一、边界测试

### 11.1 边界测试：递归宏展开导致栈溢出（编译错误）

```rust,compile_fail
// ❌ 错误：递归宏无终止条件
macro_rules! infinite_expand {
    () => { infinite_expand!() };  // 无限递归展开
}

fn main() {
    infinite_expand!();
    // 编译器错误: "recursion limit reached"
    // 默认递归限制: 128 层
}
```

> **修正**: 宏递归必须有终止条件。
> 编译器通过 `recursion_limit` 控制最大展开深度（默认 128），可通过 `#![recursion_limit = "256"]` 增加。
> [来源: [Rust Reference — Macros](https://doc.rust-lang.org/reference/macros-by-example.html)]

### 11.2 边界测试：泛型单态化导致二进制膨胀（编译/链接错误）

```rust,ignore
// ❌ 错误：过度使用泛型导致代码膨胀
fn process<T: Debug>(items: Vec<T>) { /* ... */ }

// 每个不同的 T 生成一份独立代码:
process::<i32>(vec);     // 生成 process_i32
process::<String>(vec);  // 生成 process_String
process::<Vec<u8>>(vec); // 生成 process_Vec_u8
// 若有 100 个不同类型调用 → 100 份代码 → 二进制巨大
```

> **修正**: 使用 `dyn Trait` 动态分发替代泛型：
>
> ```rust
> fn process(items: Vec<Box<dyn Debug>>) { /* 单份代码 */ }
> ```
>
> 权衡: 泛型 = 零成本 + 代码膨胀；动态分发 = 运行时开销 + 代码紧凑。
> [来源: [Rust Reference — Dynamically Sized Types](https://doc.rust-lang.org/reference/dynamically-sized-types.html)]

### 11.3 边界测试：unsafe 代码在 Miri 中触发 UB（运行时错误）

```rust,ignore
// ❌ 错误：Miri 检测到的 UB
fn undefined_behavior() {
    let mut x = 42;
    let r1 = &mut x as *mut i32;
    let r2 = &mut x as *mut i32;  // 两个可变裸指针指向同一内存
    unsafe {
        *r1 = 1;
        *r2 = 2;  // Miri: 数据竞争！两个 &mut 重叠
    }
}

// Miri 运行:
// $ cargo +nightly miri run
// error: Undefined Behavior: attempting a write access using <tag>
//        at alloc[...], but that tag does not exist in the borrow stack
```

> **修正**: Miri 是检测 unsafe 代码 UB 的强大工具，但需在 CI 中定期运行（因为它只检测执行到的代码路径）。不能替代代码审查。
> [来源: [MIRI Book](https://github.com/rust-lang/miri)] ·
> [Rustonomicon — Undefined Behavior](https://doc.rust-lang.org/nomicon/what-unsafe-does.html)

---

## 相关概念文件

- [类型系统](../01_foundation/04_type_system.md) — 类型论基础
- [泛型](../02_intermediate/02_generics.md) — 单态化、Trait bound
- [生命周期](../01_foundation/03_lifetimes.md) — 借用规则、NLL
- [Trait](../02_intermediate/01_traits.md) — 多态、Trait 解析
- [Async/Await](../03_advanced/02_async.md) — 状态机转换、MIR 生成
- [宏系统](../03_advanced/07_proc_macro.md) — 宏展开、 hygiene
- [Unsafe Rust](../03_advanced/03_unsafe.md) — Miri、UB、别名模型
- [NLL 与 Polonius](../03_advanced/08_nll_and_polonius.md) — 借用检查演进
- [形式化验证](../04_formal/05_verification_toolchain.md) — Kani、Prusti、MIRI
- [工具链](../06_ecosystem/01_toolchain.md) — Cargo、编译器标志、目标平台


> [来源: [LLVM Compiler Infrastructure](https://llvm.org/)]


> [来源: [The Dragon Book — Aho et al.](https://dl.acm.org/doi/book/10.5555/1177220)]
