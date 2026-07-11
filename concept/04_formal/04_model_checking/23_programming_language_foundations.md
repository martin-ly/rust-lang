> **内容分级**: [专家级]

# 通用程序语言理论基础：Rust 的 PL 基座
>
> **EN**: Programming Language Foundations
> **Summary**: Programming Language Foundations: formal methods foundations, semantics, and verification techniques relevant to Rust.
> **受众**: [研究者]
> ⚠️ **声明**: 本文件使用形式化符号辅助直觉理解，所呈现的"定理/引理/推论"为**教学类比**，非经机器验证的严格数学证明。如需严格形式化验证，请参考 [Verus](https://github.com/verus-lang/verus)、[Kani](https://model-checking.github.io/kani/)、[Coq](https://coq.inria.fr/)。
>
> **Bloom 层级**: L5-L6
> **权威来源**: 本文件为 `concept/` 权威页。
> **定位**: 从通用程序语言（PL）理论视角审视 Rust 的设计根基，建立从 λ 演算到 Rust 类型系统（Type System）的概念桥梁。
> **前置概念**: [Type Theory](../00_type_theory/02_type_theory.md) · [Linear Logic](../01_ownership_logic/01_linear_logic.md) · [Ownership Formal](../01_ownership_logic/03_ownership_formal.md) · [Unsafe Rust](../../03_advanced/02_unsafe/03_unsafe.md)
> **后置延伸**: [Effects System](../../07_future/03_preview_features/04_effects_system.md) · [Evolution](../../07_future/04_research_and_experimental/03_evolution.md)
>
> **来源**: [Rust Reference](https://doc.rust-lang.org/reference/introduction.html) · [RustBelt](https://plv.mpi-sws.org/rustbelt/) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
---

> **来源**: [TAPL — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/) · [SF — Software Foundations](https://softwarefoundations.cis.upenn.edu/) · [CS 242 Stanford](https://stanford-cs242.github.io/f19/) · [RustBelt](https://plv.mpi-sws.org/rustbelt/)
> **后置概念**: [Comparative Studies](../../05_comparative/01_systems_languages/01_rust_vs_cpp.md)

## 目录

- [通用程序语言理论基础：Rust 的 PL 基座](#通用程序语言理论基础rust-的-pl-基座)
  - [目录](#目录)
  - [一、为什么需要 PL 基座](#一为什么需要-pl-基座)
  - [二、求值策略（Evaluation Strategy）](#二求值策略evaluation-strategy)
    - [2.1 三种基本策略](#21-三种基本策略)
    - [2.2 Rust 的 CBV 与 Move 语义](#22-rust-的-cbv-与-move-语义)
    - [2.3 为什么 Rust 不是 CBN/CBNeed](#23-为什么-rust-不是-cbncbneed)
  - [三、副作用模型（Effect System）](#三副作用模型effect-system)
    - [3.1 什么是副作用](#31-什么是副作用)
    - [3.2 Rust 的副作用控制](#32-rust-的副作用控制)
    - [3.3 与 Haskell IO Monad 的对比](#33-与-haskell-io-monad-的对比)
  - [四、Continuation 与 CPS](#四continuation-与-cps)
    - [4.1 什么是 Continuation](#41-什么是-continuation)
    - [4.2 async/await 是 CPS 的语法糖](#42-asyncawait-是-cps-的语法糖)
    - [4.3 Pin 与 Continuation 的安全性](#43-pin-与-continuation-的安全性)
  - [五、结构化程序定理与 Rust 控制流](#五结构化程序定理与-rust-控制流)
    - [5.1 结构化程序定理](#51-结构化程序定理)
    - [5.2 Rust 的类型驱动控制流](#52-rust-的类型驱动控制流)
  - [六、变量模型：环境 vs 存储](#六变量模型环境-vs-存储)
    - [6.1 两个概念](#61-两个概念)
    - [6.2 Rust 的所有权作为存储约束](#62-rust-的所有权作为存储约束)
  - [七、来源与参考](#七来源与参考)
  - [嵌入式测验（Embedded Quiz）](#嵌入式测验embedded-quiz)
    - [测验 1：Lambda 演算（Lambda Calculus）为什么被称为"编程语言的汇编语言"？（理解层）](#测验-1lambda-演算lambda-calculus为什么被称为编程语言的汇编语言理解层)
    - [测验 2：什么是"柯里化"（Currying）？Rust 的闭包支持柯里化吗？（理解层）](#测验-2什么是柯里化curryingrust-的闭包支持柯里化吗理解层)
    - [测验 3：系统 F（System F）是什么？Rust 的泛型与它有什么关系？（理解层）](#测验-3系统-fsystem-f是什么rust-的泛型与它有什么关系理解层)
    - [测验 4：什么是"停机问题"（Halting Problem）？它对程序验证有什么实际影响？（理解层）](#测验-4什么是停机问题halting-problem它对程序验证有什么实际影响理解层)
    - [测验 5：类型论中的"依赖类型"（Dependent Types）是什么？Rust 目前支持依赖类型吗？（理解层）](#测验-5类型论中的依赖类型dependent-types是什么rust-目前支持依赖类型吗理解层)
  - [认知路径](#认知路径)
    - [核心推理链](#核心推理链)
    - [反命题与边界](#反命题与边界)

## 一、为什么需要 PL 基座

Rust 的独特性（所有权（Ownership）、借用（Borrowing）、生命周期（Lifetimes））常被描述为"工程创新"，但它们深植于**数十年的 PL 理论研究**。理解这些根基，才能：

1. **区分本质与实现**: 哪些特性是 Rust 独有，哪些是 PL 理论的必然
2. **预测语言演进**: 基于理论判断某特性是否可安全加入
3. **跨语言对比**: 解释为什么 C++ move 不安全而 Rust move 安全

---

## 二、求值策略（Evaluation Strategy）

### 2.1 三种基本策略

| 策略 | 名称 | 核心规则 | 代表语言 |
|:---|:---|:---|:---|
| **CBV** | Call-by-Value | 先求值参数，再代入 | Rust, C, Java, Scheme |
| **CBN** | Call-by-Name | 直接代入参数表达式，需要时才求值 | Haskell (近似), Algol 60 |
| **CBNeed** | Call-by-Need | CBN + 结果缓存（惰性求值）| Haskell |

### 2.2 Rust 的 CBV 与 Move 语义

Rust 是 **CBV 语言**，但参数的"值"是**有所有权（Ownership）**的：

```rust
fn take(s: String) { /* s 获得所有权 */ }

fn main() {
    let x = String::from("hello");
    take(x);        // x 的所有权 move 到 take 的参数
    // x 在此不可用 —— 这不是 CBN 的延迟求值，而是 CBV + 所有权移动
}
```

**与 C++ 的对比**:

```cpp
// C++: 默认是 copy，move 是优化（非语义必需）
void take(std::string s) { }
std::string x = "hello";
take(x);           // 可能 copy 或 move，取决于优化
// x 可能仍有效（如果发生 copy）
```

```rust
// Rust: move 是语义必需，不是优化
fn take(s: String) { }
let x = String::from("hello");
take(x);           // 语义上 x 被 move，编译器保证 x 之后不可用
```

> **关键洞察**: Rust 的 move 不是"更快的 copy"，而是 **CBV 求值在所有权（Ownership）类型系统（Type System）中的必然结果**——值被求值后传递给函数，原绑定点失去访问权。

### 2.3 为什么 Rust 不是 CBN/CBNeed

| 特性 | CBN/CBNeed | Rust (CBV) |
|:---|:---|:---|
| 副作用顺序 | 不可预测 | 确定性（从左到右） |
| 资源管理 | 困难（何时释放？） | RAII + 所有权（Ownership），确定性 |
| 性能模型 |  thunk 分配开销 | 栈分配为主，零成本抽象（Zero-Cost Abstraction） |
| 与底层交互 | 不自然 | 直接映射硬件模型 |

Rust 选择 CBV 是因为系统编程需要**确定性的资源管理和副作用顺序**。

---

## 三、副作用模型（Effect System）

### 3.1 什么是副作用

程序中的**副作用**是改变程序外部状态或依赖外部状态的操作：

```text
纯函数: f(x) → y          无副作用，相同输入必得相同输出
副作用: f(x) → y + 修改全局状态 / I/O / 随机数 / 抛出异常
```

### 3.2 Rust 的副作用控制

Rust 没有完整的**代数效应系统（Algebraic Effects）**，但通过类型系统（Type System）实现了细粒度副作用控制：

| 副作用类型 | Rust 控制机制 | 示例 |
|:---|:---|:---|
| **内存修改** | `&mut T` / `&T` / `UnsafeCell` | 编译期区分读写权限 |
| **I/O** | `std::io` 模块（Module） | 显式在函数签名中（返回 `io::Result`） |
| **panic** | `Result<T, E>` / `Option<T>` | 鼓励显式错误传播 |
| **并发** | `Send` / `Sync` trait | 编译期验证线程安全 |
| **非局部控制流** | `?` 运算符、`break`/`continue` | 结构化，非 GOTO |
| **unsafe 副作用** | `unsafe` 块 | 将证明责任转移给程序员 |

### 3.3 与 Haskell IO Monad 的对比

```haskell
-- Haskell: IO Monad 将副作用"打包"
main :: IO ()           -- main 是 IO 动作，不是纯函数
main = do
    putStrLn "Hello"    -- putStrLn :: String -> IO ()
    x <- readFile "f"   -- readFile :: FilePath -> IO String
```

```rust
// Rust: 副作用是类型系统的一部分，但不是 Monad
fn main() -> Result<(), std::io::Error> {  // 返回值表达可能的 I/O 错误
    println!("Hello");                      // 副作用直接发生
    let x = std::fs::read_to_string("f")?;  // ? 传播错误，但副作用已发生
    Ok(())
}
```

> **关键差异**: Haskell 通过 **Monad** 将副作用延迟到运行时（Runtime）解释器处理；Rust 通过 **所有权（Ownership） + 生命周期（Lifetimes）** 在编译期证明副作用的局部性和安全性。

---

## 四、Continuation 与 CPS

### 4.1 什么是 Continuation

**Continuation** 是"程序的其余部分"的抽象——表示"当前操作完成后该做什么"。

```rust
// 直接风格 (Direct Style)
fn add(a: i32, b: i32) -> i32 { a + b }

fn main() {
    let x = add(1, 2);      // 计算 1+2
    let y = x * 3;          // 然后乘以 3
    println!("{}", y);      // 然后打印
}
```

```rust
// CPS (Continuation Passing Style) — 显式传递 "接下来做什么"
fn add_cps(a: i32, b: i32, k: impl FnOnce(i32)) { k(a + b); }

fn main() {
    add_cps(1, 2, |x| {           // x = 3
        let y = x * 3;
        println!("{}", y);        // "接下来做什么" 被显式传递
    });
}
```

### 4.2 async/await 是 CPS 的语法糖

Rust 的 `async/await` 本质上是 **CPS 变换的编译器自动化**：

```rust,ignore
// 源代码
async fn fetch_and_process(url: &str) -> Result<String, Error> {
    let data = fetch(url).await?;    // .await = "获取 continuation，暂停当前任务"
    Ok(process(data))
}
```

```rust,ignore
// 编译器生成的近似 CPS 形式（概念性）
fn fetch_and_process<'a>(url: &'a str) -> impl Future<Output = Result<String, Error>> {
    FetchAndProcessStateMachine::Init { url }
}

enum FetchAndProcessStateMachine<'a> {
    Init { url: &'a str },
    AfterFetch { process_future: ProcessFuture },
    Done,
}

impl Future for FetchAndProcessStateMachine<'_> {
    type Output = Result<String, Error>;
    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        match *self {
            Init { url } => {
                // 启动 fetch，注册 continuation：完成后回到此状态机的下一阶段
                *self = AfterFetch { process_future: fetch(url) };
                Poll::Pending
            }
            AfterFetch { ref mut process_future } => {
                match process_future.poll(cx) {
                    Poll::Ready(data) => Poll::Ready(Ok(process(data))),
                    Poll::Pending => Poll::Pending,
                }
            }
            Done => unreachable!(),
        }
    }
}
```

> **关键洞察**: `await` 不是阻塞等待，而是**保存当前 continuation（状态机状态），注册 waker，然后立即返回 `Poll::Pending`**。当外部事件（I/O 完成、定时器到期）发生时，waker 被调用，executor 重新 `poll` 该状态机，从上次保存的 continuation 恢复执行。

### 4.3 Pin 与 Continuation 的安全性

CPS 变换引入的自引用（Reference）状态机需要 **Pin** 来保证安全性：

```rust
// 自引用结构体（async 状态机的核心问题）
struct SelfReferential {
    data: String,
    ptr_to_data: *const String,  // 指向 data 的指针（自引用）
}

// 如果允许移动 SelfReferential，ptr_to_data 将悬垂
// Pin<&mut SelfReferential> 禁止移动，保证 ptr_to_data 始终有效
```

---

## 五、结构化程序定理与 Rust 控制流

### 5.1 结构化程序定理

Böhm 和 Jacopini (1966) 证明：**任何程序都可以用顺序、选择（if）、循环（while）三种结构表达**，无需 GOTO。

Rust 的控制流系统是**结构化**的，但增加了类型安全的扩展：

| 控制结构 | Rust 语法 | 类型安全增强 |
|:---|:---|:---|
| 顺序 | `;` | 表达式类型强制使用返回值 |
| 选择 | `if` / `match` | `match` 穷尽性检查 |
| 循环 | `loop` / `while` / `for` | `break` 可返回值（类型统一） |
| 跳转 | `return` / `break` / `continue` | 不能跳出函数边界（无 longjmp） |
| 异常 | `Result<T, E>` / `panic!` | 错误类型显式，无隐式异常传播 |

### 5.2 Rust 的类型驱动控制流

```rust
// match 穷尽性检查是结构化程序定理的类型化扩展
enum State { On, Off }

fn action(s: State) -> String {
    match s {
        State::On => "running".to_string(),
        State::Off => "stopped".to_string(),
        // 编译器验证: 所有变体已处理，无遗漏 = 结构化安全
    }
}
```

---

## 六、变量模型：环境 vs 存储

### 6.1 两个概念

| 概念 | 定义 | Rust 对应 |
|:---|:---|:---|
| **环境（Environment）** | 变量名到存储位置的映射 | 栈帧中的变量绑定 |
| **存储（Store）** | 存储位置到值的映射 | 内存（栈/堆） |

### 6.2 Rust 的所有权作为存储约束

在传统 PL 中，环境决定变量的**作用域**，存储决定变量的**生命周期（Lifetimes）**。Rust 将两者统一：

```rust
fn example() {
    let x = 42;              // 环境: x → 栈位置 S1
                             // 存储: S1 → 42
    {
        let y = String::from("hello");
                                 // 环境: y → 栈位置 S2
                                 // 存储: S2 → 堆指针 H1 → "hello"
    }                            // y 离开环境 → S2 释放 → H1 被 drop

    // x 仍可用（S1 仍有效）
    println!("{}", x);
}                                // x 离开环境 → S1 释放
```

> **关键洞察**: Rust 的 ownership 是**环境约束在存储层的延伸**——不仅变量离开作用域时释放，而且变量 move 后原绑定点从环境中移除，防止访问已释放的存储。

---

## 七、来源与参考

| 来源 | 可信度 | 说明 |
|:---|:---:|:---|
| [TAPL](https://www.cis.upenn.edu/~bcpierce/tapl/) | ✅ 学术经典 | Types and Programming Languages |
| [SF — Software Foundations](https://softwarefoundations.cis.upenn.edu/) | ✅ 学术经典 | Coq 形式化证明教程 |
| [CS 242 Stanford](https://stanford-cs242.github.io/f19/) | ✅ 学术 | 编程语言基础课程 |
| [RustBelt](https://plv.mpi-sws.org/rustbelt/) | ✅ 一级 | Rust 形式化验证论文 |
| [Oxide](https://arxiv.org/abs/1903.00982) | ✅ 学术 | Rust  borrow checker 形式化 |

---

**文档版本**: 1.0
**Rust 版本**: 1.97.0+
**最后更新**: 2026-06-01
**状态**: ✅ 概念文档创建完成

## 嵌入式测验（Embedded Quiz）

### 测验 1：Lambda 演算（Lambda Calculus）为什么被称为"编程语言的汇编语言"？（理解层）

**题目**: Lambda 演算（Lambda Calculus）为什么被称为"编程语言的汇编语言"？

<details>
<summary>✅ 答案与解析</summary>

因为它是最小化的计算模型，只包含变量、抽象和应用三种构造。任何可计算函数都能用 Lambda 演算表达，是函数式编程语言（包括 Rust 的闭包（Closures））的理论基础。
</details>

---

### 测验 2：什么是"柯里化"（Currying）？Rust 的闭包支持柯里化吗？（理解层）

**题目**: 什么是"柯里化"（Currying）？Rust 的闭包（Closures）支持柯里化吗？

<details>
<summary>✅ 答案与解析</summary>

柯里化是将多参数函数转换为一系列单参数函数的技术，如 `f(x, y)` → `f(x)(y)`。Rust 闭包（Closures）可以手动实现柯里化（返回嵌套闭包），但语言不自动提供。
</details>

---

### 测验 3：系统 F（System F）是什么？Rust 的泛型与它有什么关系？（理解层）

**题目**: 系统 F（System F）是什么？Rust 的泛型（Generics）与它有什么关系？

<details>
<summary>✅ 答案与解析</summary>

系统 F 是带参数多态（泛型）的 Lambda 演算。Rust 的泛型是系统 F 的工业实现，但额外加入了 trait bounds（受限量化）和生命周期（Lifetimes）。
</details>

---

### 测验 4：什么是"停机问题"（Halting Problem）？它对程序验证有什么实际影响？（理解层）

**题目**: 什么是"停机问题"（Halting Problem）？它对程序验证有什么实际影响？

<details>
<summary>✅ 答案与解析</summary>

停机问题证明不存在通用算法能判定任意程序是否终止。这意味着完全自动化的程序正确性验证是不可能的，实际工具只能处理受限子集或需要人工辅助规约。
</details>

---

### 测验 5：类型论中的"依赖类型"（Dependent Types）是什么？Rust 目前支持依赖类型吗？（理解层）

**题目**: 类型论中的"依赖类型"（Dependent Types）是什么？Rust 目前支持依赖类型吗？

<details>
<summary>✅ 答案与解析</summary>

依赖类型允许类型依赖于值（如 `Vec<n>` 表示长度为 n 的向量）。Rust 目前不完全支持，但 `const generics`（如 `[T; N]`）是其受限形式。
</details>

## 认知路径

> **认知路径**: 从 L0 基础概念出发，经由本节的 **通用程序语言理论基础：Rust 的 PL 基座** 核心原理，通向 L2 进阶模式与 L3 工程实践。

### 核心推理链

| 定理 | 前提 | 结论 | 置信度 |
|:---|:---|:---|:---|
| 通用程序语言理论基础：Rust 的 PL 基座 基础定义 ⟹ 正确用法 | 理解语法与语义 | 能写出符合惯用法的代码 | 高 |
| 通用程序语言理论基础：Rust 的 PL 基座 正确用法 ⟹ 常见陷阱 | 忽略边界条件 | 编译错误或运行时（Runtime） bug | 高 |
| 通用程序语言理论基础：Rust 的 PL 基座 常见陷阱 ⟹ 深度掌握 | 系统学习反模式 | 能进行代码审查与优化 | 高 |

> **过渡**: 掌握 通用程序语言理论基础：Rust 的 PL 基座 的基础语法后，下一步需要理解其在类型系统（Type System）中的位置与与其他概念的交互关系。
> **过渡**: 在实践中应用 通用程序语言理论基础：Rust 的 PL 基座 时，务必关注边界条件与异常处理，这是从"能编译"到"能生产"的关键跃迁。
> **过渡**: 通用程序语言理论基础：Rust 的 PL 基座 的设计理念体现了 Rust 零成本抽象（Zero-Cost Abstraction）与安全保证的核心权衡，理解这一权衡有助于迁移到更高级的并发与形式化验证领域。

### 反命题与边界

> **反命题**: "通用程序语言理论基础：Rust 的 PL 基座 在所有场景下都是最佳选择" —— 错误。需要根据具体上下文权衡性能、可读性与安全性，某些场景下显式替代方案可能更优。
---

> **权威来源**: [Verus](https://github.com/verus-lang/verus) · [Kani](https://model-checking.github.io/kani/) · [Rust Reference](https://doc.rust-lang.org/reference/introduction.html) · [RustBelt](https://plv.mpi-sws.org/rustbelt/) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [TAPL — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/) · [Oxide](https://arxiv.org/abs/1903.00982)
> **权威来源对齐变更日志**: 2026-07-10 补全权威来源标注（Rust Reference、TRPL、Rustonomicon、RFCs、学术论文） [Authority Source Sprint Batch L4](../../00_meta/02_sources/international_authority_index.md)

**文档版本**: 1.0
**最后更新**: 2026-07-10
**状态**: ✅ 权威来源对齐完成 (Batch L4)
