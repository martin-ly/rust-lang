> **内容分级**: [综述级]
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **本节关键术语**: 编程语言理论 (PL Theory) · 语法 (Syntax) · 语义 (Semantics) · 求值策略 (Evaluation Strategy) · 副作用 (Side Effect) — [完整对照表](../../00_meta/01_terminology/01_terminology_glossary.md)
>
# 编程语言理论基础（PL Prerequisites）
>
> **EN**: Pl Prerequisites
> **Summary**: Pl Prerequisites — Prerequisite programming-language theory that explains why Rust is designed the way it is.
> **受众**: [初学者]
> **Bloom 层级**: L1-L2
> **权威来源**: 本文件为 `concept/` 权威页。
> **定位**: L1 基础层的**前置知识补充**。理解这些通用 PL 概念后，你将能更深刻地回答"为什么 Rust 要这样设计"，而非仅仅记忆规则。
> **阅读建议**: 可选阅读。若你已有 Haskell/Scheme/OCaml 背景，可跳过；若你只有 Python/JavaScript 背景，强烈建议先读本文。
>
> **来源**: [TRPL — Foreword](https://doc.rust-lang.org/book/foreword.html) · [Rust Reference](https://doc.rust-lang.org/reference/introduction.html) · [Brown University — Concepts in Rust Programming](https://cel.cs.brown.edu/crp/) · [Oxide: The Essence of Rust](https://arxiv.org/abs/1903.00982) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
> **前置概念**: N/A
---

> **后置概念**: [Traits](../../02_intermediate/00_traits/01_traits.md) · [Generics](../../02_intermediate/01_generics/01_generics.md)

## 📑 目录

- [编程语言理论基础（PL Prerequisites）](#编程语言理论基础pl-prerequisites)
  - [📑 目录](#-目录)
  - [一、求值策略（Evaluation Strategies）](#一求值策略evaluation-strategies)
    - [1.1 为什么需要了解求值策略？](#11-为什么需要了解求值策略)
    - [1.2 三种核心求值策略](#12-三种核心求值策略)
    - [1.3 对比表](#13-对比表)
  - [二、副作用模型（Side Effects Model）](#二副作用模型side-effects-model)
    - [2.1 什么是副作用？](#21-什么是副作用)
    - [2.2 副作用与并发的关系](#22-副作用与并发的关系)
    - [2.3 与其他语言的对比](#23-与其他语言的对比)
  - [三、变量模型：环境 vs 存储](#三变量模型环境-vs-存储)
    - [3.1 两个层面的变量](#31-两个层面的变量)
    - [3.2 Move 的存储层面解释](#32-move-的存储层面解释)
    - [3.3 对比 C++ 和 Java](#33-对比-c-和-java)
  - [四、Continuation 与 CPS](#四continuation-与-cps)
    - [4.1 什么是 Continuation？](#41-什么是-continuation)
    - [4.2 CPS：Continuation Passing Style](#42-cpscontinuation-passing-style)
    - [4.3 async/await 的本质：CPS 变换](#43-asyncawait-的本质cps-变换)
    - [4.4 与操作系统线程的对比](#44-与操作系统线程的对比)
  - [五、结构化程序定理](#五结构化程序定理)
    - [5.1 程序可以由三种结构组成](#51-程序可以由三种结构组成)
    - [5.2 Rust 的控制流安全性](#52-rust-的控制流安全性)
    - [5.3 为什么 `goto` 有害？](#53-为什么-goto-有害)
  - [六、总结：这些概念如何支撑 Rust](#六总结这些概念如何支撑-rust)
  - [嵌入式测验（Embedded Quiz）](#嵌入式测验embedded-quiz)
    - [测验 1：静态类型检查与动态类型检查的核心区别是什么？Rust 属于哪一类？（理解层）](#测验-1静态类型检查与动态类型检查的核心区别是什么rust-属于哪一类理解层)
    - [测验 2：什么是"语法"（Syntax）和"语义"（Semantics）？编译错误通常属于哪一类问题？（理解层）](#测验-2什么是语法syntax和语义semantics编译错误通常属于哪一类问题理解层)
    - [测验 3："引用透明"（Referential Transparency）对程序优化有什么意义？（理解层）](#测验-3引用透明referential-transparency对程序优化有什么意义理解层)
    - [测验 4：什么是"副作用"（Side Effect）？为什么副作用使程序推理更困难？（理解层）](#测验-4什么是副作用side-effect为什么副作用使程序推理更困难理解层)
    - [测验 5：类型系统的主要目标是什么？Rust 的类型系统额外提供了什么保证？（理解层）](#测验-5类型系统的主要目标是什么rust-的类型系统额外提供了什么保证理解层)
  - [实践](#实践)
  - [认知路径](#认知路径)
    - [核心推理链](#核心推理链)
  - [📋 关键属性](#-关键属性)
  - [🔗 概念关系](#-概念关系)
  - [国际权威参考 / International Authority References（P2 生态）](#国际权威参考--international-authority-referencesp2-生态)

## 一、求值策略（Evaluation Strategies）

> (Source: [TRPL — Foreword](https://doc.rust-lang.org/book/foreword.html))

### 1.1 为什么需要了解求值策略？

Rust 的 `move` 语义与 C++ 的 `move` 看起来相似，但根源完全不同：

| 语言 | 求值策略 | Move 语义的根源 |
|:---|:---|:---|
| **C++** | 按值复制（CBV）+ 自定义复制/移动构造函数 | 性能优化：避免深拷贝 |
| **Rust** | 按值移动（Move） | 类型系统（Type System）的必然：资源唯一性保证安全 |

> **关键洞察**: Rust 的 move 不是"优化选项"，而是**安全基础设施**。
> 如果一个值只能有一个所有者，那么就不可能存在两个指针同时释放同一块内存——这从根本上消除了 use-after-free。

### 1.2 三种核心求值策略

**按值调用（Call by Value, CBV）**

```python
# Python（CBV 的引用语义变体）
def add_one(x):
    x = x + 1      # x 重新绑定到新整数，不影响外部
    return x

n = 5
add_one(n)
print(n)           # 5（不变）
```

**按名调用（Call by Name, CBN）**

```haskell
-- Haskell（惰性求值，近似 CBN）
if' c t e = if c then t else e
result = if' True (1 `div` 0) 2   -- 不报错！因为 e 分支未被求值
```

**按需调用（Call by Need, CBNeed）**

```haskell
-- Haskell 的惰性求值 + 记忆化 = CBNeed
xs = [1..1000000]      -- 不立即生成
head xs                -- 只计算第一个元素，并记住结果
head xs                -- 直接使用记住的结果
```

**Rust 的策略**：

Rust 是**严格的 CBV**（eager evaluation），但引入了**所有权（Ownership）移动**：

```rust
fn take_ownership(s: String) { /* s 被消费 */ }

let s = String::from("hello");
take_ownership(s);      // s 的所有权移入函数
// println!("{}", s);   // 编译错误！s 已失效
```

这与 CBV 的区别：CBV 通常意味着"复制参数"，而 Rust 的 CBV 对于非 `Copy` 类型意味着"移动参数"。

### 1.3 对比表

| 策略 | 求值时机 | 重复求值 | 代表语言 | Rust 对应 |
|:---|:---|:---:|:---|:---|
| CBV | 立即 | 否 | C, Java, Python | `T`（`Copy` 类型） |
| CBN | 使用时 | 可能 | Algol 60 | 无直接对应 |
| CBNeed | 使用时 + 缓存 | 否 | Haskell | `LazyCell<T>`, `LazyLock<T>` |
| Move | 立即 + 转移所有权（Ownership） | 否 | Rust | `T`（非 `Copy` 类型） |

---

## 二、副作用模型（Side Effects Model）

「副作用模型（Side Effects Model）」部分按什么是副作用？、副作用与并发的关系与与其他语言的对比的顺序逐层展开。

### 2.1 什么是副作用？

**纯函数**：给定相同输入，永远返回相同输出，且不修改外部状态。

```rust
// 纯函数
fn add(a: i32, b: i32) -> i32 { a + b }

// 非纯函数（有副作用）
static mut COUNTER: i32 = 0;
fn increment() -> i32 {
    unsafe { COUNTER += 1; COUNTER }  // 修改了外部状态
}
```

### 2.2 副作用与并发的关系

为什么 Rust 能" fearless concurrency"？因为**所有权（Ownership）系统本质上是一种副作用控制机制**：

| 副作用类型 | Rust 的控制方式 | 为什么安全 |
|:---|:---|:---|
| 全局可变状态 | `static mut` 需要 `unsafe` | 编译器阻止无约束的共享可变 |
| 共享内存写入 | `&mut T` 的独占性 | 同一时刻只有一个写入者 |
| I/O 操作 | 显式 `unsafe` 或封装抽象 | 系统调用被隔离在安全抽象后 |
| 异常/非局部跳转 | `Result`/`panic` 显式传播 | 错误路径不可忽略 |

> **核心洞见**: Rust 不是消除副作用（那不可能），而是**将副作用显式化、局部化、可追踪**。`&mut T` 就是一个"副作用许可证"——编译器确保同一时间只发一张。

### 2.3 与其他语言的对比

```haskell
-- Haskell：通过类型系统隔离副作用（IO Monad）
readFile :: FilePath -> IO String   -- IO 标记"此函数有副作用"
```

```rust,ignore
// Rust：通过所有权隔离副作用
fn read_file(path: &str) -> Result<String, io::Error> {
    // 副作用（文件读取）被封装在函数体内
    // 调用者必须通过 ? 或 match 处理可能的失败
    fs::read_to_string(path)
}
```

```javascript
// JavaScript：副作用隐式、无约束
let data;
fetch('/api').then(r => r.json()).then(d => { data = d; });  // 副作用无处不在
```

---

## 三、变量模型：环境 vs 存储

> (Source: [Rust Reference](https://doc.rust-lang.org/reference/introduction.html))

### 3.1 两个层面的变量

理解 Rust 的 ownership 需要区分**两个层面**：

| 层面 | 名称 | 内容 | Rust 对应 |
|:---|:---|:---|:---|
| **环境（Environment）** | 变量名 → 存储位置 | 编译期的符号表 | 变量声明 `let x` |
| **存储（Store）** | 存储位置 → 值 | 运行期的内存状态 | 堆/栈上的实际数据 |

```rust
let x = 42;           // 环境: x → 栈位置 S1
                      // 存储: S1 → 42

let s = String::from("hi");
                      // 环境: s → 栈位置 S2
                      // 存储: S2 → (ptr, len, cap)
                      //        ptr → 堆位置 H1 → "hi"
```

### 3.2 Move 的存储层面解释

```rust
let s1 = String::from("hello");   // S1 → (ptr=H1, len=5, cap=5)
let s2 = s1;                       // 环境: s1 → ?（失效）
                                   // 环境: s2 → S2
                                   // 存储: S2 → (ptr=H1, len=5, cap=5)
                                   //       H1 未复制！
```

> **关键**: Move 只修改**环境**（哪个变量名绑定到哪个存储位置），不修改**存储**（不复制堆数据）。这是 Rust move 既高效又安全的根源。

### 3.3 对比 C++ 和 Java

```cpp
// C++：浅拷贝 + 手动管理
std::string s1 = "hello";
std::string s2 = s1;   // 深拷贝！H1 复制到 H2
                       // s1 和 s2 都有效（但性能代价）

std::string s3 = std::move(s1);
                       // 浅拷贝 + 置空 s1
                       // 需要程序员确保之后不使用 s1
```

```java
// Java：引用复制（环境层面）
String s1 = new String("hello");  // s1 → H1
String s2 = s1;                   // s2 → H1（环境复制，存储共享）
// GC 管理 H1 的生命周期，不存在双重释放
// 但也没有编译期的独占性保证
```

```rust
// Rust：环境移动（编译期保证唯一绑定）
let s1 = String::from("hello");   // s1 → H1
let s2 = s1;                      // s2 → H1, s1 失效
// 编译器确保 s1 之后不会被使用
// 无需 GC，无深拷贝，无手动管理
```

---

## 四、Continuation 与 CPS

「Continuation 与 CPS」涉及什么是 Continuation？、CPS：Continuation Passing Style、async/await 的本质：CPS 变换与与操作系统线程的对比，本节逐一说明其要点。

### 4.1 什么是 Continuation？

**Continuation** 是"程序剩余部分的抽象"。每个表达式都有一个隐式的 continuation："计算出结果后，接下来做什么"。

```rust
// 显式 continuation（伪代码）
let x = 1 + 2;        // 计算 1+2=3，然后 continuation 是 "let x = 3; ..."
println!("{}", x);    // continuation 是 "println!(..., 3)"
```

### 4.2 CPS：Continuation Passing Style

将隐式 continuation 显式化为函数参数：

```rust
// 直接风格
fn add(a: i32, b: i32) -> i32 { a + b }
let r = add(1, 2);
println!("{}", r);

// CPS 风格
fn add_cps(a: i32, b: i32, k: fn(i32)) { k(a + b) }
add_cps(1, 2, |r| println!("{}", r));
```

### 4.3 async/await 的本质：CPS 变换

Rust 的 `async fn` 是编译器自动执行的 CPS 变换：

```rust
// 你写的代码
async fn fetch_data(url: &str) -> Result<String, reqwest::Error> {
    let response = reqwest::get(url).await?;   // 这里"暂停"，但线程不阻塞
    let text = response.text().await?;          // 再次"暂停"
    Ok(text)
}
```

```rust
// 编译器生成的状态机（简化版）
enum FetchDataFuture {
    Start { url: String },
    WaitingResponse { future: ResponseFuture },
    WaitingText { future: TextFuture },
    Done,
}

impl Future for FetchDataFuture {
    fn poll(&mut self, cx: &mut Context) -> Poll<String> {
        loop {
            match std::mem::replace(self, FetchDataFuture::Done) {
                FetchDataFuture::Start { url } => {
                    *self = FetchDataFuture::WaitingResponse {
                        future: reqwest::get(&url)
                    };
                }
                FetchDataFuture::WaitingResponse { mut future } => {
                    match future.poll(cx) {
                        Poll::Ready(response) => {
                            *self = FetchDataFuture::WaitingText {
                                future: response.text()
                            };
                        }
                        Poll::Pending => {
                            *self = FetchDataFuture::WaitingResponse { future };
                            return Poll::Pending;
                        }
                    }
                }
                // ...
            }
        }
    }
}
```

> **核心洞察**: `await` 不是阻塞，而是**将当前函数的剩余部分（continuation）打包成一个状态机回调**，注册到事件循环中。当 I/O 完成时，事件循环调用这个回调（状态机的 `poll`），从上次暂停处继续执行。

### 4.4 与操作系统线程的对比

| 机制 | 调度者 | 上下文切换成本 | Continuation 存储 |
|:---|:---|:---:|:---|
| OS 线程 | 内核 | 高（~1μs，需切换页表） | 内核栈（MB 级） |
| Rust async | 用户态运行时（Runtime） | 低（~ns 级，状态机切换） | 状态机结构体（Struct）（按需分配） |
| Goroutine | Go 运行时（Runtime） | 中（~100ns） | Go 运行时管理的轻量栈 |

---

## 五、结构化程序定理

理解「结构化程序定理」需要把握程序可以由三种结构组成、Rust 的控制流安全性与为什么 `goto` 有害？，本节依次展开。

### 5.1 程序可以由三种结构组成

1966 年，Corrado Böhm 和 Giuseppe Jacopini 证明：**任何程序都可以仅用三种控制结构表达**：

1. **顺序**（Sequence）: `A; B`
2. **选择**（Selection）: `if condition { A } else { B }`
3. **循环**（Iteration）: `while condition { A }`

### 5.2 Rust 的控制流安全性

Rust 的所有权（Ownership）系统如何保证控制流安全？

```rust,ignore
// 顺序：变量按声明顺序初始化，按逆序 Drop
let a = resource();
let b = resource();   // a 先存在，b 后存在
// b 先 Drop，a 后 Drop

// 选择：每个分支必须产生相同类型（表达式一致性）
let x = if condition {
    vec![1, 2, 3]     // Vec<i32>
} else {
    vec![]            // Vec<i32>
};

// 循环：迭代器保证访问不越界
for item in &collection {   // 不可变借用覆盖整个循环体
    // 无法修改 collection，因此迭代器不会失效
}
```

### 5.3 为什么 `goto` 有害？

Dijkstra 的《Goto Statement Considered Harmful》核心论点：**无约束的跳转破坏了程序状态的可追踪性**。

Rust 的 `unsafe` 块允许裸指针和 `goto` 式的跳转（如 `setjmp`/`longjmp`），但编译器无法验证其安全性：

```rust
unsafe {
    // 编译器在此处"放弃"所有权检查
    // 程序员必须手动保证不变量
}
```

> **结构化程序定理的 Rust 版本**: 在 safe Rust 中，控制流的所有路径都可由编译器静态分析，因此所有资源（内存、文件、锁）的生命周期（Lifetimes）都可追踪。`unsafe` 打破了这一保证，需要程序员手动维护。

---

## 六、总结：这些概念如何支撑 Rust

| PL 概念 | Rust 设计决策 | 解决的问题 |
|:---|:---|:---|
| **Move 语义** | 非 `Copy` 类型按所有权（Ownership）转移 | use-after-free、双重释放 |
| **副作用显式化** | `&mut T` 独占、`unsafe` 标记 | 数据竞争、隐式状态修改 |
| **环境-存储分离** | 栈变量 vs 堆数据 | 理解为什么 move 不复制数据 |
| **CPS / 状态机** | `async/await` 编译为 `Future` | 高并发 I/O 不阻塞线程 |
| **结构化控制流** | safe Rust 禁止无约束跳转 | 资源泄漏、状态不一致 |

---

> **下一步**: 如果你已理解以上概念，请继续阅读 [所有权（Ownership）系统](../01_ownership_borrow_lifetime/01_ownership.md)。如果你在阅读所有权时感到困惑，返回本文对应章节寻找根源解释。

---

> **权威来源**:
>
> - [Böhm & Jacopini, 1966 — Flow Diagrams, Turing Machines and Languages with only Two Formation Rules](https://dl.acm.org/doi/10.1145/355592.365646)
> - [Dijkstra, 1968 — Go To Statement Considered Harmful](https://doi.org/10.1145/362929.362947)
> - [Plotkin, 1975 — Call-by-Name, Call-by-Value and the λ-Calculus](https://doi.org/10.1016/0304-3975(75)90017-1)
> - [Wadler, 1995 — Monads for Functional Programming](https://doi.org/10.1007/3-540-59451-5_2)
> - [TRPL Ch13 — Closures and Iterators](https://doc.rust-lang.org/book/ch13-01-closures.html)
> - [Rust Async Book — Async/Await Primer](https://rust-lang.github.io/async-book//01_getting_started/01_chapter.html)

## 嵌入式测验（Embedded Quiz）

本节从测验 1：静态类型检查与动态类型检查的核心区别是什么？Rust 属于哪…、测验 2：什么是"语法"（Syntax）和"语义"（Semantics…、测验 3："引用透明"（Referential Transparenc…、测验 4：什么是"副作用"（Side Effect）？为什么副作用使程…等5个方面切入，剖析「嵌入式测验（Embedded Quiz）」的核心内容。

### 测验 1：静态类型检查与动态类型检查的核心区别是什么？Rust 属于哪一类？（理解层）

**题目**: 静态类型检查与动态类型检查的核心区别是什么？Rust 属于哪一类？

<details>
<summary>✅ 答案与解析</summary>

静态类型检查在编译期验证类型正确性，运行时（Runtime）无类型错误；动态类型检查在运行时进行。Rust 属于静态类型语言，编译期强制类型检查。
</details>

---

### 测验 2：什么是"语法"（Syntax）和"语义"（Semantics）？编译错误通常属于哪一类问题？（理解层）

**题目**: 什么是"语法"（Syntax）和"语义"（Semantics）？编译错误通常属于哪一类问题？

<details>
<summary>✅ 答案与解析</summary>

语法是程序的形式结构规则；语义是程序的含义。编译错误通常属于语法或静态语义问题（类型不匹配、未定义变量等）。
</details>

---

### 测验 3："引用透明"（Referential Transparency）对程序优化有什么意义？（理解层）

**题目**: "引用（Reference）透明"（Referential Transparency）对程序优化有什么意义？

<details>
<summary>✅ 答案与解析</summary>

引用（Reference）透明允许编译器安全地进行表达式替换和重排，因为表达式的值不依赖于求值时机和上下文，这对内联、常量折叠、并行化等优化至关重要。
</details>

---

### 测验 4：什么是"副作用"（Side Effect）？为什么副作用使程序推理更困难？（理解层）

**题目**: 什么是"副作用"（Side Effect）？为什么副作用使程序推理更困难？

<details>
<summary>✅ 答案与解析</summary>

副作用指函数/表达式在返回值之外修改了程序状态（如修改全局变量、IO）。副作用使函数行为依赖于外部状态，破坏了局部推理能力，增加了并发错误风险。
</details>

---

### 测验 5：类型系统的主要目标是什么？Rust 的类型系统额外提供了什么保证？（理解层）

**题目**: 类型系统（Type System）的主要目标是什么？Rust 的类型系统额外提供了什么保证？

<details>
<summary>✅ 答案与解析</summary>

主要目标是防止运行时（Runtime）类型错误、提供抽象。Rust 额外通过所有权（Ownership）和生命周期（Lifetimes）系统保证内存安全（Memory Safety）（无悬垂指针、无数据竞争）无需垃圾回收。
</details>

## 实践

> **对应练习**: [`exercises/rustlings_style/`](../exercises/rustlings_style) — 基础语法与所有权（Ownership）练习
> **推荐阅读顺序**: 完成本节 → [所有权（Ownership）](../01_ownership_borrow_lifetime/01_ownership.md) → [类型系统（Type System）](../02_type_system/01_type_system.md)
>
> **建议**: 本节概念偏理论，建议快速浏览后进入 Rust 核心概念学习，在实践中反向理解这些 PL 基础。

## 认知路径

> **认知路径**: 从 L0 基础概念出发，经由本节的 **编程语言理论基础（PL Prerequisites）** 核心原理，通向 L2 进阶模式与 L3 工程实践。

### 核心推理链

| 定理 | 前提 | 结论 | 置信度 |
|:---|:---|:---|:---|
| 编程语言理论基础（PL Prerequisites） 基础定义 ⟹ 正确用法 | 理解语法与语义 | 能写出符合惯用法的代码 | 高 |
| 编程语言理论基础（PL Prerequisites） 正确用法 ⟹ 常见陷阱 | 忽略边界条件 | 编译错误或运行时（Runtime） bug | 高 |
| 编程语言理论基础（PL Prerequisites） 常见陷阱 ⟹ 深度掌握 | 系统学习反模式 | 能进行代码审查与优化 | 高 |

> 类型安全 ⟸ 静态类型检查 ⟸ 语法与语义一致性（Coherence）
> 程序正确性 ⟸ 无副作用推理 ⟸ 纯函数基础

---

## 📋 关键属性

| 属性 | 取值 / 判定 | 依据 |
|---|---|---|
| 求值策略 | Rust 采用 call-by-value：参数在调用前完成求值，引用语义靠显式 `&` | 本文 §一 求值策略 |
| 副作用模型 | 副作用显式化：写效果靠 `&mut`、未定义效果靠 `unsafe`、异常效果靠 `Result` | 本文 §二 |
| 变量模型 | 存储模型的线性扩展：绑定即资源，move 后原绑定失效 | 本文 §三 |
| async 本质 | `async/await` 是编译期 CPS 变换，生成惰性状态机 | 本文 §4.3 |
| 控制流完备性 | 顺序 / 选择 / 循环三结构即可表达全部控制流，Rust 无 `goto` | 本文 §五 结构化程序定理 |

## 🔗 概念关系

- **上位（is-a）**：编程语言理论（PLT）核心概念集在 Rust 中的落点。
- **下位（实例）**：求值策略、副作用模型、变量模型、Continuation/CPS、结构化程序定理五个子课题（本文 §一–§五）。
- **组合**：与 [副作用与纯度](04_effects_and_purity.md)、[变量模型](../03_values_and_references/03_variable_model.md) 共同构成 Rust 语义的推理底座。
- **依赖**：是理解 [所有权](../01_ownership_borrow_lifetime/01_ownership.md) 与 [Async](../../03_advanced/01_async/01_async.md) 的前置知识。

---

## 国际权威参考 / International Authority References（P2 生态）

> 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。

- **P2 生态/社区**: [This Week in Rust — Rust 社区官方周刊（语言理论落地实践的持续跟踪入口）](https://this-week-in-rust.org/)（2026-07-12 验证 HTTP 200）
