> **内容分级**: [专家级]

# 形式语言与自动机（Formal Languages and Automata）

> **EN**: Formal Languages and Automata
> **Summary**: The Chomsky hierarchy — regular, context-free, context-sensitive, and recursively enumerable languages — with pumping lemmas (regular and context-free), Myhill-Nerode theorem, closure properties, NFA/DFA power-set construction, Rust parser ecosystem mapping (regex/nom/pest/lalrpop/syn expressiveness and applicable levels), and typestate automata encoded via traits, aligned with Sipser, HMU, Barendregt, Scott, Pierce, Felleisen, Ahmed and Pitts.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **Bloom 层级**: L4-L5
> **权威来源**: 本文件为 `concept/` 权威页。
> **定位**: 从 Chomsky 层级、泵引理、Myhill-Nerode 定理、闭包性质、NFA/DFA 等价构造与自动机对应关系出发，定位 Rust 语法子集、解析生态（nom/pest/lalrpop/syn）与 typestate 模式在形式语言谱系中的位置，并桥接 λ 演算、类型理论与指称语义的国际权威视角。
> **前置概念**: [Lambda Calculus](../00_type_theory/05_lambda_calculus.md) · [Type Theory](../00_type_theory/01_type_theory.md) · [Type Inference](../00_type_theory/03_type_inference.md)
> **后置概念**: [Computability Theory](02_computability_theory.md) · [Equivalence of Computational Models](05_equivalence_of_computational_models.md) · [Observational Equivalence](../03_operational_semantics/06_observational_equivalence.md) · [Decidability Spectrum](../../00_meta/00_framework/decidability_spectrum.md)

---

## 📑 目录

- [形式语言与自动机（Formal Languages and Automata）](#形式语言与自动机formal-languages-and-automata)
  - [📑 目录](#-目录)
  - [一、核心概念](#一核心概念)
    - [1.1 为什么需要形式语言](#11-为什么需要形式语言)
    - [1.2 Chomsky 层级](#12-chomsky-层级)
    - [1.3 正则语言：DFA、NFA 与正则表达式](#13-正则语言dfanfa-与正则表达式)
    - [1.4 上下文无关语言：CFG 与 PDA](#14-上下文无关语言cfg-与-pda)
    - [1.5 图灵可识别与可判定语言](#15-图灵可识别与可判定语言)
    - [1.6 泵引理（Pumping Lemma）](#16-泵引理pumping-lemma)
      - [1.6.1 正则语言的泵引理](#161-正则语言的泵引理)
      - [1.6.2 上下文无关语言的泵引理](#162-上下文无关语言的泵引理)
    - [1.7 Myhill-Nerode 定理](#17-myhill-nerode-定理)
    - [1.8 闭包性质与 Rust 中的对应](#18-闭包性质与-rust-中的对应)
    - [1.9 NFA 到 DFA 的幂集构造](#19-nfa-到-dfa-的幂集构造)
    - [1.10 Rust 解析生态映射](#110-rust-解析生态映射)
    - [1.11 自动机与 typestate / trait 的对应](#111-自动机与-typestate--trait-的对应)
    - [1.12 Rust 中的形式语言实例](#112-rust-中的形式语言实例)
    - [1.13 从自动机到程序语言理论的桥梁](#113-从自动机到程序语言理论的桥梁)
      - [1.13.1 自动机、λ 演算与 Church-Turing 论题](#1131-自动机λ-演算与-church-turing-论题)
      - [1.13.2 类型系统作为形式语言：Pierce 的视角](#1132-类型系统作为形式语言pierce-的视角)
      - [1.13.3 指称语义与 Scott 域](#1133-指称语义与-scott-域)
      - [1.13.4 表达力：Felleisen 框架](#1134-表达力felleisen-框架)
      - [1.13.5 程序等价与观察等价：Ahmed / Pitts](#1135-程序等价与观察等价ahmed--pitts)
  - [二、反命题与边界分析](#二反命题与边界分析)
    - [2.1 反命题：Rust 语法是正则语言](#21-反命题rust-语法是正则语言)
    - [2.2 边界极限](#22-边界极限)
  - [三、常见陷阱](#三常见陷阱)
  - [四、国际权威来源与延伸阅读](#四国际权威来源与延伸阅读)
  - [相关概念](#相关概念)
  - [嵌入式测验（Embedded Quiz）](#嵌入式测验embedded-quiz)
    - [测验 1：Chomsky 层级（理解层）](#测验-1chomsky-层级理解层)
    - [测验 2：正则语言边界（分析层）](#测验-2正则语言边界分析层)
    - [测验 3：CFG 与 Rust 解析（应用层）](#测验-3cfg-与-rust-解析应用层)
    - [测验 4：NFA/DFA 与 typestate（综合层）](#测验-4nfadfa-与-typestate综合层)
    - [测验 5：可判定性边界（评价层）](#测验-5可判定性边界评价层)
  - [🧭 思维导图（Mindmap）](#-思维导图mindmap)

---

## 一、核心概念

### 1.1 为什么需要形式语言

程序语言首先是**形式语言**：它的合法程序集合必须由精确、无歧义的规则定义，否则编译器实现者、程序员和验证工具会对「什么是合法代码」产生分歧。

```text
自然语言描述 vs 形式语言定义:

  自然语言："一个函数可以接受若干参数"
  ├── "若干"是多少？
  ├── 参数顺序是否重要？
  └── 不同实现可能理解不同

  形式语言：
  Fun ::= fn Ident ( ParamList ) -> Type { Body }
  ├── 每个符号有精确语法
  ├── 可用文法、自动机或推演系统判定成员资格
  └── 编译器可据此生成解析器

  Rust 的层面:
  ├── 词法：正则语言（标识符、关键字、字面量）
  ├── 语法：上下文无关语言（表达式、语句、块）
  ├── 类型：可判定约束求解（Hindley-Milner + traits）
  └── 宏扩展：比 CFG 更强（图灵完备）
```

> **认知功能**: 形式语言理论把「Rust 程序是否合法」转化为**成员资格判定问题**，从而可以用自动机、文法和复杂度理论分析编译器的各个阶段。
> **来源**: [Hopcroft, Motwani & Ullman 2006 — Introduction to Automata Theory, Languages, and Computation, §1.1](https://en.wikipedia.org/wiki/Introduction_to_Automata_Theory,_Languages,_and_Computation) · [Sipser 2012 — Introduction to the Theory of Computation, §0.2](https://math.mit.edu/~sipser/book.html)

---

### 1.2 Chomsky 层级

Chomsky 层级把语言按**表达力**和**识别所需自动机**分为四类。每一类都有对应的文法、自动机和典型判定问题。

| 层级 | 语言类 | 文法 | 自动机 | 成员资格 |  Rust 对应 |
|:---|:---|:---|:---|:---:|:---|
| Type-3 | 正则语言 (Regular) | 正则文法 `A → aB \| a \| ε` | DFA / NFA / 正则表达式 | **可判定**（线性时间） | `regex` 模式、词法单元 |
| Type-2 | 上下文无关语言 (Context-Free) | CFG `A → α` | 下推自动机 (PDA) | **可判定**（多项式时间，CYK / LR） | Rust 表达式语法、匹配臂 |
| Type-1 | 上下文有关语言 (Context-Sensitive) | 上下文有关文法 `αAβ → αγβ` | 线性有界自动机 (LBA) | **可判定**（但非多项式） | 部分类型约束、宏 hygiene 的某些方面 |
| Type-0 | 递归可枚举语言 (Recursively Enumerable) | 无限制文法 | 图灵机 (TM) | **半可判定** | 过程宏展开、`const fn` 计算 |

> **层级洞察**: 每一层都是上一层的真子集。**表达力越强，判定问题越难**。Rust 编译器在不同阶段处理不同层级的对象：词法分析用正则，语法分析用 CFG，类型检查和宏扩展则进入可判定或半可判定领域。
> **来源**: [Chomsky 1956 — Three Models for the Description of Language](https://doi.org/10.1109/TIT.1956.1056813) · [Sipser 2012 — §2, pp. 101–104; §3, pp. 165–168](https://math.mit.edu/~sipser/book.html) · [Hopcroft, Motwani & Ullman 2006 — §4.1, §7.1](https://en.wikipedia.org/wiki/Introduction_to_Automata_Theory,_Languages,_and_Computation)

---

### 1.3 正则语言：DFA、NFA 与正则表达式

**正则语言**是能被有限自动机识别的语言类。其核心特征是：只需要有限状态即可判定成员资格，无法计数或匹配嵌套结构。

```text
确定有限自动机 (DFA):

  M = (Q, Σ, δ, q₀, F)
  ├── Q: 有限状态集
  ├── Σ: 有限字母表
  ├── δ: Q × Σ → Q 转移函数
  ├── q₀ ∈ Q: 初始状态
  └── F ⊆ Q: 接受状态集

  示例：识别二进制串中 0 的个数为偶数

      0         1
    ┌───┐     ┌───┐
    ▼   │     ▼   │
   (q0)─┘     (q1)─┘
    │0          │0
    ▼            ▼
   (q1)        (q0)

  q0 为偶数状态（接受），q1 为奇数状态。
```

Rust 中可用枚举模拟 DFA 状态：

```rust
#[derive(Clone, Copy, PartialEq, Eq)]
enum Parity { Even, Odd }

fn dfa_even_zeros(input: &str) -> bool {
    let mut state = Parity::Even;
    for ch in input.chars() {
        if ch == '0' {
            state = match state {
                Parity::Even => Parity::Odd,
                Parity::Odd => Parity::Even,
            };
        }
        // '1' 不改变状态
    }
    state == Parity::Even
}

fn main() {
    assert!(dfa_even_zeros("1001"));   // 两个 0
    assert!(!dfa_even_zeros("1000"));  // 三个 0
    assert!(dfa_even_zeros(""));       // 零个 0
}
```

**非确定有限自动机（NFA）**允许同一输入下存在多个可能的下一状态，并允许 ε-转移。Thompson 构造法把正则表达式编译为 NFA；子集构造法（powerset construction）把 NFA 转换为等价的 DFA。Rust 的 `regex` crate 在底层同样使用这类构造。

```rust
use std::collections::{HashMap, HashSet};

/// 用 NFA 识别语言 (a|b)*abb：状态 0 为起始，状态 3 为接受。
/// 这里用 ε-闭包模拟非确定性，教学用途。
struct Nfa {
    transitions: HashMap<(usize, Option<char>), Vec<usize>>,
    start: usize,
    accept: usize,
}

impl Nfa {
    fn epsilon_closure(&self, states: &HashSet<usize>) -> HashSet<usize> {
        let mut closure = states.clone();
        let mut stack: Vec<_> = states.iter().copied().collect();
        while let Some(s) = stack.pop() {
            for &next in self.transitions.get(&(s, None)).unwrap_or(&vec![]) {
                if closure.insert(next) {
                    stack.push(next);
                }
            }
        }
        closure
    }

    fn accepts(&self, input: &str) -> bool {
        let mut current = self.epsilon_closure(&HashSet::from([self.start]));
        for ch in input.chars() {
            let mut next = HashSet::new();
            for &s in &current {
                for &t in self.transitions.get(&(s, Some(ch))).unwrap_or(&vec![]) {
                    next.insert(t);
                }
            }
            current = self.epsilon_closure(&next);
        }
        current.contains(&self.accept)
    }
}

fn main() {
    let nfa = Nfa {
        transitions: HashMap::from([
            ((0, Some('a')), vec![0, 1]),
            ((0, Some('b')), vec![0]),
            ((1, Some('b')), vec![2]),
            ((2, Some('b')), vec![3]),
        ]),
        start: 0,
        accept: 3,
    };
    assert!(nfa.accepts("abb"));
    assert!(nfa.accepts("aabb"));
    assert!(nfa.accepts("babb"));
    assert!(!nfa.accepts("ab"));
    assert!(!nfa.accepts("abba"));
}
```

> **正则语言边界**: 正则语言对**并、连接、Kleene 星号**封闭，对**补、交**也封闭（因为可确定化为 DFA 后取补/积构造）。但正则语言无法计数或匹配任意深度嵌套。例如，无法用正则表达式精确匹配任意深度的成对括号。
> **来源**: [Sipser 2012 — §1.1–1.2, pp. 31–54](https://math.mit.edu/~sipser/book.html) · [Hopcroft, Motwani & Ullman 2006 — §2.3–2.5, §4.2](https://en.wikipedia.org/wiki/Introduction_to_Automata_Theory,_Languages,_and_Computation) · [Rust Reference — Lexical Structure](https://doc.rust-lang.org/reference/tokens.html)

---

### 1.4 上下文无关语言：CFG 与 PDA

**上下文无关语言 (CFL)** 由上下文无关文法 (CFG) 生成，可由**下推自动机 (PDA)** 识别。与正则语言相比，PDA 增加了一个栈，因此能够处理嵌套和匹配结构。

```text
上下文无关文法示例：平衡括号

  S → ( S )
  S → S S
  S → ε

推导 "(())":
  S ⇒ ( S ) ⇒ ( ( S ) ) ⇒ ( ( ε ) ) = (())

推导 "()()":
  S ⇒ S S ⇒ ( S ) S ⇒ ( ) S ⇒ ( ) ( S ) ⇒ ( ) ( ) = ()()
```

Rust 的表达式语法本质上是 CFG。例如，块表达式 ` { ... } `、匹配表达式 `match ... { ... }`、括号表达式以及嵌套结构都需求 CFG 能力。

```rust
fn main() {
    // Rust 表达式：嵌套深度任意，需要栈来解析
    let x = {
        let y = {
            let z = 1 + (2 + (3 + 4));
            z * 2
        };
        y + 1
    };
    assert_eq!(x, 21);
}
```

下推自动机可以用显式栈模拟：

```rust
/// 用 PDA 识别平衡括号（仅 '(' 与 ')'）。
/// 每读到一个 '(' 入栈，读到 ')' 出栈；最终栈空则接受。
fn pda_balanced_parens(input: &str) -> bool {
    let mut stack = Vec::new();
    for ch in input.chars() {
        match ch {
            '(' => stack.push(ch),
            ')' => {
                if stack.pop().is_none() {
                    return false; // 无匹配开括号
                }
            }
            _ => {}
        }
    }
    stack.is_empty()
}

fn main() {
    assert!(pda_balanced_parens("(())"));
    assert!(pda_balanced_parens("()()"));
    assert!(!pda_balanced_parens("(()"));
    assert!(!pda_balanced_parens(")()"));
}
```

CFG 与递归数据类型都允许自我指涉，但 Rust 要求递归类型必须经 `Box`、`Rc` 等间接层打破无限展开，否则会报 `E0072`（recursive type has infinite size）：

```rust,compile_fail,E0072
struct Node {
    next: Node, // ERROR E0072: 直接递归导致类型大小无限
}

fn main() {}
```

这与下推自动机形成对照：PDA 用栈处理任意深度的嵌套，而 Rust 类型系统用显式堆间接保证每个值都有有限大小。

**LL/LR 解析**是编译器构造 CFG 解析器的两类经典算法：

- **LL(k)**：自顶向下、向前看 k 个符号。Rust 的 `macro_rules!` 部分匹配采用类似 LL 的预测策略。
- **LR(k)**：自底向上、向前看 k 个符号。rustc 的解析器基于 LR 思想的手写递归下降，而非纯表驱动 LR。

```text
Rust 解析策略:

  手写递归下降 + Pratt 表达式解析
  ├── 词法：表驱动（正则/NFA）
  ├── 语法：递归下降（等价于 CFG）
  └── 宏扩展：在语法树层面进行，超越纯 CFG
```

> **CFG 洞察**: Rust 的**表达式语法是上下文无关的**，但**宏系统不是**。`macro_rules!` 可以生成并匹配比 CFG 更复杂的模式，而过程宏则直接运行在图灵完备的 Rust 代码上。
> **来源**: [Sipser 2012 — §2.1–2.2, pp. 101–124](https://math.mit.edu/~sipser/book.html) · [Hopcroft, Motwani & Ullman 2006 — §6.1–6.3](https://en.wikipedia.org/wiki/Introduction_to_Automata_Theory,_Languages,_and_Computation) · [Rust Reference — Macros By Example](https://doc.rust-lang.org/reference/macros-by-example.html)

---

### 1.5 图灵可识别与可判定语言

在 Chomsky 层级的顶端，**递归可枚举语言 (Type-0)** 由图灵机识别，**递归语言（可判定语言）**由总会停机的图灵机判定。

```text
可判定 (Decidable) vs 可识别 (Recognizable):

  可判定：
  ├── 对任意输入，图灵机必在有限步内停机
  ├── 回答是 / 否
  └── 例：DFA 成员资格、CFG 成员资格

  可识别（半可判定）：
  ├── 对「是」实例必停机接受
  ├── 对「否」实例可能永不停机
  └── 例：图灵机停机问题（自身不可判定）
```

Rust 编译器在类型检查和宏展开阶段会碰到可判定与半可判定的边界：

- **类型检查**：Rust 的类型系统被设计为可判定的（尽管某些扩展如 GATs 可能使推理更复杂）。
- **过程宏**：过程宏在编译期执行任意 Rust 代码，本质上是图灵完备的；宏展开可能不终止。
- `const fn` 求值：Rust 的常量求值器（Miri 引擎）有步数限制，因为任意 `const fn` 可能发散。

```rust,compile_fail,E0425
// ❌ 编译错误：宏展开后引用了不存在的名字，说明宏生成代码仍需通过名称解析
macro_rules! undefined {
    () => { nonexistent_var };
}

fn main() {
    let _x = undefined!(); // E0425: cannot find value `nonexistent_var`
}
```

> **判定性洞察**: 编译器前端（词法、语法）处理的是可判定问题；后端优化和宏展开则可能涉及半可判定甚至不可判定问题。区分这些阶段有助于理解「为什么 Rust 拒绝某些代码」与「为什么某些检查只能运行时进行」。
> **来源**: [Sipser 2012 — §4.1, pp. 165–170; §5.1, pp. 216–221](https://math.mit.edu/~sipser/book.html) · [Hopcroft, Motwani & Ullman 2006 — §8.1–8.5, §9.1](https://en.wikipedia.org/wiki/Introduction_to_Automata_Theory,_Languages,_and_Computation) · [Rust Reference — Introduction](https://doc.rust-lang.org/reference/introduction.html)

---

### 1.6 泵引理（Pumping Lemma）

泵引理是证明语言**不**属于某一层级的标准工具。它给出的是必要条件：若语言属于该层级，则任意足够长的字符串都能被「泵」长或泵短后仍在语言中。通过找到反例字符串，可以证明某个语言不在该层级。

> **关键认知**: 泵引理是**必要条件而非充分条件**。满足泵引理不能保证语言属于该类；但不满足泵引理则可确定不属于该类。这与 Myhill-Nerode 定理形成对照：后者对正则语言是充分且必要的。

#### 1.6.1 正则语言的泵引理

> **定理（正则语言泵引理，Sipser 2012, Theorem 1.70; HMU 2006, Theorem 4.1）**
>
> 若 `L` 是正则语言，则存在泵长度 `p ≥ 1`（仅依赖于 `L`），使得对任意字符串 `s ∈ L` 且 `|s| ≥ p`，`s` 可被分解为 `s = xyz`，满足：
>
> 1. `|xy| ≤ p`（泵窗口落在前缀 `p` 个字符内）
> 2. `|y| > 0`（被泵部分非空）
> 3. 对所有 `i ≥ 0`，`xyⁱz ∈ L`
>
> 等价表述：对任意 `s ∈ L` 且 `|s| ≥ p`，存在非空子串 `y` 位于前 `p` 个字符中，使得将 `y` 重复任意次（包括零次）后所得字符串仍在 `L` 中。

**证明思路（Sipser §1.4）**：设 DFA `M` 有 `p` 个状态，取 `|s| ≥ p`。`M` 读入 `s` 的前 `p` 个字符时必经过 `p+1` 个状态，由鸽巢原理存在重复状态 `q`。令 `x` 为到达第一次 `q` 的字符串，`y` 为两次 `q` 之间的非空字符串，`z` 为剩余部分，则重复或删除 `y` 对应于在 `q` 处循环，仍到达同一接受状态。

**典型应用：证明 `L = {aⁿbⁿ | n ≥ 0}` 不是正则语言**

假设 `L` 正则，取泵长度 `p`，令 `s = aᵖbᵖ`。由条件 1，`|xy| ≤ p`，故 `xy` 全由 `a` 组成。由条件 2，`y = aᵏ` 且 `k > 0`。取 `i = 2`，则 `xy²z = aᵖ⁺ᵏbᵖ`，其中 `a` 的数量大于 `b`，不在 `L` 中，矛盾。

```text
泵引理不是充分条件：
├── 满足泵引理 ⇒ 不一定正则
├── 不满足泵引理 ⇒ 一定不正则
└── 工程意义：任意深度计数/匹配都需要 CFG 或更强模型
```

> **来源**: [Sipser 2012 — §1.4, pp. 77–82](https://math.mit.edu/~sipser/book.html) · [Hopcroft, Motwani & Ullman 2006 — §4.1](https://en.wikipedia.org/wiki/Introduction_to_Automata_Theory,_Languages,_and_Computation)

#### 1.6.2 上下文无关语言的泵引理

> **定理（上下文无关语言泵引理，Sipser 2012, Theorem 2.34; HMU 2006, Theorem 7.2）**
>
> 若 `L` 是 CFL，则存在泵长度 `p ≥ 1`，使得对任意 `s ∈ L` 且 `|s| ≥ p`，`s` 可分解为 `s = uvxyz`，满足：
>
> 1. `|vxy| ≤ p`（泵窗口落在长度不超过 `p` 的连续子串内）
> 2. `|vy| > 0`（`v` 与 `y` 至少一个非空）
> 3. 对所有 `i ≥ 0`，`uvⁱxyⁱz ∈ L`
>
> 直观上，任何足够长的 CFG 字符串都包含两个可以同步泵长的「匹配片段」。

**证明思路（Sipser §2.3）**：设 `L` 有 CFG `G`，其变元数为 `|V|`、最长右部长度为 `b`。取 `p = b^{|V|+2}`。任何长度 ≥ `p` 的派生树必有一条高度 ≥ `|V|+1` 的路径，从而某变元 `A` 在路径上重复出现。以这两个 `A` 为根的子树生成 `vxy` 与 `x`，同步泵它们即得 `uvⁱxyⁱz`。

**典型应用：证明 `L = {aⁿbⁿcⁿ | n ≥ 0}` 不是 CFL**

假设 `L` 是 CFL，取 `s = aᵖbᵖcᵖ`。由条件 1，`|vxy| ≤ p`，故 `vxy` 最多跨越 `a` 和 `b` 或 `b` 和 `c` 两种连续字符，不可能同时包含 `a`、`b`、`c`。由条件 2，`vy` 至少含一种字符。取 `i = 2`，被泵的字符数量增加，但未被泵的第三种字符数量不变，三者不再相等，矛盾。

```text
CFG 泵引理的工程含义：
├── Rust 表达式语法可以处理任意嵌套的 {}、()、[]
├── 但无法处理需要「三个并行计数」的语言结构
└── 某些语义约束（如变量绑定唯一性）需要超出 CFG 的工具
```

> **来源**: [Sipser 2012 — §2.3, pp. 125–130](https://math.mit.edu/~sipser/book.html) · [Hopcroft, Motwani & Ullman 2006 — §7.2](https://en.wikipedia.org/wiki/Introduction_to_Automata_Theory,_Languages,_and_Computation)

---

### 1.7 Myhill-Nerode 定理

**Myhill-Nerode 定理**给出了正则语言的另一种刻画：一个语言是正则的，当且仅当它的「不可区分关系」具有有限指数。这个定理比泵引理更强，因为它既是必要条件也是充分条件。

> **定义（不可区分关系）**
>
> 对语言 `L ⊆ Σ*`，定义关系 `≡_L` 如下：`x ≡_L y` 当且仅当对所有 `z ∈ Σ*`，
> $$
> xz \in L \iff yz \in L
> $$

> **Myhill-Nerode 定理**
>
> 语言 L 是正则的，当且仅当 `≡_L` 的等价类个数（指数）是有限的。

```text
直观理解：
├── 每个等价类对应 DFA 的一个状态
├── 等价类有限 ⇔ 只需要有限状态即可识别该语言
├── 这是构造最小 DFA 的理论基础
└── 泵引理只能证非正则；Myhill-Nerode 还能用来构造最小自动机
```

示例：语言 `L = {aⁿbⁿ | n ≥ 0}` 不是正则的，因为字符串 `a⁰, a¹, a², ...` 两两不等价：对 `aⁱ` 和 `aʲ`（i ≠ j），取 `z = bⁱ`，则 `aⁱbⁱ ∈ L` 但 `aʲbⁱ ∉ L`。

```rust
/// 用 Myhill-Nerode 思路证明 {a^n b^n} 不是正则的：
/// 对任意 i ≠ j，a^i 与 a^j 可被后缀 b^i 区分。
fn distinguishable_by_suffix(i: usize, j: usize) -> bool {
    let suffix_b_i = "b".repeat(i);
    let left = format!("{}{}", "a".repeat(i), suffix_b_i);
    let right = format!("{}{}", "a".repeat(j), suffix_b_i);
    // left ∈ L，right ∉ L（当 i ≠ j 时）
    left.chars().filter(|&c| c == 'a').count() == left.chars().filter(|&c| c == 'b').count()
        && right.chars().filter(|&c| c == 'a').count() != right.chars().filter(|&c| c == 'b').count()
}

fn main() {
    assert!(distinguishable_by_suffix(2, 3));
    assert!(distinguishable_by_suffix(0, 1));
}
```

> **来源**: [Sipser 2012 — §1.4, Problem 1.52 及补充](https://math.mit.edu/~sipser/book.html) · [Hopcroft, Motwani & Ullman 2006 — §4.4](https://en.wikipedia.org/wiki/Introduction_to_Automata_Theory,_Languages,_and_Computation) · [Myhill 1957 — Finite Automata and the Representation of Events](https://doi.org/10.1515/9781400882618-008) · [Nerode 1958 — Linear Automaton Transformations](https://doi.org/10.2307/1993204)

---

### 1.8 闭包性质与 Rust 中的对应

正则语言与上下文无关语言在特定运算下封闭。理解闭包性质有助于判断「某种语言变换是否保持可识别性」。

```text
正则语言的闭包性质：
├── 对并、交、补、连接、Kleene 星号封闭
├── 交/补：通过 DFA 积构造或补状态集实现
└── 这些性质是正则表达式组合与词法分析器合并的理论基础

上下文无关语言的闭包性质：
├── 对并、连接、Kleene 星号封闭
├── 对交、补不封闭
└── 这解释了为什么把两个 CFG 求交可能得到非 CFG 的语言
```

Rust 中，正则表达式组合对应并/连接/星号：

```rust
/// 用纯 Rust 实现一个简化 DFA，识别日期格式 YYYY-MM-DD 中的数字段。
/// 实际 `regex` crate 会把 r"^\d{4}-\d{2}-\d{2}$" 编译为 DFA/NFA。
fn dfa_is_iso_date(s: &str) -> bool {
    let mut state = 0usize; // 0=year, 1=month, 2=day, 3=ok, 4=fail
    let mut count = 0usize;
    for ch in s.chars() {
        state = match (state, ch) {
            (0, '-') if count == 4 => { count = 0; 1 }
            (0, c) if c.is_ascii_digit() => { count += 1; 0 }
            (1, '-') if count == 2 => { count = 0; 2 }
            (1, c) if c.is_ascii_digit() => { count += 1; 1 }
            (2, c) if c.is_ascii_digit() => { count += 1; 2 }
            _ => 4,
        };
        if state == 4 { return false; }
    }
    state == 2 && count == 2
}

fn main() {
    assert!(dfa_is_iso_date("2026-07-28"));
    assert!(!dfa_is_iso_date("28-07-2026"));
    assert!(!dfa_is_iso_date("2026-7-28"));
}
```

> **来源**: [Sipser 2012 — §1.1–1.3](https://math.mit.edu/~sipser/book.html) · [Hopcroft, Motwani & Ullman 2006 — §4.2](https://en.wikipedia.org/wiki/Introduction_to_Automata_Theory,_Languages,_and_Computation)

---

### 1.9 NFA 到 DFA 的幂集构造

子集构造法（powerset construction / subset construction）证明：对任意 NFA，都存在一个等价的 DFA。这是正则语言在 NFA 与 DFA 之间表达力等价的核心定理。

> **定理（Rabin & Scott 1959）**
>
> 对任意 NFA `N = (Q, Σ, δ, q₀, F)`，可构造 DFA `D = (P(Q), Σ, δ', {q₀}, F')`，其中：
>
> - 状态集是 Q 的幂集 `P(Q)`
> - `δ'(S, a) = ⋃_{q ∈ S} ε-closure(δ(q, a))`
> - `F' = { S ⊆ Q | S ∩ F ≠ ∅ }`
>
> 则 `L(N) = L(D)`。

```rust
use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};

/// 把 ε-NFA 通过幂集构造转换为 DFA（教学简化版）。
/// 输入：起始状态、接受状态集合、转移表（状态，可选字符）→ 状态集合。
fn nfa_to_dfa(
    start: usize,
    accepts: &HashSet<usize>,
    nfa_delta: &HashMap<(usize, Option<char>), HashSet<usize>>,
) -> (usize, HashSet<BTreeSet<usize>>, HashMap<(BTreeSet<usize>, char), BTreeSet<usize>>) {
    let eps_closure = |states: &BTreeSet<usize>| {
        let mut closure = states.clone();
        let mut stack: Vec<_> = states.iter().copied().collect();
        while let Some(s) = stack.pop() {
            for &next in nfa_delta.get(&(s, None)).unwrap_or(&HashSet::new()) {
                if closure.insert(next) {
                    stack.push(next);
                }
            }
        }
        closure
    };

    let start_set = eps_closure(&BTreeSet::from([start]));
    let mut dfa_states = HashSet::from([start_set.clone()]);
    let mut dfa_delta = HashMap::new();
    let mut queue = VecDeque::from([start_set.clone()]);

    while let Some(current) = queue.pop_front() {
        for ch in ['a', 'b'] {
            let mut raw_next = BTreeSet::new();
            for &s in &current {
                for &t in nfa_delta.get(&(s, Some(ch))).unwrap_or(&HashSet::new()) {
                    raw_next.insert(t);
                }
            }
            let next = eps_closure(&raw_next);
            if !next.is_empty() {
                dfa_delta.insert((current.clone(), ch), next.clone());
                if dfa_states.insert(next.clone()) {
                    queue.push_back(next);
                }
            }
        }
    }
    (0, dfa_states, dfa_delta) // 起始标记；dfa_states 中已包含接受状态信息
}

fn main() {
    // 简单 NFA：识别以 "ab" 结尾的 {a,b}* 串
    let mut nfa_delta: HashMap<(usize, Option<char>), HashSet<usize>> = HashMap::new();
    nfa_delta.insert((0, Some('a')), HashSet::from([0, 1]));
    nfa_delta.insert((0, Some('b')), HashSet::from([0]));
    nfa_delta.insert((1, Some('b')), HashSet::from([2]));

    let (_, dfa_states, dfa_delta) = nfa_to_dfa(0, &HashSet::from([2]), &nfa_delta);
    assert!(dfa_states.len() <= 8); // 2^3 上界
    assert!(dfa_delta.contains_key(&(BTreeSet::from([0]), 'a')));
}
```

> **认知要点**: 幂集构造说明 NFA 并不比 DFA 表达力更强，只是更紧凑。实际 `regex` 等库先用 Thompson 构造生成 NFA，再用子集构造隐式模拟 DFA 以提高匹配效率。
> **来源**: [Rabin & Scott 1959 — Finite Automata and Their Decision Problems](https://doi.org/10.1515/9781400882618-010) · [Sipser 2012 — §1.2, pp. 55–62](https://math.mit.edu/~sipser/book.html) · [Hopcroft, Motwani & Ullman 2006 — §2.3.5](https://en.wikipedia.org/wiki/Introduction_to_Automata_Theory,_Languages,_and_Computation)

---

### 1.10 Rust 解析生态映射

Rust 生态提供了从正则表达式到完整语法解析的多层工具，分别对应形式语言层级的不同位置：

| 工具 / Crate | 形式能力 | 典型用途 | 与 Chomsky 层级关系 |
|:---|:---|:---|:---|
| `regex` | 正则语言 | 词法匹配、日志过滤、配置校验 | Type-3；编译为 DFA/NFA |
| `nom` | 解析器组合子；覆盖 CFG 及轻量上下文有关模式 | 二进制/文本协议解析、配置文件 | Type-2 为主，可扩展 |
| `pest` | PEG（解析表达式文法） | 领域特定语言（DSL）、配置文件 | 比 CFG 表达能力略有不同（无歧义，有序选择） |
| `lalrpop` | LR(1) / LALR | 完整编程语言语法、表达式语法 | Type-2；确定性 CFG 子集 |
| `syn` | 手写递归下降 | proc-macro 解析 Rust 语法树 | 实用 CFG + Rust 特定规则 |

```text
选择建议：
├── 需要快速正则匹配 → regex
├── 需要组合式、零拷贝解析 → nom
├── 需要声明式 DSL 且要求无歧义 → pest
├── 需要完整语言前端 → lalrpop / 手写递归下降（如 syn）
└── 需要解析 Rust 自身语法 → syn
```

> **认知要点**：这些工具不是「越强越好」。`regex` 虽然能力有限，但性能极高且可判定；`nom`/`pest`/`lalrpop` 进入 CFG 领域后，表达能力增强但错误恢复、歧义处理变得更复杂；`syn` 则直接面向 Rust 语法这一特定 CFG 变体。
>
> **来源**: [regex crate documentation](https://docs.rs/regex) · [nom crate documentation](https://docs.rs/nom) · [pest crate documentation](https://docs.rs/pest) · [lalrpop documentation](https://lalrpop.github.io/lalrpop/) · [syn crate documentation](https://docs.rs/syn)

---

### 1.11 自动机与 typestate / trait 的对应

**Typestate** 是一种将状态机编码进类型系统的设计模式：对象在不同状态下具有不同的类型，只有特定状态下才能调用特定方法。这与 DFA/PDA 的「状态 + 转移」思想直接对应。

Rust 的所有权与 trait 系统特别适合实现 typestate。下面的例子用类型模拟一个具有 `Open` 和 `Closed` 两种状态的门：

```rust
struct Closed;
struct Open;

struct Door<State> {
    state: State,
}

impl Door<Closed> {
    fn new() -> Self { Door { state: Closed } }
    fn open(self) -> Door<Open> { Door { state: Open } }
}

impl Door<Open> {
    fn close(self) -> Door<Closed> { Door { state: Closed } }
    fn walk_through(&self) -> &'static str { "walking through" }
}

fn main() {
    let door = Door::new();
    let door = door.open();
    println!("{}", door.walk_through());
    let _door = door.close();
}
```

> 这个模式的关键在于：**编译器在类型层面强制执行状态转移规则**。`Door<Closed>` 不能调用 `walk_through`，`Door<Open>` 不能调用 `open`。这相当于把 DFA 的转移函数编码为类型系统的 method 签名。

更复杂的例子可以用 trait 表达「在当前状态下允许的操作」：

```rust
trait State {}
struct Locked;
struct Unlocked;
impl State for Locked {}
impl State for Unlocked {}

struct Safe<S: State> { _state: S }

impl Safe<Locked> {
    fn unlock(self, key: u32) -> Result<Safe<Unlocked>, Self> {
        if key == 42 { Ok(Safe { _state: Unlocked }) } else { Err(self) }
    }
}

impl Safe<Unlocked> {
    fn retrieve(&self) -> &'static str { "secret" }
    fn lock(self) -> Safe<Locked> { Safe { _state: Locked } }
}

fn main() {
    let safe = Safe { _state: Locked };
    match safe.unlock(42) {
        Ok(open) => { println!("{}", open.retrieve()); let _ = open.lock(); }
        Err(_) => {}
    }
}
```

Typestate 的编译期保证也可以用 `compile_fail` 展示。以下代码在锁定状态下调用 `retrieve`，触发 `E0599`：

```rust,compile_fail,E0599
struct Locked;
struct Unlocked;

struct Safe<S> { _state: S }

impl Safe<Locked> {
    fn unlock(self, key: u32) -> Result<Safe<Unlocked>, Self> {
        if key == 42 { Ok(Safe { _state: Unlocked }) } else { Err(self) }
    }
}

impl Safe<Unlocked> {
    fn retrieve(&self) -> &'static str { "secret" }
}

fn main() {
    let safe = Safe { _state: Locked };
    // ❌ E0599：Locked 状态没有 retrieve 方法
    println!("{}", safe.retrieve());
}
```

> **来源**: [Rust Reference — Items](https://doc.rust-lang.org/reference/items.html) · [Rust By Example — Generics](https://doc.rust-lang.org/rust-by-example/generics.html)

---

### 1.12 Rust 中的形式语言实例

Rust 程序在不同编译阶段对应形式语言层级的不同对象：

| Rust 对象 | 形式语言层级 | 识别工具 | 关键特征 |
|:---|:---|:---|:---|
| 词法 token（`fn`, `let`, 标识符） | 正则 | 词法分析器 | 有限状态即可识别 |
| 表达式/语句语法 | 上下文无关 | rustc 解析器 | 需要嵌套/匹配结构 |
| `macro_rules!` 匹配 | 超越 CFG | 宏展开器 | 可生成上下文有关模式 |
| 过程宏 (proc-macro) | 图灵完备 | proc-macro crate | 编译期执行任意 Rust 代码 |
| 类型约束求解 | 可判定（核心） | trait solver | 保证编译终止 |
| `const` 求值 | 半可判定 | CTFE / Miri | 可能有步数限制 |

```rust
// Rust 宏系统比 CFG 更强的简单示例：
// macro_rules! 可以重复匹配嵌套模式并生成新代码
macro_rules! count_tts {
    () => { 0usize };
    ($head:tt $($tail:tt)*) => { 1usize + count_tts!($($tail)*) };
}

fn main() {
    let n = count_tts!(a b c d e);
    assert_eq!(n, 5);
}
```

宏展开后的代码才进入 CFG 解析阶段。下面展示「移动后继续使用」的所有权错误 `E0382`，说明宏生成的代码也必须遵守 Rust 的语义约束，而这些约束超出了纯形式语法：

```rust,compile_fail,E0382
macro_rules! move_and_use {
    ($v:expr) => { {
        let x = $v;
        x.len()
    } };
}

fn main() {
    let v = vec![1, 2, 3];
    let n = move_and_use!(v);
    // ❌ E0382：v 已被移动进宏生成的 let x = v;
    println!("{} {}", n, v.len());
}
```

> **Rust 实例洞察**: `regex` crate 实现 DFA/NFA；rustc 解析器处理 CFG；`macro_rules!` 和过程宏进入图灵完备领域。理解这三层有助于判断「哪些编译错误来自语法，哪些来自语义/类型」。
> (Source: [Rust Reference — Items](https://doc.rust-lang.org/reference/items.html))

---

### 1.13 从自动机到程序语言理论的桥梁

形式语言不是孤立的分类游戏，它与 λ 演算、类型理论、指称语义和程序等价理论共享同一套「能识别什么 / 能表达什么」的核心问题。

#### 1.13.1 自动机、λ 演算与 Church-Turing 论题

无类型 λ 演算与图灵机在计算能力上等价，而 λ 项的合法语法本身也可以视为一种形式语言。Barendregt 把 λ 演算的语法、归约理论与可计算函数统一起来：λ 项的集合由上下文无关文法定义，但其归约行为（β-归约）则进入半可判定领域（Barendregt, 1984, §2.1, §3.2; Church, 1936; Turing, 1936）。

```text
λ 项的文法（CFG）:
  M ::= x | λx.M | M M

β 归约（半可判定）:
  (λx.M) N →β M[x := N]
```

Rust 的闭包与 λ 抽象有直观对应，但 Rust 的类型系统、所有权和求值策略使其行为与无类型 λ 演算不同。详见 [Lambda Calculus](../00_type_theory/05_lambda_calculus.md)。

> **来源**: [Barendregt 1984 — The Lambda Calculus: Its Syntax and Semantics, §2.1, §3.2](https://doi.org/10.1016/B978-0-444-87508-2.50006-X) · [Church 1936 — An Unsolvable Problem of Elementary Number Theory](https://doi.org/10.2307/1968981) · [Turing 1936 — On Computable Numbers](https://doi.org/10.1112/plms/s2-42.1.230) · [Sipser 2013 — Introduction to the Theory of Computation](https://math.mit.edu/~sipser/book.html) · [Soare 2016 — Turing Computability](https://doi.org/10.1007/978-3-642-31933-4) · [Cutland 1980 — Computability](https://doi.org/10.1017/CBO9780511574916)

#### 1.13.2 类型系统作为形式语言：Pierce 的视角

Pierce 在 *Types and Programming Languages* 中指出：类型检查本质上是判定一个项是否属于「良类型项」集合，而这个集合的复杂性取决于类型系统的规则。简单类型 λ 演算的类型检查是可判定的；加入递归类型、多态或依赖类型后，复杂度逐渐上升。

在 Rust 中，trait bound 的满足性判定可以看作一种受限的逻辑程序；关联类型与泛型 monomorphization 则把类型层面的判定问题投射到代码生成阶段。详见 [Type Theory](../00_type_theory/01_type_theory.md) 与 [Type Inference](../00_type_theory/03_type_inference.md)。

> **来源**: [Pierce 2002 — Types and Programming Languages, Ch. 9–12, 22](https://www.cis.upenn.edu/~bcpierce/tapl/)

#### 1.13.3 指称语义与 Scott 域

Scott 把数据类型建模为完全偏序（complete partial order）上的格，把程序解释为从输入域到输出域的连续函数。在这一视角下，一个语言的「可观察行为」可以被看作其指称域中的元素集合；形式语言中的「语言 L」则是这种集合的离散特例。

Rust 中的发散类型 `!`、递归类型与 `Option`/`Result` 都可以在 Scott 域的框架下理解：发散对应底元 ⊥，`Option<T>` 对应在 `T` 上加入一个额外的底部/失败元素。详见 [Denotational Semantics](../03_operational_semantics/01_denotational_semantics.md)。

> **来源**: [Scott 1976 — Data Types as Lattices](https://doi.org/10.1137/0205037) · [Scott & Strachey 1971 — Toward a Mathematical Semantics for Computer Languages](https://www.cs.tufts.edu/~nr/cs257/archive/tony-hoare/mathematical-semantics.pdf)

#### 1.13.4 表达力：Felleisen 框架

Felleisen 区分了「计算能力」与「表达能力」。所有图灵完备语言计算能力相同，但表达特定概念所需的局部/全局变换代价不同。形式语言层级中的「层级提升」正是表达能力代价的一种度量：从正则到 CFG 需要引入栈；从 CFG 到图灵完备需要引入无界存储。

Rust 的 `async/await`、`?`、`try` 块等构造并不提升图灵完备性，但通过局部去糖降低工程成本。详见 [Equivalence of Computational Models](05_equivalence_of_computational_models.md)。

> **来源**: [Felleisen 1991 — On the Expressive Power of Programming Languages](https://www.cs.tufts.edu/~nr/cs257/archive/matthias-felleisen/expressive-as-published.pdf) · [Felleisen & Flatt 1998 — Units: Cool Modules for HOT Languages](https://doi.org/10.1145/277650.277731)

#### 1.13.5 程序等价与观察等价：Ahmed / Pitts

当两个 typestate 实现或两个解析器被宣称「行为相同」时，其精确含义是**观察等价**：在所有合法程序上下文中，它们产生相同的外部可观察结果。Pitts 的 operationally-based logical relations 与 Ahmed 的 step-indexed logical relations 为证明这种等价提供了结构化方法。

在 Rust 中，「`safe_swap` 的 safe 封装与其内部 unsafe 实现在所有 safe 上下文下观察等价」正是 unsafe 抽象正确性的形式化表述。详见 [Observational Equivalence](../03_operational_semantics/06_observational_equivalence.md) 与 [RustBelt](../02_separation_logic/01_rustbelt.md)。

> **来源**: [Ahmed 2006 — Step-Indexed Syntactic Logical Relations for Recursive and Quantified Types](https://doi.org/10.1007/11693024_6) · [Pitts 1997 — Operationally-Based Theories of Program Equivalence](https://www.cl.cam.ac.uk/~amp12/papers/index.html) · [Pitts & Stark 1998 — Operational Reasoning for Functions with Local State](https://www.cl.cam.ac.uk/~amp12/papers/operfl/operfl.pdf)

---

## 二、反命题与边界分析

本节检验形式语言学习中的三条常见误判：

1. **「Rust 语法是正则语言」**：错——任意嵌套的块和括号需要栈，已超出 DFA 能力；
2. **「正则表达式可以匹配任意嵌套结构」**：错——泵引理证明正则语言无法计数嵌套深度；
3. **「上下文无关语言足以描述全部 Rust」**：错——宏 hygiene、过程宏和某些语义约束需要更强的形式化工具。

每条误判附最小反例与形式语言层面的解释。

### 2.1 反命题：Rust 语法是正则语言

```mermaid
graph TD
    ROOT["命题: Rust 语法是正则语言"]
    ROOT --> Q1{"是否存在任意嵌套的成对分隔符?"}
    Q1 -->|是| CFG["❌ 不是正则语言，至少是 CFG"]
    Q1 -->|否| REG["✅ 可能是正则语言"]

    style CFG fill:#ffcdd2
    style REG fill:#c8e6c9
```

**形式化证明（泵引理反证）**：

假设 Rust 语法是正则语言，则存在泵长度 `p`。取程序：

```text
fn main() { { { ... { } ... } } }
```

其中包含 `p+1` 层嵌套大括号。根据泵引理，这部分可被分解为 `xyz`，且 `|xy| ≤ p`、`|y| > 0`，使得对所有 `i ≥ 0`，`xyⁱz` 仍在语言中。 pumping `y` 会改变嵌套深度，导致括号不平衡——与 Rust 语法矛盾。因此 Rust 语法不是正则语言。

```rust,compile_fail,E0004
// ❌ 编译错误：非穷举的 match 证明有限状态必须处理所有状态
enum State { A, B, C }

fn transition(s: State) -> bool {
    match s {
        State::A => true,
        State::B => false,
        // 缺少 State::C 分支 ⇒ E0004
    }
}

fn main() {}
```

> **反命题修正**: Rust 的**词法**可用正则处理，但**语法**需要 CFG 及以上。把「词法简单」误认为「语法简单」是常见错误。
> (Source: [Rust Reference — Expressions](https://doc.rust-lang.org/reference/expressions.html))

---

### 2.2 边界极限

```text
边界 1: 正则 vs CFG
├── 正则语言无法表达任意嵌套
├── Rust 的 {}、()、[] 必须成对匹配
└── 解析器必须维护栈结构

边界 2: CFG 的封闭性
├── CFG 对并、连接、Kleene 星号封闭
├── CFG 对交、补不封闭
└── 某些 Rust 语义约束（如变量作用域）不能用纯 CFG 表达

边界 3: 宏系统超越 CFG
├── macro_rules! 可生成上下文有关模式
├── 过程宏直接运行 Rust 代码
└── 宏展开后的代码才进入 CFG 解析阶段

边界 4: 判定性边界
├── 词法/语法分析时间可控
├── 类型检查在核心 Rust 中可判定
└── 某些泛型/关联类型场景接近判定性边界

边界 5: 形式语言与 PL 理论的交汇
├── 自动机 ↔ 类型状态（typestate）
├── CFG ↔ 表达式语法 / 类型检查
├── 图灵机 ↔ λ 演算 / 过程宏 / const 求值
└── 表达能力 ↔ Felleisen 局部/全局变换框架

边界 6: 工程实践
├── 形式语言给出的是「合法字符串集合」
├── 实际编译器还需处理错误恢复、 hygiene、span 信息
└── 形式化模型是理想化抽象
```

> **边界要点**: Rust 编译器是形式语言理论与工程实现的结合。形式层级决定「能识别什么」，工程细节决定「如何优雅地报告错误」。

---

## 三、常见陷阱

```text
陷阱 1: 用正则表达式解析 Rust 源代码
  ❌ 尝试用 regex 匹配任意嵌套结构
     let re = Regex::new(r"\{[^}]*\}").unwrap();
     // 无法匹配 { { } }

  ✅ 使用 syn / rustc 解析器处理 CFG

陷阱 2: 混淆「语法合法」与「类型正确」
  ❌ 认为通过解析就保证编译成功
     let x: String = 42; // 语法合法，类型错误

  ✅ 语法只是第一层过滤；类型/借用检查在更上层

陷阱 3: 低估宏系统的表达力
  ❌ 把 macro_rules! 等同于简单的文本替换

  ✅ macro_rules! 有 hygiene 和重复匹配；过程宏是完整程序

陷阱 4: 忽视泵引理的实际含义
  ❌ "这个语言看起来简单，应该是正则的"

  ✅ 只要需要任意深度计数或匹配，就需要 CFG 或更强模型

陷阱 5: 混淆可识别与可判定
  ❌ "编译器总能告诉我程序是否合法"

  ✅ 宏展开和 const 求值可能不终止；编译器有步数/超时限制

陷阱 6: 把 NFA/DFA 等价当作「实现等价」
  ❌ "NFA 和 DFA 等价，所以用哪个实现都一样快"

  ✅ NFA 到 DFA 的幂集构造可能指数级膨胀；实际库采用按需模拟或 Thompson + 子集构造
```

> **陷阱总结**: 形式语言理论的陷阱主要与**正则语言边界**、**语法与语义分层**、**宏系统表达力**、**泵引理应用**、**判定性边界**和**自动机实现复杂度**相关。

---

## 四、权威来源 / International Authority References

| 来源 | 可信度 | 说明 |
|:---|:---:|:---|
| [Turing 1936 — On computable numbers, with an application to the Entscheidungsproblem](https://doi.org/10.1112/plms/s2-42.1.230) | ✅ 一级 | 图灵机奠基；停机问题原始证明 |
| [Church 1936 — An Unsolvable Problem of Elementary Number Theory](https://doi.org/10.2307/1968981) | ✅ 一级 | λ 可定义函数；Church-Turing 论题 |
| [Rice 1953 — Classes of Recursively Enumerable Sets and Their Decision Problems](https://doi.org/10.1090/S0002-9904-1953-09692-2) | ✅ 一级 | 语义性质不可判定性（Rice 定理） |
| [Hopcroft, Motwani & Ullman 2006 — Introduction to Automata Theory, Languages, and Computation, 3rd ed.](https://en.wikipedia.org/wiki/Introduction_to_Automata_Theory,_Languages,_and_Computation) | ✅ 一级 | 自动机理论经典教材；DFA/NFA §2，泵引理 §4.1/§7.2，Myhill-Nerode §4.4，PCP §9.4 |
| [Sipser 2013 — Introduction to the Theory of Computation, 3rd ed.](https://math.mit.edu/~sipser/book.html) | ✅ 一级 | 可计算性与复杂度理论；正则泵引理 §1.4，CFG 泵引理 §2.3，Myhill-Nerode §1.4，可判定性 §4，Rice §5.1，PCP §5.2 |
| [Soare 2016 — Turing Computability. Theory and Applications](https://doi.org/10.1007/978-3-642-31933-4) | ✅ 一级 | 现代可计算性理论；算术层级 |
| [Cutland 1980 — Computability: An Introduction to Recursive Function Theory](https://doi.org/10.1017/CBO9780511574916) | ✅ 一级 | 递归函数与可计算性入门 |
| [Kozen 1997 — Automata and Computability](https://doi.org/10.1007/978-1-4612-1844-9) | ✅ 一级 | 自动机、可计算性与复杂度理论 |
| [Appel 2004 — Modern Compiler Implementation in Java/C/ML, 2nd ed.](https://www.cs.princeton.edu/~appel/modern/) | ✅ 一级 | 编译器实现与语义后端（Tiger Book） |
| [Chomsky 1956 — Three Models for the Description of Language](https://doi.org/10.1109/TIT.1956.1056813) | ✅ 一级 | Chomsky 层级奠基论文 |
| [Rabin & Scott 1959 — Finite Automata and Their Decision Problems](https://doi.org/10.1515/9781400882618-010) | ✅ 一级 | NFA-DFA 等价与幂集构造 |
| [Myhill 1957 — Finite Automata and the Representation of Events](https://doi.org/10.1515/9781400882618-008) | ✅ 一级 | Myhill-Nerode 定理前身 |
| [Nerode 1958 — Linear Automaton Transformations](https://doi.org/10.2307/1993204) | ✅ 一级 | Myhill-Nerode 定理的代数形式 |
| [Barendregt 1984 — The Lambda Calculus: Its Syntax and Semantics](https://doi.org/10.1016/B978-0-444-87508-2.50006-X) | ✅ 一级 | λ 演算标准参考书；连接形式语言与可计算性 |
| [Scott 1972 — Continuous Lattices](https://doi.org/10.1007/BFb0073967) | ✅ 一级 | 连续格与 Scott 域奠基 |
| [Scott 1976 — Data Types as Lattices](https://doi.org/10.1137/0205037) | ✅ 一级 | Scott 域与指称语义；数据类型作为格的奠基 |
| [Scott & Strachey 1971/2000 — Toward a Mathematical Semantics for Computer Languages](https://www.cs.ox.ac.uk/files/3232/PRG06.pdf) | ✅ 一级 | 指称语义奠基文献（PRG-6） |
| [Strachey 1973 — The Varieties of Programming Language](https://doi.org/10.1016/S0065-2458(08)60314-4) | ✅ 一级 | 程序语言语义分类 |
| [Pierce 2002 — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/) | ✅ 一级 | 类型系统作为形式语言；Ch. 9–12, 22 |
| [Wadler 2015 — Propositions as Types](https://doi.org/10.1145/2699407) | ✅ 一级 | Curry-Howard 对应现代综述 |
| [Felleisen 1991 — On the Expressive Power of Programming Languages](https://www.cs.tufts.edu/~nr/cs257/archive/matthias-felleisen/expressive-as-published.pdf) | ✅ 一级 | 表达力比较框架；局部 vs 全局变换 |
| [Ahmed 2006 — Step-Indexed Syntactic Logical Relations for Recursive and Quantified Types](https://doi.org/10.1007/11693024_6) | ✅ 一级 | step-indexed logical relations；证明程序等价 |
| [Pitts 1997 — Operationally-Based Theories of Program Equivalence](https://www.cl.cam.ac.uk/~amp12/papers/index.html) | ✅ 一级 | 基于操作语义的程序等价；CIU 与 logical relations |
| [Pitts & Stark 1998 — Operational Reasoning for Functions with Local State](https://www.cl.cam.ac.uk/~amp12/papers/operfl/operfl.pdf) | ✅ 一级 | 高阶状态化语言的观察等价推理 |
| [Ord 2006 — The Many Forms of Hypercomputation](https://doi.org/10.1016/j.apal.2005.09.012) | ✅ 一级 | 超计算与 Church-Turing 边界讨论 |
| [Rust Reference — Introduction](https://doc.rust-lang.org/reference/introduction.html) | ✅ P0 | Rust 官方参考手册 |
| [Rust Reference — Macros By Example](https://doc.rust-lang.org/reference/macros-by-example.html) | ✅ P0 | 声明宏官方规格 |
| [Rust Reference — Expressions](https://doc.rust-lang.org/reference/expressions.html) | ✅ P0 | Rust 表达式语法 |
| [Rust Reference — Lexical Structure](https://doc.rust-lang.org/reference/tokens.html) | ✅ P0 | Rust 词法结构 |
| [regex crate documentation](https://docs.rs/regex) | ✅ 二级 | Rust 正则表达式实现 |
| [nom crate documentation](https://docs.rs/nom) | ✅ 二级 | 解析器组合子 |
| [pest crate documentation](https://docs.rs/pest) | ✅ 二级 | PEG 解析器生成器 |
| [lalrpop documentation](https://lalrpop.github.io/lalrpop/) | ✅ 二级 | LR(1)/LALR 解析器生成器 |
| [syn crate documentation](https://docs.rs/syn) | ✅ 二级 | Rust 语法树解析 |

---

## 相关概念

- [Type Theory](../00_type_theory/01_type_theory.md) — 类型理论
- [Type Inference](../00_type_theory/03_type_inference.md) — 类型推断与约束求解
- [Lambda Calculus](../00_type_theory/05_lambda_calculus.md) — 函数式计算模型
- [Macros](../../03_advanced/03_proc_macros/01_macros.md) — Rust 宏系统
- [Computability Theory](02_computability_theory.md) — 可计算性理论
- [Equivalence of Computational Models](05_equivalence_of_computational_models.md) — 计算模型等价性
- [Observational Equivalence](../03_operational_semantics/06_observational_equivalence.md) — 观察等价性
- [Denotational Semantics](../03_operational_semantics/01_denotational_semantics.md) — 指称语义
- [Decidability Spectrum](../../00_meta/00_framework/decidability_spectrum.md) — 可判定性谱系

---

## 嵌入式测验（Embedded Quiz）

### 测验 1：Chomsky 层级（理解层）

Rust 源代码中的**标识符**（如 `foo`、`bar_baz`）属于 Chomsky 层级的哪一类？

- A. 上下文无关语言
- B. 正则语言
- C. 上下文有关语言
- D. 递归可枚举语言

<details>
<summary>✅ 答案</summary>

**B. 正则语言**。

标识符由有限字母表上的有限模式定义（字母/下划线开头，后跟字母/数字/下划线），可用正则表达式 `[A-Za-z_][A-Za-z0-9_]*` 描述，因此属于正则语言。Rust 的词法分析阶段使用正则/NFA 类方法识别 token。

</details>

---

### 测验 2：正则语言边界（分析层）

下列哪个 Rust 结构**不能**用正则语言精确描述？

- A. `let x = 1;` 形式的简单变量声明
- B. 任意嵌套深度的 `{ ... { ... } ... }` 块表达式
- C. 由逗号分隔的标识符列表
- D. 十六进制整数字面量

<details>
<summary>✅ 答案</summary>

**B. 任意嵌套深度的 `{ ... { ... } ... }` 块表达式**。

正则语言无法计数或匹配任意深度的嵌套结构（泵引理可证）。块表达式需要 CFG 或更强的文法。其余选项都是局部、有限状态可识别的模式。

</details>

---

### 测验 3：CFG 与 Rust 解析（应用层）

Rust 的 `match` 表达式为什么需要 CFG 而不是正则语言？

- A. 因为 `match` 关键字太长
- B. 因为 `match` 分支之间可能嵌套块和花括号
- C. 因为 `match` 会调用 trait 方法
- D. 因为 `match` 只能在函数内部使用

<details>
<summary>✅ 答案</summary>

**B. 因为 `match` 分支之间可能嵌套块和花括号**。

`match expr { pat => { ... }, ... }` 的语法包含成对且可能嵌套的花括号，这种匹配结构需要栈来解析，已超出 DFA/正则的能力范围。

</details>

---

### 测验 4：NFA/DFA 与 typestate（综合层）

下面关于 NFA、DFA 与 typestate 的说法，哪一项是**正确**的？

- A. NFA 比 DFA 能识别更多语言
- B. 幂集构造说明任何 NFA 都可转换为等价的 DFA
- C. typestate 只能模拟无限状态机
- D. Rust 的类型系统不能表达状态转移约束

<details>
<summary>✅ 答案</summary>

**B. 幂集构造说明任何 NFA 都可转换为等价的 DFA**。

Rabin & Scott（1959）的子集构造证明 NFA 与 DFA 表达力等价，但 DFA 状态数可能指数级增长。typestate 用泛型把状态编码为类型，是有限状态机在类型系统中的实现；Rust 编译器会拒绝违反状态转移约束的代码。

</details>

---

### 测验 5：可判定性边界（评价层）

下列 Rust 编译阶段中，哪一项可能涉及**半可判定**问题？

- A. 词法分析（tokenization）
- B. 语法分析（parsing）
- C. `const fn` 的编译期求值
- D. 识别关键字 `fn`

<details>
<summary>✅ 答案</summary>

**C. `const fn` 的编译期求值**。

词法分析、语法分析和关键字识别都是可判定问题（有限时间内必有结果）。`const fn` 可能包含任意循环/递归，其终止性由停机问题限制，因此编译器只能设置步数上限，属于半可判定问题。

</details>

---

## 🧭 思维导图（Mindmap）

```mermaid
mindmap
  root((形式语言与自动机))
    Chomsky 层级
      Type-3 正则语言
        DFA
        NFA
        正则表达式
      Type-2 上下文无关语言
        CFG
        PDA
        LL/LR 解析
      Type-1 上下文有关语言
        LBA
      Type-0 递归可枚举语言
        图灵机
    泵引理
      正则语言泵引理
      上下文无关语言泵引理
    Myhill-Nerode 定理
      不可区分关系
      有限指数 ⇔ 正则
    闭包性质
      正则：并/交/补/连接/星号
      CFL：并/连接/星号；不交/补
    NFA/DFA 等价
      Thompson 构造
      幂集构造
      状态数指数上界
    Rust 解析生态
      regex
      nom
      pest
      lalrpop
      syn
    Typestate 与自动机
      状态编码为类型
      trait 表达转移
      E0599 错误示例
      E0382 移动示例
    Rust 实例
      词法：正则
      表达式语法：CFG
      macro_rules!：超越 CFG
      过程宏：图灵完备
      const 求值：半可判定
    PL 理论桥梁
      Barendregt λ 演算
      Scott 指称语义
      Pierce 类型系统
      Felleisen 表达力
      Ahmed/Pitts 观察等价
    边界与反命题
      Rust 语法不是正则语言
      正则表达式无法匹配任意嵌套
      CFG 不能描述全部 Rust
      形式层级 vs 工程实现
```

> **认知功能**: 本 mindmap 从本页「形式语言与自动机」的章节结构提炼，一级分支对应核心主题，叶子节点为关键子概念，可作为本页的快速导航与复习索引。
