> **内容分级**: [专家级]

# 计算语义统一框架（A Unified Framework of Computational Semantics）

> **EN**: A Unified Framework of Computational Semantics
> **Summary**: Unifying operational, denotational, axiomatic, and type semantics as four complementary lenses on the same computational reality.

> **Rust 版本**: 1.97.0+ (Edition 2024)
> **Bloom 层级**: L4-L5
> **权威来源**: 本文件为 `concept/` 权威页。
> **定位**: 把操作、指称、公理、类型四种语义统一为观察同一程序行为的四种互补视角，为后续可计算性、形式语言与程序等价性讨论奠定共同语言。
> **前置概念**: [Async/Await](../../03_advanced/01_async/01_async.md) · [Lambda Calculus](../00_type_theory/05_lambda_calculus.md) · [Type Theory](../00_type_theory/01_type_theory.md)
> **后置概念**: [Computability Theory](02_computability_theory.md) · [Mathematical Functions of Computation](04_mathematical_functions_of_computation.md) · [Equivalence of Computational Models](05_equivalence_of_computational_models.md)

---

## 📑 目录

- [计算语义统一框架（A Unified Framework of Computational Semantics）](#计算语义统一框架a-unified-framework-of-computational-semantics)
  - [📑 目录](#-目录)
  - [一、核心概念](#一核心概念)
    - [1.1 四种语义风格](#11-四种语义风格)
    - [1.2 它们之间的关系](#12-它们之间的关系)
    - [1.3 Rust 示例：`let x = 1 + 1`](#13-rust-示例let-x--1--1)
    - [1.4 `unsafe` 作为公理契约](#14-unsafe-作为公理契约)
    - [1.5 计算语义与 Church-Turing 论题](#15-计算语义与-church-turing-论题)
  - [二、反命题与边界分析](#二反命题与边界分析)
  - [三、相关概念](#三相关概念)
  - [四、嵌入式测验（Embedded Quiz）](#四嵌入式测验embedded-quiz)
    - [测验 1：四种语义的核心问题（理解层）](#测验-1四种语义的核心问题理解层)
    - [测验 2：`unsafe` 的最合适语义视角（分析层）](#测验-2unsafe-的最合适语义视角分析层)
    - [测验 3：指称语义的普遍性（评价层）](#测验-3指称语义的普遍性评价层)
  - [五、权威来源索引](#五权威来源索引)
  - [六、🧭 思维导图（Mindmap）](#六-思维导图mindmap)

---

## 一、核心概念

### 1.1 四种语义风格

程序语义回答「这段代码是什么意思」。不同语义风格关注不同问题：

```text
四种语义风格：
┌─────────────────┬─────────────────┬─────────────────┐
│ 语义风格        │ 核心问题        │ 典型工具/符号   │
├─────────────────┼─────────────────┼─────────────────┤
│ 操作语义        │ 如何执行        │ 转换规则 e → e' │
│ 指称语义        │ 表示什么数学对象│ 函数 ⟦e⟧ : D → D│
│ 公理语义        │ 为什么正确      │ 霍尔三元组 {P}C{Q}│
│ 类型语义        │ 哪些值可以使用  │ 类型判断 Γ ⊢ e:T│
└─────────────────┴─────────────────┴─────────────────┘
```

- **操作语义（Operational）**：用抽象机器或重写规则描述「程序一步一步如何运行」。Plotkin 的结构化操作语义（SOS）是现代教材与工具中的标准表述（Plotkin, 1981; Winskel, 1993, Ch. 2）。
- **指称语义（Denotational）**：把程序映射为数学对象（通常是域上的连续函数），强调「程序表示什么」。Scott 与 Strachey 的域论语义为递归构造提供了数学基础（Scott & Strachey, 1971/2000; Scott, 1976）。
- **公理语义（Axiomatic）**：用霍尔逻辑 `{P} C {Q}` 描述命令前后断言关系，强调「程序满足什么规约」。
- **类型语义（Type）**：把类型视为对程序行为的静态分类，回答「哪些值可以出现在哪些位置」。Pierce 将类型系统作为程序语义的核心透镜之一（Pierce, 2002, Ch. 1 & Ch. 9）。

---

### 1.2 它们之间的关系

四种语义并非竞争关系，而是同一程序的不同投影：

```text
关键关系：
├── 充分性（Adequacy）：操作语义与指称语义在可观察行为上一致
│   └── ⟦e⟧ = ⟦e'⟧  ⇒  e 与 e' 在操作语义下不可区分
├── 完全抽象（Full Abstraction）：
│   └── e 与 e' 在操作语义下不可区分 ⇔ ⟦e⟧ = ⟦e'⟧
├── 公理语义的声音性（Soundness）：
│   └── 若 ⊢ {P} C {Q}，则任何满足 P 的初始状态执行 C 后都满足 Q
└── 公理语义的完备性（Completeness）：
    └── 若 C 确实把 P 状态变为 Q 状态，则 ⊢ {P} C {Q} 可证
```

> **认知要点**：没有哪一种语义能回答所有问题。证明编译器正确性常用操作语义；证明程序等价性常用指称语义；验证安全属性常用公理语义；静态保证则依赖类型语义。Felleisen 的表达力框架进一步区分「计算能力」与「表达能力」：所有图灵完备模型能计算相同函数，但表达同一概念所需的局部/全局变换代价不同（Felleisen, 1991; Felleisen & Flatt, 1998）。

---

### 1.3 Rust 示例：`let x = 1 + 1`

对同一条 Rust 语句，四种语义给出不同描述：

```text
let x = 1 + 1;

操作语义：
  ⟨1 + 1, σ⟩ → ⟨2, σ⟩
  ⟨let x = 2, σ⟩ → ⟨(), σ[x ↦ 2]⟩

指称语义：
  ⟦let x = 1 + 1⟧(σ) = σ[x ↦ 2]

公理语义：
  {true} let x = 1 + 1 {x = 2}

类型语义：
  Γ ⊢ 1 + 1 : i32
  Γ, x:i32 ⊢ let x = 1 + 1 : ()
```

```rust
fn main() {
    let x = 1 + 1;
    assert_eq!(x, 2);
}
```

---

### 1.4 `unsafe` 作为公理契约

Rust 的 `unsafe` 块可以被理解为一种**公理契约**：调用者承诺满足某些前置条件，编译器则信任这些承诺并允许执行超出 safe 子集的操作。

```text
unsafe { *ptr = 0; }

公理视角：
  { ptr 有效 ∧ ptr 对齐 ∧ 无数据竞争 }
    unsafe { *ptr = 0; }
  { *ptr = 0 }

如果前置条件不满足，操作语义进入未定义行为（UB）状态，
指称语义可能无定义，类型语义也无法保证内存安全。
```

```rust
fn main() {
    let mut x = 0;
    let ptr = &mut x as *mut i32;
    unsafe {
        *ptr = 42;
    }
    assert_eq!(x, 42);
}
```

> **来源**: [Rust Reference — Unsafe blocks](https://doc.rust-lang.org/reference/unsafe-keyword.html#unsafe-blocks) · [Rustonomicon](https://doc.rust-lang.org/nomicon/index.html)

---

### 1.5 计算语义与 Church-Turing 论题

**Church-Turing 论题**（Church, 1936; Turing, 1936）不是一条可在形式系统内证明的定理，而是关于「有效可计算」边界的经验性/哲学性论断。它得到 Sipser、Soare、Cutland、Hopcroft-Motwani-Ullman 等教材的共同强调（Sipser, 2013, §3.3; Soare, 2016, §1.1; Cutland, 1980, §8.1; Hopcroft, Motwani & Ullman, 2006, §8.6）：

> 任何可被人类或机械「有效计算」的函数，都可以由图灵机计算，也可以由无类型 λ 演算表达，也可以由部分递归函数定义。

这三种经典模型在表达力上是等价的：

```text
计算等价链：
  图灵机  ≡  无类型 λ 演算  ≡  部分递归函数
           ≡  通用寄存器机  ≡  所有图灵完备编程语言（无资源限制）
```

- **图灵机**从「状态-磁带」角度刻画计算：一条无限长磁带、一个读写头、有限状态控制器（Turing, 1936; Sipser, 2013, §3.1）。
- **λ 演算**从「函数与应用」角度刻画计算：通过 λ 抽象与 β 归约表达任意可计算函数（Church, 1936; Barendregt, 1984, §6.3）。
- **部分递归函数**从「函数构造」角度刻画计算：从零、后继、投影出发，经组合、原始递归与无界最小化得到所有可计算函数（Kleene, 1952; Cutland, 1980, §3.1）。

它们之间的相互模拟（simulation）正是**计算语义**要回答的问题：给定一种语言的程序，如何把它映射到另一种语义模型，并证明映射保持可观察行为。超计算（hypercomputation）研究则探讨若允许无限资源或非图灵计算模型，能否超越 Church-Turing 边界（Ord, 2006）。

#### Rust const 求值：受约束的可计算性

Rust 的 **const 求值（const evaluation）** 是 Church-Turing 论题在工程语言中的一个**受约束实例**。`const fn` 与 `const` 上下文允许在编译期执行计算，但这些计算被严格限制，以保证编译期终止性、确定性与无堆分配（Sipser, 2013, §3.3; Cutland, 1980, §8.1）：

| 能力 | const 上下文 | 说明 |
|:---|:---:|:---|
| 算术与位运算 | ✅ | 基本整数、布尔、字符运算 |
| 条件表达式 `if` / `match` | ✅ | 自 Rust 1.46 起允许 |
| `loop` / `while` / `for` | ✅ | 允许，但受解释器迭代步数上限约束 |
| 递归调用 | ✅ | 允许，但展开深度与步数受 const 求值限制器约束 |
| 调用其他 `const fn` | ✅ | 只能调用已标记为 `const fn` 的函数 |
| 堆分配（`Box`、`Vec` 等） | ❌ | 编译期无堆，会报 E0015 等错误 |
| 调用非 `const` 标准库方法 | ❌ | 例如 `Vec::push` 未 const-stabilized |
| 未定义行为 / 任意 I/O | ❌ | const 求值必须是纯函数式的 |

```rust,compile_fail,E0015
const fn heap_alloc_in_const() -> Vec<i32> {
    vec![1, 2, 3] // ERROR: vec! 宏在 const fn 中会触发堆分配，
                  // 其底层调用（如 Box::new_uninit）不是 const fn
}
```

`const fn` 中的无界递归或算术溢出会在编译期触发 `E0080`（evaluation of constant value failed），这直接体现了 Church-Turing 论题在受约束子集中的投影：通用计算允许不终止，但编译期求值必须被强制截断：

```rust,compile_fail,E0080
const fn forever() -> i32 {
    forever() // ERROR E0080: 常量求值器在有限步内无法完成，
              // 说明 const 上下文不允许无界递归
}

const X: i32 = forever();

fn main() {}
```

> **认知要点**：const 求值不是「可计算性更弱」——它在理论上仍是图灵完备的受限子集；其限制主要来自**编译期资源与确定性要求**，而非计算理论本身。循环、递归、条件都能写，但一旦超出内部解释器的步数/迭代上限，编译器会报告 `evaluation of constant value failed`。

> **来源**: [Church 1936 / Church-Turing 论题综述](https://arxiv.org/abs/cs/0503082) · [Turing 1936 — On computable numbers, with an application to the Entscheidungsproblem](https://doi.org/10.1112/plms/s2-42.1.230) · [Sipser 2013 — Introduction to the Theory of Computation, 3rd ed.](https://math.mit.edu/~sipser/book.html) · [Cutland 1980 — Computability: An Introduction to Recursive Function Theory](https://doi.org/10.1017/CBO9780511574916) · [Winskel 1993 — The Formal Semantics of Programming Languages](https://www.cs.cmu.edu/~crary/819-f09/Winskel.pdf) · [Pierce 2002 — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/)

---

## 二、反命题与边界分析

一个常见误判是：**「每种语言都有现成的指称语义」**。事实上，指称语义需要为语言构造找到合适的数学空间（domain）。对于无类型 λ 演算加无限制递归，直接构造集合论函数会导致悖论，必须引入**Scott 域（Scott domain）**和**连续函数（continuous functions）**才能给出一致的指称语义。

```text
反命题：指称语义总是存在。
├── 错误：无类型 λ 演算 + 无限制递归不能直接用普通集合论函数解释
├── 修正：需要域论（domain theory）和 Scott 连续函数
└── 边界：某些语言构造（如反射、任意宏展开）至今仍无满意指称语义
```

> **来源**: [Scott & Strachey — Toward a Mathematical Semantics for Computer Languages](https://www.cs.ox.ac.uk/files/3232/PRG06.pdf) · [Winskel 1993 — The Formal Semantics of Programming Languages](https://www.cs.cmu.edu/~crary/819-f09/Winskel.pdf)

---

## 三、相关概念

- [Lambda Calculus](../00_type_theory/05_lambda_calculus.md) — λ 演算与函数抽象
- [Operational Semantics](../03_operational_semantics/03_operational_semantics.md) — 程序行为的小步/大步规则
- [Denotational Semantics](../03_operational_semantics/01_denotational_semantics.md) — 程序到数学对象的映射
- [Axiomatic Semantics](../03_operational_semantics/05_axiomatic_semantics.md) — 霍尔逻辑与程序规约
- [Type Semantics](../00_type_theory/06_type_semantics.md) — 类型作为语义分类
- [Equivalence of Computational Models](05_equivalence_of_computational_models.md) — 模型等价与表达力

---

## 四、嵌入式测验（Embedded Quiz）

### 测验 1：四种语义的核心问题（理解层）

哪一种语义主要回答「程序一步一步如何执行」？

- A. 指称语义
- B. 操作语义
- C. 公理语义
- D. 类型语义

<details>
<summary>✅ 答案</summary>

**B. 操作语义**。操作语义用转换规则或抽象机器刻画执行步骤。
</details>

---

### 测验 2：`unsafe` 的最合适语义视角（分析层）

`unsafe` 块最适合用哪种语义框架理解？

- A. 指称语义中的连续函数
- B. 公理语义中的前置/后置条件契约
- C. 类型语义中的泛型约束
- D. 操作语义中的求值上下文

<details>
<summary>✅ 答案</summary>

**B. 公理语义中的前置/后置条件契约**。`unsafe` 块要求程序员保证前置条件，否则行为无定义。
</details>

---

### 测验 3：指称语义的普遍性（评价层）

「所有编程语言都可以直接构造集合论语义」这一说法是否正确？

- A. 正确
- B. 错误，递归构造通常需要域论
- C. 仅对函数式语言错误
- D. 仅对命令式语言错误

<details>
<summary>✅ 答案</summary>

**B. 错误，递归构造通常需要域论**。无类型 λ 演算等语言需要 Scott 域和连续函数才能避免自引用悖论。
</details>

---

## 五、权威来源 / International Authority References

| 来源 | 可信度 | 说明 |
|:---|:---:|:---|
| [Turing 1936 — On computable numbers, with an application to the Entscheidungsproblem](https://doi.org/10.1112/plms/s2-42.1.230) | ✅ 一级 | 图灵机奠基；停机问题原始证明 |
| [Church 1936 — An Unsolvable Problem of Elementary Number Theory](https://doi.org/10.2307/1968981) | ✅ 一级 | λ 可定义函数；Church-Turing 论题 |
| [Rice 1953 — Classes of Recursively Enumerable Sets and Their Decision Problems](https://doi.org/10.1090/S0002-9904-1953-09692-2) | ✅ 一级 | 语义性质不可判定性（Rice 定理） |
| [Felleisen 1991 — On the Expressive Power of Programming Languages](https://doi.org/10.1007/BF00119888) | ✅ 一级 | 表达力比较框架；局部 vs 全局变换 |
| [Felleisen & Flatt 1998 — Programming Languages and Their Calculi](https://www2.ccs.neu.edu/racket/pubs/scp91-felleisen.pdf) | ✅ 一级 | 表达力与演算扩展 |
| [Sipser 2013 — Introduction to the Theory of Computation, 3rd ed.](https://math.mit.edu/~sipser/book.html) | ✅ 一级 | 可计算性、形式语言与复杂度理论标准教材 |
| [Soare 2016 — Turing Computability. Theory and Applications](https://doi.org/10.1007/978-3-642-31933-4) | ✅ 一级 | 现代可计算性理论；算术层级 |
| [Cutland 1980 — Computability: An Introduction to Recursive Function Theory](https://doi.org/10.1017/CBO9780511574916) | ✅ 一级 | 递归函数与可计算性入门 |
| [Hopcroft, Motwani & Ullman 2006 — Introduction to Automata Theory, Languages, and Computation, 3rd ed.](https://en.wikipedia.org/wiki/Introduction_to_Automata_Theory,_Languages,_and_Computation) | ✅ 一级 | 自动机与形式语言经典教材 |
| [Kozen 1997 — Automata and Computability](https://doi.org/10.1007/978-1-4612-1844-9) | ✅ 一级 | 自动机、可计算性与复杂度理论 |
| [Appel 2004 — Modern Compiler Implementation in Java/C/ML, 2nd ed.](https://www.cs.princeton.edu/~appel/modern/) | ✅ 一级 | 编译器实现与语义后端（Tiger Book） |
| [Barendregt 1984 — The Lambda Calculus: Its Syntax and Semantics](https://doi.org/10.1016/B978-0-444-87508-2.50006-X) | ✅ 一级 | λ 演算标准参考书 |
| [Scott 1972 — Continuous Lattices](https://doi.org/10.1007/BFb0073967) | ✅ 一级 | 连续格与 Scott 域奠基 |
| [Scott 1976 — Data types as lattices](https://doi.org/10.1137/0205037) | ✅ 一级 | 数据类型作为格；Scott 域与指称语义 |
| [Scott & Strachey 1971/2000 — Toward a Mathematical Semantics for Computer Languages](https://www.cs.ox.ac.uk/files/3232/PRG06.pdf) | ✅ 一级 | 指称语义奠基文献（PRG-6） |
| [Strachey 1973 — The Varieties of Programming Language](https://doi.org/10.1016/S0065-2458(08)60314-4) | ✅ 一级 | 程序语言语义分类 |
| [Wadler 2015 — Propositions as Types](https://doi.org/10.1145/2699407) | ✅ 一级 | Curry-Howard 对应现代综述 |
| [Ord 2006 — The Many Forms of Hypercomputation](https://doi.org/10.1016/j.apal.2005.09.012) | ✅ 一级 | 超计算与 Church-Turing 边界讨论 |
| [Plotkin 1981 — A Structural Approach to Operational Semantics](https://homepages.inf.ed.ac.uk/gdp/publications/sos_jlap.pdf) | ✅ 一级 | 结构化操作语义奠基 |
| [Winskel 1993 — The Formal Semantics of Programming Languages](https://www.cs.cmu.edu/~crary/819-f09/Winskel.pdf) | ✅ 一级 | 形式语义教材（CMU 课程 PDF） |
| [Pierce 2002 — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/) | ✅ 一级 | 类型与编程语言（TAPL 主页） |
| [Rust Reference — Unsafe blocks](https://doc.rust-lang.org/reference/unsafe-keyword.html#unsafe-blocks) | ✅ P0 | Rust unsafe 块语义 |

---

## 六、🧭 思维导图（Mindmap）

```mermaid
mindmap
  root((计算语义统一框架))
    操作语义
      如何执行
      小步/大步规则
    指称语义
      表示什么
      域论
      连续函数
    公理语义
      为什么正确
      霍尔逻辑
      unsafe 契约
    类型语义
      哪些值可用
      类型判断
    关系
      充分性
      完全抽象
      声音性/完备性
    Church-Turing 论题
      图灵机
      λ 演算
      部分递归函数
    Rust const 求值
      受约束的可计算性
      E0015 边界
```
