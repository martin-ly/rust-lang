> **内容分级**: [专家级]

# Axiomatic Semantics（公理语义）
>
> **EN**: Axiomatic Semantics
> **Summary**: Axiomatic Semantics. Guide to 20 Axiomatic Semantics.
> **受众**: [研究者]
> ⚠️ **声明**: 本文件使用形式化符号辅助直觉理解，所呈现的"定理/引理/推论"为**教学类比**，非经机器验证的严格数学证明。如需严格形式化验证，请参考 [Verus](https://github.com/verus-lang/verus)、[Kani](https://model-checking.github.io/kani/)、[Coq](https://coq.inria.fr/)。
>
> **层次定位**: L4 形式化理论 / 公理语义子域 [来源: [Winskel 1993 — The Formal Semantics of Programming Languages](https://mitpress.mit.edu/9780262731034)]
> **A/S/P 标记**: **S+P** — Structure + Procedure
> **双维定位**: C×Eva — 评价形式化规约的完备性
> **前置依赖**: [Type Theory](../00_type_theory/02_type_theory.md) · [Ownership Formalization](../01_ownership_logic/03_ownership_formal.md) · [Operational Semantics](17_operational_semantics.md) · [Unsafe Rust](../../03_advanced/02_unsafe/03_unsafe.md)
> **后置延伸**: [RustBelt](../02_separation_logic/04_rustbelt.md) · [Separation Logic](../02_separation_logic/11_separation_logic.md) · [Verification Toolchain](../04_model_checking/05_verification_toolchain.md)
> **跨层映射**: L4→L1 公理规约 ↔ 工程直觉 | L4→L3 Unsafe 边界 ↔ 公理失效区域
> **定理链编号**: T-120 霍尔三元组可判定性 → T-121 wp 计算完备性 → T-122 所有权（Ownership）不变式可验证性
> **后置概念**: [Comparative Studies](../../05_comparative/01_systems_languages/01_rust_vs_cpp.md)
> **来源**: [Rust Reference](https://doc.rust-lang.org/reference/introduction.html) · [RustBelt](https://plv.mpi-sws.org/rustbelt/) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)

## 📑 目录

- [Axiomatic Semantics（公理语义）](#axiomatic-semantics公理语义)
  - [📑 目录](#-目录)
  - [一、权威定义（Definition）](#一权威定义definition)
    - [1.1 Hoare 逻辑与霍尔三元组](#11-hoare-逻辑与霍尔三元组)
    - [1.2 最弱前置条件（Weakest Precondition）](#12-最弱前置条件weakest-precondition)
    - [1.3 最强后置条件（Strongest Postcondition）](#13-最强后置条件strongest-postcondition)
    - [1.4 三种语义谱系：操作 · 指称 · 公理](#14-三种语义谱系操作--指称--公理)
  - [二、概念属性矩阵](#二概念属性矩阵)
    - [2.1 公理语义方法对比矩阵](#21-公理语义方法对比矩阵)
  - [三、技术细节](#三技术细节)
    - [3.1 Rust 赋值规则的公理化](#31-rust-赋值规则的公理化)
    - [3.2 所有权转移的 wp 计算](#32-所有权转移的-wp-计算)
    - [3.3 借用规则的不变式](#33-借用规则的不变式)
    - [3.4 unsafe 块的公理边界](#34-unsafe-块的公理边界)
  - [四、工具链映射](#四工具链映射)
    - [4.1 Prusti：Viper 后端的契约推导](#41-prustiviper-后端的契约推导)
    - [4.2 Creusot：Why3 逻辑下的 WP 计算](#42-creusotwhy3-逻辑下的-wp-计算)
    - [4.3 Kani：符号执行与断言验证](#43-kani符号执行与断言验证)
  - [五、反命题与边界分析](#五反命题与边界分析)
    - [5.1 反命题树](#51-反命题树)
    - [5.2 边界极限](#52-边界极限)
  - [六、在 Rust 语义谱系中的位置](#六在-rust-语义谱系中的位置)
  - [十、边界测试](#十边界测试)
    - [10.1 边界测试：wp 计算的无限 descending chain（逻辑错误）](#101-边界测试wp-计算的无限-descending-chain逻辑错误)
    - [10.2 边界测试：借用不变式违反的验证失败（验证错误）](#102-边界测试借用不变式违反的验证失败验证错误)
    - [10.3 边界测试：unsafe 块的公理逃逸（运行时 UB）](#103-边界测试unsafe-块的公理逃逸运行时-ub)
  - [嵌入式测验（Embedded Quiz）](#嵌入式测验embedded-quiz)
    - [测验 1：Hoare 三元组 `{P} C {Q}` 中，P、C、Q 分别代表什么？（理解层）](#测验-1hoare-三元组-p-c-q-中pcq-分别代表什么理解层)
    - [测验 2：什么是"最弱前置条件"（Weakest Precondition, wp）？它在程序验证中的作用是什么？（理解层）](#测验-2什么是最弱前置条件weakest-precondition-wp它在程序验证中的作用是什么理解层)
    - [测验 3：Rust 的 `unsafe` 块为什么特别需要形式化验证？（理解层）](#测验-3rust-的-unsafe-块为什么特别需要形式化验证理解层)
    - [测验 4：分离逻辑（Separation Logic）的"框架规则"（Frame Rule）为什么对 Rust 所有权建模特别重要？（理解层）](#测验-4分离逻辑separation-logic的框架规则frame-rule为什么对-rust-所有权建模特别重要理解层)
    - [测验 5：Creusot 和 Prusti 在验证 Rust 程序时分别依赖什么后端？（理解层）](#测验-5creusot-和-prusti-在验证-rust-程序时分别依赖什么后端理解层)
  - [零、认知路径（Cognitive Path）](#零认知路径cognitive-path)
    - [路径总览](#路径总览)
    - [Step 1: 为什么需要公理语义？](#step-1-为什么需要公理语义)
    - [Step 2: wp 和 sp 怎么计算？](#step-2-wp-和-sp-怎么计算)
    - [Step 3: Rust 的所有权怎么公理化？](#step-3-rust-的所有权怎么公理化)
    - [Step 4: 工具怎么自动验证？](#step-4-工具怎么自动验证)
    - [Step 5: 公理语义的边界在哪里？](#step-5-公理语义的边界在哪里)
  - [六、定理推理链](#六定理推理链)
    - [6.1 定理一致性矩阵](#61-定理一致性矩阵)
    - [6.2 反命题决策树](#62-反命题决策树)
  - [七、工具链深度对比矩阵](#七工具链深度对比矩阵)
    - [7.1 Prusti vs Creusot vs Kani](#71-prusti-vs-creusot-vs-kani)
  - [八、更多边界测试](#八更多边界测试)
    - [10.4 边界测试：Prusti 对泛型 Trait 的验证失败](#104-边界测试prusti-对泛型-trait-的验证失败)
    - [10.5 边界测试：Kani 的路径爆炸与有界验证](#105-边界测试kani-的路径爆炸与有界验证)
    - [10.6 边界测试：Creusot 的 Ghost 代码与零成本抽象](#106-边界测试creusot-的-ghost-代码与零成本抽象)
  - [相关概念文件](#相关概念文件)
    - [补充定理链](#补充定理链)

## 一、权威定义（Definition）
>

### 1.1 Hoare 逻辑与霍尔三元组
>
> **[Hoare 1969 — An Axiomatic Basis for Computer Programming](https://doi.org/10.1145/363235.363259)** Tony Hoare 提出的公理语义框架通过**霍尔三元组**（Hoare Triple）形式化程序的正确性：
>
> $$\{P\}\ C\ \{Q\}$$
>
> 含义：若程序状态满足前置条件 \(P\)，执行命令 \(C\) 后，状态满足后置条件 \(Q\)。霍尔逻辑不关注程序**如何**执行（操作语义），而是关注程序**满足什么规约**（公理）。

Hoare 逻辑的核心公理包括：

| 公理 | 规则 | Rust 对应 |
|:---|:---|:---|
| **赋值公理** | \(\{Q[x/e]\}\ x := e\ \{Q\}\) | `let x = e;` 的最弱前置条件 |
| **顺序组合** | \(\frac{\{P\}C_1\{R\},\ \{R\}C_2\{Q\}}{\{P\}C_1;C_2\{Q\}}\) | 语句块 `{ stmt1; stmt2; }` |
| **条件规则** | \(\frac{\{P \land B\}C_1\{Q\},\ \{P \land \neg B\}C_2\{Q\}}{\{P\}\text{if }B\text{ then }C_1\text{ else }C_2\{Q\}}\) | `if` / `match` 表达式 |
| **循环规则** | \(\frac{\{I \land B\}C\{I\}}{\{I\}\text{while }B\text{ do }C\{I \land \neg B\}}\) | `while` / `loop`（需循环不变式） |

> **关键洞察**: Hoare 逻辑的**赋值公理**假设变量是无别名的（aliasing-free）。在 Rust 中，这一假设由**所有权（Ownership）系统**在编译期保证——`&mut T` 的独占性确保了赋值操作的公理化不会受到别名干扰。这与 C/C++ 形成鲜明对比：C 中任意指针可能别名同一内存，导致赋值公理失效，需要更复杂的分离逻辑来恢复。来源: [Hoare 1969] · 来源: [Separation Logic — Reynolds 2002]

### 1.2 最弱前置条件（Weakest Precondition）
>
> **[Dijkstra 1975 — Guarded Commands, Nondeterminacy and Formal Derivation of Programs](https://doi.org/10.1145/360933.360975)** Dijkstra 扩展了 Hoare 逻辑，引入**最弱前置条件**（Weakest Precondition, wp）作为从程序规约反向推导实现的形式化方法：
>
> $$\text{wp}(C, Q) = \text{最弱的前置条件 } P \text{，使得 } \{P\}C\{Q\} \text{ 成立}$$

Dijkstra 的 wp 计算规则（谓词转换器语义）：

```text
wp(skip, Q)           = Q
wp(x := e, Q)         = Q[x/e]          （文本替换）
wp(C1; C2, Q)         = wp(C1, wp(C2, Q))
wp(if B then C1 else C2, Q) = (B → wp(C1, Q)) ∧ (¬B → wp(C2, Q))
wp(while B do C, Q)   = ∃k. H_k(Q)      （极限构造，H_0 = false, H_{k+1} = (¬B → Q) ∧ (B → wp(C, H_k))）
```

> **认知桥梁**: wp 计算是**程序合成的数学基础**——给定后置条件 \(Q\)，通过反向应用 wp 规则，可以机械地推导出实现 \(Q\) 的程序。Creusot 工具正是基于这一原理，从 Why3 逻辑规约自动生成 Rust 代码的验证条件。[来源: [Dijkstra 1975](https://doi.org/10.1145/360933.360975)] · [来源: [Creusot Documentation](https://creusot.rs/))]

### 1.3 最强后置条件（Strongest Postcondition）
>
> **[Winskel 1993 — The Formal Semantics of Programming Languages, §7](https://mitpress.mit.edu/9780262731034)** 与 wp 对偶的概念是**最强后置条件**（Strongest Postcondition, sp）：
>
> $$\text{sp}(P, C) = \text{最强的后置条件 } Q \text{，使得 } \{P\}C\{Q\} \text{ 成立}$$

sp 在**程序分析**和**抽象解释**中更为常用——给定前置条件 \(P\)，计算程序执行后必然成立的所有性质。Prusti 的抽象解释引擎使用 sp 的变体来推断循环不变式。

wp 与 sp 的对偶关系：

```text
P → wp(C, Q)    ⟺    sp(P, C) → Q
```

> **直觉**: wp 是"向后看"（从目标推导起点），sp 是"向前看"（从起点推导目标）。在 Rust 验证中，**Kani 使用符号执行（sp 方向）** 从初始状态探索所有可达状态；**Creusot 使用 wp 计算** 从断言反向推导验证条件。两种方向各有优劣：wp 适合验证给定规约，sp 适合发现未预期的程序行为。[来源: [Winskel 1993, §7](https://mitpress.mit.edu/9780262731034)]

### 1.4 三种语义谱系：操作 · 指称 · 公理
>

| **维度** | **操作语义** | **指称语义** | **公理语义** |
|:---|:---|:---|:---|
| **核心问题** | 程序**如何**执行？ | 程序**表示什么**数学对象？ | 程序**满足什么规约**？ |
| **形式化工具** | 转换规则 / 状态机 | 域论 / CPO / 不动点 | 霍尔三元组 / wp / sp |
| **Rust 对应** | `17_operational_semantics.md` | `12_denotational_semantics.md` | **本文件** |
| **验证方法** | 模型检测 / 迹分析 | 不动点计算 / 抽象解释 | 定理证明 / SMT 求解 |
| **表达能力** | 强（可描述非终止、并发交织） | 强（可描述无限行为） | 弱（需循环不变式辅助） |
| **主要局限** | 状态空间爆炸 | 复杂数学基础 | 无法直接处理别名、并发 |
| **互补关系** | 提供执行迹的精确定义 | 提供类型安全的不动点证明 | 提供工程可验证的规约框架 |

> **形式化谱系图**:
>
> ```text
>                    程序行为的数学描述
>                           │
>           ┌───────────────┼───────────────┐
>           ▼               ▼               ▼
>      操作语义          指称语义          公理语义
>      (How?)           (What?)          (Spec?)
>           │               │               │
>           ▼               ▼               ▼
>      小步/大步          CPO/不动点       Hoare/wp/sp
>      SOS/ CESK          Scott-Strachey   Dijkstra/Gries
>           │               │               │
>           └───────────────┴───────────────┘
>                           │
>                    Rust 形式化验证
>                    (RustBelt + Prusti/Creusot/Kani)
> ```

三种语义在 Rust 形式化中的协同：

1. **操作语义**定义 Rust 的执行模型（Stacked Borrows / Tree Borrows 的内存模型）
2. **指称语义**证明类型系统（Type System）的 soundness（Progress + Preservation 定理）
3. **公理语义**为工程师提供可验证的规约语言（Prusti 的 `#[requires]/#[ensures]` 契约）

> **来源**: [Winskel 1993 — Formal Semantics](https://mitpress.mit.edu/9780262731034) · [Pierce 2002 — TAPL](https://www.cis.upenn.edu/~bcpierce/tapl/) · [Plotkin 1981 — A Structural Approach to Operational Semantics](https://homepages.inf.ed.ac.uk/gdp/publications/sos_jlap.pdf)
> **前置概念**: N/A
---

## 二、概念属性矩阵

### 2.1 公理语义方法对比矩阵
>

| **方法** | **规约语言** | **自动化程度** | **Rust 工具** | **适用场景** | **主要局限** |
|:---|:---|:---:|:---|:---|:---|
| **Hoare 逻辑** | `{P} C {Q}` | 低（手动推导）| 无直接工具 | 教学/理论分析 | 需循环不变式，无别名支持 |
| **最弱前置条件** | `wp(C, Q)` | 中（自动计算）| Creusot | 逆向规约推导 | 无限 descending chain 不保证终止 |
| **分离逻辑** | `P * Q`（资源分离）| 中（交互式证明）| RustBelt (Iris) | 别名/并发推理 | 证明复杂度高，需专家 |
| **抽象解释** | 抽象域 +  widening | 高（全自动）| Miri（部分）、Prusti | 数值/数组边界检查 | 假阳性/假阴性，精度受限 |
| **符号执行** | 路径条件 + SMT | 高（路径爆炸）| Kani | 断言验证/反例生成 | 路径空间指数级增长 |
| **类型系统（Type System）即规约** | 类型签名 | 全自动 | Rust 编译器本身 | 内存安全（Memory Safety）/数据竞争 | 无法表达功能性规约 |

> **洞察**:
>
> Rust 编译器的**借用（Borrowing）检查器**本质上是一个轻量级的、全自动的公理验证器——它通过类型推导自动计算所有权和生命周期（Lifetimes）的不变式，无需程序员手动书写 `{P} C {Q}`。
> 这是 Hoare 逻辑从学术研究走向工业实践的最成功范例：将公理规约"编译进"类型系统（Type System），使验证成为零成本抽象（Zero-Cost Abstraction）。
> [来源: [RustBelt Paper](https://doi.org/10.1145/3158154)] ·
> [来源: [Rust Reference — Ownership](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html)]

---

## 三、技术细节

### 3.1 Rust 赋值规则的公理化
>

在标准 Hoare 逻辑中，赋值公理是：

$$\{Q[x/e]\}\ x := e\ \{Q\}$$

Rust 的赋值操作 `x = e;` 需要额外考虑：

1. **所有权转移**：若 `e` 是拥有所有权的值，赋值后原变量失效
2. **借用（Borrowing）检查**：若 `x` 当前被借用（`&x` 或 `&mut x` 活跃），赋值被禁止
3. **Drop 语义**：旧值在赋值前自动调用 `drop`

Rust 赋值的扩展霍尔三元组：

```text
{ owns(Σ, x, T) ∧ moved(Σ, e) ∧ no_borrows_active(x) }
    x = e;
{ owns(Σ', x, T) ∧ ¬alive(Σ', source(e)) ∧ dropped(Σ, old(x)) }
```

其中：

- `owns(Σ, x, T)`：状态 Σ 中变量 `x` 拥有类型 `T` 的值
- `moved(Σ, e)`：表达式 `e` 是可移动的所有权值
- `no_borrows_active(x)`：`x` 没有活跃的借用（Borrowing）
- `dropped(Σ, old(x))`：旧值已被正确释放

```rust
// 正确示例：所有权转移的公理化
let s1 = String::from("hello");  // { owns(Σ, s1, String) }
let s2 = s1;                      // { moved(Σ, s1) ∧ no_borrows_active(s2) }
                                  // { owns(Σ', s2, String) ∧ ¬alive(Σ', s1) }
// println!("{}", s1);           // ❌ 编译错误: s1 已失效
```

> **形式化洞察**: Rust 的赋值公理比标准 Hoare 逻辑更复杂，因为它不仅是**状态更新**（`Q[x/e]`），还是**资源转移**——`s1` 的所有权被"消耗"并转移到 `s2`。这与分离逻辑中的**框架规则**（Frame Rule）天然契合：赋值操作只影响局部资源，不变的部分自动保持。[来源: [Separation Logic — Reynolds 2002](https://www.cs.cmu.edu/~jcr/seplogic.pdf)] · [来源: [RustBelt — Jung et al. 2018](https://plv.mpi-sws.org/rustbelt/popl18/)]

### 3.2 所有权转移的 wp 计算
>

对于所有权转移 `x = e`，wp 计算需要考虑**资源消耗**：

```text
wp(x = e, Q) = own(e) * (Q[x/e] ⊗ ¬alive(e))
```

其中 `own(e)` 表示 `e` 是可移动的所有权值，`*` 是分离合取，`⊗` 表示"消耗后"。

**示例：所有权转移的 wp 推导**

```rust
// 后置条件 Q: s2 拥有字符串 "hello" 且 s1 已失效
let s1 = String::from("hello");
let s2 = s1;
// Q: owns(s2, String::from("hello")) ∧ ¬alive(s1)

// wp 计算:
// wp(let s2 = s1, Q) = wp(s1 的初始化, wp(let s2 = s1, Q))
//                    = own(s1) * Q[s2/s1][¬alive(s1)]
//                    = own(s1) * owns(s2, String::from("hello")) * ¬alive(s1)
// 但 s1 在赋值后失效，所以 Q 中不能有 alive(s1)
```

更精确的 Rust wp 规则（基于 RustBelt 的 Iris 规约）：

```text
wp(let x = e, Q) =
    match e 的类型:
        Copy 类型 (i32, bool, ...):
            Q[x/e]                    // 标准 Hoare 赋值公理
        Move 类型 (String, Vec, ...):
            own(e) → Q[x/e] ⊗ ¬alive(e)   // 消耗 e 的所有权
        Borrow (&T / &mut T):
            borrow(e, κ) → Q[x/e]     // 引入借用令牌 κ
```

> **关键区别**: `Copy` 类型的 wp 就是标准 Hoare 赋值公理；`Move` 类型的 wp 引入了**资源消耗**，这是 Rust 所有权系统对公理语义的独特贡献。RustBelt 通过**Iris 幽灵状态**（ghost state）形式化地追踪这些资源令牌，使得 wp 计算可以精确建模所有权转移。[来源: [RustBelt — Jung et al. 2018](https://plv.mpi-sws.org/rustbelt/popl18/)] · [来源: [Iris Project](https://iris-project.org/)]

### 3.3 借用规则的不变式
>

Rust 借用规则的核心不变式可以通过公理语义表达：

**不变式 1：共享借用的只读性**

```text
∀x. (alive(&x) → ¬mutated(x)) ∧ (count(&x) ≥ 0)
```

含义：若存在任何共享借用 `&x` 活跃，则 `x` 不可被修改。

**不变式 2：独占借用的排他性**

```text
∀x. (alive(&mut x) → (count(&mut x) = 1 ∧ ¬alive(&x)))
```

含义：若存在独占借用 `&mut x` 活跃，则不存在任何其他借用（共享或独占）。

**不变式 3：生命周期（Lifetimes）包含性**

```text
∀'a, 'b. ('a : 'b) → (lifetime(&'a x) ⊆ lifetime(&'b x))
```

含义：较长生命周期（Lifetimes） `'a` 的借用可以安全地降级为较短生命周期 `'b` 的借用。

```rust
// 边界测试：不变式验证
fn check_invariants() {
    let mut x = 5;

    let r1 = &x;      // 不变式1: count(&x) = 1, alive(r1)
    let r2 = &x;      // 不变式1: count(&x) = 2, alive(r1), alive(r2)
    // x = 6;         // ❌ 编译错误: 违反不变式1（共享借用存在时修改 x）
    println!("{} {}", r1, r2);

    let r3 = &mut x;  // ✅ 合法: r1, r2 生命周期已结束
                      // 不变式2: count(&mut x) = 1, ¬alive(&x)
    // let r4 = &x;   // ❌ 编译错误: 违反不变式2（独占借用存在时创建共享借用）
    *r3 = 6;
}
```

> **形式化表达**: 借用检查器通过**区域约束系统**（Region Constraint System）在编译期验证这三个不变式。NLL（Non-Lexical Lifetimes）将生命周期从词法作用域精确到**使用点**（use-site），使得不变式的验证更加精确。Polonius 进一步将区域约束转化为 Datalog 规则，实现 borrow check 的声明式表达。[来源: [Rust [RFC 2094](https://rust-lang.github.io/rfcs//2094-nll.html) — NLL](https://rust-lang.github.io/rfcs//2094-nll.html)] · [来源: [Polonius — rust-lang/polonius](https://github.com/rust-lang/polonius)] · [来源: [Rust Reference — Lifetimes](https://doc.rust-lang.org/reference/items/generics.html)]

### 3.4 unsafe 块的公理边界
>

Rust 的 `unsafe` 块是公理语义的**信任边界**（Trust Boundary）——在 `unsafe` 内部，编译器不再保证借用规则、别名规则和内存安全（Memory Safety）。公理语义需要明确标注这一边界：

```text
{ P }
unsafe {            // 公理边界开始: 编译器信任程序员维护不变式
    // 程序员责任: 手动保证所有不变式在 unsafe 块内外保持
    // - 不创建悬垂指针
    // - 不违反 &mut T 的独占性
    // - 不跨线程共享非 Send/Sync 类型
}
{ Q }               // 公理边界结束: 编译器恢复自动验证
```

`unsafe` 块的公理化挑战：

1. **裸指针别名**：`*const T` 和 `*mut T` 可以同时指向同一地址，违反标准 Hoare 逻辑的别名自由假设
2. **类型转换**：`mem::transmute` 可以任意重解释内存，wp 计算无法预测结果
3. **并发原语**：`std::sync::atomic` 操作需要额外的 happens-before 关系公理化

```rust,ignore
// 正确示例: unsafe 块的公理规约
/// # Safety
/// - `ptr` 必须指向有效的、已分配的 `T`
/// - `ptr` 必须对齐到 `T` 的对齐要求
/// - `ptr` 必须独占（没有活跃的引用）
unsafe fn dereference_raw<T>(ptr: *const T) -> T {
    *ptr  // 公理假设: 程序员已验证三个 safety 条件
}

// wp 计算在 unsafe 边界处"暂停":
// wp(unsafe { *ptr }, Q) = unsafe_assumptions(ptr) → Q
// 其中 unsafe_assumptions(ptr) 是程序员手动保证的前置条件
```

> **关键洞察**: `unsafe` 块不是"无规则"的区域，而是**公理由程序员手动提供**的区域。Rust 的 `// SAFETY:` 注释文化正是公理语义在工程实践中的体现——程序员在 unsafe 块前显式声明所需的前置条件，这些条件构成了人工的霍尔三元组。然而，当前工具链（Prusti/Creusot/Kani）对 `unsafe` 的支持仍然有限，这是 Rust 形式化验证的最大缺口之一。[来源: [Rustonomicon — Unsafe Rust](https://doc.rust-lang.org/nomicon/index.html)] · [来源: [RustBelt — Unsafe Code Guidelines](https://rust-lang.github.io/unsafe-code-guidelines/)]

---

## 四、工具链映射

### 4.1 Prusti：Viper 后端的契约推导
>
> **Prusti — Viper-based Verification Tool** Prusti 是 ETH Zurich 开发的 Rust 验证工具，基于 Viper 验证基础设施。它将 Rust 程序翻译为 Viper 中间语言，利用分离逻辑自动验证内存安全（Memory Safety）和用户提供的函数契约。

Prusti 的核心公理语义能力：

| 能力 | 公理语义对应 | 示例 |
|:---|:---|:---|
| `#[requires(P)]` | 前置条件 | `#[requires(x > 0)]` |
| `#[ensures(Q)]` | 后置条件 | `#[ensures(result > x)]` |
| `#[pure]` | 无副作用（Referential Transparency）| 纯函数可自由重写 |
| `#[trusted]` | 手动公理（类似 `unsafe`）| 外部函数的契约由程序员提供 |
| 自动不变式推断 | sp 计算 + 抽象解释 | 循环不变式自动生成 |

```rust
use prusti_contracts::*;

#[requires(x > 0)]
#[ensures(result > x)]
fn increment_positive(x: i32) -> i32 {
    x + 1
}

// Prusti 自动验证:
// { x > 0 } increment_positive(x) { result > x }
// wp(increment_positive, result > x) = (x + 1 > x) = true (given x > 0)
```

> **局限**: Prusti 目前不支持 `unsafe` 块、并发、`dyn Trait` 和复杂的生命周期（Lifetimes）泛型（Generics）。其验证范围本质上是"安全的 Rust 子集"——这正是公理语义在工业工具中的典型边界。[来源: [Prusti Documentation](https://www.pm.inf.ethz.ch/research/prusti.html)] · [来源: [Viper Project](https://www.pm.inf.ethz.ch/research/viper.html)]

### 4.2 Creusot：Why3 逻辑下的 WP 计算
>
> **[Creusot — Deductive Verification for Rust](https://creusot.rs/)** Creusot 是 Inria 开发的 Rust 验证工具，基于 Why3 平台和 Dijkstra 的 wp 计算。与 Prusti 不同，Creusot 显式使用**最弱前置条件**作为验证的核心机制。

Creusot 的公理语义特色：

1. **PEARLite 规约语言**：Rust 语法的规约方言，降低学习成本
2. **模块（Module）化验证**：利用 Rust 的模块边界进行分层的 wp 计算
3. **Ghost 代码**：允许在规约中编写不编译到目标的纯逻辑代码

```rust
use creusot_contracts::*;

#[requires(x @ > 0)]
#[ensures(result @ > x @)]
pub fn increment(x: i32) -> i32 {
    x + 1
}

// Creusot 的 wp 推导:
// wp(x + 1, result > x)
//   = wp(x + 1, result > x)[result/(x+1)]
//   = (x + 1 > x)
//   = true
// 结合前置条件 x > 0，验证通过。
```

> **与 RustBelt 的关系**: Creusot 验证的是**功能性正确性**（函数输出满足规约），而 RustBelt 验证的是**内存安全（Memory Safety）性**（无悬垂指针、无数据竞争）。两者互补：Creusot 的 wp 计算假设底层内存安全已由 Rust 编译器保证，RustBelt 的形式化证明为这一假设提供了数学基础。[来源: [Creusot Documentation](https://creusot.rs/)] · [来源: [Why3 Platform](https://why3.lri.fr/)]

### 4.3 Kani：符号执行与断言验证
>
> **[Kani — Rust Verification Tool by AWS](https://github.com/model-checking/kani)** Kani 是 AWS 开发的 Rust 符号执行工具，基于 CBMC（C Bounded Model Checker）。与 Prusti/Creusot 的 wp 方向不同，Kani 采用**符号执行**（sp 方向）：从初始状态出发，探索所有可能的执行路径。

Kani 的公理语义特征：

| 特征 | 公理语义表达 | 说明 |
|:---|:---|:---|
| `kani::assert(cond)` | 后置条件断言 | 在路径终点检查条件 |
| `kani::any()` | 全称量化 | 生成任意值的符号变量 |
| `kani::assume(cond)` | 前置条件假设 | 限制探索的状态空间 |
| 路径覆盖 | 穷举所有执行路径 | 通过 SMT 求解器验证 |

```rust
#[kani::proof]
fn check_increment() {
    let x: i32 = kani::any();       // 符号变量: ∀x ∈ i32
    kani::assume(x > 0);            // 前置条件: { x > 0 }
    let result = increment(x);       // 执行路径
    kani::assert(result > x);       // 后置条件: { result > x }
}

// Kani 的符号执行 (sp 方向):
// sp(x > 0, let result = increment(x))
//   = sp(true, result = x + 1)[x > 0]
//   = (result = x + 1 ∧ x > 0)
//   → (result > x) ✓
```

> **局限与优势**: Kani 的优势是**全自动**（无需手动写循环不变式），局限是**路径爆炸**（复杂程序的状态空间过大）。它更适合验证小规模的核心抽象（如标准库原语），而非大型应用程序。这与公理语义的理论边界一致：全自动验证（无不变式辅助）仅在有限状态空间下可判定。[来源: [Kani Documentation](https://model-checking.github.io/kani/)] · [来源: [CBMC — C Bounded Model Checker](https://github.com/diffblue/cbmc)]

---

## 五、反命题与边界分析

### 5.1 反命题树
>

```text
反命题 1: "公理语义可以完全替代 Rust 编译器的借用检查"
├── 前提: wp 计算可以自动推导所有权不变式
├── 反驳: 借用检查涉及**高阶约束**（生命周期参数、泛型 Trait 边界），
│         这些约束的 wp 计算在一般情况下是不可判定的
└── 结论: ❌ 公理语义是借用检查的**补充**而非替代

反命题 2: "Prusti/Creusot/Kani 可以验证所有 Rust 程序"
├── 前提: 工具链覆盖了 Rust 的全部语法和语义
├── 反驳:
│   ├── Prusti: 不支持 `unsafe`、并发、`dyn Trait`
│   ├── Creusot: 不支持异步、裸指针、部分标准库
│   └── Kani: 路径爆炸限制规模，不支持无限循环
└── 结论: ❌ 当前工具链仅覆盖 Rust 的**安全子集 + 有限规模**

反命题 3: "unsafe 块可以用标准 Hoare 逻辑验证"
├── 前提: `unsafe` 块内的代码仍满足 Hoare 三元组
├── 反驳: `unsafe` 块允许**裸指针别名**和**类型重解释**，
│         标准 Hoare 逻辑的赋值公理在别名存在时失效
│         需要**分离逻辑**（Separation Logic）来恢复正确性
└── 结论: ⚠️ 标准 Hoare 逻辑不足，需分离逻辑或 RustBelt 的 Iris 扩展
```

> **来源**: [RustBelt — Jung et al. 2018](https://plv.mpi-sws.org/rustbelt/popl18/) · [Prusti Limitations](https://www.pm.inf.ethz.ch/research/prusti.html) · [Creusot Limitations](https://creusot.rs/)

### 5.2 边界极限
>

| **边界** | **现状** | **理论极限** | **工程意义** |
|:---|:---|:---|:---|
| **循环不变式自动推断** | Prusti 使用抽象解释推断简单不变式 | Rice 定理：完全自动推断不可判定 | 复杂循环仍需人工标注 |
| **并发程序验证** | RustBelt (Iris) 支持，但证明复杂 | 并发程序的霍尔逻辑需要**并发分离逻辑**（CSL）| 工业工具尚不成熟 |
| **unsafe 代码验证** | 无直接工具支持 | 需程序员手动提供公理 | Rust 形式化的最大缺口 |
| **标准库验证** | Kani 验证部分原语 | 标准库规模巨大，全覆盖不现实 | 聚焦安全关键路径 |
| **Trait 对象验证** | 无工具支持 | `dyn Trait` 的 vtable 调度增加 wp 复杂度 | 面向对象形式的 Rust 验证空白 |

> **前沿方向**:
>
> 1. **A-mir-formality**: Rust 编译器团队正在开发的 MIR 层形式化规格，旨在为公理语义提供**编译器可信的基础**
> 2. **rustc 规格项目**: 将 Rust 语义写入机器可读的规格，使公理工具可以直接引用（Reference）编译器定义的语义
> 3. **Ghost code 标准化**: 在 Rust 中引入官方支持的 ghost/规约代码语法（类似 SPARK 的 `with Ghost`），降低契约编写的门槛
>
> **来源**: [A-mir-formality](https://github.com/rust-lang/a-mir-formality) · [Rust Specification Project](https://rust-lang.github.io/rfcs//3355-rust-spec.html) · [Rust Verification Workshop 2024](https://hacspec.github.io/RustVerify24.pdf)

---

## 六、在 Rust 语义谱系中的位置
>

公理语义在 Rust 知识体系中的角色：

```text
L1 工程直觉          L3 高级抽象           L4 形式化理论          L7 工具实现
    │                    │                      │                      │
    │   "编译器帮我      │   "借用检查是        │   "霍尔三元组        │   "Prusti/
    │    保证了安全"     │    轻量级验证器"     │    形式化了安全"     │     Creusot/
    │                    │                      │                      │     Kani"
    └────────────────────┴──────────────────────┴──────────────────────┘
                           L4 公理语义（本文件）
                           ├──→ 提供规约语言（Hoare/wp/sp）
                           ├──→ 连接理论（类型系统 soundness）与工具（验证器）
                           └──→ 定义 unsafe 边界的人工公理责任
```

公理语义与 Rust 其他形式化主题的关系：

- **操作语义**（`17_operational_semantics.md`）：公理语义的**可靠性基础**——若公理证明程序满足规约，操作语义保证程序执行确实满足该规约
- **指称语义**（`12_denotational_semantics.md`）：公理语义的**完备性基础**——指称语义证明类型系统（Type System）的 soundness，为公理规约的良定义性提供保证
- **分离逻辑**（`11_separation_logic.md`）：公理语义在**别名/并发**场景下的扩展——标准 Hoare 逻辑在别名存在时失效，分离逻辑通过资源分离恢复正确性
- **RustBelt**（`04_rustbelt.md`）：公理语义的**Rust 实例化**——RustBelt 使用 Iris 高阶分离逻辑形式化 Rust 的所有权语义，本质上是公理语义在系统编程语言中的高级表达

---

## 十、边界测试

### 10.1 边界测试：wp 计算的无限 descending chain（逻辑错误）

```rust,ignore
// 错误示例：循环不变式不足导致 wp 计算不终止
fn bad_loop(n: u32) -> u32 {
    let mut i = 0;
    while i < n {
        i += 1;
    }
    i
}

// Creusot/Prusti 在此会报错：
// "无法自动推断循环不变式"
// 原因：wp(while B do C, Q) = ∃k. H_k(Q)，若循环体 C 不能使状态"收敛"
//       到不动点，则 H_k 序列无限 descending，wp 计算不终止。
//
// 解决：人工提供循环不变式
// #[invariant(i <= n)]
```

> **修正**: wp 计算的终止性依赖于循环不变式的存在。Dijkstra 的 wp 理论证明：若循环不变式存在，则 H_k 序列在有限步内收敛到不动点；若不存在，wp 计算可能不终止。这与 Rust 的借用检查形成对比——借用检查器总是终止的，因为它验证的是**语法可判定的**约束（生命周期（Lifetimes）包含），而非**语义不可判定的**不变式。[来源: [Dijkstra 1975](https://doi.org/10.1145/360933.360975)] · [来源: [Winskel 1993, §7.4](https://mitpress.mit.edu/9780262731034)]

### 10.2 边界测试：借用不变式违反的验证失败（验证错误）

```rust,ignore
use prusti_contracts::*;

#[requires(x > 0)]
#[ensures(result > 0)]
fn borrow_violation(x: &mut i32) -> i32 {
    let r = &*x;        // 共享借用 &i32
    *x = *x + 1;        // ❌ 编译错误: 违反借用不变式1
                        //   (共享借用 r 活跃时修改 x)
    *r
}

// Prusti 在此会提前失败——不是验证失败，而是编译失败。
// 这说明 Rust 编译器的借用检查本身就是公理验证的第一道防线。
// Prusti 只需验证编译通过后的代码的功能性正确性。
```

> **修正**: Rust 编译器的借用检查器可以被视为一个**全自动的、零成本的公理验证器**。它自动推断并验证了借用规则的不变式（3.3 节），无需程序员手动书写 `{P} C {Q}`。这是 Hoare 逻辑从学术走向工业的最成功实践——将公理规约"编译"进类型系统（Type System）。[来源: [Rust Reference — Borrowing](https://doc.rust-lang.org/reference/expressions.html?highlight=borrow#evaluation-order)] · [来源: [RustBelt Paper](https://doi.org/10.1145/3158154)]

### 10.3 边界测试：unsafe 块的公理逃逸（运行时 UB）

```rust,ignore
// 错误示例：unsafe 块中违反公理假设
fn undefined_behavior() {
    let mut x = 5;
    let r1 = &mut x as *mut i32;
    let r2 = &mut x as *mut i32;  // 两个 &mut x 同时存在，但通过裸指针"隐藏"

    unsafe {
        *r1 = 1;
        *r2 = 2;                  // ❌ 运行时 UB: 两个可变裸指针别名同一地址
    }
    println!("{}", x);
}

// 当前工具链（Prusti/Creusot/Kani）对此无能为力：
// - Prusti: 不支持 unsafe
// - Creusot: 不支持裸指针
// - Kani: 可以检测部分 UB，但符号执行在 unsafe 代码中路径爆炸严重
//
// 公理语义视角：unsafe 块是"公理由程序员手动提供"的区域。
// 程序员的 SAFETY 注释构成了人工霍尔三元组，但工具无法自动验证
// 这些人工公理的正确性。
```

> **修正**: `unsafe` 块的验证是 Rust 形式化的**终极边界**。当前最可行的策略是：
>
> 1. **限制 unsafe 范围**：将 unsafe 封装在安全抽象中（Safe Abstraction），使公理边界最小化
> 2. **Miri 动态检测**：使用 Miri 解释器在运行时（Runtime）检测 Stacked Borrows/Tree Borrows 违规
> 3. **RustBelt 手动证明**：对关键 unsafe 代码，使用 Iris 分离逻辑进行交互式证明
> 4. **BorrowSanitizer（实验性）**：Rust 编译器团队正在开发的运行时（Runtime）借用检查器，未来可能自动验证部分 unsafe 模式
>
> **来源**: [Rustonomicon — Undefined Behavior](https://doc.rust-lang.org/nomicon/what-unsafe-does.html) · [Miri — Stacked Borrows](https://github.com/rust-lang/miri) · [RustBelt — Unsafe Code Guidelines](https://rust-lang.github.io/unsafe-code-guidelines/)

---

## 嵌入式测验（Embedded Quiz）

### 测验 1：Hoare 三元组 `{P} C {Q}` 中，P、C、Q 分别代表什么？（理解层）

**题目**: Hoare 三元组 `{P} C {Q}` 中，P、C、Q 分别代表什么？

<details>
<summary>✅ 答案与解析</summary>

`P` 是前置条件（precondition），`C` 是命令/程序片段，`Q` 是后置条件（postcondition）。含义：若执行前 `P` 成立且 `C` 终止，则执行后 `Q` 成立。
</details>

---

### 测验 2：什么是"最弱前置条件"（Weakest Precondition, wp）？它在程序验证中的作用是什么？（理解层）

**题目**: 什么是"最弱前置条件"（Weakest Precondition, wp）？它在程序验证中的作用是什么？

<details>
<summary>✅ 答案与解析</summary>

wp(C, Q) 是使命令 C 执行后 Q 成立的最弱（最一般）前置条件。它是自动验证的核心：给定后置条件 Q，计算所需前置条件，检查实际前置条件是否蕴含它。
</details>

---

### 测验 3：Rust 的 `unsafe` 块为什么特别需要形式化验证？（理解层）

**题目**: Rust 的 `unsafe` 块为什么特别需要形式化验证？

<details>
<summary>✅ 答案与解析</summary>

因为 `unsafe` 块绕过了编译器的安全检查，可能引入悬垂指针、数据竞争、类型混淆等 UB。形式化验证可证明 `unsafe` 代码在特定契约下仍然是内存安全（Memory Safety）的。
</details>

---

### 测验 4：分离逻辑（Separation Logic）的"框架规则"（Frame Rule）为什么对 Rust 所有权建模特别重要？（理解层）

**题目**: 分离逻辑（Separation Logic）的"框架规则"（Frame Rule）为什么对 Rust 所有权建模特别重要？

<details>
<summary>✅ 答案与解析</summary>

框架规则允许验证局部资源时自动忽略不相关的资源。这恰好对应 Rust 的所有权局部性：修改一个所有权不影响其他无关的所有权。
</details>

---

### 测验 5：Creusot 和 Prusti 在验证 Rust 程序时分别依赖什么后端？（理解层）

**题目**: Creusot 和 Prusti 在验证 Rust 程序时分别依赖什么后端？

<details>
<summary>✅ 答案与解析</summary>

Creusot 依赖 Why3 平台和 SMT 求解器（如 Alt-Ergo、Z3）。Prusti 依赖 Viper 验证基础设施，使用其内置的符号执行和权限系统。
</details>

## 零、认知路径（Cognitive Path）
>

### 路径总览

```text
公理语义的 5 步认知路径
    │
    ├──→ Step 1: 为什么需要公理语义？（Hoare 的逻辑革命）
    ├──→ Step 2: wp 和 sp 怎么计算？（Dijkstra 的谓词转换器）
    ├──→ Step 3: Rust 的所有权怎么公理化？（资源感知的 wp）
    ├──→ Step 4: 工具怎么自动验证？（Prusti/Creusot/Kani 原理）
    └──→ Step 5: 公理语义的边界在哪里？（unsafe、并发、无限状态）
```

### Step 1: 为什么需要公理语义？

操作语义告诉我们程序**如何**执行（一步一步的状态转换），指称语义告诉我们程序**表示什么**数学对象（不动点、CPO）。
但它们都无法直接回答：**我怎么知道这个程序是正确的？**

公理语义通过**霍尔三元组** `{P} C {Q}` 将正确性转化为逻辑命题：给定前置条件 `P`，执行命令 `C` 后，后置条件 `Q` 必然成立。
这是从"描述程序"到"规约程序"的范式跃迁。

### Step 2: wp 和 sp 怎么计算？

wp（最弱前置条件）是**反向推导**：从目标 `Q` 出发，计算实现 `Q` 所需的最弱前提。sp（最强后置条件）是**正向推导**：从前提 `P` 出发，计算程序执行后必然成立的所有结论。

两种方向在 Rust 验证中各有用途：Creusot 用 wp 从断言反向推导验证条件；Kani 用 sp（符号执行）从初始状态探索所有可达状态。

### Step 3: Rust 的所有权怎么公理化？

标准 Hoare 逻辑假设变量无别名。Rust 的所有权系统通过编译期检查**在语法层面保证了这一假设**——`&mut T` 的独占性使得赋值公理无需分离逻辑即可成立。

但 `Move` 类型引入了**资源消耗**：`let s2 = s1;` 不仅更新状态，还使 `s1` 失效。这需要用扩展的 wp 规则建模：`wp(x = e, Q) = own(e) → Q[x/e] ⊗ ¬alive(e)`。

### Step 4: 工具怎么自动验证？

Prusti 将 Rust 翻译为 Viper 中间语言，使用分离逻辑自动验证内存安全（Memory Safety）；Creusot 基于 Why3 平台，显式使用 wp 计算推导验证条件；Kani 使用 CBMC 的符号执行引擎，从初始状态穷举路径。

三种工具覆盖的 Rust 子集不同：Prusti 适合安全 Rust 的内存安全（Memory Safety）验证，Creusot 适合功能性规约的 wp 推导，Kani 适合小规模核心抽象的自动反例生成。

### Step 5: 公理语义的边界在哪里？

公理语义有三道"硬边界"：

1. **循环不变式**：Rice 定理证明完全自动推断不可判定
2. **unsafe 块**：允许裸指针别名，标准 Hoare 逻辑失效
3. **并发程序**：需要并发分离逻辑（CSL），工业工具尚不成熟

这些边界不是 Rust 的缺陷，而是**计算理论的根本极限**——任何足够强大的程序验证系统都必然存在不可判定的角落。

---

## 六、定理推理链

### 6.1 定理一致性矩阵
>

| **定理/命题** | **前提** | **结论** | **Rust 体现** | **权威来源** |
|:---|:---|:---|:---|:---|
| **T-120: 霍尔三元组可判定性** | 程序无循环/无递归 | `{P}C{Q}` 可在多项式时间内验证 | `const fn` 的编译期求值 | Hoare 1969 · Cook 1978 |
| **T-121: wp 计算完备性** | 循环不变式存在 | `wp(C, Q)` 可机械计算 | Creusot 的验证条件生成 | Dijkstra 1975 · Winskel 1993 §7 |
| **T-122: 所有权不变式可验证性** | 程序为 safe Rust | 借用规则在编译期自动验证 | Rust 编译器借用检查 | RustBelt 2018 · [RFC 2094](https://rust-lang.github.io/rfcs//2094-nll.html) |
| **T-123: 分离逻辑框架规则** | 命令只访问局部资源 | 未访问资源自动保持 | `&mut T` 的独占性保证 | Reynolds 2002 · Iris |
| **T-124: unsafe 块公理不可判定** | 允许裸指针别名 | 标准 Hoare 逻辑失效 | `unsafe` 需人工公理 | Rustonomicon · RustBelt |
| **T-125: 循环不变式自动推断不完备** | Rice 定理 | 存在循环其不变式不可自动推断 | Prusti 对复杂循环的失效 | Rice 1953 · Cousot 1977 |
| **T-126: 并发程序验证的 CSL 需求** | 存在数据竞争可能 | 需并发分离逻辑（CSL）| `std::sync` 的原语验证 | Brookes 2007 · RustBelt |
| **T-127: 类型安全 → 内存安全** | Progress + Preservation | well-typed 程序不触发段错误 | Rust 的类型系统（Type System） | Pierce TAPL Ch.8 · RustBelt |
| **T-128: 抽象解释的 Galois 连接** | 抽象域满足单调性 | 分析结果 sound（无漏报）| Prusti 的数值范围推断 | Cousot & Cousot 1977 |
| **T-129: SMT 求解器的 Nelson-Oppen 组合** | 理论片段满足凸性 | 组合理论可判定 | Z3 / CVC5 在 Kani 中的使用 | Nelson & Oppen 1979 |

### 6.2 反命题决策树

```text
反命题决策树 1: "公理语义可以完全自动化 Rust 验证"
├── 分支 A: 程序不含循环
│   ├── 子分支: 程序为 safe Rust
│   │   └── 结论: ✅ 几乎可完全自动化（借用检查已自动化）
│   └── 子分支: 程序含 unsafe
│       └── 结论: ❌ 需人工提供公理
├── 分支 B: 程序含循环
│   ├── 子分支: 循环不变式简单（数值范围）
│   │   └── 结论: ⚠️ 部分自动化（Prusti/Creusot 可推断）
│   └── 子分支: 循环不变式复杂（数据结构）
│       └── 结论: ❌ 需人工标注不变式
└── 根结论: ❌ 公理语义无法完全自动化 Rust 验证
             （循环不变式、unsafe、并发是硬边界）

反命题决策树 2: "wp 计算比操作语义更适合 Rust 验证"
├── 分支 A: 验证目标是功能性正确性
│   └── 结论: ✅ wp 更适合（从规约反向推导）
├── 分支 B: 验证目标是内存安全
│   ├── 子分支: 程序为 safe Rust
│   │   └── 结论: ⚠️ 两者等价（编译器已保证内存安全）
│   └── 子分支: 程序含 unsafe
│       └── 结论: ❌ 两者均困难（需分离逻辑 / Miri）
├── 分支 C: 验证目标是找到反例
│   └── 结论: ❌ 操作语义更适合（Kani 的符号执行是 sp 方向）
└── 根结论: ⚠️ wp 和 sp 互补，无绝对优劣

反命题决策树 3: "Rust 的借用检查器是一个完备的公理验证器"
├── 分支 A: 验证内存安全
│   └── 结论: ✅ 完备（对所有 safe Rust 程序）
├── 分支 B: 验证功能性正确性
│   └── 结论: ❌ 不完备（类型系统不保证输出值正确）
├── 分支 C: 验证并发无数据竞争
│   └── 结论: ✅ 完备（Send/Sync trait 自动推导）
├── 分支 D: 验证终止性
│   └── 结论: ❌ 不完备（Rust 允许无限循环）
└── 根结论: ⚠️ 借用检查器是"内存安全"的完备验证器，
             但不是"任意属性"的完备验证器
```

---

## 七、工具链深度对比矩阵

### 7.1 Prusti vs Creusot vs Kani
>

| **维度** | **Prusti** | **Creusot** | **Kani** |
|:---|:---|:---|:---|
| **核心方法** | 分离逻辑 + Viper | wp 计算 + Why3 | 符号执行 + CBMC |
| **公理方向** | 双向（sp + wp 混合）| wp（反向）| sp（正向）|
| **规约语言** | `#[requires]/#[ensures]` | PEARLite（Rust 方言）| `kani::assert/assume` |
| **自动化程度** | 中（需编译器插件）| 中（需 Why3 IDE）| 高（命令行全自动）|
| **unsafe 支持** | ❌ 不支持 | ❌ 不支持 | ⚠️ 部分支持（符号执行可覆盖简单 unsafe）|
| **并发支持** | ❌ 不支持 | ❌ 不支持 | ❌ 不支持 |
| **泛型（Generics）/Trait** | 部分支持 | 良好支持 | 部分支持 |
| **异步（Async）支持** | ❌ 不支持 | ❌ 不支持 | ❌ 不支持 |
| **循环处理** | 抽象解释推断不变式 | 需人工标注不变式 | 自动展开（有界）|
| **标准库验证** | 有限 | 有限 | 较多（核心原语）|
| **学习曲线** | 中等 | 中等 | 低 |
| **典型场景** | 内存安全教学验证 | 功能性规约深度验证 | 快速反例生成/回归测试 |

> **选型建议**:
>
> - **教学/研究**: Prusti（分离逻辑可视化 + ETH 学术支持）
> - **高可信软件**: Creusot（wp 计算与 Why3 证明器深度集成）
> - **CI/CD 集成**: Kani（命令行全自动、低学习成本、快速反馈）
>
> **来源**: [Prusti Documentation](https://www.pm.inf.ethz.ch/research/prusti.html) · [Creusot Documentation](https://creusot.rs/) · [Kani Documentation](https://model-checking.github.io/kani/)

---

## 八、更多边界测试

### 10.4 边界测试：Prusti 对泛型 Trait 的验证失败

```rust,ignore
use prusti_contracts::*;

// 错误示例：Prusti 目前不支持泛型 Trait 方法的契约验证
#[requires(x > 0)]
fn generic_trait_issue<T: PartialOrd + Copy>(x: T) -> T {
    x
}

// Prusti 报错：
// "不支持泛型类型参数上的 trait bounds 推理"
// 原因：Prusti 的 Viper 翻译在将 Rust 的泛型实例化时，
//       丢失了部分 trait 约束信息，导致 wp 计算无法生成
//       有效的验证条件。
//
// 这反映了公理语义的一个理论边界：泛型多态的 wp 计算
// 需要高阶逻辑（System F 的 ∀ 量词），而一阶 SMT 求解器
// 无法直接处理高阶量化。
```

> **修正**: 泛型（Generics）代码的公理验证需要**参数化规约**（parametric specifications）。当前工业工具的通用策略是**单态化**（monomorphization）——将泛型代码实例化为具体类型后分别验证。这与 Rust 编译器的策略一致（rustc 在 MIR 层进行单态化），但代价是验证时间随实例化数量线性增长。未来方向：利用**参数化多态的语义**（Reynolds' relational parametricity）一次性验证所有实例。来源: [Reynolds 1983 — Types, Abstraction and Parametric Polymorphism] · 来源: [Prusti GitHub Issues]

### 10.5 边界测试：Kani 的路径爆炸与有界验证

```rust,ignore
#[kani::proof]
fn path_explosion_demo() {
    let mut sum = 0;
    for i in 0..100 {          // 循环 100 次
        let flag: bool = kani::any();
        if flag {
            sum += 1;
        } else {
            sum -= 1;
        }
    }
    kani::assert(sum >= -100 && sum <= 100);
}

// Kani 在此会严重缓慢或内存耗尽。
// 原因：每次循环迭代引入一个分支（if flag），
//       100 次迭代产生 2^100 条路径。
//       符号执行的路径空间指数级增长（路径爆炸）。
//
// 公理语义视角：Kani 使用有界模型检测（BMC），
// 将循环展开为 k 次迭代。若 k < 100，则验证不完备；
// 若 k >= 100，则 SMT 公式过大，求解器超时。
```

> **修正**: 路径爆炸是符号执行的**根本局限**，不是 Kani 的实现缺陷。缓解策略：
>
> 1. **循环抽象**：用人工不变式替代循环展开（Kani 支持 `#[kani::loop_invariant]`）
> 2. **切片（Slice）**：只验证与目标断言相关的代码路径
> 3. **有界验证**：接受"在 k 次迭代内正确"的较弱保证
> 4. **抽象解释结合**：先用 Prusti 推断不变式，再用 Kani 验证具体断言
>
> **来源**: [Kani Loop Contracts](https://model-checking.github.io/kani/reference/experimental/loop-contracts.html) · [CBMC Bounded Model Checking](https://github.com/diffblue/cbmc)

### 10.6 边界测试：Creusot 的 Ghost 代码与零成本抽象

```rust,ignore
use creusot_contracts::*;

// 正确示例：Ghost 代码不参与运行时，仅用于规约
#[requires(n @ > 0)]
#[ensures(result @ >= n @)]
pub fn factorial_ghost(n: u64) -> u64 {
    let mut res = 1u64;
    let mut i = 1u64;

    #[invariant(i @ <= n @ + 1)]
    #[invariant(res @ == factorial(i @ - 1))]
    while i <= n {
        res *= i;
        i += 1;
    }
    res
}

// Ghost 函数（不编译到目标代码）
#[logic]
fn factorial(n: Int) -> Int {
    if n <= 0 { 1 } else { n * factorial(n - 1) }
}

// 关键洞察：Ghost 代码是公理语义在 Rust 中的"编译时存在"。
// `#[logic]` 标记的函数只存在于验证阶段，不参与运行时。
// 这实现了公理规约的"零成本"——规约不带来运行时开销。
//
// 然而，Ghost 代码的正确性本身无法被工具验证（元层次问题）。
// 若 `factorial` 的定义有误，整个验证结论都是不可靠的。
```

> **修正**: Ghost 代码的正确性是**信任根基**（trusted computing base）的一部分。当前最佳实践：
>
> 1. Ghost 函数应尽量简单（纯递归、无复杂控制流）
> 2. 对关键 Ghost 函数，使用辅助断言自我验证
> 3. 社区共享经过审查的 Ghost 函数库（类似标准库的信任模型）
>
> **来源**: [Creusot Ghost Code](https://creusot.rs/guide/ghost.html) · [Why3 Standard Library](https://why3.lri.fr/stdlib/)

---

## 相关概念文件

- [操作语义：程序行为的形式化定义](17_operational_semantics.md) — 小步/大步语义、求值上下文
- [指称语义：CPO 与不动点](12_denotational_semantics.md) — Scott-Strachey 语义
- [类型论基础](../00_type_theory/02_type_theory.md) — HM 类型系统（Type System）、System F、Rust 类型扩展
- [所有权形式化](../01_ownership_logic/03_ownership_formal.md) — COR、RustBelt、权限系统
- [分离逻辑：Rust 所有权的形式化根基](../02_separation_logic/11_separation_logic.md) — 框架规则、Iris、CSL
- [RustBelt 与验证工具链](../02_separation_logic/04_rustbelt.md) — 高阶幽灵状态、验证工具生态
- [验证工具链选择指南](../04_model_checking/05_verification_toolchain.md) — Prusti/Creusot/Kani/Miri 选型
- [线性逻辑与仿射逻辑](../01_ownership_logic/01_linear_logic.md) — 资源敏感性基础

> **过渡**: Axiomatic Semantics（公理语义） 的深入理解需要结合具体代码实践，建议通过编写测试用例验证边界行为。
> **过渡**: Axiomatic Semantics（公理语义） 的深入理解需要结合具体代码实践，建议通过编写测试用例验证边界行为。
> **过渡**: Axiomatic Semantics（公理语义） 的深入理解需要结合具体代码实践，建议通过编写测试用例验证边界行为。

### 补充定理链

- **定理**: Axiomatic Semantics（公理语义） 定义 ⟹ 类型安全保证
- **定理**: Axiomatic Semantics（公理语义） 定义 ⟹ 类型安全保证
- **定理**: Axiomatic Semantics（公理语义） 定义 ⟹ 类型安全保证
