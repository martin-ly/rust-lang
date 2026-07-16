> **内容分级**: [综述级]
>
# 测验：通用 PL 基座
>
> **EN**: Quiz: General PL Foundations
> **Summary**: Embedded quiz for the general programming-language mechanism files: variable model, evaluation strategies, effects and purity, control flow, and data abstraction spectrum.
> **Rust 版本**: 1.97.0+ (Edition 2024)
>
> **受众**: [初学者]
> **权威来源**: 本文件为 `concept/` 权威页。
> **层级**: L1 基础概念
> **A/S/P 标记**: S — Structure
> **双维定位**: C×Eva
> **前置概念**: · [自测题库](../../00_meta/04_navigation/12_self_assessment.md)
>
> [Variable Model](../03_values_and_references/03_variable_model.md) ·
> [Evaluation Strategies](../../04_formal/03_operational_semantics/04_evaluation_strategies.md) ·
> [Effects and Purity](../00_start/04_effects_and_purity.md) ·
> [Control Flow](../04_control_flow/01_control_flow.md) ·
> [Data Abstraction Spectrum](../02_type_system/05_data_abstraction_spectrum.md)
> **后置概念**: N/A
> **主要来源**:
> [TRPL](https://doc.rust-lang.org/book/title-page.html) ·
> [Rust Reference](https://doc.rust-lang.org/reference/introduction.html) ·
> [Rustonomicon](https://doc.rust-lang.org/nomicon/index.html) ·
> [Brown University — Concepts in Rust Programming](https://cel.cs.brown.edu/crp/) ·
> [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html) ·
> [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/)
---

> **Bloom 层级**: L1-L3
> **难度图例**: 🟢 基础（概念直接考察）｜ 🟡 进阶（需理解深层原理）｜ 🔴 专家（多概念综合 / 边界情况）
> **题型构成**: 代码阅读题（能否编译 / 输出分析，本测验特色）+ 规范题型【单选】【多选】【判断】（按 mdbook-quiz 指南四级题型规范（`docs/02_learning/07_mdbook_quiz_guide.md`） 的 .md 落地形态组织，不引入 TOML 插件）

---
> **权威来源**: [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Rust Reference](https://doc.rust-lang.org/reference/introduction.html) · [Rustonomicon](https://doc.rust-lang.org/nomicon/index.html)
>
> **权威来源对齐变更日志**: 2026-07-10 补充权威来源标注（TRPL、Rust Reference、Rustonomicon）

---

## 一、变量模型

本组题目考察「环境-存储」模型下 Rust 变量语义的定位：所有权（Ownership）约束的是存储层（位置的值与有效性），借用（Borrowing）检查是环境到存储访问权限的静态分析。
理解这一分层是回答后续「为什么 move 后源失效是编译期事实」「`&mut` 可建模为哪种效果」等题目的理论底座——建议先回顾 [变量模型](../03_values_and_references/03_variable_model.md) 的环境/存储分离再作答。

### 问题 1：🟡 在通用 PL 的"环境-存储"模型中，Rust 的所有权系统主要约束的是哪一层？

- A. 环境层（Environment）
- B. 存储层（Store）
- C. 语法层（Syntax）
- D. 类型层（Type）

<details>
<summary>✅ 答案与解析</summary>

**答案：B**

环境层将变量名映射到资源标识符；存储层管理资源本身及其所有权（Ownership）状态。
Rust 的所有权约束主要作用于存储层，确保每个资源在任意时刻只有一个所有者。

</details>

---

## 二、求值策略

本节聚焦「求值策略」，核心内容为问题 2：Rust 默认使用哪种求值策略？`&T` 和 `&mut T…。

### 问题 2：🟡 Rust 默认使用哪种求值策略？`&T` 和 `&mut T` 在求值策略上分别对应什么？

- A. CBV；`&T` 对应 CBN，`&mut T` 对应 CBR
- B. CBN；`&T` 对应 CBV，`&mut T` 对应 CBR
- C. CBV；`&T` 和 `&mut T` 都是受限的 CBR
- D. CBR；`&T` 和 `&mut T` 都是 CBV

<details>
<summary>✅ 答案与解析</summary>

**答案：C**

Rust 是严格求值语言，默认参数传递是 Call-by-Value（对于 `Copy` 类型是复制值，对于非 `Copy` 类型是转移所有权（Ownership））。
`&T` 和 `&mut T` 提供受限的 Call-by-Reference 能力，允许函数访问或修改调用者的数据而不转移所有权。

</details>

---

## 三、副作用与纯度

本节专门讨论「副作用与纯度」下的问题 3：在 Rust 中，`&mut T` 可以被建模为什么样的效果？。

### 问题 3：🔴 在 Rust 中，`&mut T` 可以被建模为什么样的效果？

- A. Read effect
- B. Write effect
- C. Exception effect
- D. Nondeterminism effect

<details>
<summary>✅ 答案与解析</summary>

**答案：B**

`&mut T` 允许修改被引用（Reference）的数据，因此可以被建模为 write effect。
Rust 通过借用（Borrowing）检查器限制 write effect 的别名，从而防止数据竞争和不一致状态。

</details>

---

## 四、控制流

本组题目考察控制流的理论基础：Böhm–Jacopini 定理（顺序/选择/循环的表达充分性）、结构化控制与 `goto` 的关系、以及 Rust 控制流的「表达式化」特征（`if`/`match`/`loop` 皆产生值）。
作答时注意区分「表达力等价」（图灵完备层面）与「工程适用性」（可维护性、编译器可分析性）——定理只承诺前者。

### 问题 4：🟢 结构化程序定理（Böhm–Jacopini 定理）指出，任何可计算函数都可以用哪些控制结构表达？

- A. `goto`、`if`、`while`
- B. sequence、selection、iteration
- C. recursion、pattern matching、exception
- D. continuation、monad、generator

<details>
<summary>✅ 答案与解析</summary>

**答案：B**

结构化程序定理指出：任何可计算函数都可以仅用 sequence（顺序）、selection（选择）、iteration（迭代）三种控制结构表达，无需 `goto`。

</details>

---

## 五、数据抽象谱系

本组题目考察数据抽象的谱系定位：Rust 的 `enum` + `match` 对应 ML 系的代数数据类型传统（区别于 OOP 的类继承与 Lisp 的列表结构），`struct` 是积类型、trait 接近 typeclass。关键判别点：ADT 的价值在「和类型的穷尽分解」，OOP 的价值在「开放扩展」——Rust 选择前者并用 `#[non_exhaustive]` 提供受控的开放后门。

### 问题 5：🟡 从数据抽象谱系看，Rust 的 `enum` + `match` 最接近以下哪种传统抽象？

- A. C struct
- B. C++ class with inheritance
- C. Haskell ADT（代数数据类型）
- D. Java interface

<details>
<summary>✅ 答案与解析</summary>

**答案：C**

Rust 的 `enum` 可以携带数据，结合 `match` 进行穷尽性模式匹配（Pattern Matching），这与 Haskell 的代数数据类型（ADT）最为接近。它比 C struct 更抽象，比 C++ class 继承更轻量，比 Java interface 更注重数据与行为的统一。

</details>

---

## 六、综合应用

本节聚焦「综合应用」，核心内容为问题 6：为什么 Rust 能在不使用垃圾回收器的情况下保证内存安全（Memory Safety）？。

### 问题 6：🔴 为什么 Rust 能在不使用垃圾回收器的情况下保证内存安全？

- A. 因为 Rust 使用引用（Reference）计数管理所有内存
- B. 因为 Rust 的所有权（Ownership）系统在编译期跟踪资源生命周期（Lifetimes）
- C. 因为 Rust 不允许使用堆内存
- D. 因为 Rust 的运行时（Runtime）会自动回收内存

<details>
<summary>✅ 答案与解析</summary>

**答案：B**

Rust 通过所有权（Ownership）、借用（Borrowing）和生命周期（Lifetimes）规则在编译期跟踪资源的生命周期。当所有者离开作用域时，`Drop` trait 自动释放资源，无需垃圾回收器或手动释放。

</details>

---

> **Checklist**: 已覆盖变量模型 / 求值策略 / 副作用 / 控制流 / 数据抽象 / 综合应用，共 6 题。

---

## 七、规范题型补充：单选 · 多选 · 判断

> 本节按四级题型规范补充单选、多选与判断题，知识点与
> [Variable Model](../03_values_and_references/03_variable_model.md)、
> [Evaluation Strategies](../../04_formal/03_operational_semantics/04_evaluation_strategies.md)、
> [Effects and Purity](../00_start/04_effects_and_purity.md)、
> [Control Flow](../04_control_flow/01_control_flow.md) 权威页一致；
> 干扰项针对常见误解设计。

### 问题 7：🟡【单选】在"环境-存储"模型中，Rust 借用检查器在编译期静态分析引用的有效性，这对应 PL 理论中的哪一类机制？

- A. 运行时（Runtime）类型检查（dynamic type checking）
- B. 静态语义分析：在求值之前验证存储层资源的使用约束
- C. 垃圾回收的可达性分析
- D. 动态方法分派

<details>
<summary>✅ 答案与解析</summary>

**答案：B**

**解析**：借用检查不改变任何运行时行为，它在编译期拒绝违反别名/可变性约束的程序，属于**静态语义**层面的分析（类似类型检查，但作用于"存储层资源的使用方式"）。A 错：检查发生在编译期而非运行时；C 错：可达性分析是运行时机制，Rust 没有 GC；D 与资源约束无关。

</details>

---

### 问题 8：🟡【单选】Rust 迭代器的"惰性求值"在求值策略谱系上与下列哪种思想最接近？

- A. call-by-value（传值调用）
- B. call-by-need（按需调用：推迟求值且结果记忆化）
- C. call-by-reference（传引用调用）
- D. 与 call-by-name 完全等同，无任何差别

<details>
<summary>✅ 答案与解析</summary>

**答案：B**

**解析**：惰性迭代器（Iterator）推迟计算到"被需要"（消费）时才发生，且每个元素只求值一次——这正是 call-by-need 的思想。D 有教学价值：call-by-name 每次使用都**重新求值**且无记忆化，与迭代器"至多求值一次"不同；A 是 Rust 函数参数的默认策略，恰为对照。

</details>

---

### 问题 9：🔴【多选】从"效果（effects）与纯度"视角看 Rust，下列说法正确的有？（选出所有正确项）

- A. `&mut T` 可以建模为对存储的写效果，且该效果在同一时刻是独占的
- B. Rust 的类型系统（Type System）完全不跟踪任何效果
- C. 所有权系统对"何时何地允许可变性"施加了静态约束
- D. `unsafe` 块内的代码完全不受类型系统约束

<details>
<summary>✅ 答案与解析</summary>

**答案：A、C**

**解析**：Rust 虽无 Haskell 式的效果类型，但通过所有权与借用规则**静态地约束了最重要的效果——可变性**（A、C，详见 [Effects and Purity](../00_start/04_effects_and_purity.md)）。B 错：可变性约束本身就是效果跟踪的特例。D 错：`unsafe` 只放宽了借用检查等**部分**规则，类型检查、trait 约束依然完全生效——"unsafe 绕过类型系统"是危险误解。

</details>

---

### 问题 10：🟢【判断】Böhm–Jacopini（结构化程序）定理表明：顺序、选择、循环三种控制结构足以表达任何可计算函数，因此 `goto` 在表达力上不是必需的。（对 / 错）

<details>
<summary>✅ 答案与解析</summary>

**答案：对**

**解析**：该定理（1966）证明了三种结构化构造的完备性，是"结构化编程取代 goto"的理论基础。注意区分**表达力**与**便利性**：Rust 没有 goto，但提供带标签的 `break`/`continue`、`loop`、`match` 等结构化等价物，覆盖了实践中 goto 的正当用途（如跳出多层循环），见 [Control Flow](../04_control_flow/01_control_flow.md)。

</details>

---

### 问题 11：🟡【判断】Rust 的 `enum` 是可判别联合（tagged union）：标签由编译器管理，`match` 的穷尽性检查保证不会误解释变体，这与 C 的裸 `union` 有本质区别。（对 / 错）

<details>
<summary>✅ 答案与解析</summary>

**答案：对**

**解析**：C 的 `union` 不带标签，"当前是哪个变体"全凭程序员约定，误读即 UB；Rust 的 `enum` 把标签与数据绑定为一个整体，读取变体必须经过 `match`/`if let` 的模式匹配（Pattern Matching），编译器保证标签与数据一致且分支穷尽。这是数据抽象谱系上"类型安全的和类型（sum type）"对"无标签联合"的胜出。

</details>
