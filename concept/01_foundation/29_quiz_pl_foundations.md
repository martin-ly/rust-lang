> **内容分级**: [综述级]
>
# 测验：通用 PL 基座
>
> **EN**: Quiz: General PL Foundations
> **Summary**: Embedded quiz for the general programming-language mechanism files: variable model, evaluation strategies, effects and purity, control flow, and data abstraction spectrum.
>
> **受众**: [初学者]
> **层级**: L1 基础概念
> **A/S/P 标记**: S — Structure
> **双维定位**: C×Eva
> **前置概念**: · [自测题库](../00_meta/self_assessment.md)
>
> [Variable Model](20_variable_model.md) ·
> [Evaluation Strategies](../04_formal/18_evaluation_strategies.md) ·
> [Effects and Purity](21_effects_and_purity.md) ·
> [Control Flow](07_control_flow.md) ·
> [Data Abstraction Spectrum](22_data_abstraction_spectrum.md)
> **后置概念**: N/A
> **主要来源**: [TRPL](https://doc.rust-lang.org/book/) · [Rust Reference](https://doc.rust-lang.org/reference/) · [Rustonomicon](https://doc.rust-lang.org/nomicon/) · [Brown University — Concepts in Rust Programming](https://cel.cs.brown.edu/crp/) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/)
---

> **Bloom 层级**: 理解 → 应用


---

## 认知路径

> **认知路径**: 本节从 "测验" 的核心问题出发，依次建立直观理解、形式化模型与工程实践之间的联系。

1. **问题识别**: 为什么 测验 在 Rust 中值得关注？它与日常编程中的哪些痛点相关？
2. **概念建立**: 掌握 测验 的核心定义、关键术语与类型系统（Type System）/运行时（Runtime）边界。
3. **机制推理**: 通过 ⟹ 定理链将语法规则、编译期检查与运行时（Runtime）语义串联起来。
4. **边界辨析**: 借助反命题/反例理解常见错误与测验的适用边界。
5. **迁移应用**: 将 测验 与前置/后置概念链接，形成跨层知识网络。


---

## 反命题决策树

> **反命题 1**: "测验 在所有场景下都适用" ⟹ 不成立。存在特定的边界条件（如 `unsafe`、FFI、递归类型）会使常规推理失效。

> **反命题 2**: "忽略 测验 的细节也能写出正确代码" ⟹ 不成立。编译错误通常是 测验 规则被违反的直接信号。

> **反命题 3**: "其他语言对 测验 的处理方式可以直接迁移到 Rust" ⟹ 不成立。Rust 的所有权（Ownership）和借用（Borrowing）约束使 测验 具有语言特有的形态。


## 一、变量模型

### 问题 1：在通用 PL 的"环境-存储"模型中，Rust 的所有权系统主要约束的是哪一层？

- A. 环境层（Environment）
- B. 存储层（Store）
- C. 语法层（Syntax）
- D. 类型层（Type）

<details>
<summary>✅ 答案与解析</summary>

**答案：B**

环境层将变量名映射到资源标识符；存储层管理资源本身及其所有权（Ownership）状态。Rust 的所有权约束主要作用于存储层，确保每个资源在任意时刻只有一个所有者。

</details>

---

## 二、求值策略

### 问题 2：Rust 默认使用哪种求值策略？`&T` 和 `&mut T` 在求值策略上分别对应什么？

- A. CBV；`&T` 对应 CBN，`&mut T` 对应 CBR
- B. CBN；`&T` 对应 CBV，`&mut T` 对应 CBR
- C. CBV；`&T` 和 `&mut T` 都是受限的 CBR
- D. CBR；`&T` 和 `&mut T` 都是 CBV

<details>
<summary>✅ 答案与解析</summary>

**答案：C**

Rust 是严格求值语言，默认参数传递是 Call-by-Value（对于 `Copy` 类型是复制值，对于非 `Copy` 类型是转移所有权（Ownership））。`&T` 和 `&mut T` 提供受限的 Call-by-Reference 能力，允许函数访问或修改调用者的数据而不转移所有权。

</details>

---

## 三、副作用与纯度

### 问题 3：在 Rust 中，`&mut T` 可以被建模为什么样的效果？

- A. Read effect
- B. Write effect
- C. Exception effect
- D. Nondeterminism effect

<details>
<summary>✅ 答案与解析</summary>

**答案：B**

`&mut T` 允许修改被引用（Reference）的数据，因此可以被建模为 write effect。Rust 通过借用（Borrowing）检查器限制 write effect 的别名，从而防止数据竞争和不一致状态。

</details>

---

## 四、控制流

### 问题 4：结构化程序定理（Böhm–Jacopini 定理）指出，任何可计算函数都可以用哪些控制结构表达？

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

### 问题 5：从数据抽象谱系看，Rust 的 `enum` + `match` 最接近以下哪种传统抽象？

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

### 问题 6：为什么 Rust 能在不使用垃圾回收器的情况下保证内存安全？

- A. 因为 Rust 使用引用（Reference）计数管理所有内存
- B. 因为 Rust 的所有权（Ownership）系统在编译期跟踪资源生命周期（Lifetimes）
- C. 因为 Rust 不允许使用堆内存
- D. 因为 Rust 的运行时（Runtime）会自动回收内存

<details>
<summary>✅ 答案与解析</summary>

**答案：B**

Rust 通过所有权、借用（Borrowing）和生命周期（Lifetimes）规则在编译期跟踪资源的生命周期。当所有者离开作用域时，`Drop` trait 自动释放资源，无需垃圾回收器或手动释放。

</details>

---

> **Checklist**: 已覆盖变量模型 / 求值策略 / 副作用 / 控制流 / 数据抽象 / 综合应用，共 6 题。
