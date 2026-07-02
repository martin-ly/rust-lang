# 通用 PL 基座路线图：Rust 在编程语言坐标系中的位置
>
> **EN**: General PL Foundations Roadmap
> **Summary**: A unified index for general programming-language mechanism files that provide the foundational context for understanding Rust's specific design choices.
>
> **受众**: [初学者]
> **层级**: L1-L4 跨层导航
> **A/S/P 标记**: S+S — Structure + Science
> **双维定位**: C×Ana
> **前置概念**: [Type System](../01_foundation/04_type_system.md) · [Ownership](../01_foundation/01_ownership.md)
> **后置概念**: [C/C++ → Rust Engineering Roadmap](cpp_rust_engineering_roadmap.md) · [Pattern Semantic Space Index](pattern_semantic_space_index.md)
> **主要来源**: [Pierce TAPL] · [Harper PFPL] · [Felleisen & Flatt PLAI] · [Nottingham PL Semantics]
> **来源**: [Rust Reference](https://doc.rust-lang.org/reference/) · [TRPL](https://doc.rust-lang.org/book/) · [RFCs](https://github.com/rust-lang/rfcs)
---

> **Bloom 层级**: 理解 → 分析

## 一、核心命题

> **Rust 的许多设计选择（所有权、借用、生命周期、`Result`、`unsafe`）只有在更广泛的编程语言机制坐标系中才能被真正理解。
> 本路线图将通用 PL 基座内容组织为四个主题：变量与存储、求值与计算、副作用与控制、数据抽象，
> 帮助学习者从"Rust 特有语法"上升到"通用 PL 机制"，再落回"Rust 的具体实现"。**

---

## 二、基座主题地图

### 2.1 变量与存储

| 通用 PL 概念 | Rust 具体机制 | 文件 |
|:---|:---|:---|
| 环境模型 vs 存储模型 | 所有权 = 存储模型 + 线性约束 | [Variable Model](../01_foundation/20_variable_model.md) |
| 值语义 vs 引用语义 | `Copy` / `Move` / `Clone` | [Variable Model](../01_foundation/20_variable_model.md) |
| L-value / R-value | place expression / value expression | [Variable Model](../01_foundation/20_variable_model.md) |
| 赋值语义 | 绑定 vs 存储更新 | [Variable Model](../01_foundation/20_variable_model.md) |

### 2.2 求值与计算

| 通用 PL 概念 | Rust 具体机制 | 文件 |
|:---|:---|:---|
| Call-by-Value (CBV) | 默认参数传递 + 所有权转移 | [Evaluation Strategies](../04_formal/18_evaluation_strategies.md) |
| Call-by-Reference (CBR) | `&T` / `&mut T` | [Evaluation Strategies](../04_formal/18_evaluation_strategies.md) |
| Call-by-Name / Call-by-Need | `lazy_static` / `once_cell` / `Iterator` | [Evaluation Strategies](../04_formal/18_evaluation_strategies.md) |
| 严格 vs 非严格求值 | `&&` / `\|\|` 短路、`Future` 显式惰性 | [Evaluation Strategies](../04_formal/18_evaluation_strategies.md) |
| 归约策略 | normal order / applicative order | [Lambda Calculus](../04_formal/14_lambda_calculus.md) |

### 2.3 副作用与控制

| 通用 PL 概念 | Rust 具体机制 | 文件 |
|:---|:---|:---|
| 引用透明 | 纯函数、不可变借用 | [Effects and Purity](../01_foundation/21_effects_and_purity.md) |
| 副作用分类 | State / IO / Exception / Nondeterminism / Time | [Effects and Purity](../01_foundation/21_effects_and_purity.md) |
| Mutation as Effect | `&mut T` 作为 write effect | [Effects and Purity](../01_foundation/21_effects_and_purity.md) |
| 结构化程序定理 | sequence / selection / iteration | [Control Flow](../01_foundation/07_control_flow.md) |
| Continuation | `?` / `break 'label` / async / CPS | [Control Flow](../01_foundation/07_control_flow.md) |
| 控制流图（CFG） | 基本块、支配树、编译器优化 | [Control Flow](../01_foundation/07_control_flow.md) |

### 2.4 数据抽象

| 通用 PL 概念 | Rust 具体机制 | 文件 |
|:---|:---|:---|
| C struct / 内存布局 | `struct` / `repr(C)` | [Data Abstraction Spectrum](../01_foundation/22_data_abstraction_spectrum.md) |
| C++ class / 封装 | `struct` + `impl` + 模块可见性 | [Data Abstraction Spectrum](../01_foundation/22_data_abstraction_spectrum.md) |
| ADT / 代数数据类型 | `enum` + 模式匹配 | [Data Abstraction Spectrum](../01_foundation/22_data_abstraction_spectrum.md) |
| 子类型多态 | Trait + `dyn Trait` | [Data Abstraction Spectrum](../01_foundation/22_data_abstraction_spectrum.md) |

---

## 三、推荐学习路径

### 路径 A：从通用 PL 到 Rust

```text
Variable Model（理解环境与存储）
    ↓
Evaluation Strategies（理解参数如何传递、何时求值）
    ↓
Effects and Purity（理解副作用如何被分类和控制）
    ↓
Control Flow（理解控制流的结构化与连续性）
    ↓
Data Abstraction Spectrum（理解 Rust enum+trait 在数据抽象史中的位置）
```

### 路径 B：从 Rust 问题出发反向学习 PL 机制

| 你遇到的 Rust 问题 | 对应的 PL 基座 | 文件 |
|:---|:---|:---|
| 为什么 move 后不能访问原变量？ | 存储模型 + 线性类型 | [Variable Model](../01_foundation/20_variable_model.md) |
| 为什么 `&mut` 只能有一个？ | 副作用模型 + alias discipline | [Effects and Purity](../01_foundation/21_effects_and_purity.md) |
| 为什么 `?` 能传播错误？ | Continuation / 控制流 | [Control Flow](../01_foundation/07_control_flow.md) |
| 为什么 `Iterator` 是惰性的？ | 求值策略 | [Evaluation Strategies](../04_formal/18_evaluation_strategies.md) |
| 为什么 `enum` 比 class 更适合某些场景？ | 数据抽象谱系 | [Data Abstraction Spectrum](../01_foundation/22_data_abstraction_spectrum.md) |

---

## 四、与 Phase A 计划的衔接

本路线图属于 **Phase A（通用 PL 基座）** 的导航层。审计报告 [SEMANTIC_SPACE_CRITICAL_AUDIT_2026_05_24.md](../../archive/reports/2026_07/SEMANTIC_SPACE_CRITICAL_AUDIT_2026_05_24.md) 指出的 Phase A 缺口包括：

- 变量模型 ✅ [Variable Model](../01_foundation/20_variable_model.md)
- 求值策略 ✅ [Evaluation Strategies](../04_formal/18_evaluation_strategies.md)
- 副作用与纯度 ✅ [Effects and Purity](../01_foundation/21_effects_and_purity.md)
- 控制流深化 ✅ [Control Flow](../01_foundation/07_control_flow.md)
- 数据抽象谱系 ✅ [Data Abstraction Spectrum](../01_foundation/22_data_abstraction_spectrum.md)

---

## 五、L1 / L2 / L3 总结

| 层级 | 要点 |
|:---|:---|
| **L1** | Rust 的所有权、借用、`Result`、`enum` 等机制都可以在通用 PL 框架中找到对应概念。 |
| **L2** | 通用 PL 基座帮助理解"Rust 为什么这样设计"，而不是只记忆"Rust 怎么用"。 |
| **L3** | Rust 的设计是把通用 PL 机制（线性类型、求值策略、效果系统、代数数据类型）以工程可用的方式落地，形成了一门"有形式化根基的系统编程语言"。 |

---

## 六、延伸阅读

- [Pierce — Types and Programming Languages (TAPL)](https://www.cis.upenn.edu/~bcpierce/tapl/)
- [Harper — Practical Foundations for Programming Languages (PFPL)](https://cs.cmu.edu/~rwh/pfpl/)
- [Felleisen & Flatt — Programming Languages: Application and Interpretation (PLAI)](https://cs.brown.edu/~sk/Publications/Books/ProgLangs/2007-04-26/plai-2007-04-26.pdf)
- [Nottingham — Programming Language Semantics](https://people.cs.nott.ac.uk/pszgmh/123.pdf)

---

> **Checklist**: 已建立通用 PL 基座主题地图 / 提供学习路径 / 衔接 Phase A 审计计划。
