# 航空航天认证与形式化方法 (Aerospace Certification & Formal Methods)

> **Bloom 层级**: 分析 → 评价
> **定位**: 系统讲解 **DO-178C 航空软件标准** 与 **DO-333 形式化方法补充** 的 Rust 映射——从软件等级 A~E 到定理证明、模型检查、抽象解释三类形式化方法在 Rust 生态中的工具链映射，分析 Rust 所有权系统在航空航天安全关键软件中的独特形式化优势。
> **前置概念**: [形式化方法](./13_formal_methods.md) · [Hoare 逻辑](./15_hoare_logic.md) · [RustBelt](./04_rustbelt.md)
> **后置概念**: [Unsafe](../03_advanced/03_unsafe.md) · [并发安全](../03_advanced/01_concurrency.md) · [验证工具链](./05_verification_toolchain.md)

---

> **来源**: [DO-178C - Software Considerations in Airborne Systems](https://www.rtca.org/) ·
> [DO-333 - Formal Methods Supplement](https://www.rtca.org/) ·
> [DO-330 - Software Tool Qualification](https://www.rtca.org/) ·
> [Ferrocene - Qualified Rust Compiler](https://ferrocene.dev/) ·
> [Rockwell Collins - Field Guidance System Case Study](https://arxiv.org/abs/1409.7643) ·
> [Rust Reference](https://doc.rust-lang.org/reference/) ·
> [Wikipedia — DO-178C](https://en.wikipedia.org/wiki/DO-178C)

## 📑 目录
>
> [来源: [DO-178C Standard](https://www.rtca.org/)]
>
> [来源: [Ferrocene Documentation](https://ferrocene.dev/)]

- [航空航天认证与形式化方法 (Aerospace Certification \& Formal Methods)](#航空航天认证与形式化方法-aerospace-certification--formal-methods)
  - [📑 目录](#-目录)
  - [一、引言](#一引言)
    - [1.1 DO-178C 航空软件标准](#11-do-178c-航空软件标准)
    - [1.2 DO-333 Formal Methods Supplement](#12-do-333-formal-methods-supplement)
  - [二、DO-178C 等级要求矩阵](#二do-178c-等级要求矩阵)
  - [三、DO-333 形式化方法映射](#三do-333-形式化方法映射)
    - [3.1 定理证明 (Theorem Proving)](#31-定理证明-theorem-proving)
    - [3.2 模型检查 (Model Checking)](#32-模型检查-model-checking)
    - [3.3 抽象解释 (Abstract Interpretation)](#33-抽象解释-abstract-interpretation)
  - [四、形式化目标 → 工具映射表](#四形式化目标--工具映射表)
  - [五、认证案例研究](#五认证案例研究)
    - [5.1 Rockwell Collins 双通道场引导系统](#51-rockwell-collins-双通道场引导系统)
    - [5.2 适配 Rust 的形式化验证方案](#52-适配-rust-的形式化验证方案)
  - [六、Property Preservation](#六property-preservation)
    - [6.1 源代码到目标代码的性质保持](#61-源代码到目标代码的性质保持)
    - [6.2 Ferrocene 的合格编译论证](#62-ferrocene-的合格编译论证)
  - [七、工具鉴定 (DO-330)](#七工具鉴定-do-330)
    - [7.1 TQL-1 至 TQL-5 映射](#71-tql-1-至-tql-5-映射)
    - [7.2 Rust 形式化工具的鉴定路径](#72-rust-形式化工具的鉴定路径)
  - [八、Ferrocene 认证范围](#八ferrocene-认证范围)
  - [九、Rust 独特优势](#九rust-独特优势)
  - [十、边界与缺口](#十边界与缺口)
    - [10.1 Trait 系统未形式化](#101-trait-系统未形式化)
    - [10.2 Unsafe Rust 缺口](#102-unsafe-rust-缺口)
    - [10.3 缺少 CompCert 级认证编译器](#103-缺少-compcert-级认证编译器)
  - [十一、来源与延伸阅读](#十一来源与延伸阅读)
  - [相关概念文件](#相关概念文件)
  - [权威来源索引](#权威来源索引)
  - [十、边界测试：航空航天认证形式化方法的编译错误](#十边界测试航空航天认证形式化方法的编译错误)
    - [10.1 边界测试：MISRA C 规则的 Rust 类比（编译错误）](#101-边界测试misra-c-规则的-rust-类比编译错误)
    - [10.2 边界测试：确定性执行与 `const fn`（编译错误）](#102-边界测试确定性执行与-const-fn编译错误)
    - [10.3 边界测试：SPARK 模式的 Rust 近似与 `no_panic`（编译错误）](#103-边界测试spark-模式的-rust-近似与-no_panic编译错误)
    - [10.4 边界测试：MC/DC 覆盖率与短路逻辑（逻辑错误）](#104-边界测试mcdc-覆盖率与短路逻辑逻辑错误)

---

## 一、引言
>
> [来源: [DO-178C Standard](https://www.rtca.org/)]
>
> [来源: [Wikipedia — DO-178C](https://en.wikipedia.org/wiki/DO-178C)]

航空航天软件认证是安全关键系统开发中最严格的软件质量保证流程。DO-178C（Software Considerations in Airborne Systems and Equipment Certification）是国际航空界广泛采用的软件适航标准，由 RTCA（Radio Technical Commission for Aeronautics）发布。它为机载软件的开发、验证和认证提供了系统化的框架。

Rust 编程语言的所有权系统和形式化验证生态，为 DO-178C 的合规性提供了独特的技术路径。本文件系统性地映射 DO-178C/DO-333 的目标到 Rust 工具链，分析 Rust 在航空航天安全关键软件开发中的形式化验证能力、认证路径与现存缺口。

### 1.1 DO-178C 航空软件标准
>
> [来源: [DO-178C Standard](https://www.rtca.org/)]

**DO-178C 核心结构**:

```text
DO-178C 软件生命周期:

  软件计划过程 (Software Planning Process)
  ├── 软件开发计划 (PSAC - Plan for Software Aspects of Certification)
  ├── 软件开发标准
  └── 软件生命周期环境

  软件开发过程 (Software Development Processes)
  ├── 软件需求过程
  ├── 软件设计过程
  ├── 软件编码过程
  └── 集成过程

  软件验证过程 (Software Verification Processes)
  ├── 评审与分析
  ├── 测试 (Requirements-based testing)
  └── 验证结果分析

  软件配置管理 (Software Configuration Management)
  软件质量保证 (Software Quality Assurance)
  合格审定联络 (Certification Liaison)
```

> **认知功能**: DO-178C 的核心洞察是**验证强度必须与失效影响成正比**——A 级软件的验证深度远高于 D 级软件。Rust 的所有权系统可以在编译期消除一整类内存安全错误，相当于为所有等级提供了"零成本"的额外验证层。
> [来源: [DO-178C Introductory Course - RTCA](https://www.rtca.org/)]

### 1.2 DO-333 Formal Methods Supplement
>
> [来源: [DO-333 Standard](https://www.rtca.org/)]
>
> [来源: [Formal Methods in Aerospace - NASA](https://ntrs.nasa.gov/)]

DO-333 是 DO-178C 的技术补充（Technology Supplement），专门定义如何在 DO-178C 框架内使用形式化方法满足验证目标。DO-333 承认三种形式化方法类别：

1. **定理证明 (Theorem Proving)**: 基于逻辑推理的证明系统
2. **模型检查 (Model Checking)**: 自动状态空间穷举
3. **抽象解释 (Abstract Interpretation)**: 静态程序分析的理论基础

> **关键规定**: DO-333 允许形式化方法**替代或补充**传统的评审、分析和测试活动，但要求：
>
> - 形式化规格必须精确、无歧义
> - 工具必须经过鉴定（qualified）或输出经过独立验证
> - 形式化验证的覆盖范围必须明确声明
> [来源: [DO-333 Section 2.3](https://www.rtca.org/)]

---

## 二、DO-178C 等级要求矩阵
>
> [来源: [DO-178C Table A-1 to A-10](https://www.rtca.org/)]
>
> [来源: [Ferrocene Documentation](https://ferrocene.dev/)]

DO-178C 定义五个软件等级（Software Level），从 A（灾难性失效）到 E（无安全影响）。每个等级对应不同数量的验证目标：

| 等级 | 失效条件分类 | 目标数 | 独立验证 | Rust 能力满足 |
|:---|:---|:---:|:---:|:---|
| **A** | 灾难性 (Catastrophic) | 71 | ✅ Level 1 | 需形式化验证工具链 + Ferrocene |
| **B** | 危险/严重 (Hazardous) | 69 | ✅ Level 2 | 需形式化验证工具链 + Ferrocene |
| **C** | 重大 (Major) | 62 | ✅ Level 2 | Ferrocene + 标准验证活动 |
| **D** | 轻微 (Minor) | 26 | ⚠️ Level 2 | Ferrocene + 标准验证活动 |
| **E** | 无安全影响 (No Effect) | 0 | ❌ 不需要 | 标准 Rust 工具链 |

**Rust 满足 DO-178C 目标的映射**:

```text
DO-178C 目标类别与 Rust 映射:

  软件需求过程 (A-1):
  ├── 目标1: 高层需求正确 → 需求追溯工具 + Rust 类型系统
  ├── 目标2: 高层需求准确 → 形式化规格语言 (Verus/Creusot)
  └── 目标3: 需求可验证 → #[requires]/#[ensures] 注解

  软件设计过程 (A-2):
  ├── 目标1: 架构正确 → 模块边界类型检查
  └── 目标2: 低层需求准确 → 契约驱动设计 (Creusot Pearlite)

  软件编码过程 (A-5):
  ├── 目标1: 源代码可追溯 → 编译期宏/属性系统
  ├── 目标2: 源代码准确 → 借用检查器 + 形式化验证
  ├── 目标3: 源代码可验证 → Kani/Miri/Prusti
  └── 目标4: 代码标准合规 → rustfmt + clippy + ferrocene linter

  软件验证过程 (A-6 至 A-7):
  ├── 基于需求的测试 → Kani proof harness + unit tests
  ├── 结构覆盖分析 → coverage + Miri (路径探索)
  ├── 数据耦合分析 → 借用检查器 + Send/Sync 分析
  └── 控制耦合分析 → CFG 分析 + Kani 状态空间探索
```

> **认知功能**: Rust 的类型系统和所有权模型在编译期自动满足了 DO-178C 中大量与"数据耦合"、"内存安全"相关的验证目标——这是传统 C/C++ 航空软件需要额外工具（如 Polyspace、Astrée）才能实现的。
> [来源: [DO-178C Section 6.0](https://www.rtca.org/)]
> [来源: [Ferrocene - DO-178C Compliance](https://ferrocene.dev/)]

---

## 三、DO-333 形式化方法映射
>
> [来源: [DO-333 Section 3.0](https://www.rtca.org/)]
>
> [来源: [Formal Methods in Rust - arXiv:2305.02275](https://arxiv.org/abs/2305.02275)]

DO-333 定义的三类形式化方法与 Rust 生态工具的映射关系：

```text
DO-333 形式化方法 → Rust 工具映射:

  定理证明 (Theorem Proving)
  ├── Verus      → Z3 SMT + 所有权类型系统
  ├── Creusot    → Why3 + Pearlite 规格语言
  ├── Aeneas     → Coq/Lean + 函数式翻译
  └── RefinedRust → Iris 分离逻辑 + Coq

  模型检查 (Model Checking)
  ├── Kani       → CBMC 符号执行 + Rust MIR
  ├── Miri       → MIR 解释器 + Tree Borrows
  └── Loom       → 并发状态空间枚举

  抽象解释 (Abstract Interpretation)
  ├── Prusti     → Viper 框架 + 分离逻辑
  └── TrustInSoft Analyzer → C 抽象解释 (FFI 边界)
```

### 3.1 定理证明 (Theorem Proving)
>
> [来源: [Verus - SOSP 2023](https://www.microsoft.com/en-us/research/publication/verus/)]
>
> [来源: [Creusot - FM 2022](https://doi.org/10.1007/978-3-031-15077-8_26)]

**定理证明**基于数学逻辑，通过公理和推理规则证明程序满足规格。

```text
Rust 定理证明工具对比:

  Verus:
  ├── 基础: Z3 SMT 求解器 + Rust 子集
  ├── 规格: #[spec], #[proof], #[exec] 函数
  ├── 能力: 功能正确性、终止性、并发不变量
  ├── 自动化: 高（SMT 自动推理）
  └── 局限: 不支持 unsafe、部分高级 Rust 特性

  示例:
  #[verifier::loop_body]
  pub fn binary_search(v: &Vec<u64>, x: u64) -> (r: usize)
      requires
          forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] <= v[j],
      ensures
          r == v.len() || v[r as int] >= x,
          forall|k: int| 0 <= k < r ==> v[k] < x,
  { ... }
```

```text
  Creusot:
  ├── 基础: Why3 平台 + Rust MIR
  ├── 规格: Pearlite 语言 (Rust 子集 + 逻辑扩展)
  ├── 能力: 分离逻辑证明、循环不变量、递归终止
  ├── 自动化: 中（Why3 自动证明器 + 交互式）
  └── 局限: 学习曲线陡，规格编写成本高

  Aeneas:
  ├── 基础: Lean 4 / Coq + 函数式核心提取
  ├── 规格: 手工 Coq/Lean 证明
  ├── 能力: 任意复杂度的功能正确性证明
  ├── 自动化: 低（主要手动证明）
  └── 局限: 需深厚的定理证明背景

  RefinedRust:
  ├── 基础: Iris 高阶分离逻辑 + Coq
  ├── 规格: 类型精炼 + 所有权逻辑
  ├── 能力: unsafe Rust 的形式化验证
  ├── 自动化: 低
  └── 局限: 研究原型，工具链不成熟
```

> **定理证明洞察**: 定理证明工具链提供最强的验证保证，但成本最高。在航空 A/B 级软件中，定理证明通常用于验证最核心的安全算法（如飞行控制律、故障检测逻辑）。
> [来源: [DO-333 FM.6.1 - Theorem Proving Objectives](https://www.rtca.org/)]

### 3.2 模型检查 (Model Checking)
>
> [来源: [Kani - CAV 2022](https://model-checking.github.io/kani/)]
>
> [来源: [Miri - Rust Internals](https://github.com/rust-lang/miri)]

**模型检查**自动穷举程序的状态空间，验证属性在所有可达状态下成立。

```text
Rust 模型检查工具对比:

  Kani:
  ├── 基础: CBMC (C Bounded Model Checker) + Rust MIR → GOTO-C
  ├── 方法: 有界符号执行 + SMT
  ├── 能力: panic 检测、溢出检测、未定义行为检测
  ├── 规格: #[kani::proof] + kani::any() 非确定性输入
  └── 局限: 状态空间爆炸、循环需展开、递归深度受限

  示例:
  #[kani::proof]
  fn check_rotate_left() {
      let x: u32 = kani::any();
      let n: u32 = kani::any();
      kani::assume(n < 32);
      let result = x.rotate_left(n);
      assert_eq!(result.rotate_right(n), x);
  }
```

```text
  Miri:
  ├── 基础: MIR (Mid-level IR) 解释器
  ├── 方法: 动态解释执行 + UB 检测
  ├── 能力: 栈借用违反、数据竞争、未对齐访问、UAF
  ├── 规格: 无（运行时检测）
  └── 局限: 仅检测可达路径、外部 FFI 受限、大型程序慢

  Loom:
  ├── 基础: 并发执行的所有可能调度枚举
  ├── 方法: 模型检查并发状态空间
  ├── 能力: 数据竞争、死锁、原子顺序错误
  ├── 规格: loom::model(|| { ... })
  └── 局限: 状态空间随线程数指数增长
```

> **模型检查洞察**: Kani 和 Miri 是 Rust 形式化验证生态中**最实用**的入口工具——无需规格标注即可自动发现错误，非常适合 DO-178C 中"基于需求的测试"和"结构覆盖分析"的补充验证。
> [来源: [Kani Documentation](https://model-checking.github.io/kani/)]
> [来源: [Miri Documentation](https://github.com/rust-lang/miri)]

### 3.3 抽象解释 (Abstract Interpretation)
>
> [来源: [Prusti - POPL 2022](https://www.pm.inf.ethz.ch/research/prusti.html)]
>
> [来源: [TrustInSoft Analyzer](https://trust-in-soft.com/)]

**抽象解释**通过构造程序语义的抽象逼近，在可计算性和精度之间取得平衡。

```text
Rust 抽象解释工具:

  Prusti:
  ├── 基础: Viper 验证基础设施 (分离逻辑 + SMT)
  ├── 方法: 注解驱动的演绎验证
  ├── 能力: 前置/后置条件、循环不变量、panic 自由
  ├── 规格: #[requires(...)], #[ensures(...)], #[invariant(...)]
  └── 状态: 研究工具，开发活跃度下降

  示例:
  #[requires(a < i32::MAX - b)]
  #[ensures(result == a + b)]
  fn add(a: i32, b: i32) -> i32 {
      a + b
  }
```

```text
  编译器常量传播/优化:
  ├── rustc 的 MIR 常量传播
  ├── 类型级计算 (typenum, generic-array)
  └── const generics (const N: usize)
  └── 这些可视为轻量级抽象解释

  TrustInSoft Analyzer (FFI 边界):
  ├── 基础: C 代码的抽象解释分析
  ├── 应用: Rust FFI 调用的 C 库验证
  ├── 能力: 运行时错误消除证明
  └── 局限: 不直接分析 Rust 代码
```

> **抽象解释洞察**: Prusti 的注解风格与 DO-333 的"规格即文档"理念高度契合。虽然工具成熟度不及 Kani，但其分离逻辑基础与 Rust 所有权模型在理论上有天然的同构性。
> [来源: [Viper Project](https://www.pm.inf.ethz.ch/research/viper.html)]

---

## 四、形式化目标 → 工具映射表
>
> [来源: [DO-333 FM Objectives Table](https://www.rtca.org/)]
>
> [来源: [Rust Verification Tools Survey - arXiv:2305.02275](https://arxiv.org/abs/2305.02275)]

| DO-333 目标 ID | 描述 | Rust 工具 | 验证方法 | 局限性 |
|:---|:---|:---|:---|:---|
| **FM.1.1** | 形式化方法计划 | 文档 + `#[doc]` | 过程合规 | 工具选择需论证 |
| **FM.2.1** | 软件需求的形式化规格 | Verus / Creusot | 前置/后置条件 | 需求可形式化程度 |
| **FM.2.2** | 高层需求的形式化分析 | Kani + `kani::any()` | 符号执行 | 需求抽象级别 |
| **FM.3.1** | 架构的形式化规格 | Creusot / RefinedRust | 模块契约 | Trait 边界难规格化 |
| **FM.4.1** | 低层需求的形式化规格 | Verus / Creusot | 函数契约 | 循环不变量需手工 |
| **FM.5.1** | 源代码的形式化分析 | Kani / Miri / Prusti | 符号执行 / 解释 | unsafe 代码覆盖有限 |
| **FM.6.1** | 形式化方法补充测试 | Kani proof harness | 属性验证 | 状态空间爆炸 |
| **FM.6.2** | 形式化方法补充结构覆盖 | Miri (路径探索) | 动态分析 | 非穷举 |
| **FM.6.3** | 形式化方法补充数据耦合 | 借用检查器 | 编译期分析 | 仅 Safe Rust |
| **FM.6.4** | 形式化方法补充控制耦合 | Kani CFG 分析 | 控制流验证 | 复杂控制流 |
| **FM.7.1** | 形式化验证结果正确性 | SMT 求解器日志 | 证明检查 | 求解器信任假设 |
| **FM.8.1** | 工具鉴定 | DO-330 TQL 评估 | 过程合规 | 无已鉴定 Rust 验证工具 |

> **映射要点**: Rust 编译器本身（尤其是借用检查器）可视为一种**隐式形式化验证工具**，它在编译期自动完成了 FM.6.3（数据耦合）和 FM.6.4（控制耦合）的大量验证工作——这是传统 C/C++ 航空软件无法获得的"免费"验证层。
> [来源: [DO-178C Section 6.4](https://www.rtca.org/)]
> [来源: [RustBelt - POPL 2018](https://doi.org/10.1145/3158154)]

---

## 五、认证案例研究
>
> [来源: [Rockwell Collins - Field Guidance System](https://arxiv.org/abs/1409.7643)]
>
> [来源: [DO-333 Case Studies - FAA](https://www.faa.gov/)]

### 5.1 Rockwell Collins 双通道场引导系统
>
> [来源: [Rockwell Collins AAMP7 Case Study](https://arxiv.org/abs/1409.7643)]

Rockwell Collins 的 Field Guidance System 是 DO-333 形式化方法补充的经典认证案例。该系统使用双通道架构（dual-channel）实现故障-安全（fail-safe）设计：

```text
Rockwell Collins 双通道架构:

  通道 A (Primary)          通道 B (Monitor)
  ┌──────────────┐          ┌──────────────┐
  │ 传感器输入    │          │ 传感器输入    │
  └──────┬───────┘          └──────┬───────┘
         │                         │
  ┌──────▼───────┐          ┌──────▼───────┐
  │ 控制算法      │          │ 控制算法      │
  │ (形式化验证)  │          │ (形式化验证)  │
  └──────┬───────┘          └──────┬───────┘
         │                         │
  ┌──────▼───────┐          ┌──────▼───────┐
  │ 输出驱动      │          │ 输出监控      │
  └──────────────┘          └──────┬───────┘
                                   │
                            ┌──────▼───────┐
                            │ 交叉比较器    │
                            │ (形式化规格)  │
                            └──────────────┘

  形式化验证范围:
  ├── PVS (Prototype Verification System) 证明控制算法正确性
  ├── 模型检查验证状态机无死锁
  └── 抽象解释验证数值范围安全
```

**原系统技术栈**: AAMP7 处理器、Ada/SPARK、PVS 定理证明器。

### 5.2 适配 Rust 的形式化验证方案
>
> [来源: [Ferrocene - Qualified Rust](https://ferrocene.dev/)]
>
> [来源: [Verus - SOSP 2023](https://www.microsoft.com/en-us/research/publication/verus/)]

若将 Rockwell Collins 案例适配到 Rust 技术栈：

```text
Rust 适配方案:

  通道 A (Primary)          通道 B (Monitor)
  ┌──────────────┐          ┌──────────────┐
  │ 传感器输入    │          │ 传感器输入    │
  └──────┬───────┘          └──────┬───────┘
         │                         │
  ┌──────▼───────┐          ┌──────▼───────┐
  │ no_std Rust   │          │ no_std Rust   │
  │ 控制算法      │          │ 控制算法      │
  ├──────────────┤          ├──────────────┤
  │ Verus 证明    │          │ Verus 证明    │
  │ #[requires]   │          │ #[requires]   │
  │ #[ensures]    │          │ #[ensures]    │
  └──────┬───────┘          └──────┬───────┘
         │                         │
  ┌──────▼───────┐          ┌──────▼───────┐
  │ Ferrocene     │          │ Ferrocene     │
  │ 目标代码       │          │ 目标代码       │
  └──────────────┘          └──────┬───────┘
                                   │
                            ┌──────▼───────┐
                            │ Kani 模型检查 │
                            │ 交叉比较逻辑  │
                            └──────────────┘

  验证工具链映射:
  ┌─────────────────┬─────────────────────────────┐
  │ 原技术          │ Rust 适配                    │
  ├─────────────────┼─────────────────────────────┤
  │ Ada/SPARK       │ no_std Rust + Verus         │
  │ PVS 定理证明    │ Verus + Z3 SMT              │
  │ 模型检查        │ Kani (CBMC 后端)            │
  │ 抽象解释        │ Miri + 常量传播             │
  │ 合格编译器      │ Ferrocene ( rustc 鉴定版 )   │
  └─────────────────┴─────────────────────────────┘
```

> **适配洞察**: Rust 的所有权系统提供了 Ada/SPARK 中指针安全规则（Access Type Rules）的现代化替代，而 Verus 的规格语言比 SPARK 的 Anna 注解更接近 Rust 原生语法，降低了形式化验证的学习成本。
> [来源: [SPARK Pro - AdaCore](https://www.adacore.com/about-spark)]

---

## 六、Property Preservation
>
> [来源: [DO-178C Section 6.0](https://www.rtca.org/)]
>
> [来源: [CompCert - POPL 2006](https://compcert.org/)]
>
> [来源: [Ferrocene - Source to Object Code](https://ferrocene.dev/)]

### 6.1 源代码到目标代码的性质保持
>
> [来源: [DO-178C Objectives A-5 & A-6](https://www.rtca.org/)]

DO-178C 要求验证过程必须证明：源代码中验证通过的属性在目标代码中仍然保持。这是航空认证中最具挑战性的环节之一。

```text
性质保持论证链 (Property Preservation Chain):

  源代码层 (Source)
  ├── Rust 源代码经过借用检查
  ├── 形式化验证工具证明功能属性
  └── 规格: P(src) 成立
       │
       ▼ 编译
  MIR 层 (Mid-level IR)
  ├── rustc 从 AST  lowering 到 MIR
  ├── MIR 语义保持源程序行为
  └── borrowck 在 MIR 层运行
       │
       ▼ 优化 + 代码生成
  LLVM IR 层
  ├── rustc 生成 LLVM IR
  ├── LLVM 优化管道转换 IR
  └── 每次转换需保持语义
       │
       ▼ 目标代码
  机器码层 (Object Code)
  ├── LLVM 后端生成目标架构汇编
  ├── 汇编器生成目标文件
  └── 链接器生成可执行文件

  关键问题: 如何证明 P(src) → P(obj) ?
```

### 6.2 Ferrocene 的合格编译论证
>
> [来源: [Ferrocene Documentation](https://ferrocene.dev/)]
>
> [来源: [DO-330 Tool Qualification](https://www.rtca.org/)]

Ferrocene 是 Rust 编译器 `rustc` 的合格化版本，旨在满足 DO-178C / DO-330 的工具鉴定要求。

```text
Ferrocene 合格编译器策略:

  鉴定范围:
  ├── rustc 前端 (Parser + AST + HIR + MIR)
  ├── borrowck + typeck
  ├── MIR → LLVM IR  lowering
  └── 不直接鉴定 LLVM 后端（依赖 LLVM 自身鉴定或额外验证）

  性质保持论证:
  ┌─────────────────┬────────────────────────────────────┐
  │ 层级转换        │ 保持论证                            │
  ├─────────────────┼────────────────────────────────────┤
  │ Rust → MIR      │ 形式化语义规范 (RustBelt 基础)      │
  │ MIR borrowck    │ 类型系统可靠性定理                  │
  │ MIR → LLVM IR   │ 转换器验证 + 测试套件               │
  │ LLVM 优化       │ LLVM 验证基础设施 + Ferrocene 限制  │
  │ LLVM IR → ASM   │ LLVM 后端测试 + 反汇编对比          │
  └─────────────────┴────────────────────────────────────┘

  与 CompCert 的差异:
  ┌─────────────────┬────────────────────┬────────────────────┐
  │ 维度            │ CompCert           │ Ferrocene          │
  ├─────────────────┼────────────────────┼────────────────────┤
  │ 源语言          │ C 子集 (Clight)    │ Rust (子集)        │
  │ 证明方式        │ Coq 完全形式化证明  │ 过程合规 + 测试     │
  │ 后端            │ 自研 (已证明)      │ LLVM (信任假设)    │
  │ 优化            │ 有限但已证明        │ 完整优化管道        │
  │ 鉴定状态        │ 已用于航空认证      │ 进行中 (core/alloc)│
  └─────────────────┴────────────────────┴────────────────────┘
```

> **Property Preservation 洞察**: Ferrocene 目前采用的策略是**过程合规 + 降级使用**——在 LLVM 后端尚未完全形式化的情况下，通过限制优化级别、增加测试覆盖和独立验证来弥补。这与传统 C 编译器（如 GCC/Clang）的鉴定策略类似，但 Rust 的前端（借用检查器 + MIR）提供了更强的语义保证基础。
> [来源: [Ferrocene - Qualification Strategy](https://ferrocene.dev/)]

---

## 七、工具鉴定 (DO-330)
>
> [来源: [DO-330 Standard](https://www.rtca.org/)]
>
> [来源: [Ferrocene - TQL Assessment](https://ferrocene.dev/)]

DO-330 定义了软件开发工具的鉴定要求。工具鉴定级别（TQL, Tool Qualification Level）从 TQL-1（最严格）到 TQL-5（最不严格），取决于工具失效对软件验证结果的影响。

### 7.1 TQL-1 至 TQL-5 映射
>
> [来源: [DO-330 Table T-0](https://www.rtca.org/)]

| TQL | 工具失效影响 | 适用 Rust 工具 | 鉴定要求 |
|:---|:---|:---|:---|
| **TQL-1** | 工具失效无法检测 → 灾难性 | Ferrocene (编译器) | 完整开发过程 + 独立验证 |
| **TQL-2** | 工具失效可检测 → 灾难性 | Kani / Verus (核心验证) | 完整开发过程 |
| **TQL-3** | 工具失效无法检测 → 危险 | Miri / Prusti | 部分开发过程 |
| **TQL-4** | 工具失效可检测 → 危险 | Clippy / rustfmt | 基本开发过程 |
| **TQL-5** | 工具失效无法检测 → 重大 | cargo-doc / rustdoc | 最低要求 |

### 7.2 Rust 形式化工具的鉴定路径
>
> [来源: [DO-330 Section 2.0](https://www.rtca.org/)]
>
> [来源: [Ferrocene - Tool Qualification](https://ferrocene.dev/)]

```text
Rust 工具鉴定路径:

  Ferrocene (TQL-1):
  ├── 开发过程: 符合 DO-330 要求的过程文档
  ├── 需求追溯: 从 DO-178C 目标到 rustc 功能的需求矩阵
  ├── 测试覆盖: rustc 测试套件 + Ferrocene 专用测试
  ├── 独立验证: 第三方对编译器输出的验证
  └── 鉴定状态: core (已认证), alloc (已认证), std (未认证)

  定理证明工具 (TQL-2/3):
  ├── Verus: 开源项目，无当前鉴定计划
  ├── Creusot: 学术研究工具，不适合直接鉴定
  └── 鉴定路径: 需商业支持 + 鉴定文档工程

  模型检查工具 (TQL-2/3):
  ├── Kani: AWS 支持，有鉴定可能性
  ├── Miri: Rust 官方项目，过程较规范
  └── 鉴定路径: 需求规范 + 测试套件 + 过程文档

  抽象解释工具 (TQL-3/4):
  ├── Prusti: 学术项目，维护不稳定
  └── 鉴定路径: 当前不推荐用于认证项目
```

> **工具鉴定洞察**: 当前 Rust 形式化验证生态中，**唯一具有明确鉴定路径的是 Ferrocene 编译器**。其他验证工具（Kani、Verus、Miri）虽然技术上成熟，但缺乏 DO-330 要求的完整过程文档和独立验证。对于航空认证项目，当前可行的策略是：使用 Ferrocene 编译器 + 传统测试/评审（满足 DO-178C），形式化工具作为补充证据（DO-333 FM）。
> [来源: [DO-330 Tool Qualification Guidance](https://www.rtca.org/)]

---

## 八、Ferrocene 认证范围
>
> [来源: [Ferrocene Documentation](https://ferrocene.dev/)]
>
> [来源: [Rust Reference - no_std](https://doc.rust-lang.org/reference/)]

Ferrocene 的认证采用分层策略，不同 Rust 标准库组件的认证状态不同：

```text
Ferrocene 认证分层:

  ✅ core (完全认证)
  ├── 原始类型 (i32, u64, bool, etc.)
  ├── 切片、数组、字符串核心操作
  ├── 迭代器核心 trait (Iterator, IntoIterator)
  ├── Option, Result, Ordering
  ├── 指针操作 (ptr, NonNull)
  ├── mem, alloc (原始分配器接口)
  └── 关键保证: 所有 safe API 的内存安全已验证

  ⚠️ alloc (部分认证)
  ├── Vec, String, Box
  ├── VecDeque, LinkedList
  ├── BinaryHeap, BTreeMap, BTreeSet
  └── 限制: 某些复杂集合的溢出/性能边界未完全验证

  ❌ std (未认证)
  ├── 文件系统操作 (fs)
  ├── 网络操作 (net)
  ├── 进程管理 (process)
  ├── 线程同步 (sync 中部分高级原语)
  ├── 环境变量、命令行参数 (env)
  └── 原因: 依赖于操作系统接口，行为平台相关
```

**航空航天开发影响**:

```text
 aerospace 开发策略:

  推荐: no_std + core + alloc
  ├── 使用 core 中的安全抽象
  ├── 使用 alloc 中的堆分配集合
  ├── 避免 std（或使用平台特定的 HAL）
  └── 所有 I/O 通过认证的 BSP (Board Support Package) 实现

  认证优势:
  ├── core 已认证 → 内存安全无需额外论证
  ├── borrowck 已认证 → 数据耦合/竞争自由编译期保证
  └── alloc 部分认证 → 需补充测试覆盖未验证部分

  认证缺口:
  ├── std 未认证 → 需自定义 OS 抽象层
  ├── async/await 未认证 → 同步模型优先
  └── panic_handler 需自定义 → 避免 unwind
```

> **Ferrocene 洞察**: Ferrocene 的 `core` 认证是 Rust 进入航空领域的**关键里程碑**——它意味着 Rust 的最小安全子集已经过独立机构的审查，其内存安全保证可被认证机构接受。这对于替代传统 C/C++ 航空嵌入式代码具有战略意义。
> [来源: [Ferrocene - Certification Scope](https://ferrocene.dev/)]

---

## 九、Rust 独特优势
>
> [来源: [Rust Reference - Ownership](https://doc.rust-lang.org/reference/)]
>
> [来源: [RustBelt - POPL 2018](https://doi.org/10.1145/3158154)]
>
> [来源: [Astrée - Airbus Case Study](https://www.absint.com/astree/airbus.htm)]

Rust 在航空航天安全关键软件开发中具有传统语言无法比拟的形式化优势：

```text
Rust 的隐式形式化验证层:

  编译期保证 (零成本):
  ├── 无 dangling pointers
  │   └── borrowck 确保引用生命周期有效
  ├── 无 use-after-free
  │   └── 所有权转移确保释放后无访问
  ├── 无 double-free
  │   └── 所有权唯一性确保每个值只释放一次
  ├── 无数据竞争
  │   └── Send/Sync + borrowck 确保并发安全
  ├── 无缓冲区溢出 (数组索引)
  │   └── bounds check（运行时）+ 迭代器安全（编译期）
  └── 无未初始化内存读取
      └── 编译器拒绝未初始化变量使用

  对比传统 C/C++ 航空开发:
  ┌─────────────────────┬─────────────────────┬─────────────────────┐
  │ 属性                │ C/C++ + MISRA       │ Rust (Safe)         │
  ├─────────────────────┼─────────────────────┼─────────────────────┤
  │ 内存安全            │ 编码规范 + 静态分析  │ 编译器保证 ✅       │
  │ 数据竞争            │ 人工审查 + 工具辅助  │ 编译器保证 ✅       │
  │ 空指针解引用        │ 运行时检查/断言      │ 编译器拒绝 ✅       │
  │ 缓冲区溢出          │ 工具检测 (Coverity)  │ 运行时检查/类型避免 │
  │ 未定义行为          │ 规范禁止 + 工具检测  │ 编译器/ Miri 检测   │
  │ 形式化基础          │ 弱 (C 语义复杂)      │ 强 (RustBelt 证明)  │
  └─────────────────────┴─────────────────────┴─────────────────────┘
```

**安全关键软件的成本效益**:

```text
  C/C++ 航空开发成本结构:
  ├── 编码: 30% (含 MISRA 合规)
  ├── 静态分析: 15% (Polyspace, Coverity, Astrée)
  ├── 测试: 30% (MC/DC 覆盖)
  ├── 评审: 15% (需求/设计/代码评审)
  └── 认证文档: 10%

  Rust 航空开发预期成本结构:
  ├── 编码: 35% (学习曲线 + 所有权设计)
  ├── 静态分析: 5% (编译器已覆盖大部分)
  ├── 测试: 25% (MC/DC 仍需，但基线错误更少)
  ├── 评审: 15% (不变)
  ├── 形式化验证: 10% (DO-333 补充)
  └── 认证文档: 10%

  净效益: 验证阶段成本降低，但需前期投资培训
```

> **Rust 优势洞察**: Rust 的所有权系统本质上是一个**全自动的、编译期运行的轻量级形式化验证器**。它验证的属性（内存安全、无数据竞争）恰好是航空航天软件中最难通过传统测试穷尽的属性。这意味着 Rust 程序进入形式化验证阶段时，已经排除了大量底层错误，使验证资源可以集中在功能正确性上。
> [来源: [RustBelt - POPL 2018](https://doi.org/10.1145/3158154)]
> [来源: [MISRA C Guidelines](https://misra.org.uk/)]

---

## 十、边界与缺口
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]
>
> [来源: [Rust Verification Tools Survey](https://arxiv.org/abs/2305.02275)]

尽管 Rust 在航空航天形式化验证方面具有显著优势，仍存在关键边界和缺口：

### 10.1 Trait 系统未形式化
>
> [来源: [RustBelt - Limitations](https://plv.mpi-sws.org/rustbelt/)]
>
> [来源: [Rust Reference - Traits](https://doc.rust-lang.org/reference/items/traits.html)]

```text
Trait 系统的形式化缺口:

  现状:
  ├── RustBelt 证明了基础类型系统的安全性
  ├── 但 Trait 的 coherence rules (孤儿规则) 未完全形式化
  ├── Associated types 的复杂约束未完全覆盖
  └── Generic trait bounds 的组合爆炸难以穷举

  影响:
  ├── 复杂的泛型代码难以用现有工具验证
  ├── Trait objects (dyn Trait) 的动态分发增加验证复杂度
  └── 自动化证明工具 (Verus/Kani) 对 Trait 支持有限

  缓解:
  ├── 航空代码限制泛型使用深度
  ├── 优先使用具体类型 + 有限的泛型抽象
  └── 等待 RefinedRust 等项目的 Trait 形式化进展
```

### 10.2 Unsafe Rust 缺口
>
> [来源: [The Rustonomicon](https://doc.rust-lang.org/nomicon/)]
>
> [来源: [RustBelt - Unsafe Code Guidelines](https://github.com/rust-lang/unsafe-code-guidelines)]

```text
Unsafe Rust 的形式化缺口:

  现状:
  ├── Safe Rust 的安全性由编译器保证
  ├── Unsafe Rust 的正确性依赖开发者维护不变量
  ├── 目前无工业级工具可自动验证 unsafe 块契约
  └── Miri 可检测部分 UB，但不验证功能正确性

  航空开发影响:
  ├── 嵌入式开发通常需要 unsafe (寄存器访问、DMA)
  ├── 每个 unsafe 块需要人工评审 + 文档化 SAFETY 注释
  ├── 缺乏类似 SPARK Ada 的 "safe subset" 保证
  └── Ferrocene 的认证范围限于 safe Rust

  缓解策略:
  ├── 最小化 unsafe 代码范围（隔离到 HAL 层）
  ├── 使用 RefinedRust / Aeneas 对关键 unsafe 代码形式化验证
  ├── 对 unsafe 代码使用 Kani 符号执行探索边界条件
  └── 建立 unsafe 代码评审清单（类比 MISRA C 的 Rule 1.1）
```

### 10.3 缺少 CompCert 级认证编译器
>
> [来源: [CompCert Project](https://compcert.org/)]
>
> [来源: [Ferrocene - vs CompCert](https://ferrocene.dev/)]

```text
认证编译器的差距:

  CompCert (C 语言):
  ├── Coq 完全形式化证明的编译器
  ├── 每个编译阶段 (Clight → Cminor → ... → Asm) 都有证明
  ├── 已用于多个航空认证项目
  └── 局限: 源语言是 C 子集，优化有限

  Ferrocene (Rust):
  ├── 过程合规的合格编译器
  ├── 测试 + 评审 + 独立验证
  ├── 完整 Rust 语言支持（在认证子集内）
  └── 局限: 非数学证明，依赖测试覆盖和过程信任

  差距影响:
  ├── Ferrocene 无法提供 CompCert 级的"零 bug"编译保证
  ├── 对于 A 级软件，可能需要额外的目标代码验证
  └── 解决方案: Ferrocene + 反汇编对比测试 + 独立验证器

  未来方向:
  ├── 逐步形式化 rustc 的 MIR → LLVM IR  lowering
  ├── 探索 Cranelift 作为替代后端（更简单，更易验证）
  ├── 社区推动 Rust 编译器的数学正确性证明
  └── Safety-Critical Rust Consortium (2024-03 成立) 协调工业需求与 Rust Project 合作
```

> **边界总结**: Rust 航空形式化验证的三大缺口——**Trait 系统**、**Unsafe 代码**和**认证编译器**——反映了从"理论安全"到"认证安全"的实践鸿沟。当前策略应是：在 safe Rust 子集内最大化利用编译器保证，对 unsafe 和复杂泛型代码采用保守策略并辅以人工评审和传统测试。
> [来源: [Rust Verification Roadmap](https://alastairreid.github.io/rust-verification-tools/)]

---

## 十一、来源与延伸阅读
>
> [来源: [DO-178C Standard](https://www.rtca.org/)]
>
> [来源: [Ferrocene Documentation](https://ferrocene.dev/)]

| 来源 | 可信度 | 说明 |
|:---|:---:|:---|
| [DO-178C - RTCA](https://www.rtca.org/) | ✅ 一级 | 航空软件认证核心标准 |
| [DO-333 - Formal Methods Supplement](https://www.rtca.org/) | ✅ 一级 | 形式化方法认证路径 |
| [DO-330 - Tool Qualification](https://www.rtca.org/) | ✅ 一级 | 工具鉴定标准 |
| [Ferrocene](https://ferrocene.dev/) | ✅ 一级 | 合格 Rust 编译器；ISO 26262 ASIL D / IEC 61508 SIL 3 / IEC 62304 Class C |
| [RustBelt - POPL 2018](https://doi.org/10.1145/3158154) | ✅ 一级 | Rust 类型系统形式化证明 |
| [Verus - SOSP 2023](https://www.microsoft.com/en-us/research/publication/verus/) | ✅ 一级 | Rust SMT 验证 |
| [Creusot - FM 2022](https://doi.org/10.1007/978-3-031-15077-8_26) | ✅ 一级 | Rust Why3 验证 |
| [Kani](https://model-checking.github.io/kani/) | ✅ 一级 | Rust 模型检查 |
| [Miri](https://github.com/rust-lang/miri) | ✅ 一级 | Rust UB 检测 |
| [Prusti](https://www.pm.inf.ethz.ch/research/prusti.html) | ✅ 一级 | Rust Viper 验证 |
| [Rockwell Collins Case Study](https://arxiv.org/abs/1409.7643) | ✅ 一级 | DO-333 实际应用 |
| [CompCert](https://compcert.org/) | ✅ 一级 | 认证 C 编译器 |
| [Rust Verification Tools Survey](https://arxiv.org/abs/2305.02275) | ✅ 一级 | 工具综述论文 |
| [Rust Reference](https://doc.rust-lang.org/reference/) | ✅ 一级 | 语言规范 |
| [The Rustonomicon](https://doc.rust-lang.org/nomicon/) | ✅ 一级 | Unsafe Rust 权威 |

---

```mermaid
graph TD
    subgraph "DO-178C / DO-333 Framework"
        A[DO-178C<br/>Software Levels A-E] --> B[DO-333<br/>Formal Methods Supplement]
        B --> C[Theorem Proving]
        B --> D[Model Checking]
        B --> E[Abstract Interpretation]
    end

    subgraph "Rust Ecosystem"
        C --> C1[Verus]
        C --> C2[Creusot]
        C --> C3[Aeneas]
        D --> D1[Kani]
        D --> D2[Miri]
        E --> E1[Prusti]
    end

    subgraph "Certification Infrastructure"
        F[Ferrocene<br/>Qualified Compiler] --> F1[core ✅<br/>SIL 2 / ASIL B]
        F --> F2[alloc 🟡<br/>计划中]
        F --> F3[std ❌<br/>未开始]
        G[DO-330<br/>TQL-1 to TQL-5] --> F
        H[Safety-Critical Rust<br/>Consortium] --> F
    end

    style F1 fill:#c8e6c9
    style F2 fill:#fff3e0
    style F3 fill:#ffcdd2
```

## 相关概念文件
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]

- [形式化方法](./13_formal_methods.md) — Rust 形式化验证工具概览
- [Hoare 逻辑](./15_hoare_logic.md) — 程序验证的形式化基础
- [RustBelt](./04_rustbelt.md) — Rust 类型系统的 Iris 形式化
- [Separation Logic](./07_separation_logic.md) — 分离逻辑与内存模型
- [Unsafe](../03_advanced/03_unsafe.md) — Unsafe Rust 的边界
- [并发安全](../03_advanced/01_concurrency.md) — 并发模型与数据竞争

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [DO-178C/DO-333/DO-330 - RTCA](https://www.rtca.org/), [Ferrocene](https://ferrocene.dev/)
>
> **权威来源对齐变更日志**: 2026-05-22 创建 [来源: Authority Source Sprint Batch 10]; 2026-05-22 网络对齐：Ferrocene 26.02.0 ISO 26262 ASIL B core 认证、IEC 61508 SIL 2 core 认证、Safety-Critical Rust Consortium 成立 [来源: Web Authority Alignment Sprint]

**文档版本**: 1.0
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**对应 DO-178C 版本**: DO-178C / DO-333 / DO-330
**最后更新**: 2026-05-22
**状态**: ✅ 概念文件创建完成

---

## 权威来源索引

> **[来源: [RustBelt](https://plv.mpi-sws.org/rustbelt/)]**
>
> **[来源: [Iris Project](https://iris-project.org/)]**
>
> **[来源: [POPL/PLDI 论文](https://dblp.org/db/conf/pldi/index.html)]**
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
>

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

## 十、边界测试：航空航天认证形式化方法的编译错误

### 10.1 边界测试：MISRA C 规则的 Rust 类比（编译错误）

```rust,compile_fail
fn main() {
    let mut x = 5;
    let r = &mut x;
    // ❌ 编译错误: cannot borrow `x` as mutable more than once at a time
    // MISRA C 规则禁止同一对象的多个可变别名
    let r2 = &mut x; // 违反别名规则
    *r = 10;
    *r2 = 20;
}

// 正确: Rust 编译器自动强制执行别名规则
fn fixed() {
    let mut x = 5;
    {
        let r = &mut x;
        *r = 10;
    } // r 在此释放
    {
        let r2 = &mut x;
        *r2 = 20;
    } // r2 在此释放
}
```

> **修正**: 航空航天软件标准（DO-178C、MISRA C）严格限制指针别名、动态内存分配和未定义行为。Rust 的所有权系统**在编译期自动强制执行** MISRA C 的核心规则：无数据竞争、无悬垂指针、无 use-after-free。这消除了大量需要手动审查和工具检查的代码模式。Rust 的 `unsafe` 块对应于 DO-178C 中的"需要额外验证的代码"，但 Rust 要求 unsafe 代码被 safe API 封装，形成清晰的安全边界。[来源: [DO-178C](https://en.wikipedia.org/wiki/DO-178C)] · [来源: [MISRA C](https://www.misra.org.uk/)]

### 10.2 边界测试：确定性执行与 `const fn`（编译错误）

```rust,compile_fail
const fn calculate(x: i32) -> i32 {
    // ❌ 编译错误: `println!` 不是 const 操作
    // 航空航天要求确定性执行，const fn 保证编译期可求值
    println!("calculating");
    x * 2
}

// 正确: const fn 仅使用编译期可求值操作
const fn calculate_fixed(x: i32) -> i32 {
    x * 2 // ✅ 纯计算，无副作用
}

fn main() {
    const RESULT: i32 = calculate_fixed(21); // 编译期求值
    println!("{}", RESULT);
}
```

> **修正**: 航空航天系统要求**确定性执行**——相同输入总是产生相同输出，无未定义行为，无外部状态依赖。`const fn` 限制函数只能执行编译期可求值的操作（算术、控制流、调用其他 const fn），禁止 I/O、堆分配、可变静态变量。这与 SPARK/Ada 的 pure function 或 C 的 `constexpr` 类似，但 Rust 的 `const fn` 与类型系统集成更紧密——const 值可用于类型参数（数组大小、常量泛型）。形式化验证中，const fn 对应于"全函数"（total function）——对所有输入都终止并返回结果。[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]

### 10.3 边界测试：SPARK 模式的 Rust 近似与 `no_panic`（编译错误）

```rust,compile_fail
#![no_panic]

fn safe_divide(a: i32, b: i32) -> i32 {
    // ❌ 编译错误/验证失败: 除零导致 panic，违反 no_panic
    a / b
}

fn main() {
    println!("{}", safe_divide(10, 0));
}
```

> **修正**: SPARK（Ada 的子集，用于形式化验证）通过语言子集和工具（GNATprove）保证无运行时错误。Rust 中，`no_panic` crate 通过链接时检查验证函数不 panic，但前提是代码本身不使用可能 panic 的操作。`a / b` 在 `b = 0` 时 panic，因此 `no_panic` 构建会失败。安全替代：1) `a.checked_div(b).unwrap_or(0)`（返回 `Option`）；2) 前置条件检查 `assert!(b != 0)`（但 assert 在 `no_panic` 下也失败）；3) 使用 `wrapping_div`（不 panic，但结果可能无意义）。航空软件的 Rust 应用（如 Ferrocene 项目）正在探索将 Rust 子集用于 DO-178C 认证，但完整的形式化验证工具链（如 SPARK 的 GNATprove）尚未成熟。[来源: [no_panic Crate](https://docs.rs/no-panic/)] · [来源: [DO-178C Standard](https://www.rtca.org/product/do-178c/)]

### 10.4 边界测试：MC/DC 覆盖率与短路逻辑（逻辑错误）

```rust,compile_fail
fn decision(a: bool, b: bool, c: bool) -> bool {
    // ⚠️ 逻辑注意: 短路逻辑使 MCDC 分析复杂化
    a && b || c
}

#[test]
fn test_mcdc() {
    // MC/DC 要求每个条件独立影响决策结果
    // 但由于短路，某些条件在某些路径上不被求值
    assert!(decision(true, true, false));  // a=T, b=T -> T
    assert!(!decision(false, true, false)); // a=F, c=F -> F
    assert!(decision(false, false, true));  // a=F, c=T -> T
    // 缺少 b 独立变化的测试（b=F 时 a=T, c=F → a&&b=F, F||c=F）
}
```

> **修正**: MC/DC（Modified Condition/Decision Coverage）要求证明每个条件的独立影响。短路逻辑（`&&`、`||`）使某些条件在特定路径上不求值，增加了 MC/DC 的测试用例数量。`a && b || c` 需要 4 个测试用例满足 MC/DC（比无短路的 3 个多），因为 `b` 的独立影响需要 `a = true` 才能暴露。Rust 的 `&&` 和 `||` 是短路的（与 C/Java 相同），这与 VHDL 的 `and`/`or`（无短路，所有操作数都求值）不同。形式化验证中，短路逻辑增加了路径复杂度，但也提供了优化机会（提前终止）。DO-178C 的 MC/DC 要求对安全关键软件是强制性的，Rust 的短路语义必须被测试充分覆盖。[来源: [DO-178C Standard](https://www.rtca.org/product/do-178c/)] · [来源: [MC/DC Analysis](https://en.wikipedia.org/wiki/Modified_condition/decision_coverage)]
