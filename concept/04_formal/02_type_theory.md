# Type Theory（类型论基础）

> **层级**: L4 形式化理论
> **前置概念**: [Type System](../01_foundation/04_type_system.md) · [Generics](../02_intermediate/02_generics.md) · [Traits](../02_intermediate/01_traits.md) [来源: [Wikipedia — Hindley-Milner](https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system)]
> **后置概念**: [Ownership Formalization](./03_ownership_formal.md) · [RustBelt](./04_rustbelt.md)
> **主要来源**: [Wikipedia: Type theory](https://en.wikipedia.org/wiki/Type_theory) · [Pierce 2002, *Types and Programming Languages*](https://www.cis.upenn.edu/~bcpierce/tapl/) · [Cardelli 1996, *Type Systems* (ACM Computing Surveys)](https://dl.acm.org/doi/10.1145/6041.6042)

---

> **Bloom 层级**: 分析 → 评价
**变更日志**:

- v2.0 (2026-05-13): 深度重构——定理一致性矩阵扩展至11行（带⟹推理链），新增3个反命题决策树，认知路径重构为5步递进，全章补充Wikipedia/Pierce TAPL/Cardelli引用与L1-L3层次一致性标注
- v1.0 (2026-05-12): 初始版本

---

## 一、权威定义（Definition）

### 1.1 Wikipedia 定义

> **[Wikipedia: Type theory](https://en.wikipedia.org/wiki/Type_theory)** In mathematics, logic, and computer science, a type theory is any of a class of formal systems, some of which can serve as alternatives to set theory as a foundation for mathematics. In type theory, every term has a "type", and operations are restricted to terms of a certain type.

> **[Wikipedia: Simply typed lambda calculus](https://en.wikipedia.org/wiki/Simply_typed_lambda_calculus)** The simply typed lambda calculus (λ→) is a typed interpretation of the lambda calculus with only one type constructor: → (function type). It is the canonical and simplest example of a typed programming language.

> **[Wikipedia: Hindley-Milner](https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system)** In type theory, Hindley-Milner is a classical type inference method with parametric polymorphism for the lambda calculus. The algorithm is commonly named W. [来源: [Wikipedia — Type Theory](https://en.wikipedia.org/wiki/Type_theory)]

### 1.2 Pierce *TAPL* 与 Cardelli 定义

> **[Pierce 2002, *TAPL* Ch.8-9]** A type system is a tractable syntactic method for proving the absence of certain program behaviors by classifying phrases according to the kinds of values they compute. The simply typed lambda calculus is the foundation upon which all modern static type systems are built.

> **[Pierce 2002, Ch.23]** System F (λ2) extends λ→ with universal quantification over types. This is the theoretical basis for parametric polymorphism in ML, Haskell, and Rust.

> **[Cardelli 1996, *Type Systems* (ACM Computing Surveys 28(1))]** A type system is a syntactic discipline for enforcing levels of abstraction. Type soundness — the guarantee that well-typed programs do not cause certain errors — is the central meta-theorem of type theory.

Rust 的类型系统是 **Hindley-Milner + 所有权约束 + 子类型（生命周期）** 的扩展：

```text
HM 核心:          Γ ⊢ e : τ  （上下文 Γ 下表达式 e 具有类型 τ） [来源: Pierce 2002, Ch.22] ✅
Rust 扩展:
  Γ; Σ ⊢ e : τ {Σ'}    （Σ = 所有权/借用状态）
  Γ ⊢ 'a <: 'b          （生命周期子类型）
  Γ ⊢ T: Trait          （Trait 约束）
```

---

## 二、概念属性矩阵（Attribute Matrix）

### 2.1 类型论层次矩阵

| **层次** | **系统** | **多态性** | **类型推断** | **Rust 对应** |
|:---|:---|:---|:---|:---|
| **简单类型 λ 演算** | λ→ | 无 | 无 | 无泛型的函数 |
| **参数多态（System F）** | λ2 | ∀α.τ | 无（需显式标注） | `identity::<T>` |
| **HM 类型系统** | ML | let-多态 | ✅ 完备 | 大多数局部推断 |
| **约束类型** | λc | 类型约束 | 部分 | `T: Trait` |
| **依赖类型** | λΠ | 类型依赖值 | 部分 | `const N: usize` |
| **子类型** | λ<: | 子类型关系 | 部分 | `'a: 'b` |
| **线性/仿射** | 线性 λ | 资源敏感 | 部分 | 所有权系统 |

### 2.2 Variance 矩阵

| **Variance** | **语法** | **含义** | **Rust 示例** |
|:---|:---|:---|:---|
| **协变（Covariant）** | `C<T>`: T 向上则 C<T> 向上 | 子类型方向相同 | `&'a T` 对 `'a` 协变 |
| **逆变（Contravariant）** | `C<T>`: T 向上则 C<T> 向下 | 子类型方向相反 | `fn(T)` 的参数 T 逆变 |
| **不变（Invariant）** | `C<T>`: 无子类型关系 | 必须完全匹配 | `&mut T`、`Cell<T>` |
| **双变（Bivariant）** | 任意方向 | 无实际约束 | （Rust 中无） |

### 2.3 Rust 类型的 Variance

| **类型构造器** | **对生命周期** | **对类型参数** |
|:---|:---|:---|
| `&'a T` | `'a`: 协变 | `T`: 协变 |
| `&'a mut T` | `'a`: 协变 | `T`: 不变 |
| `Box<T>` | — | `T`: 协变 |
| `Vec<T>` | — | `T`: 协变 |
| `Cell<T>` | — | `T`: 不变 |
| `fn(T) -> U` | — | `T`: 逆变, `U`: 协变 |
| `*const T` | — | `T`: 协变 |
| `*mut T` | — | `T`: 不变 |

---

## 三、形式化理论根基

> **[学术来源: Pierce 2002, *TAPL* Ch.11; Cardelli 1996]** 代数数据类型（ADT）的积与余积语义是类型论的标准结论。

```text
积类型:     struct Pair<A, B> { first: A, second: B }  ≅  A × B
余积类型:   enum Either<A, B> { Left(A), Right(B) }   ≅  A + B
单位类型:   () : 1       （单元素类型）
空类型:     ! : 0        （never）

代数等式:
  Option<A> ≅ 1 + A
  Result<A, E> ≅ A + E
  Vec<A> ≅ μX. 1 + (A × X)   （递归类型） [来源: Pierce 2002, Ch.20] ✅
```

> **[学术来源: Damas & Milner 1982 POPL; Pierce 2002, Ch.22]** 算法 W 是 HM 类型推断的经典形式化描述。

```text
算法 W 核心规则:
  [Var]   x:σ ∈ Γ           ─────────────        Γ ⊢ x : σ
  [App]   Γ ⊢ e₁ : τ → τ'   Γ ⊢ e₂ : τ           ───────────────────────────        Γ ⊢ e₁ e₂ : τ'
  [Abs]   Γ, x:τ ⊢ e : τ'   ─────────────────    Γ ⊢ λx.e : τ → τ'
  [Let]   Γ ⊢ e₁ : τ    Γ, x:gen(Γ,τ) ⊢ e₂ : τ'  ─────────────────────────────────    Γ ⊢ let x = e₁ in e₂ : τ'
Rust 扩展: 在 [Var] 和 [App] 之间插入所有权检查
```

**类型系统层次类图（Mermaid classDiagram）**: [来源: [Iris Project](https://iris-project.org/)]

```mermaid
classDiagram
    class TypeSystem {
        <<trait>>
        +well_typed()
        +type_safe()
    }

    class UntypedLambda {
        <<基线>>
        +任意自应用
        +Curry 悖论风险
    }

    class SimplyTyped {
        <<λ→>>
        +类型保持
        +终止性不保证
    }

    class SystemF {
        <<λ2>>
        +参数多态 ∀α.τ
        +单态化实例化
    }

    class SystemFOmega {
        <<λω>>
        +类型构造子抽象
        +GATs 理论基础
    }

    class DependentTypes {
        <<λΠ>>
        +值依赖类型
        +完整规范表达能力
    }

    class HMInference {
        <<算法>>
        +Principal Type
        +约束合一
    }

    class LinearTypes {
        <<资源敏感>>
        +所有权唯一
        +仿射弱化
    }

    TypeSystem <|-- SimplyTyped : 扩展
    TypeSystem <|-- UntypedLambda : 基线
    SimplyTyped <|-- SystemF : +多态
    SystemF <|-- SystemFOmega : +类型构造子
    SystemFOmega <|-- DependentTypes : +值依赖
    SystemF <|-- HMInference : 推断算法
    SimplyTyped <|-- LinearTypes : +资源敏感

    note for SystemF "Rust 泛型 <T> 的理论基础"
    note for SystemFOmega "Rust GATs 的理论基础"
    note for LinearTypes "Rust 所有权系统的理论基础"
    note for HMInference "Rust 局部类型推断的理论基础"
```

> **认知功能**: 本类图将类型论八十年演进压缩为一张层次地图——从 λ→ 到 Dependent Types 的每一步扩展都清晰可见。建议对照 Rust 实际特性（泛型、GATs、所有权）定位其理论根基。关键洞察：Rust 刻意选择位于 `System F + HM + 线性类型` 的交集，排除了不可判定的 Dependent Types 和推断困难的完整 `System Fω`。 [来源: 💡 原创分析]

> **思维表征说明**: `classDiagram` 将类型论中的**层次扩展关系**可视化——每个类型系统不是孤立的存在，而是在前一级基础上增加新能力。箭头方向表示「继承/扩展」：`λ→` 在无类型 λ 上添加类型，`System F` 在 `λ→` 上添加参数多态，`System Fω` 在 `System F` 上添加类型构造子抽象。Rust 的设计哲学是「选择足够表达力但可判定的子集」——因此 Rust 位于 `System F` + `HM` + `线性类型` 的交集，刻意排除了 `Dependent Types`（不可判定）和完整 `System Fω`（推断困难）。 [来源: Pierce 2002, *TAPL* Ch.11-30; Cardelli 1996, *Type Systems*]

---

## 四、定理推理链（Theorem Chain）

> **[学术来源: Wright & Felleisen 1994; Pierce 2002, *TAPL* Ch.8]** Progress + Preservation 是类型安全的标准证明框架。

```text
Progress:     若 ⊢ e : τ，则 e 是值，或存在 e' 使 e → e'          [来源: Pierce 2002, Ch.8] ✅
Preservation: 若 ⊢ e : τ 且 e → e'，则 ⊢ e' : τ                    [来源: Pierce 2002, Ch.8] ✅
合起来 = "类型良好的程序不会卡住（除非已终止）且保持类型"
```

### 4.1 定理一致性矩阵（11行，带⟹推理链）

> **[学术来源: Pierce 2002, *TAPL*; Cardelli 1996; Wright & Felleisen 1994]** 以下矩阵建立从 λ→ 到 Rust 扩展的完整定理依赖网络。

| **定理/引理** | **⟹ 推理链** | **前提** | **结论** | **被哪些定理依赖** | **失效条件** |
|:---|:---|:---|:---|:---|:---|
| **L1**: 简单类型 λ 演算 | λ→ 良类型性 ⟹ **类型保持（Subject Reduction）** | 项在 Γ 下良类型，β-归约一步 | 归约后项仍保持原类型 | T1（类型安全性）; L2（System F 扩展基础） | 引入非终止（`loop {}`）或运行时 panic（`unwrap()` 空值） |
| **L2**: System F 参数多态 | L1 + ∀α.τ ⟹ **Rust 泛型理论基础** | 类型变量无约束，替换保持良类型 | 零成本单态化实例化，Parametricity 成立 | T3（约束可满足性）; C2（高阶类型） | 存在类型（`dyn Trait`）引入运行时开销；GATs 高阶约束不可推断 |
| **T1**: 类型安全性 | L1 + L2 ⟹ **进展性 + 保持性** | 程序通过类型检查，无 `unsafe` | 运行时无类型错误、无 UB | C1（递归类型安全性）; 所有 Rust Safe 代码 | `unsafe` 块；FFI；`std::mem::transmute`；非终止/资源耗尽 |
| **T2**: 子类型传递性 | 偏序关系 ⟹ **trait bound 层次关系** | `'long <: 'short`，协变/逆变/不变定义清晰 | 生命周期替换安全，协变容器替换合法 | 生命周期替换、协变检查 | 逆变误用（`&mut T` 协变假设）; 循环子类型（`'a: 'b` 且 `'b: 'a` 非传递） |
| **T3**: 约束可满足性 | L2 + Trait Bound ⟹ **类型推导可判定** | `where` 子句为 Horn 子句形式，约束图无环 | 类型推导终止，主类型存在 | 所有带 Trait Bound 的泛型代码 | GATs 无界递归导致不终止；重叠 impl（E0119）; HRTB 过度约束 |
| **C1**: 递归类型 | μX.A(X) ⟹ **Rust enum 自引用** | 递归锚点（`Box<T>` 指针间接），类型方程有最小不动点 | 链表/树等递归结构类型安全，大小有限 | T1（作为类型安全子情况） | 无 `Box`/`Rc` 间接层 → 无限大小（E0072）; 循环引用导致内存泄漏 |
| **C2**: 高阶类型 | System Fω ⟹ **关联类型/高阶 Trait bound** | 类型构造子可抽象（`Vec` 作为参数），GATs 参数合法 | `Iterator<Item=T>` 归一化唯一，`for<'a>` 全称约束可解 | HKT 模拟；GATs 使用 | 关联类型重叠定义（coherence 破坏，E0119）; 归一化无限递归（E0275） |
| **L3**: 线性/仿射类型 | 资源敏感 ⟹ **Rust 所有权系统** | 每个值有唯一所有者，借用不重叠 | 无悬垂引用，无 use-after-free，无数据竞争 | T1（内存安全层面） | `unsafe` 绕过；`Rc`/`Arc` 打破唯一性；自引用结构（pinning 前） |
| **T4**: 子类型 + Variance | T2 + 构造器 Variance ⟹ **容器替换安全** | `&'a T` 对 `'a` 协变，`fn(T)` 对 T 逆变 | 子类型关系通过容器正确传播 | 所有含引用的泛型容器 | `Cell<T>` 协变假设（实际不变）; `*mut T` 协变误用（实际不变） |
| **C3**: 存在类型 | `impl Trait` / `dyn Trait` ⟹ **抽象与分发** | 返回位置单一具体类型，或 Trait 对象安全 | 隐藏实现细节，保持静态/动态分发能力 | API 设计；版本兼容性 | 多分支返回不同类型（E0746，除非 `dyn Trait`）; 非对象安全 Trait（E0038） |
| **T5**: HM 推断完备性 | L1 + 合一算法 ⟹ **Rust 局部推断** | 约束为 Hindley-Milner 片段，无显式高阶多态 | 主类型（Principal Type）存在且可自动推导 | 所有无歧义的局部变量声明 | 数值字面量多义（E0283）; `collect()` 多解（E0282）; HRTB/存在类型需标注 |

> **⟹ 一致性推理链**:
>
> **链 A（类型安全链）**: L1 (λ→ 类型保持) ⟹ L2 (System F 参数多态) ⟹ T1 (进展+保持=类型安全) ⟹ C1 (递归类型安全) / L3 (所有权安全)
>
> **链 B（子类型链）**: T2 (子类型传递性) ⟹ T4 (Variance 传播) ⟹ Rust 生命周期替换与容器协变检查
>
> **链 C（推断链）**: T5 (HM 推断完备性) ⟹ T3 (约束可满足性) ⟹ C2 (高阶类型归一化) / C3 (存在类型抽象)
>
> **跨层映射**: 本文件定理 ↔ [`00_meta/inter_layer_map.md`](../00_meta/inter_layer_map.md) §3.1 "L1-L4 形式化映射" · §4.2 "类型系统一致性"

---

## 五、反命题决策树（Counter-proposition Decision Trees）

> **[学术来源: Cardelli 1996, §5; Pierce 2002, Ch.8]** 类型安全的边界是类型论的核心教学点。

### 5.1 反命题 1: "类型安全保证无运行时错误"

> 语义/运行时层 — 类型安全排除的是**类型错误**和**未定义行为**，不保证终止性、资源充足性或 FFI 安全。 [来源: [RustBelt Project](https://plv.mpi-sws.org/rustbelt/)]

```mermaid
graph TD
    P["命题: 类型安全保证无运行时错误"] --> Q1{"程序是否终止?"}
    Q1 -->|否| F1["反例: `loop {}` 或递归无基准<br/>→ 非终止是类型正确的行为<br/>→ 类型系统不保证终止性"]
    Q1 -->|是| Q2{"是否资源耗尽?"}
    Q2 -->|是| F2["反例: `vec![0; usize::MAX]` 或栈溢出<br/>→ 类型正确但运行时 panic/abort<br/>→ 资源不在类型论管辖范围"]
    Q2 -->|否| Q3{"是否使用 FFI / unsafe?"}
    Q3 -->|是| F3["反例: `unsafe` 块或 extern C 调用<br/>→ 可引入任意 UB，类型系统已弃权"]
    Q3 -->|否| Q4{"是否调用 unwrap / expect?"}
    Q4 -->|是| F4["反例: `Option::unwrap` on None → panic<br/>→ panic 是安全 Rust 的受控崩溃"]
    Q4 -->|否| T1["定理局部成立: Safe Rust 无 UB<br/>✅ Progress + Preservation 保证"]

    style F1 fill:#f66
    style F2 fill:#f66
    style F3 fill:#f66
    style F4 fill:#f96
    style T1 fill:#6f6
```

> **认知功能**: 此决策树将「类型安全」的边界逐层剥离，训练读者区分「类型错误」与「非类型错误」（非终止、资源耗尽、unsafe）。建议遇到 panic 时沿树回溯，判断问题是否属于类型系统管辖范围。关键洞察：Progress + Preservation 仅保证良类型程序「不卡住」，不保证终止性、资源充足或 FFI 安全。 [来源: 💡 原创分析]

**四层分析**:

| **层面** | **反例** | **性质** |
|:---|:---|:---|
| 语义 | `loop {}` 非终止 | 类型正确，但无进展性（Progress 假设程序可归约） |
| 运行时 | 栈溢出、堆耗尽 | 类型正确，资源约束超出类型系统表达力 |
| 编译期 | `unsafe` / FFI | 显式绕过类型系统，类型安全承诺失效 |
| 工程 | `unwrap()` panic | Safe Rust 内的受控崩溃，非 UB 但属错误 |

### 5.2 反命题 2: "所有类型系统都是 sound 的"

> 历史/理论层 — 类型系统的 soundness 是元定理，需证明，非天然成立。Curry 悖论等历史案例展示了无类型或弱类型系统的内在不一致性。

```mermaid
graph TD
    P["命题: 所有类型系统都是 sound 的"] --> Q1{"是否包含自指构造?"}
    Q1 -->|是| F1["反例: Curry 悖论（无类型 λ 演算）<br/>→ Y 组合子允许自应用，导致逻辑不一致<br/>→ 无类型系统无法阻止"]
    Q1 -->|否| Q2{"是否允许任意递归类型?"}
    Q2 -->|是| F2["反例: `μX.X → ⊥` 构造罗素式悖论<br/>→ 朴素递归类型系统可能不一致<br/>→ 需正性/负性检查"]
    Q2 -->|否| Q3{"是否包含 `null` 作为所有类型的子类型?"}
    Q3 -->|是| F3["反例: Java/C# 的 billion-dollar mistake<br/>→ `null` 是任意引用类型的值，调用方法时 NPE<br/>→ 类型系统声称安全，实际运行时崩溃"]
    Q3 -->|否| Q4{"是否经验证（Progress + Preservation 证明）?"}
    Q4 -->|否| N1["状态: soundness 未知<br/>→ 如早期 Rust 生命周期系统（pre-NLL）存在已知 soundness bug"]
    Q4 -->|是| T1["定理成立: 类型系统 sound<br/>✅ 元定理已证明，如 λ→ / System F / RustBelt"]

    style F1 fill:#f66
    style F2 fill:#f66
    style F3 fill:#f66
    style N1 fill:#69f
    style T1 fill:#6f6
```

> **认知功能**: 该决策树以四个历史/理论反例说明 soundness 不是天然属性，而是需证明的元定理。建议在设计或评估新类型系统扩展时，逐一排查自指构造、任意递归类型和 `null` 子类型三类风险。关键洞察：Curry 悖论与 billion-dollar mistake 是类型论教科书级漏洞——它们解释了为什么现代语言必须限制自指并消除 null。 [来源: 💡 原创分析]

**历史反例对照**:

| **系统** | **声称** | **实际缺陷** | **教训** |
|:---|:---|:---|:---|
| 无类型 λ 演算 | 表达任意计算 | Curry 悖论导致不一致 | 需要类型来限制自指 |
| Java `null` | 引用类型安全 | `NullPointerException` 无处不在 | `null` 破坏 soundness 边界 |
| 早期 Scala（2.x） | 类型安全 | 高阶类型与路径依赖类型存在 soundness hole | 复杂类型系统需形式化验证 |
| pre-NLL Rust | 借用检查安全 | 某些合法模式被错误拒绝（不完备），存在悬垂借用误放过 | 生命周期算法需持续验证 |

### 5.3 反命题 3: "子类型总是安全的"

> 类型论层 — 子类型的安全性高度依赖 Variance 的正确标注。协变/逆变/不变的混淆是真实类型系统漏洞的常见来源。

```mermaid
graph TD
    P["命题: 子类型总是安全的"] --> Q1{"容器中类型参数是协变?"}
    Q1 -->|是| Q2{"是否涉及可变写入?"}
    Q2 -->|是| F1["反例: 数组协变 + 写入 = 类型污染<br/>→ Java `Object[] obj = new String[1]; obj[0] = Integer.valueOf(1)`<br/>→ `ArrayStoreException`，协变数组是不安全的"]
    Q2 -->|否| T1["只读场景协变安全<br/>✅ 如 `&'a T` 对 T 协变"]
    Q1 -->|否| Q3{"容器中类型参数是逆变?"}
    Q3 -->|是| F2["反例: 逆变误用导致不接受预期类型<br/>→ `fn(Animal)` 是 `fn(Dog)` 的子类型<br/>→ 但将 `fn(Dog)` 变量赋 `fn(Animal)` 值是安全的（Rust 正确）"]
    Q3 -->|否| Q4{"容器中类型参数是不变?"}
    Q4 -->|是| F3["反例: 强行替换不变类型导致 UB<br/>→ `Cell<T>` 要求 T 不变，若假设协变：<br/>→ 写入短生命周期引用 → 悬垂指针 / use-after-free"]
    Q4 -->|否| T2["双变（Bivariant）无约束<br/>✅ Rust 中无此场景"]

    style F1 fill:#f66
    style F2 fill:#f66
    style F3 fill:#f66
    style T1 fill:#6f6
    style T2 fill:#6f6
```

> **认知功能**: 此决策树将协变/逆变/不变理论转化为可操作的类型安全检查清单。建议在设计泛型容器或阅读标准库源码时，据此验证 Variance 标注是否与内部可变性一致。关键洞察：协变加可变写入等于类型污染（Java 数组的设计缺陷），而 `Cell<T>` 和 `&mut T` 的不变性正是 Rust 为此付出的安全成本。 [来源: 💡 原创分析]

**Variance 安全性分析**:

| **Variance** | **安全条件** | **典型反例** |
|:---|:---|:---|
| 协变 | 只读访问，无内部可变性 | Java 协变数组 + 写入 → `ArrayStoreException` |
| 逆变 | 仅作为输入位置（函数参数） | 错误标注为协变 → 接受非法参数 |
| 不变 | 涉及内部可变性或读写双向 | 强行协变/逆变替换 → 悬垂引用、类型混淆 |
| 混合（`fn(T) -> U`） | T 逆变且 U 协变 | T 协变或 U 逆变标注错误 → 调用链类型破坏 |

---

## 六、认知路径（Cognitive Path）

> **[原创分析]** · **[Pierce 2002, *TAPL*]** 五步递进，每步标注 L1-L3 概念锚点。 💡 原创分析

### Step 1: "为什么需要类型？"

**L1 映射**: [`../01_foundation/04_type_system.md`](../01_foundation/04_type_system.md) §1

```text
直觉: 无类型程序 ≈ 所有数据都是原始位模式，解释取决于运行时上下文
形式化: 类型是"编译期谓词"——在运行前证明"此操作对此数据合法"
关键: λ→ 阻止 Y 组合子和 Curry 悖论的方式——类型自指非法
```

**锚点**: `3 + "hello"` 在无类型语言中可能拼接或崩溃，在 Rust 中是编译错误 E0277。

### Step 2: "类型和集合的关系？"

**L1-L2 映射**: [`../01_foundation/04_type_system.md`](../01_foundation/04_type_system.md) §2 ADT 代数语义 · [`../02_intermediate/01_traits.md`](../02_intermediate/01_traits.md) §1 Type Class [来源: [PLDI 2025 — Tree Borrows](https://plv.mpi-sws.org/rustbelt/tree-borrows/)]

```text
直觉: 类型 ≈ 值的集合（粗略类比）
区别: 类型有操作限制；类型论可作为数学基础替代集合论（Martin-Löf）
代数: struct (A, B) = A × B; enum A | B = A + B; fn(A) -> B = A → B
```

### Step 3: "λ 演算怎么表达计算？"

**L4 映射**: 本节核心——λ→ 是类型系统的根基。

```text
直觉: λx.x + 1 ≈ "一个函数，输入 x，返回 x+1"
加类型: λx:i32. x + 1 : i32 → i32
关键限制: λx:τ. x x ❌ 非法！x 的类型不能同时是 τ 和 τ → σ
→ 这正是 λ→ 阻止自指和 Curry 悖论的方式
```

### Step 4: "多态是什么意思？"

**L2-L4 映射**: [`../02_intermediate/02_generics.md`](../02_intermediate/02_generics.md) §4.1 System F · 本节 L2

```text
System F 形式化:  identity = ΛT. λx:T. x : ∀T. T → T
Parametricity:    任何 fn f<T>(x: T) -> T 只能是恒等或发散
                  类型完全决定行为！（Wadler 1989, Theorems for Free）
Rust 约束:        纯多态过于受限，加入 Trait Bound
                  fn max<T: Ord>(a: T, b: T) -> T  （约束多态）
```

### Step 5: "Rust 的类型系统在哪一层？"

**L1-L4 综合映射**:

```text
Rust 类型系统 = λ→ + System F + HM + λ<: + 线性类型 + 约束类型

层次堆叠:
  ┌─────────────────────────────────────┐
  │ 线性/所有权类型   (L4: 本节 L3)      │  ← Rust 独有：资源敏感
  ├─────────────────────────────────────┤
  │ 约束类型 λc      (L4: 本节 T3)       │  ← T: Trait
  ├─────────────────────────────────────┤
  │ 子类型 λ<:       (L4: 本节 T2/T4)    │  ← 'a: 'b
  ├─────────────────────────────────────┤
  │ 依赖类型（有限）  (L4: Const Generics)│  ← const N: usize
  ├─────────────────────────────────────┤
  │ System F λ2      (L4: 本节 L2)       │  ← <T> 泛型
  ├─────────────────────────────────────┤
  │ HM 推断          (L4: 本节 T5)       │  ← let x = vec![1,2,3]
  ├─────────────────────────────────────┤
  │ 简单类型 λ→      (L4: 本节 L1)       │  ← fn add(x: i32, y: i32) -> i32
  └─────────────────────────────────────┘
```

**认知脚手架**:

- **类比**: 类型系统像"建筑的抗震规范"——不限制设计创意，但确保在地震（错误输入）时不倒塌（UB）。
- **反直觉点**: 很多人觉得类型是"束缚"，类型论证明它是"自动化推理引擎"——编译器替你证明了程序无类型错误。
- **形式化过渡**: "类型匹配" → "合一算法" → "HM 推断" → "System F / Parametricity" → "线性类型/所有权"。

---

## 七、层次一致性标注（Layer Consistency Annotations）

### 7.1 L4 → L1 下行映射

| **L4 形式化概念** | **L1 基础文件** | **映射精度** | **标注** |
|:---|:---|:---|:---|
| L1: λ→ 简单类型 | [`../01_foundation/04_type_system.md`](../01_foundation/04_type_system.md) §4.5 T3 | **精确** | L1 的 T3 类型安全定理依赖 L4 的 λ→ 基础 |
| T5: HM 推断完备性 | [`../01_foundation/04_type_system.md`](../01_foundation/04_type_system.md) §4.4 T2 | **精确** | L1 T2（类型推断完备性）是 T5 的工程实例 |
| T1: 进展+保持=类型安全 | [`../01_foundation/04_type_system.md`](../01_foundation/04_type_system.md) §4.5 T3 | **精确** | L1 T3 是 T1 在 Rust 中的受限形式 |
| L3: 线性/所有权类型 | [`../01_foundation/01_ownership.md`](../01_foundation/01_ownership.md) | **精确** | L1 所有权规则是 L3 线性类型的工程化 |

### 7.2 L4 → L2 下行映射

| **L4 形式化概念** | **L2 进阶文件** | **映射精度** | **标注** |
|:---|:---|:---|:---|
| L2: System F 参数多态 | [`../02_intermediate/02_generics.md`](../02_intermediate/02_generics.md) §4.1 | **精确** | L2 泛型形式化 = System F 的单态化实现 |
| T3: 约束可满足性 | [`../02_intermediate/02_generics.md`](../02_intermediate/02_generics.md) §4.4 | **精确** | L2 约束多态是 T3 的工程语法 |
| C2: 高阶类型/GATs | [`../02_intermediate/02_generics.md`](../02_intermediate/02_generics.md) §2.3 | **精确** | L2 GATs 是 C2 的 Rust 语法 |
| T2: 子类型传递性 | [`../02_intermediate/01_traits.md`](../02_intermediate/01_traits.md) §4.3 | **近似** | L2 Supertrait 传递依赖 T2 子类型理论 |
| C3: 存在类型 | [`../02_intermediate/01_traits.md`](../02_intermediate/01_traits.md) §4.4 | **精确** | L2 `impl Trait` / `dyn Trait` = C3 的 Rust 语法 |

### 7.3 L2/L1 → L4 上行映射

| **L1/L2 工程概念** | **L4 理论来源** | **映射路径** |
|:---|:---|:---|
| `fn<T>(x: T) -> T` | L2: System F `∀T. T → T` | L2 泛型 §4.1 → L4 L2 |
| `T: Trait` | T3: 约束可满足性 | L2 约束 §4.4 → L4 T3 |
| `'a: 'b` | T2: 子类型传递性 | L1 生命周期 → L4 T2 |
| `&mut T` 不变 | T4: Variance | L1 借用 → L4 T4 |
| `Option<T>` / `Result<T, E>` | C1: 递归类型 + ADT | L1 ADT §4.1 → L4 C1 |
| `impl Trait` | C3: 存在类型 | L2 Trait §4.4 → L4 C3 |

---

## 八、思维导图

```mermaid
graph TD
    A[Type Theory 类型论] --> B[λ 演算层次]
    A --> C[多态性]
    A --> D[ADT 代数语义]
    A --> E[Variance]
    A --> F[Rust 扩展]
    A --> G[类型安全]

    B --> B1[λ→ 简单类型]
    B --> B2[System F 参数多态]
    B --> B3[System Fω 高阶类型]

    C --> C1[Parametric: <T>]
    C --> C2[Ad hoc: Trait]
    C --> C3[Subtype: 'a: 'b]

    D --> D1[Product: struct]
    D --> D2[Coproduct: enum]
    D --> D3[Recursive: Vec]

    E --> E1[Covariant]
    E --> E2[Contravariant]
    E --> E3[Invariant]

    F --> F1[Ownership]
    F --> F2[Lifetimes]
    F --> F3[Trait Bounds]

    G --> G1[Progress]
    G --> G2[Preservation]
    G --> G3[Subject Reduction]
```

> **认知功能**: 本思维导图提供类型论六大知识模块的导航索引，将 λ 演算、多态性、ADT 代数语义、Variance、Rust 扩展和类型安全整合为一张定位地图。建议在学习或查阅时以此为「你在哪」的参照系。关键洞察：六轴并非独立——λ→ 是根基，System F 和 HM 是 Rust 泛型的双支柱，线性类型是所有权唯一性的理论来源。 [来源: 💡 原创分析]

---

## 九、示例与反例

### 9.1 Variance 示例

```rust,compile_fail
// ✅ 协变: &'static str 可转为 &'a str
fn covariant<'a>(s: &'static str) -> &'a str { s }

// ✅ 逆变: 接受 Animal 的函数可传给需要 Dog 的位置
fn takes_animal(f: fn(Animal)) {}
fn dog_handler(d: Dog) {}
// takes_animal(dog_handler); // ✅ fn(Dog) 是 fn(Animal) 的子类型

// ❌ 不变: &mut T 不能协变
fn invariant<'a, 'b: 'a>(r: &'b mut &'static str) -> &'b mut &'a str {
    r  // ❌ 编译错误: &mut 对生命周期不变
}

```

### 9.2 递归类型边界

```rust
// ✅ 正确: 递归类型需 Box 间接层
enum List<T> {
    Cons(T, Box<List<T>>),
    Nil,
}

// ❌ 错误: 直接自引用导致无限大小
// enum BadList<T> {
//     Cons(T, BadList<T>),  // E0072: recursive type has infinite size
//     Nil,
// }
```

### 9.3 类型论到 Rust 的映射精度评估

| 类型论 | Rust 对应 | **映射精度** | 偏差说明 |
|:---|:---|:---|:---|
| 和类型 (A + B) | `enum { A, B }` | **精确** | 一对一 [来源: Pierce 2002, Ch.11] ✅ |
| 积类型 (A × B) | `struct { a: A, b: B }` | **精确** | 一对一 [来源: Pierce 2002, Ch.11] ✅ |
| 函数类型 (A → B) | `fn(A) -> B` | **近似** | Rust 函数有 effects（如 panic） [来源: Pierce 2002, Ch.9] 💡 |
| 全称量词 (∀α.A) | `fn<T>(x: T)` | **近似** | 受 Trait Bounds 约束限制 [来源: Pierce 2002, Ch.23] 💡 |
| 存在类型 (∃α.A) | `impl Trait` / `dyn Trait` | **近似** | `impl` 隐藏，`dyn` 动态 [来源: Pierce 2002, Ch.24] 💡 |
| 递归类型 (μα.A) | 递归 enum/struct | **近似** | 需 `Box` 解除无限大小 [来源: Pierce 2002, Ch.20] 💡 |
| 依赖类型 | Const Generics（有限） | **部分** | 仅限编译期常量 [来源: 原创分析] ⚠️ |

### 9.3 HRTB 与全称量词的形式化语义

> **[学术来源: System F_ω]** · **[Rust Reference: Higher-Ranked Trait Bounds]** `for<'a> T: Trait<'a>` 是 Rust 类型系统中**高阶 Trait Bound**的语法，其形式化语义对应于一阶逻辑中的受限全称量词。✅

**语法与逻辑对应**

| Rust 语法 | 逻辑形式 | 类型论对应 | 限制 |
|:---|:---|:---|:---|
| `for<'a> T: Trait<'a>` | `∀'a. Trait(T, 'a)` | System F 的 `∀α.τ`（α 限定为生命周期）| 仅量化生命周期，不量化类型 |
| `fn foo<'a>(x: &'a T)` | `λ'a.λx:&'a T. ...` | HM 推断 + 区域参数 | 生命周期参数不参与类型推断的多解歧义 |
| `dyn for<'a> Fn(&'a T)` | `∃f. ∀'a. f: Fn(&'a T)` | 存在类型 + 全称量化 | 对象安全限制：不能出现在返回位置 |

**与 System F 的精确关系**

System F（Girard 1972, Reynolds 1974）的通用类型 `∀α.τ` 允许量化任意类型变量。Rust 的 HRTB 是 System F 的一个**受限子集**： [来源: [POPL 2019 — Stacked Borrows](https://dl.acm.org/doi/10.1145/3290380)]

```text
System F:        ∀α.τ   where α ∈ Type
Rust HRTB:       ∀'a.τ  where 'a ∈ Lifetime (Region)

关键区别:
  1. 量化域不同: System F 量化类型；HRTB 量化生命周期
  2. 消去规则不同: System F 的 ∀ 消去是类型应用（τ[σ/α]）
                   HRTB 的 ∀ 消去是生命周期求解（'a ⊆ 'b）
  3. 可满足性: System F 的类型 inhabitation 不可判定
                HRTB 的生命周期约束可满足性是多项式时间可判定的
```

**可满足性分析**

生命周期约束系统是一个**偏序约束系统**：

```text
约束形式:  'a: 'b   （'a 包含 'b，即 'a 比 'b 长）
求解算法:  图可达性（Graph Reachability）
复杂度:    O(V + E)  其中 V = 生命周期变量数, E = 约束数

对比:
  HM 类型推断:     O(n³) 最坏情况（n = 表达式大小）
  GATs 约束求解:   不可判定（无限制时）
  HRTB 约束求解:   O(V + E) — 多项式时间
```

> **关键洞察**: HRTB 的**可判定性**来自生命周期量化域的结构性——生命周期是偏序关系上的点，而非任意类型。这使得 Rust 可以在编译期高效求解高阶生命周期约束，而无需面对 System F 的不可判定性噩梦。

> **深入阅读**: 生命周期约束求解详见 [`03_lifetimes.md`](../01_foundation/03_lifetimes.md) §4；泛型约束系统详见 [`02_generics.md`](../02_intermediate/02_generics.md) §4.1。

---

## 十、知识来源与国际课程对齐

| **论断/来源** | **核心内容** | **对应章节** | **可信度** |
|:---|:---|:---|:---|
| [Wikipedia: Type theory](https://en.wikipedia.org/wiki/Type_theory) | 类型论通用定义 | §1.1 | ✅ |
| [Wikipedia: Simply typed lambda calculus](https://en.wikipedia.org/wiki/Simply_typed_lambda_calculus) | λ→ 基础定义 | §1.1 | ✅ |
| [Pierce 2002, *TAPL*](https://www.cis.upenn.edu/~bcpierce/tapl/) Ch.8-9,11,15,20,22-24 | λ→, System F, HM, 子类型, 递归类型, 存在类型 | 贯穿全章 | ✅ |
| [Cardelli 1996, *Type Systems*](https://dl.acm.org/doi/10.1145/6041.6042) | 类型系统综述与 soundness 定义 | §1.3, §5.2 | ✅ |
| Wright & Felleisen 1994 | Progress + Preservation 证明框架 | §4 | ✅ |
| Wadler 1989, *Theorems for Free* | Parametricity 参数性定理 | §6 Step 4 | ✅ |
| Damas & Milner 1982 POPL | 算法 W 与 Principal Type | §3 | ✅ |
| [RustBelt: POPL 2018](https://plv.mpi-sws.org/rustbelt/) | Rust 类型系统形式化验证 | §4 L3 | ✅ |
| [CMU 17-363: PL Pragmatics](https://www.cs.cmu.edu/~aldrich/courses/17-363/) | 类型规则、类型安全 | 课程对齐 | ✅ |

---

> **过渡: L4 → L2**
>
> System F 的 `Λα.λx:α. x` 在 Rust 中写作 `fn identity<T>(x: T) -> T { x }`，但 System F 无法表达生命周期——后者需要 **System F_ω + 区域类型** 的扩展。HRTB 的 `for<'a>` 是全称量词 `∀` 在类型约束中的具体实现，而 GATs 则用类型族（type family）模拟了 Haskell 中缺失的 HKT。
>
> Rust 的具体实现见 [`../02_intermediate/02_generics.md`](../02_intermediate/02_generics.md)（泛型与单态化）与 [`../02_intermediate/01_traits.md`](../02_intermediate/01_traits.md)（Trait 作为 Type Class 的变体）。

## 十一、相关概念链接

| 概念 | 文件 | 关系 |
|:---|:---|:---|
| 类型系统 | [`../01_foundation/04_type_system.md`](../01_foundation/04_type_system.md) | 类型论的应用（L1 映射） |
| 泛型 | [`../02_intermediate/02_generics.md`](../02_intermediate/02_generics.md) | 参数多态的应用（L2 映射） |
| Trait | [`../02_intermediate/01_traits.md`](../02_intermediate/01_traits.md) | Type Class 的应用（L2 映射） |
| 线性逻辑 | [`./01_linear_logic.md`](./01_linear_logic.md) | 形式化同层（所有权理论来源） |
| 所有权形式化 | [`./03_ownership_formal.md`](./03_ownership_formal.md) | 类型规则的扩展 |
| RustBelt | [`./04_rustbelt.md`](./04_rustbelt.md) | 验证框架 |
| 范式矩阵 | [`../05_comparative/03_paradigm_matrix.md`](../05_comparative/03_paradigm_matrix.md) | 类型系统谱系 |

---

## 十之一、补充：Dependent Type、Const Generics 与 HKT workaround

> **[Wikipedia: Dependent type]** · **[Wikipedia: Higher-kinded type]** · **[RFC 2000: Const Generics]** · **[Rust Reference: Const Generics]** 本节补充 Rust 类型系统与更高级类型论概念的关系，以及 Rust 在表达力边界上的工程妥协。✅ [来源: [POPL 2018 — RustBelt](https://dl.acm.org/doi/10.1145/3158154)]

### 10.1 Dependent Type 与 Const Generics 的关系

**Dependent type**（依赖类型）是**值可出现在类型中**的类型系统。在完整依赖类型（如 Coq、Agda、Idris）中，类型可以依赖项（term）的值：

```text
Idris:  Vec : Nat -> Type -> Type
       Vec 3 Int  -- 长度为 3 的 Int 向量，类型本身包含值 3
```

Rust 的 **Const Generics**（常量泛型，Rust 1.51+ 稳定）是依赖类型的**有限子集**：

```rust,ignore
// ✅ Rust: 值（常量）出现在类型参数中
struct Array<T, const N: usize> {
    data: [T; N],  // N 是编译期常量，属于类型的一部分
}

let a: Array<i32, 3> = Array { data: [1, 2, 3] };
let b: Array<i32, 4> = Array { data: [1, 2, 3, 4] };
// Array<i32, 3> 和 Array<i32, 4> 是不同的类型
```

| 维度 | 完整依赖类型（Idris/Coq） | Rust Const Generics |
|:---|:---|:---|
| **值的范围** | 任意项（包括递归函数结果） | 仅 `usize`、`bool`、`char` 等少量原始类型的常量表达式 |
| **类型检查时机** | 编译期 + 运行期（依赖值可能运行时才知） | 仅编译期（常量求值器 `miri` 子集） |
| **表达能力** | 可证明任意性质（对应 Curry-Howard 的完整对应） | 可表达数组长度、位掩码尺寸等工程场景 |
| **类型相等判定** | 依赖项的归约（可能不可判定） | 常量表达式的编译期求值（可判定） |
| **与unsafe关系** | 无 unsafe 概念（证明即程序） | 仍依赖 unsafe 进行底层优化 |

> **关键洞察**: Const Generics 不是"依赖类型的弱化版"，而是**工程上的精确裁剪**——它保留了依赖类型在系统编程中最有用的子集（数组长度、缓冲区大小、维度参数），同时避免了完整依赖类型带来的编译期不可判定性问题。
>
> **来源**: [Wikipedia: Dependent type] · [RFC 2000: Const Generics] · [Idris 文档: Dependent Types]

### 10.1b Const Generics 的形式化演进（1.89+）

> **[来源: Rust 1.89 Release Notes; RFC 2000]** Rust 1.89 稳定了 `_` 推断 const generics 参数，使常量参数获得与类型参数同等的 HM 推断能力。

**`_` 推断的形式化意义**:

```text
此前（1.89 之前）:
  let arr: Array<i32, 3> = Array::new();
  // 必须显式提供 const generic 参数 3

1.89 之后:
  let arr = Array::new();  // 编译器从上下文推断 _: usize = 3
  // HM 推断扩展到常量级别: Γ ⊢ e : Array<i32, N>, N 由约束求解确定
```

这对应类型论中的**隐式参数推断（implicit argument synthesis）**：常量参数 `N` 现在与类型参数 `T` 一样，可由局部约束图推导。

**单态化语义（Monomorphization）**:

Const Generics 的单态化与类型泛型一致，但常量参数在实例化时**被求值为具体值**： [来源: [Wikipedia — Separation Logic](https://en.wikipedia.org/wiki/Separation_logic)]

```text
泛型定义:   struct Array<T, const N: usize> { ... }
实例化:     Array<i32, 3>
单态化后:   struct Array_i32_3 { data: [i32; 3] }

常量参数在单态化时完全消解:
  Array<i32, {2+1}>  ──求值──→  Array<i32, 3>  ──单态化──→  Array_i32_3
```

**Const Trait Impl（`~const Trait` / `[const]`）**:

> **[来源: RFC 3762; Tracking Issue #143874]** ⚠️ nightly only

`const fn` 中无法调用泛型 trait 方法，因为编译器无法确认该 impl 是否在 const context 中有效。`~const Trait`（演进中语法可能变为 `[const] Trait`）允许标记某些 trait impl 为"const 安全"：

```rust,ignore
// 推测性语法（ nightly 迭代中）
impl const Add for MyInt {  // 此 impl 在 const context 中可用
    fn add(self, other: Self) -> Self { ... }
}

const fn sum<T: ~const Add>(a: T, b: T) -> T {  // T 必须支持 const Add
    a + b  // ✅ 合法：在 const fn 中调用泛型 + 运算符
}
```

形式化上，`~const Trait` 将 trait 约束系统从**二值**（实现/未实现）扩展为**三值**（实现 + const 安全 / 实现但仅运行时 / 未实现），增加了约束求解的复杂度。

**与 System Fω 的关联**:

Const Generics 将 Rust 的类型系统从 System F（类型抽象）向 **System Fω 的受限形式**推进：

```text
System F:     Λα.λx:α. x          —— 类型抽象（泛型）
System Fω:    Λα:*→*. λx:α Int. x  —— 类型构造器抽象（HKT）
Rust Const:   Λn:usize. λx:[i32;n]. x  —— 值级抽象（依赖类型子集）
```

Rust 目前不支持 HKT，但 Const Generics 在另一个维度上扩展了表达能力：**值 → 类型**的依赖性。 [来源: [Wikipedia — Affine Logic](https://en.wikipedia.org/wiki/Affine_logic)]

> **跨层映射**: 本文件 Const Generics 形式化 ↔ [`../02_intermediate/02_generics.md`](../02_intermediate/02_generics.md) §5.7 "Const Generics 进阶用法" · [`../07_future/05_rust_version_tracking.md`](../07_future/05_rust_version_tracking.md) §3.3 "`_` 推断 const generics"

### 10.2 Higher-Kinded Types（HKT）的缺失与 workaround

**HKT** 允许类型构造器（如 `Vec`、`Option`）本身作为类型参数：

```text
Haskell:  fmap :: Functor f => (a -> b) -> f a -> f b
          -- f 不是类型，而是类型构造器（kind: * -> *）
```

Rust **当前不支持 HKT**。`Vec<T>` 中的 `Vec` 不能作为泛型参数传递。

#### Workaround 1: GATs 模拟类型族

```rust
// 用 GATs 模拟 "类型构造器作为关联类型"
trait TypeConstructor {
    type Apply<T>;  // 模拟 * -> *
}

struct VecConstructor;
impl TypeConstructor for VecConstructor {
    type Apply<T> = Vec<T>;
}

struct OptionConstructor;
impl TypeConstructor for OptionConstructor {
    type Apply<T> = Option<T>;
}
```

#### Workaround 2: 宏生成单态代码

```rust,ignore
macro_rules! monomorphic_map {
    ($container:ty, $f:expr, $input:expr) => {{
        $input.into_iter().map($f).collect::<$container>()
    }};
}

let v: Vec<i32> = monomorphic_map!(Vec<i32>, |x| x + 1, vec![1, 2, 3]);
```

#### Workaround 3: 显式 trait 层级（Rust 标准库做法）

```rust,ignore
// 不为 "所有 Functor" 抽象，而为每种容器单独定义方法
impl<T> Vec<T> { fn map<U>(self, f: impl FnMut(T) -> U) -> Vec<U> { ... } }
impl<T> Option<T> { fn map<U>(self, f: impl FnOnce(T) -> U) -> Option<U> { ... } }
impl<T> Result<T, E> { fn map<U>(self, f: impl FnOnce(T) -> U) -> Result<U, E> { ... } }
```

> **形式化视角**: HKT 需要 **System F_ω**（允许类型抽象的类型构造器）。Rust 的类型系统接近 System F_ω + 区域类型，但出于**单态化实现的复杂性**和**类型推断的实用性**，HKT 尚未加入语言。GATs 提供了约 80% 的 HKT 表达能力，剩余 20%（高阶类型抽象）需通过宏或显式实例化弥补。
>
> **来源**: [Wikipedia: Higher-kinded type] · [TAPL Ch.29] · [Rust Internals: HKT Discussion] · [RFC 1598: GATs]

### 10.3 线性逻辑与所有权类型的 Curry-Howard 对应

**Curry-Howard 对应**断言：**命题 = 类型，证明 = 程序**。在线性逻辑与 Rust 的语境下： [来源: [Wikipedia — Linear Logic](https://en.wikipedia.org/wiki/Linear_logic)]

| 线性逻辑 | Rust 类型/构造 | 逻辑语义 | 计算语义 |
|:---|:---|:---|:---|
| **A ⊗ B** | `(A, B)` | A 且 B（同时成立，各自独立） | 元组：两个资源同时存在 |
| **A ⊸ B** | `fn(A) -> B` | A 蕴含 B | 函数：消耗 A，产生 B |
| **A ⊕ B** | `enum { A, B }` | A 或 B（二者择一） | 枚举：只有一个变体激活 |
| **!A** | `impl Copy` | A 可任意复制 | Copy：资源可 weakening/contraction |
| **切消（Cut）** | `let y = f(x)` | 中间命题的消除 | 函数调用：求值后替换为结果 |
| **证明网（Proof Net）** | 控制流图（CFG） | 无冗余的规范证明形式 | 编译器的中间表示（MIR） |

```text
Curry-Howard 在 Rust 中的具体实例:

  命题 "若拥有 String，则可获得其长度"
    ⟺ 类型 `fn(String) -> usize`
    ⟺ 程序 `fn len(s: String) -> usize { s.len() }`

  证明的正确性（类型检查通过）
    ⟺ 程序的资源安全（borrow checker 通过）
```

> **来源**: [Wikipedia: Curry–Howard correspondence] · [Wadler 2015 · Propositions as Types] · [Girard 1989 · Proofs and Types] · [TAPL Ch.9]

---

### 10.4 Pierce *TAPL* Ch.15 子类型与 Rust 生命周期映射

#### 子类型的核心规则（TAPL Ch.15）

子类型关系 `S <: T`（S 是 T 的子类型）的核心规则集：

**自反与传递**：

```text
S-Refl:  ───────────    S-Trans:  S <: U   U <: T
         S <: S                   ─────────────────
                                          S <: T
```

**函数子类型（逆变-协变）**：

```text
S-Arrow:  T₁ <: S₁    S₂ <: T₂
          ─────────────────────────────
          (S₁ → S₂) <: (T₁ → T₂)
```

> **关键洞察**：函数类型的参数位置是**逆变**的（contravariant），返回位置是**协变**的（covariant）。这对应 Rust 中 `fn(T) -> U` 的参数 `T` 必须满足逆变约束。

**记录子类型（宽度子类型化）**：

```text
S-Record:  {lᵢ: Tᵢ} <: {lᵢ: Sᵢ}  若 ∀i. Tᵢ <: Sᵢ
           ─────────────────────────────────────────
           {lᵢ: Tᵢ, lⱼ: Tⱼ} <: {lᵢ: Sᵢ}  （字段多的是子类型）
```

#### Rust 生命周期作为子类型关系

Rust 中生命周期 `'a: 'b` 的语法表示 **"'a 至少和 'b 一样长"**，即 `'a` 是 `'b` 的子类型：

```rust
// ✅ 生命周期子类型的直观理解
fn example<'a, 'b>(x: &'a i32, y: &'b i32)
where
    'a: 'b,  // 'a 是 'b 的子类型：'a 活得比 'b 长
{
    let z: &'b i32 = x;  // ✅ 合法：&'a i32 <: &'b i32（协变）
}
```

**生命周期方差与子类型**：

| 类型构造器 | 参数位置 | 方差 | 子类型方向 |
|:---|:---|:---:|:---|
| `&'a T` | `'a` | 协变 | `'long <: 'short` ⟹ `&'long T <: &'short T` |
| `&'a T` | `T` | 协变 | `U <: V` ⟹ `&'a U <: &'a V` |
| `&'a mut T` | `'a` | 协变 | `'long <: 'short` ⟹ `&'long mut T <: &'short mut T` |
| `&'a mut T` | `T` | 不变 | `U <: V` ⟹ `&'a mut U` ⋈ `&'a mut V`（无子类型关系） |
| `fn(T) -> U` | `T` | 逆变 | `V <: U` ⟹ `fn(U) -> R <: fn(V) -> R` |
| `fn(T) -> U` | `U` | 协变 | `R <: S` ⟹ `fn(T) -> R <: fn(T) -> S` |
| `Box<T>` | `T` | 协变 | `U <: V` ⟹ `Box<U> <: Box<V>` |
| `*const T` | `T` | 协变 | `U <: V` ⟹ `*const U <: *const V` |
| `*mut T` | `T` | 不变 | `U <: V` ⟹ `*mut U` ⋈ `*mut V` |

```rust,ignore
// ✅ 协变示例：&'a T 对 'a 和 T 都是协变
fn covariant_lifetime<'long: 'short>(x: &'long i32) -> &'short i32 {
    x  // &'long i32 <: &'short i32，因为 'long <: 'short
}

fn covariant_type(x: &'static String) -> &'static str {
    x.as_str()  // String <: str ⟹ &'static String 可安全转为 &'static str
}

// ❌ 不变示例：&mut T 对 T 是不变的
fn invariant<'a>(x: &'a mut String) -> &'a mut str {
    // x  // E0308: 无法将 &mut String 转为 &mut str
    // &mut T 对 T 是不变的，因为写入操作要求类型完全匹配
    unimplemented!()
}
```

> **定理**：Rust 的生命周期子类型化是**结构子类型**（structural subtyping）的特例——子类型关系由类型的结构（生命周期参数）决定，而非名义（name-based）。
>
> **来源**: [Pierce · Types and Programming Languages Ch.15–16] · [Rust Reference: Subtyping] · [Rust Nomicon: Variance] · [Wikipedia: Subtyping]

---

## 十二、待补充与演进方向（TODOs）

- [x] **TODO**: 补充 Dependent type 与 Const Generics 的关系 —— 优先级: 中 —— 已完成 §10.1
- [x] **TODO**: 补充 Higher-Kinded Types 的缺失与 workaround —— 优先级: 中 —— 已完成 §10.2
- [x] **TODO**: 补充线性逻辑（Linear Logic）与所有权类型的 Curry-Howard 对应 —— 优先级: 高 —— 已完成 §10.3
- [x] **TODO**: 补充 Pierce *TAPL* Ch.15 子类型章节的完整规则与 Rust 生命周期映射 —— 优先级: 中 —— 已完成 §10.4

> **过渡: L4 → L3**
>
> 类型论中的全称量词 `∀α.τ` 在 Rust 中就是 `fn foo<T>(x: T)`，存在量词 `∃α.τ` 就是 `impl Trait`。类型论不是抽象数学——它是编译器类型检查算法的理论基础。理解 HM 算法如何推导 `let x = 5` 的类型，就是理解 `rustc` 如何处理 90% 的日常代码。
>
> 编译器实现见 [`../03_advanced/04_macros.md`](../03_advanced/04_macros.md)（宏扩展与类型检查交互）与 [`../06_ecosystem/01_toolchain.md`](../06_ecosystem/01_toolchain.md)（编译流程）。

> **过渡: L4 → L7**
>
> Rust 的类型系统正在向更丰富的方向发展：Effects System 将副作用编码为类型约束、Generic Const Items 允许常量作为类型参数、Type Alias Impl Trait 简化存在类型的表达。这些演进不是偶然——它们都是类型论中已有概念的工程化落地。
>
> 演进方向见 [`../07_future/03_evolution.md`](../07_future/03_evolution.md)（语言演进路线图）与 [`../07_future/02_formal_methods.md`](../07_future/02_formal_methods.md)（形式化方法的未来）。
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rustonomicon](https://doc.rust-lang.org/nomicon/)
>
> **权威来源对齐变更日志**: 2026-05-19 补全权威来源标注（Rust Reference、TRPL、Rustonomicon、RFCs、学术论文） [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
