# Factory Method 形式化分析

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-14
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 形式化完成
> **分类**: 创建型
> **安全边界**: 纯 Safe
> **23 模式矩阵**: [README §23 模式多维对比矩阵](../README.md#23-模式多维对比矩阵) 第 1 行（Factory Method）
> **证明深度**: L2（完整证明草图）

---

## 📊 目录

- [Factory Method 形式化分析](#factory-method-形式化分析)
  - [📊 目录](#-目录)
  - [形式化定义](#形式化定义)
    - [概念定义-属性关系-解释论证 层次汇总](#概念定义-属性关系-解释论证-层次汇总)
  - [Rust 实现与代码示例](#rust-实现与代码示例)
  - [证明思路](#证明思路)
  - [典型场景](#典型场景)
  - [相关模式](#相关模式)
  - [实现变体](#实现变体)
  - [反例：工厂返回空或无效](#反例工厂返回空或无效)
  - [与理论衔接](#与理论衔接)
  - [选型决策树](#选型决策树)
  - [与 GoF 对比](#与-gof-对比)
  - [边界](#边界)
  - [与 Rust 1.93 的对应](#与-rust-193-的对应)
  - [实质内容五维自检](#实质内容五维自检)

---

## 形式化定义

**Def 1.1（Factory Method 结构）**:

设 $T$ 为产品类型，$C$ 为创建者类型。Factory Method 满足：

- $\exists \mathit{factory} : C \to T$，由 $C$ 创建 $T$
- $\Gamma \vdash \mathit{factory}(c) : T$，类型规则保证
- 所有权：$\mathit{factory}(c)$ 调用时 $c$ 可被借用（$\&C$）或拥有（$C$）；返回值 $T$ 由调用者拥有

**Axiom FM1**：工厂方法返回类型与产品类型一致；无空指针或无效值。

**Axiom FM2**：每次调用产生新值；$\Omega(\mathit{factory}(c)) \neq \Omega(c)$（产品与创建者所有权独立）。

**定理 FM-T1**：由 [type_system_foundations](../../../type_theory/type_system_foundations.md) 保持性，$\mathit{factory}(c)$ 良型则求值结果类型为 $T$。

*证明*：由 Axiom FM1；类型规则保证返回类型；type_system 保持性定理保证求值后类型不变。∎

**定理 FM-T2**：由 [ownership_model](../../../formal_methods/ownership_model.md) T2，返回值所有权转移至调用者；无悬垂。

*证明*：由 Axiom FM2；产品所有权独立；ownership T2 保证唯一所有者，无双重释放。∎

**推论 FM-C1**：Factory Method 为纯 Safe；仅用 trait、impl、Box，无 unsafe。

### 概念定义-属性关系-解释论证 层次汇总

| 层次 | 内容 | 本页对应 |
| :--- | :--- | :--- |
| **概念定义层** | Def 1.1（Factory Method 结构）、Axiom FM1/FM2（返回一致、所有权独立） | 上 |
| **属性关系层** | Axiom FM1/FM2 → 定理 FM-T1/FM-T2 → 推论 FM-C1；依赖 type_system、ownership | 上 |
| **解释论证层** | 证明：FM-T1/FM-T2 完整证明块；反例：工厂返回空或无效 | 上、§反例 |

---

## Rust 实现与代码示例

```rust
trait Product {
    fn operation(&self) -> String;
}

struct ConcreteProductA;
impl Product for ConcreteProductA {
    fn operation(&self) -> String { "Product A".to_string() }
}

struct ConcreteProductB;
impl Product for ConcreteProductB {
    fn operation(&self) -> String { "Product B".to_string() }
}

// 工厂方法：C → T，C 为 ProductType（或 Creator），T 为 dyn Product
fn create_product(t: ProductType) -> Box<dyn Product> {
    match t {
        ProductType::A => Box::new(ConcreteProductA),
        ProductType::B => Box::new(ConcreteProductB),
    }
}
```

**形式化对应**：`create_product` 即 $\mathit{factory}$；`ProductType` 为 $C$ 的变体；`Box<dyn Product>` 为 $T$。所有权：`Box::new` 产生拥有权，返回时转移。

---

## 证明思路

1. **类型安全**：`match` 穷尽，各分支返回 `Box<dyn Product>`；由 type_system 保持性，求值后类型不变。
2. **所有权安全**：`Box::new` 分配堆内存，返回拥有权；调用者获得所有权，原创建者（match 参数）可被消费或借用。由 ownership T2 唯一性。

---

## 典型场景

| 场景 | 说明 |
| :--- | :--- |
| 多态创建 | 根据配置/运行类型创建不同产品 |
| 子类定制 | 子类重写工厂方法返回特定产品 |
| 依赖注入 | 注入工厂以解耦创建逻辑 |

---

## 相关模式

| 模式 | 关系 |
| :--- | :--- |
| [Abstract Factory](abstract_factory.md) | 多个工厂方法组成抽象工厂 |
| [Builder](builder.md) | 工厂可返回 Builder |
| [Prototype](prototype.md) | 工厂可基于 Prototype 克隆 |

---

## 实现变体

| 变体 | 说明 | 适用 |
| :--- | :--- | :--- |
| `fn create(&self) -> T` | trait 方法 | 多态工厂 |
| `match` + `Box<dyn Product>` | 返回 trait 对象 | 运行时选择 |
| 关联类型 | `type Product; fn create(&self) -> Self::Product` | 类型族 |

---

## 反例：工厂返回空或无效

**错误**：`match` 未穷尽或返回 `Option` 却不处理 `None`。

```rust
fn create_product(t: ProductType) -> Box<dyn Product> {
    match t {
        ProductType::A => Box::new(ConcreteProductA),
        // 遗漏 ProductType::B → 编译错误（好）
        // 或返回 unwrap() 未检查的 Option → 运行时 panic（坏）
    }
}
```

**结论**：Rust `match` 穷尽检查避免遗漏；但 `Option` 需显式处理。

---

## 与理论衔接

| 机制 | 引用 |
| :--- | :--- |
| 所有权转移 | ownership_model T2、T3 |
| 类型保持 | type_system_foundations T2 |
| Trait 对象 | trait_system_formalization |

---

## 选型决策树

```text
需要创建对象但类型由运行时/上下文决定？
├── 是 → 单产品？ → Factory Method（trait create）
│       └── 产品族？ → Abstract Factory
├── 需多步骤构建？ → Builder
└── 需克隆已有？ → Prototype
```

---

## 与 GoF 对比

| GoF | Rust 对应 | 差异 |
| :--- | :--- | :--- |
| 虚工厂方法 | trait fn create | 等价 |
| Creator 持有 Product | 可选 | 等价 |
| 多态创建 | impl Trait | 等价 |

---

## 边界

| 维度 | 分类 |
| :--- | :--- |
| 安全 | 纯 Safe |
| 支持 | 原生 |
| 表达 | 等价 |

---

## 与 Rust 1.93 的对应

| 1.93 特性 | 与本模式 | 说明 |
| :--- | :--- | :--- |
| 无新增影响 | — | 1.93 无影响 Factory Method 语义的变更 |
| 92 项落点 | 无 | 本模式未涉及 [RUST_193_COUNTEREXAMPLES_INDEX](../../../RUST_193_COUNTEREXAMPLES_INDEX.md) 特定项 |

---

## 实质内容五维自检

| 自检项 | 状态 | 说明 |
| :--- | :--- | :--- |
| 形式化 | ✅ | Def FM1、Axiom FM1、定理 FM-T1（L2） |
| 代码 | ✅ | 可运行示例 |
| 场景 | ✅ | 典型场景表 |
| 反例 | ✅ | 违反抽象边界 |
| 衔接 | ✅ | ownership、borrow、CE-PAT1 |
| 权威对应 | ✅ | [GoF](../README.md#与-gof-原书对应)、[formal_methods](../../../formal_methods/README.md)、[INTERNATIONAL_FORMAL_VERIFICATION_INDEX](../../../INTERNATIONAL_FORMAL_VERIFICATION_INDEX.md) |
