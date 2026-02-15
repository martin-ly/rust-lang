# Template Method 形式化分析

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-14
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 形式化完成
> **分类**: 行为型
> **安全边界**: 纯 Safe
> **23 模式矩阵**: [README §23 模式多维对比矩阵](../README.md#23-模式多维对比矩阵) 第 22 行（Template Method）
> **证明深度**: L2（完整证明草图）

---

## 📊 目录

- [Template Method 形式化分析](#template-method-形式化分析)
  - [形式化定义](#形式化定义)
    - [概念定义-属性关系-解释论证 层次汇总](#概念定义-属性关系-解释论证-层次汇总)
  - [Rust 实现与代码示例](#rust-实现与代码示例)
  - [证明思路](#证明思路)
  - [与继承对比](#与继承对比)
  - [典型场景](#典型场景)
  - [相关模式](#相关模式)
  - [实现变体](#实现变体)
  - [反例：覆盖 template 破坏骨架](#反例覆盖-template-破坏骨架)
  - [选型决策树](#选型决策树)
  - [边界](#边界)
  - [与 Rust 1.93 的对应](#与-rust-193-的对应)
  - [实质内容五维自检](#实质内容五维自检)

---

## 形式化定义

**Def 1.1（Template Method 结构）**:

设 $T$ 为模板类型。Template Method 满足：

- $\exists \mathit{template\_op} : T \to R$，定义算法骨架
- $\mathit{template\_op}$ 内部调用 $h_1(), h_2(), \ldots$ 钩子
- 子类实现 $h_i$；Rust 用 trait 默认方法 + override

**Axiom TM1**：骨架不变；钩子可定制。

**Axiom TM2**：钩子可有无默认实现；`impl` 可选择性覆盖。

**定理 TM-T1**：trait 默认方法：`fn template(&self) { self.hook1(); self.hook2(); }`；由 [trait_system_formalization](../../../type_theory/trait_system_formalization.md)。

*证明*：由 Axiom TM1、TM2；trait 默认方法即骨架；required 方法即钩子；impl 选择性覆盖；无 OOP 继承，组合优于继承。∎

**引理 TM-L1（骨架不变）**：`template` 方法体固定；各 `impl` 仅提供 `step_i`，不修改 `template` 调用顺序。

*证明*：由 Def 1.1；trait 默认方法为固定实现；`impl` 不能覆盖 `template` 除非显式写 `fn template`；可约定仅覆盖钩子。∎

**推论 TM-C1**：Template Method 与 [expressive_inexpressive_matrix](../../05_boundary_system/expressive_inexpressive_matrix.md) 表一致；$\mathit{ExprB}(\mathrm{TemplateMethod}) = \mathrm{Approx}$。

**反例**：若钩子内调用 `template` 形成递归，需保证终止；否则栈溢出。

### 概念定义-属性关系-解释论证 层次汇总

| 层次 | 内容 | 本页对应 |
| :--- | :--- | :--- |
| **概念定义层** | Def 1.1（Template Method 结构）、Axiom TM1/TM2（骨架不变、钩子可覆盖） | 上 |
| **属性关系层** | Axiom TM1/TM2 → 定理 TM-T1、引理 TM-L1 → 推论 TM-C1；依赖 trait、expressive_inexpressive_matrix | 上 |
| **解释论证层** | 证明：TM-T1、TM-L1；反例：覆盖 template 破坏骨架、递归未终止 | 上、§反例 |

---

## Rust 实现与代码示例

```rust
trait Algorithm {
    fn template(&self) -> String {
        let mut s = String::new();
        s.push_str(&self.step1());
        s.push_str(&self.step2());
        s
    }
    fn step1(&self) -> String;
    fn step2(&self) -> String;
}

struct ImplA;
impl Algorithm for ImplA {
    fn step1(&self) -> String { "A1".into() }
    fn step2(&self) -> String { "A2".into() }
}

struct ImplB;
impl Algorithm for ImplB {
    fn step1(&self) -> String { "B1".into() }
    fn step2(&self) -> String { "B2".into() }
}

// 使用
let a = ImplA;
assert_eq!(a.template(), "A1A2");
let b = ImplB;
assert_eq!(b.template(), "B1B2");
```

**形式化对应**：`template` 即 $\mathit{template\_op}$；`step1`、`step2` 即钩子。

---

## 证明思路

1. **骨架**：`template` 为默认方法，调用 `step1`、`step2`；各 impl 提供具体实现。
2. **类型安全**：trait 解析保证 `step1`、`step2` 存在；由 trait_system。

---

## 与继承对比

GoF 用继承；Rust 用 trait + 默认方法，无继承，组合优于继承。

---

## 典型场景

| 场景 | 说明 |
| :--- | :--- |
| 算法骨架 | 排序、搜索、序列化流程 |
| 生命周期钩子 | 初始化/清理、before/after |
| 测试框架 | setup/teardown、用例执行流程 |

### 典型场景完整示例：数据导入流水线

**场景**：不同数据源（CSV、JSON）导入，骨架固定：验证 → 解析 → 转换 → 持久化；各步骤可定制。

```rust
trait DataImport {
    fn run(&self, raw: &str) -> Result<u64, String> {
        let validated = self.validate(raw)?;
        let parsed = self.parse(&validated)?;
        let transformed = self.transform(parsed)?;
        self.persist(&transformed)
    }
    fn validate(&self, raw: &str) -> Result<String, String>;
    fn parse(&self, s: &str) -> Result<Vec<Record>, String>;
    fn transform(&self, records: Vec<Record>) -> Result<Vec<Record>, String>;
    fn persist(&self, records: &[Record]) -> Result<u64, String>;
}

struct Record { id: u64, name: String }

struct CsvImport;
impl DataImport for CsvImport {
    fn validate(&self, raw: &str) -> Result<String, String> {
        if raw.is_empty() { Err("empty".into()) } else { Ok(raw.into()) }
    }
    fn parse(&self, s: &str) -> Result<Vec<Record>, String> {
        Ok(s.lines().enumerate().map(|(i, l)| Record { id: i as u64, name: l.into() }).collect())
    }
    fn transform(&self, r: Vec<Record>) -> Result<Vec<Record>, String> { Ok(r) }
    fn persist(&self, r: &[Record]) -> Result<u64, String> { Ok(r.len() as u64) }
}

// 使用：let imp = CsvImport; imp.run("a\nb\nc")?;
```

**形式化对应**：`run` 即 $\mathit{template\_op}$；`validate`、`parse`、`transform`、`persist` 为钩子。

---

## 相关模式

| 模式 | 关系 |
| :--- | :--- |
| [Strategy](strategy.md) | 同为算法定制；Template 为骨架，Strategy 为替换 |
| [Factory Method](../01_creational/factory_method.md) | 工厂方法可为模板钩子 |
| [Observer](observer.md) | 钩子可触发观察者 |

---

## 实现变体

| 变体 | 说明 | 适用 |
| :--- | :--- | :--- |
| trait 默认方法 | `fn template(&self)` 调用钩子 | 标准实现 |
| 宏 | 生成模板骨架 | 减少样板 |
| 组合 + 策略 | 钩子由 Strategy 提供 | 更灵活 |

---

## 反例：覆盖 template 破坏骨架

**错误**：某 impl 覆盖 `template` 而非钩子，破坏算法骨架。

```rust
impl Algorithm for BadImpl {
    fn template(&self) -> String { "hardcoded".into() }  // 忽略 step1/step2
}
```

**后果**：违反 Axiom TM1；钩子定制失效，失去模板方法意义。

---

## 选型决策树

```text
需要算法骨架、步骤可定制？
├── 是 → trait 默认方法？ → Template Method
├── 需完全替换算法？ → Strategy
├── 需工厂创建？ → Factory Method（可作钩子）
└── 需状态转换？ → State
```

---

## 边界

| 维度 | 分类 |
| :--- | :--- |
| 安全 | 纯 Safe |
| 支持 | 原生 |
| 表达 | 近似（无继承） |

---

## 与 Rust 1.93 的对应

| 1.93 特性 | 与本模式 | 说明 |
| :--- | :--- | :--- |
| 无新增影响 | — | 1.93 无影响 Template Method 语义的变更 |
| 92 项落点 | 无 | 本模式未涉及 [RUST_193_COUNTEREXAMPLES_INDEX](../../../RUST_193_COUNTEREXAMPLES_INDEX.md) 特定项 |

---

## 实质内容五维自检

| 自检项 | 状态 | 说明 |
| :--- | :--- | :--- |
| 形式化 | ✅ | Def 1.1、定理 TM-T1（L2） |
| 代码 | ✅ | 可运行示例 |
| 场景 | ✅ | 典型场景表 |
| 反例 | ✅ | 覆盖 template 破坏骨架 |
| 衔接 | ✅ | trait 默认方法、ownership |
| 权威对应 | ✅ | [GoF](../README.md#与-gof-原书对应)、[formal_methods](../../../formal_methods/README.md)、[INTERNATIONAL_FORMAL_VERIFICATION_INDEX](../../../INTERNATIONAL_FORMAL_VERIFICATION_INDEX.md) |
