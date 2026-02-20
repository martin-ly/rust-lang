# Visitor 形式化分析

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **分类**: 行为型
> **安全边界**: 纯 Safe
> **23 模式矩阵**: [README §23 模式多维对比矩阵](../README.md#23-模式多维对比矩阵) 第 23 行（Visitor）
> **证明深度**: L2（完整证明草图）

---

## 📊 目录

- [Visitor 形式化分析](#visitor-形式化分析)
  - [📊 目录](#-目录)
  - [形式化定义](#形式化定义)
    - [概念定义-属性关系-解释论证 层次汇总](#概念定义-属性关系-解释论证-层次汇总)
  - [Rust 实现与代码示例](#rust-实现与代码示例)
    - [方式一：match 单分发（推荐）](#方式一match-单分发推荐)
    - [方式二：trait 多态](#方式二trait-多态)
  - [证明思路](#证明思路)
  - [与 GoF 对比](#与-gof-对比)
  - [完整场景示例：AST 美化打印（Visitor）](#完整场景示例ast-美化打印visitor)
  - [典型场景](#典型场景)
  - [相关模式](#相关模式)
  - [实现变体](#实现变体)
  - [反例：新增变体遗漏访问](#反例新增变体遗漏访问)
  - [选型决策树](#选型决策树)
  - [边界](#边界)
  - [与 Rust 1.93 的对应](#与-rust-193-的对应)
  - [实质内容五维自检](#实质内容五维自检)

---

## 形式化定义

**Def 1.1（Visitor 结构）**:

设 $E$ 为元素类型（AST/节点），$V$ 为访问者类型。Visitor 满足：

- $\exists \mathit{visit} : V \times E \to R$
- $E$ 为代数数据类型
- 双重分发：$e.\mathit{accept}(v)$ 调用 $v.\mathit{visit}(e)$；或单分发：`match e` 后调用 `v.visit_X(e)`

**Axiom VI1**：访问者可访问所有节点变体；可扩展新操作。

**定理 VI-T1**：Rust 用 `match` 单分发或 trait 模拟；无 OOP 风格双重分发，表达为近似。

*证明*：由 Axiom VI1；`match` 穷尽所有变体，编译期检查；新 Visitor 实现 trait 即可扩展；无 OOP 虚函数双重分发，故为近似。∎

**引理 VI-L1（穷尽匹配）**：`match e { ... }` 必须覆盖 $E$ 所有变体；新增变体需新增分支，否则编译错误。

*证明*：由 Rust 类型系统；穷尽匹配为语言保证；[type_system_foundations](../../../type_theory/type_system_foundations.md) 保持性。∎

**推论 VI-C1**：Visitor 与 [expressive_inexpressive_matrix](../../05_boundary_system/expressive_inexpressive_matrix.md) 表一致；$\mathit{ExprB}(\mathrm{Visitor}) = \mathrm{Approx}$。

**反例**：若 `match` 漏分支，编译错误；若用 `dyn Trait` 做双重分发，需对象安全，`Self` 返回等可能违规。

### 概念定义-属性关系-解释论证 层次汇总

| 层次 | 内容 | 本页对应 |
| :--- | :--- | :--- |
| **概念定义层** | Def 1.1（Visitor 结构）、Axiom VI1（访问所有变体、可扩展） | 上 |
| **属性关系层** | Axiom VI1 → 定理 VI-T1、引理 VI-L1 → 推论 VI-C1；依赖 type、expressive_inexpressive_matrix | 上 |
| **解释论证层** | 证明：VI-T1、VI-L1；反例：新增变体遗漏访问、match 漏分支 | 上、§反例 |

---

## Rust 实现与代码示例

### 方式一：match 单分发（推荐）

```rust
enum Expr {
    Int(i32),
    Add(Box<Expr>, Box<Expr>),
}

trait Visitor {
    fn visit_int(&mut self, n: i32);
    fn visit_add(&mut self, a: &Expr, b: &Expr);
}

fn visit<V: Visitor>(v: &mut V, e: &Expr) {
    match e {
        Expr::Int(n) => v.visit_int(*n),
        Expr::Add(a, b) => {
            visit(v, a);
            visit(v, b);
            v.visit_add(a, b);
        }
    }
}

struct PrintVisitor;
impl Visitor for PrintVisitor {
    fn visit_int(&mut self, n: i32) { println!("{}", n); }
    fn visit_add(&mut self, _: &Expr, _: &Expr) { println!("+"); }
}
```

### 方式二：trait 多态

```rust
trait Node {
    fn accept<V: Visitor>(&self, v: &mut V);
}

impl Node for Expr {
    fn accept<V: Visitor>(&self, v: &mut V) {
        visit(v, self);
    }
}
```

**形式化对应**：`visit` 即 $\mathit{visit}$；`match` 分支对应各变体的处理。

---

## 证明思路

1. **穷尽**：`match` 必须覆盖所有变体；新变体需新分支，编译期检查。
2. **可扩展**：新 Visitor 实现 trait；无需修改 Expr。

---

## 与 GoF 对比

GoF 双重分发：`e.accept(v)` 内调用 `v.visit(e)`，根据 $e$ 与 $v$ 类型选择。Rust 用 `match` 单分发更自然，风格不同但等价。

---

## 完整场景示例：AST 美化打印（Visitor）

**场景**：对 Expr AST 做多种遍历；PrettyPrintVisitor 输出可读字符串。

```rust
enum Expr { Int(i32), Add(Box<Expr>, Box<Expr>) }

trait ExprVisitor<T> {
    fn visit_int(&mut self, n: i32) -> T;
    fn visit_add(&mut self, a: &Expr, b: &Expr, la: T, lb: T) -> T;
}

fn visit<V: ExprVisitor<String>>(v: &mut V, e: &Expr) -> String {
    match e {
        Expr::Int(n) => v.visit_int(*n),
        Expr::Add(a, b) => {
            let la = visit(v, a);
            let lb = visit(v, b);
            v.visit_add(a, b, la, lb)
        }
    }
}

struct PrettyPrint;
impl ExprVisitor<String> for PrettyPrint {
    fn visit_int(&mut self, n: i32) -> String { n.to_string() }
    fn visit_add(&mut self, _: &Expr, _: &Expr, la: String, lb: String) -> String {
        format!("({} + {})", la, lb)
    }
}

// 使用：visit(&mut PrettyPrint, &Expr::Add(Box::new(Expr::Int(1)), Box::new(Expr::Int(2))))
// 输出："(1 + 2)"
```

**形式化对应**：`visit` 即 $\mathit{visit}$；`match` 穷尽变体；由 Axiom VI1、引理 VI-L1。

---

## 典型场景

| 场景 | 说明 |
| :--- | :--- |
| AST 遍历 | 编译器、解释器、代码生成 |
| 文档/树遍历 | DOM、配置树、语法树 |
| 序列化/反序列化 | 各节点类型不同处理 |
| 类型检查 | 按节点类型施加不同规则 |

---

## 相关模式

| 模式 | 关系 |
| :--- | :--- |
| [Composite](../02_structural/composite.md) | 遍历 Composite 常用 Visitor |
| [Interpreter](interpreter.md) | 同为 AST 处理；Interpreter 求值，Visitor 遍历 |
| [Iterator](iterator.md) | 遍历方式不同；Visitor 深度优先，Iterator 可定制 |

---

## 实现变体

| 变体 | 说明 | 适用 |
| :--- | :--- | :--- |
| match + 函数 | `fn visit<V: Visitor>(v: &mut V, e: &Expr)` | 单分发；穷尽 |
| trait accept | `fn accept<V: Visitor>(&self, v: &mut V)` | 模拟双重分发 |
| 宏 | 自动生成 visit 分支 | 减少样板 |

---

## 反例：新增变体遗漏访问

**错误**：`Expr` 新增 `Expr::Mul` 变体，`visit` 中 `match` 未补充分支。

```rust
enum Expr { Int(i32), Add(Box<Expr>, Box<Expr>), Mul(Box<Expr>, Box<Expr>) }
fn visit<V: Visitor>(v: &mut V, e: &Expr) {
    match e {
        Expr::Int(n) => v.visit_int(*n),
        Expr::Add(a, b) => { ... },
        // 遗漏 Expr::Mul => 编译错误！
    }
}
```

**结论**：Rust 穷尽匹配在编译期强制补全；优于 OOP 的运行时遗漏。

---

## 选型决策树

```text
需要按节点类型施加不同操作？
├── 是 → 结构稳定、操作常变？ → Visitor（match 或 accept）
│       └── 操作简单、顺序遍历？ → Iterator
├── 需求值/解释？ → Interpreter
└── 需建树？ → Composite
```

---

## 边界

| 维度 | 分类 |
| :--- | :--- |
| 安全 | 纯 Safe |
| 支持 | 原生 |
| 表达 | 近似 |

---

## 与 Rust 1.93 的对应

| 1.93 特性 | 与本模式 | 说明 |
| :--- | :--- | :--- |
| 无新增影响 | — | 1.93 无影响 Visitor 语义的变更 |
| 92 项落点 | 无 | 本模式未涉及 [RUST_193_COUNTEREXAMPLES_INDEX](../../../RUST_193_COUNTEREXAMPLES_INDEX.md) 特定项 |

---

## 实质内容五维自检

| 自检项 | 状态 | 说明 |
| :--- | :--- | :--- |
| 形式化 | ✅ | Def 1.1、定理 VI-T1（L2） |
| 代码 | ✅ | 可运行示例、AST 美化 |
| 场景 | ✅ | 典型场景、完整示例 |
| 反例 | ✅ | 新增变体遗漏访问 |
| 衔接 | ✅ | match、trait、Composite |
| 权威对应 | ✅ | [GoF](../README.md#与-gof-原书对应)、[formal_methods](../../../formal_methods/README.md)、[INTERNATIONAL_FORMAL_VERIFICATION_INDEX](../../../INTERNATIONAL_FORMAL_VERIFICATION_INDEX.md) |
