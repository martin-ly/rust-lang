# Interpreter 形式化分析

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-14
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 形式化完成
> **分类**: 行为型
> **安全边界**: 纯 Safe
> **23 模式矩阵**: [README §23 模式多维对比矩阵](../README.md#23-模式多维对比矩阵) 第 15 行（Interpreter）

---

## 📊 目录

- [Interpreter 形式化分析](#interpreter-形式化分析)
  - [形式化定义](#形式化定义)
  - [Rust 实现与代码示例](#rust-实现与代码示例)
  - [证明思路](#证明思路)
  - [典型场景](#典型场景)
  - [典型场景完整代码示例（过滤表达式）](#典型场景完整代码示例过滤表达式)
  - [完整 DSL 示例：简易查询语言（层次推进）](#完整-dsl-示例简易查询语言层次推进)
  - [相关模式](#相关模式)
  - [实现变体](#实现变体)
  - [与 GoF 对比](#与-gof-对比)
  - [反例：AST 含环或无限递归](#反例ast-含环或无限递归)
  - [选型决策树](#选型决策树)
  - [边界](#边界)

---

## 形式化定义

**Def 1.1（Interpreter 结构）**:

设 $E$ 为表达式类型（AST），$V$ 为值类型。Interpreter 满足：

- $\exists \mathit{eval} : E \to V$
- $E$ 为代数数据类型：$E = \mathrm{Const}(V) \mid \mathrm{Op}(\mathit{Op}, E, E) \mid \ldots$
- 递归求值：$\mathit{eval}(\mathrm{Op}(e_1,e_2)) = f(\mathit{eval}(e_1), \mathit{eval}(e_2))$

**Axiom IN1**：AST 有穷；无环（由结构保证）。

**Axiom IN2**：`match` 穷尽所有变体；无遗漏。

**定理 IN-T1**：枚举 + match 求值，由 [type_system_foundations](../../../type_theory/type_system_foundations.md) 穷尽匹配保证完备性。

*证明*：由 Axiom IN1、IN2；枚举定义 $E$ 结构，match 穷尽所有变体；递归求值由结构归纳保证终止；type_system 保持性保证类型正确。∎

**引理 IN-L1（终止性）**：若 $E$ 有穷且无环，则 $\mathit{eval}(e)$ 终止。

*证明*：由 Axiom IN1；$E$ 为树结构，递归下降至叶节点（Const）；结构归纳保证每步子表达式规模减小。∎

**推论 IN-C1**：Interpreter 与 [expressive_inexpressive_matrix](../../05_boundary_system/expressive_inexpressive_matrix.md) 表一致；$\mathit{ExprB}(\mathrm{Interpreter}) = \mathrm{Approx}$（无 OOP 继承）。

**反例**：若 AST 含环（自引用），递归求值不终止；由 Axiom IN1 排除。若漏 match 分支，编译错误。

---

## Rust 实现与代码示例

```rust
enum Expr {
    Const(i32),
    Add(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
}

impl Expr {
    fn eval(&self) -> i32 {
        match self {
            Expr::Const(n) => *n,
            Expr::Add(a, b) => a.eval() + b.eval(),
            Expr::Mul(a, b) => a.eval() * b.eval(),
        }
    }
}

// 1 + 2 * 3
let e = Expr::Add(
    Box::new(Expr::Const(1)),
    Box::new(Expr::Mul(
        Box::new(Expr::Const(2)),
        Box::new(Expr::Const(3)),
    )),
);
assert_eq!(e.eval(), 7);
```

**形式化对应**：`Expr` 即 $E$；`Const`、`Add`、`Mul` 为变体；`eval` 即 $\mathit{eval}$。

---

## 证明思路

1. **有穷**：`Box` 递归，深度有界；无自引用则无无限类型。
2. **穷尽**：`match` 必须覆盖所有变体；编译期检查。

---

## 典型场景

| 场景 | 说明 |
| :--- | :--- |
| 表达式求值 | 算术、布尔、正则 |
| 脚本解析 | DSL、配置语言 |
| 查询解析 | SQL 子集、过滤表达式 |

---

## 典型场景完整代码示例（过滤表达式）

**场景**：配置中允许简单过滤表达式 `field > 100`，运行时求值。

```rust
use std::collections::HashMap;

#[derive(Clone)]
enum FilterExpr {
    Lit(i64),
    Field(&'static str),
    Gt(Box<FilterExpr>, Box<FilterExpr>),
}

impl FilterExpr {
    fn eval(&self, ctx: &HashMap<&str, i64>) -> Option<bool> {
        match self {
            FilterExpr::Lit(n) => Some(*n != 0),
            FilterExpr::Field(f) => ctx.get(*f).map(|&v| v != 0),
            FilterExpr::Gt(a, b) => {
                let va = match a.as_ref() { FilterExpr::Lit(n) => *n, FilterExpr::Field(f) => *ctx.get(*f)?, _ => return None };
                let vb = match b.as_ref() { FilterExpr::Lit(n) => *n, FilterExpr::Field(f) => *ctx.get(*f)?, _ => return None };
                Some(va > vb)
            }
        }
    }
}

// 示例：FilterExpr::Gt(Box::new(FilterExpr::Field("count")), Box::new(FilterExpr::Lit(10)))
// 表示 "count > 10"；ctx = [("count", 15)] => Some(true)
```

---

## 完整 DSL 示例：简易查询语言（层次推进）

**场景**：配置层允许 `field op value` 形式过滤，支持 `>`, `==`, `&&`, `||`；解析→AST→求值。

### 1. AST 定义（Def 1.1 对应）

```rust
#[derive(Debug, Clone)]
pub enum QueryExpr {
    Lit(i64),
    Field(String),
    Eq(Box<QueryExpr>, Box<QueryExpr>),
    Gt(Box<QueryExpr>, Box<QueryExpr>),
    And(Box<QueryExpr>, Box<QueryExpr>),
    Or(Box<QueryExpr>, Box<QueryExpr>),
}

impl QueryExpr {
    pub fn eval(&self, ctx: &std::collections::HashMap<String, i64>) -> Option<bool> {
        match self {
            QueryExpr::Lit(n) => Some(*n != 0),
            QueryExpr::Field(f) => ctx.get(f).map(|&v| v != 0),
            QueryExpr::Eq(a, b) => {
                let (va, vb) = (eval_num(a, ctx)?, eval_num(b, ctx)?);
                Some(va == vb)
            }
            QueryExpr::Gt(a, b) => {
                let (va, vb) = (eval_num(a, ctx)?, eval_num(b, ctx)?);
                Some(va > vb)
            }
            QueryExpr::And(a, b) => Some(a.eval(ctx)? && b.eval(ctx)?),
            QueryExpr::Or(a, b) => Some(a.eval(ctx)? || b.eval(ctx)?),
        }
    }
}

fn eval_num(e: &QueryExpr, ctx: &std::collections::HashMap<String, i64>) -> Option<i64> {
    match e {
        QueryExpr::Lit(n) => Some(*n),
        QueryExpr::Field(f) => ctx.get(f).copied(),
        _ => None,
    }
}
```

### 2. 简易解析器（递归下降，先低优先级后高优先级）

```rust
fn parse(s: &str) -> Result<QueryExpr, String> {
    let s = s.trim();
    if let Some(idx) = s.rfind("||") {
        let (left, right) = (s[..idx].trim(), s[idx + 2..].trim());
        if !left.is_empty() && !right.is_empty() {
            return Ok(QueryExpr::Or(Box::new(parse(left)?), Box::new(parse(right)?)));
        }
    }
    if let Some(idx) = s.rfind("&&") {
        let (left, right) = (s[..idx].trim(), s[idx + 2..].trim());
        if !left.is_empty() && !right.is_empty() {
            return Ok(QueryExpr::And(Box::new(parse(left)?), Box::new(parse(right)?)));
        }
    }
    if let Some(idx) = s.find('>') {
        let (left, right) = (s[..idx].trim(), s[idx + 1..].trim());
        if !left.is_empty() && !right.is_empty() {
            return Ok(QueryExpr::Gt(Box::new(parse(left)?), Box::new(parse(right)?)));
        }
    }
    if let Some(idx) = s.find("==") {
        let (left, right) = (s[..idx].trim(), s[idx + 2..].trim());
        if !left.is_empty() && !right.is_empty() {
            return Ok(QueryExpr::Eq(Box::new(parse(left)?), Box::new(parse(right)?)));
        }
    }
    if let Ok(n) = s.parse::<i64>() {
        return Ok(QueryExpr::Lit(n));
    }
    if !s.is_empty() && s.chars().all(|c| c.is_alphanumeric() || c == '_') {
        return Ok(QueryExpr::Field(s.to_string()));
    }
    Err(format!("cannot parse: {}", s))
}
```

### 3. 使用示例

```rust
// "age > 18 && score == 100"
let ast = parse("age > 18 && score == 100")?;
let ctx: HashMap<_, _> = [("age".into(), 20), ("score".into(), 100)].into();
assert_eq!(ast.eval(&ctx), Some(true));

// "x > 0 || y > 0"
let ast = parse("x > 0 || y > 0")?;
let ctx: HashMap<_, _> = [("x".into(), 0), ("y".into(), 1)].into();
assert_eq!(ast.eval(&ctx), Some(true));
```

**形式化对应**：AST 即 $E$；`parse` 为语法→$E$；`eval` 即 $\mathit{eval}$；Axiom IN1 由 `Box` 递归深度有界保证；Axiom IN2 由 `match` 穷尽保证。

---

## 相关模式

| 模式 | 关系 |
| :--- | :--- |
| [Visitor](visitor.md) | 同为 AST 处理；Interpreter 求值，Visitor 遍历 |
| [Composite](../02_structural/composite.md) | AST 即 Composite 结构 |
| [Strategy](strategy.md) | 不同求值策略可替换 |

---

## 实现变体

| 变体 | 说明 | 适用 |
| :--- | :--- | :--- |
| 枚举 + match | 同质 AST；穷尽匹配 | 简单 DSL |
| trait 节点 | 异质节点；多态求值 | 可扩展语法 |
| 访问者分离 | 求值逻辑在 Visitor | 多操作（求值、打印、优化） |

---

## 与 GoF 对比

GoF 用继承定义 AST 节点；Rust 用枚举更简洁，且穷尽匹配保证完备性。

---

## 反例：AST 含环或无限递归

**错误**：自引用表达式导致 `eval` 无限递归。

```rust
// 若 Expr 允许 Expr::Ref(Box<Expr>) 指向自身 → 无限递归
```

**Axiom IN1**：AST 有穷、无环；由 `Box` 递归与无自引用保证。

---

## 选型决策树

```text
需要解析并求值 DSL/表达式？
├── 是 → 枚举 AST + match 求值？ → Interpreter
│       └── 需多操作（求值、打印、优化）？ → Visitor
├── 需遍历树？ → Visitor 或 Iterator
└── 需策略替换？ → Strategy
```

---

## 边界

| 维度 | 分类 |
| :--- | :--- |
| 安全 | 纯 Safe |
| 支持 | 原生 |
| 表达 | 近似（无继承，用枚举） |
