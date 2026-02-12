# Interpreter 形式化分析

> **创建日期**: 2026-02-12
> **分类**: 行为型
> **安全边界**: 纯 Safe

---

## 形式化定义

**Def 1.1（Interpreter 结构）**

设 $E$ 为表达式类型（AST），$V$ 为值类型。Interpreter 满足：

- $\exists \mathit{eval} : E \to V$
- $E$ 为代数数据类型：$E = \mathrm{Const}(V) \mid \mathrm{Op}(\mathit{Op}, E, E) \mid \ldots$
- 递归求值：$\mathit{eval}(\mathrm{Op}(e_1,e_2)) = f(\mathit{eval}(e_1), \mathit{eval}(e_2))$

**Axiom IN1**：AST 有穷；无环（由结构保证）。

**Axiom IN2**：`match` 穷尽所有变体；无遗漏。

**定理 IN-T1**：枚举 + match 求值，由 [type_system_foundations](../../../type_theory/type_system_foundations.md) 穷尽匹配保证完备性。

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
|------|------|
| 表达式求值 | 算术、布尔、正则 |
| 脚本解析 | DSL、配置语言 |
| 查询解析 | SQL 子集、过滤表达式 |

---

## 相关模式

| 模式 | 关系 |
|------|------|
| [Visitor](visitor.md) | 同为 AST 处理；Interpreter 求值，Visitor 遍历 |
| [Composite](../02_structural/composite.md) | AST 即 Composite 结构 |
| [Strategy](strategy.md) | 不同求值策略可替换 |

---

## 实现变体

| 变体 | 说明 | 适用 |
|------|------|------|
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

```
需要解析并求值 DSL/表达式？
├── 是 → 枚举 AST + match 求值？ → Interpreter
│       └── 需多操作（求值、打印、优化）？ → Visitor
├── 需遍历树？ → Visitor 或 Iterator
└── 需策略替换？ → Strategy
```

---

## 边界

| 维度 | 分类 |
|------|------|
| 安全 | 纯 Safe |
| 支持 | 原生 |
| 表达 | 近似（无继承，用枚举） |
