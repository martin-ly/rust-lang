# Visitor 形式化分析

> **创建日期**: 2026-02-12
> **分类**: 行为型
> **安全边界**: 纯 Safe

---

## 形式化定义

**Def 1.1（Visitor 结构）**

设 $E$ 为元素类型（AST/节点），$V$ 为访问者类型。Visitor 满足：

- $\exists \mathit{visit} : V \times E \to R$
- $E$ 为代数数据类型
- 双重分发：$e.\mathit{accept}(v)$ 调用 $v.\mathit{visit}(e)$；或单分发：`match e` 后调用 `v.visit_X(e)`

**Axiom VI1**：访问者可访问所有节点变体；可扩展新操作。

**定理 VI-T1**：Rust 用 `match` 单分发或 trait 模拟；无 OOP 风格双重分发，表达为近似。

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

## 典型场景

| 场景 | 说明 |
|------|------|
| AST 遍历 | 编译器、解释器、代码生成 |
| 文档/树遍历 | DOM、配置树、语法树 |
| 序列化/反序列化 | 各节点类型不同处理 |
| 类型检查 | 按节点类型施加不同规则 |

---

## 相关模式

| 模式 | 关系 |
|------|------|
| [Composite](../02_structural/composite.md) | 遍历 Composite 常用 Visitor |
| [Interpreter](interpreter.md) | 同为 AST 处理；Interpreter 求值，Visitor 遍历 |
| [Iterator](iterator.md) | 遍历方式不同；Visitor 深度优先，Iterator 可定制 |

---

## 实现变体

| 变体 | 说明 | 适用 |
|------|------|------|
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

```
需要按节点类型施加不同操作？
├── 是 → 结构稳定、操作常变？ → Visitor（match 或 accept）
│       └── 操作简单、顺序遍历？ → Iterator
├── 需求值/解释？ → Interpreter
└── 需建树？ → Composite
```

---

## 边界

| 维度 | 分类 |
|------|------|
| 安全 | 纯 Safe |
| 支持 | 原生 |
| 表达 | 近似 |
