# Composite 形式化分析

> **创建日期**: 2026-02-12
> **分类**: 结构型
> **安全边界**: 纯 Safe

---

## 形式化定义

**Def 1.1（Composite 结构）**:

设 $C$ 为组件类型。Composite 满足：

$$C = \mathrm{Leaf}(T) \mid \mathrm{Composite}(\mathrm{Vec}\langle C \rangle)$$

- Leaf：叶子节点，持有数据 $T$，无子节点
- Composite：持有子组件列表 $\mathrm{Vec}\langle C \rangle$，递归结构
- $\Gamma \vdash \mathrm{Composite}(cs) : C$ 当 $\forall c \in cs,\, \Gamma \vdash c : C$

**Axiom CO1**：树结构，无环；深度有界（由程序结构决定）。

**Axiom CO2**：遍历时借用规则：不可在迭代时修改结构；或使用 `Vec` 拥有权无共享。

**定理 CO-T1**：`Box` 或 `Vec` 递归结构保证有界深度；由 [ownership_model](../../../formal_methods/ownership_model.md) 无泄漏、无悬垂。

**定理 CO-T2**：遍历时 `&self` 借用全部子节点；`&mut self` 可变遍历需小心别名。由 [borrow_checker_proof](../../../formal_methods/borrow_checker_proof.md) 保证无数据竞争。

**推论 CO-C1**：Composite 为纯 Safe；`enum` + `Vec`/`Box` 递归，无 `unsafe`；无环由类型结构保证。由 CO-T1、CO-T2 及 [safe_unsafe_matrix](../../05_boundary_system/safe_unsafe_matrix.md) SBM-T1。

---

## Rust 实现与代码示例

```rust
enum Node {
    Leaf(i32),
    Composite(Vec<Node>),
}

impl Node {
    fn sum(&self) -> i32 {
        match self {
            Node::Leaf(n) => *n,
            Node::Composite(children) => children.iter().map(|c| c.sum()).sum(),
        }
    }
}

// 构建：Vec 拥有子节点，递归
let tree = Node::Composite(vec![
    Node::Leaf(1),
    Node::Composite(vec![Node::Leaf(2), Node::Leaf(3)]),
]);
assert_eq!(tree.sum(), 6);
```

**形式化对应**：`Node` 即 $C$；`Leaf(i32)` 为 $\mathrm{Leaf}(T)$；`Composite(Vec<Node>)` 为 $\mathrm{Composite}(\mathrm{Vec}\langle C \rangle)$。

---

## 证明思路

1. **结构有界**：枚举递归，无 `Box<Node>` 自引用则无无限类型；`Vec` 大小运行时确定。
2. **遍历安全**：`iter()` 产生 `&Node`，不可变；匹配 [borrow_checker_proof](../../../formal_methods/borrow_checker_proof.md) 互斥规则。

---

## 典型场景

| 场景 | 说明 |
| :--- | :--- |
| 文件系统 | 文件/目录树 |
| UI 组件树 | 控件/容器层级 |
| 表达式 AST | 叶子/复合节点 |
| 配置/菜单 | 嵌套结构 |
| 组织架构 | 部门/人员层级 |

---

## 相关模式

| 模式 | 关系 |
| :--- | :--- |
| [Visitor](../03_behavioral/visitor.md) | 遍历 Composite 常用 Visitor |
| [Decorator](decorator.md) | 同为组合；Decorator 为链式，Composite 为树 |
| [Chain of Responsibility](../03_behavioral/chain_of_responsibility.md) | 链 vs 树；委托传递 |

---

## 实现变体

| 变体 | 说明 | 适用 |
| :--- | :--- | :--- |
| 枚举递归 `enum { Leaf(T), Composite(Vec<Node>) }` | 同质节点；简单 | AST、配置树 |
| trait + Box | 异质节点；多态 | UI 控件、插件系统 |
| `Rc`/`Weak` | 父→子→父 引用；需破环 | 图结构、DOM 式 |

---

## 反例

**反例**：父子循环引用（父→子→父）在 Rust 中无法用普通所有权表达；需 `Rc`/`Weak` 或重构为无环结构，否则所有权无法建立。

---

## 选型决策树

```text
需要表示树状/层次结构？
├── 是 → 节点同质？ → 枚举递归（Leaf/Composite）
│       └── 节点异质？ → trait + Box<dyn>
├── 需父→子→父引用？ → Rc<RefCell> + Weak（破环）
└── 仅链式？ → Chain of Responsibility
```

---

## 与 GoF 对比

| GoF | Rust 对应 | 差异 |
| :--- | :--- | :--- |
| 组合 + 叶子 | 枚举 Leaf/Composite | 完全等价 |
| 统一接口 | trait Component | 等价 |
| 循环引用 | Rc + Weak | 需显式破环 |

---

## 边界

| 维度 | 分类 |
| :--- | :--- |
| 安全 | 纯 Safe |
| 支持 | 原生 |
| 表达 | 等价 |
