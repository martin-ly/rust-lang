# Composite 形式化分析

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-14
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 形式化完成
> **分类**: 结构型
> **安全边界**: 纯 Safe
> **23 模式矩阵**: [README §23 模式多维对比矩阵](../README.md#23-模式多维对比矩阵) 第 8 行（Composite）
> **证明深度**: L2（完整证明草图）

---

## 📊 目录

- [Composite 形式化分析](#composite-形式化分析)
  - [形式化定义](#形式化定义)
    - [概念定义-属性关系-解释论证 层次汇总](#概念定义-属性关系-解释论证-层次汇总)
  - [Rust 实现与代码示例](#rust-实现与代码示例)
  - [证明思路](#证明思路)
  - [典型场景](#典型场景)
  - [完整场景示例：文件系统树（File/Directory）](#完整场景示例文件系统树filedirectory)
  - [相关模式](#相关模式)
  - [实现变体](#实现变体)
  - [反例](#反例)
  - [选型决策树](#选型决策树)
  - [与 GoF 对比](#与-gof-对比)
  - [边界](#边界)
  - [与 Rust 1.93 的对应](#与-rust-193-的对应)
  - [实质内容五维自检](#实质内容五维自检)

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

### 概念定义-属性关系-解释论证 层次汇总

| 层次 | 内容 | 本页对应 |
| :--- | :--- | :--- |
| **概念定义层** | Def 1.1（Composite 结构）、Axiom CO1/CO2（无环、遍历借用） | 上 |
| **属性关系层** | Axiom CO1/CO2 → 定理 CO-T1/CO-T2 → 推论 CO-C1；依赖 ownership、borrow | 上 |
| **解释论证层** | 证明思路：结构有界、遍历安全；反例：§反例 | §证明思路、§反例 |

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

## 完整场景示例：文件系统树（File/Directory）

**场景**：文件与目录组成树；目录可含子文件/子目录；递归计算大小。

```rust
enum FsNode {
    File { name: String, size: u64 },
    Dir { name: String, children: Vec<FsNode> },
}

impl FsNode {
    fn size(&self) -> u64 {
        match self {
            FsNode::File { size, .. } => *size,
            FsNode::Dir { children, .. } => children.iter().map(|c| c.size()).sum(),
        }
    }
}

// 构建：docs/ 含 readme.txt、src/main.rs
let tree = FsNode::Dir {
    name: "docs".into(),
    children: vec![
        FsNode::File { name: "readme.txt".into(), size: 100 },
        FsNode::Dir {
            name: "src".into(),
            children: vec![FsNode::File { name: "main.rs".into(), size: 500 }],
        },
    ],
};
assert_eq!(tree.size(), 600);
```

**形式化对应**：`FsNode` 即 $C$；`File` 为 Leaf；`Dir` 为 Composite；由 Axiom CO1、CO2。

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

---

## 与 Rust 1.93 的对应

| 1.93 特性 | 与本模式 | 说明 |
| :--- | :--- | :--- |
| 无新增影响 | — | 1.93 无影响 Composite 语义的变更 |
| 92 项落点 | 无 | 本模式未涉及 [RUST_193_COUNTEREXAMPLES_INDEX](../../../RUST_193_COUNTEREXAMPLES_INDEX.md) 特定项 |

---

## 实质内容五维自检

| 自检项 | 状态 | 说明 |
| :--- | :--- | :--- |
| 形式化 | ✅ | Def 1.1、Axiom CO1/CO2、定理 CO-T1/T2（L2） |
| 代码 | ✅ | 可运行示例、完整场景 |
| 场景 | ✅ | 典型场景、文件系统树 |
| 反例 | ✅ | 反例小节 |
| 衔接 | ✅ | ownership、borrow、CE-T1 |
| 权威对应 | ✅ | [GoF](../README.md#与-gof-原书对应)、[formal_methods](../../../formal_methods/README.md)、[INTERNATIONAL_FORMAL_VERIFICATION_INDEX](../../../INTERNATIONAL_FORMAL_VERIFICATION_INDEX.md) |
