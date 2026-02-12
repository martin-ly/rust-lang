# Prototype 形式化分析

> **创建日期**: 2026-02-12
> **分类**: 创建型
> **安全边界**: 纯 Safe

---

## 形式化定义

**Def 1.1（Prototype 结构）**

设 $T$ 为原型类型。Prototype 满足：

- $\exists \mathit{clone} : T \to T$，$\mathit{clone}(t)$ 返回 $t$ 的副本
- $\Omega(\mathit{clone}(t)) \neq \Omega(t)$（不同所有者，独立副本）
- 引用 [ownership_model](../../../formal_methods/ownership_model.md) 复制语义

**Axiom P1**：Clone 不改变原对象，产生独立副本。

**Axiom P2**：若 $T$ 含引用，Clone 需复制引用目标或产生新副本；由实现决定（浅拷贝 vs 深拷贝）。

**定理 P-T1**：若 $T$ 实现 `Clone`，则 $\mathit{clone}(t)$ 类型为 $T$，所有权独立。由 [type_system_foundations](../../../type_theory/type_system_foundations.md)。

**定理 P-T2**：`&self` 借用，返回值拥有所有权；原对象仍有效。由 ownership T2。

---

## Rust 实现与代码示例

```rust
#[derive(Clone)]
struct Config {
    host: String,
    port: u16,
}

// 使用
let a = Config { host: "localhost".into(), port: 8080 };
let b = a.clone();  // a 仍有效，b 为独立副本
assert_eq!(a.host, b.host);
```

**深拷贝（含嵌套）**：

```rust
#[derive(Clone)]
struct Node {
    value: i32,
    children: Vec<Node>,
}

let tree = Node { value: 1, children: vec![] };
let copy = tree.clone();  // 递归 clone
```

**形式化对应**：`clone(&self) -> Self` 即 $\mathit{clone}$；`#[derive(Clone)]` 自动生成实现。

---

## 证明思路

1. **所有权**：`clone` 返回新值，调用者获得所有权；原 `self` 未被消费。
2. **类型**：返回 `Self`，与 $T$ 一致；由 type_system。

---

## 典型场景

| 场景 | 说明 |
|------|------|
| 对象复制 | 配置、文档、游戏实体 |
| 缓存模板 | 以原型为基础做小修改 |
| 深拷贝结构 | 树、图等嵌套结构 |

---

## 相关模式

| 模式 | 关系 |
|------|------|
| [Factory Method](factory_method.md) | 工厂可基于 Prototype 克隆 |
| [Builder](builder.md) | Builder 可基于 Prototype 克隆 |
| [Memento](../03_behavioral/memento.md) | Clone 可作 Memento 实现 |

---

## 实现变体

| 变体 | 说明 | 适用 |
|------|------|------|
| `#[derive(Clone)]` | 自动实现；浅拷贝 | 无嵌套引用 |
| 手动 Clone | 自定义深拷贝 | 含 Rc、引用等 |
| `Copy` | 隐式复制；无堆 | 小值类型 |

---

## 反例：Clone 含浅拷贝引用

**错误**：`Clone` 仅复制指针，未克隆指向内容；多副本共享同一可变状态。

```rust
struct BadNode { data: Rc<RefCell<i32>> }
impl Clone for BadNode {
    fn clone(&self) -> Self {
        Self { data: Rc::clone(&self.data) }  // 浅拷贝：共享同一 RefCell
    }
}
// 两个 clone 副本修改 data → 互相影响
```

**结论**：若需独立副本，应深拷贝 `RefCell` 内容；或显式文档说明共享语义。

---

## 与 Copy 的关系

`Copy` 为 `Clone` 的子集：隐式复制，无显式 `clone()` 调用。`Clone` 可显式、可含堆分配。

---

## 选型决策树

```
需要基于已有对象创建副本？
├── 是 → 浅拷贝即可？ → Clone / Copy
│       └── 深拷贝？ → 手动 Clone impl
├── 需多步骤构建？ → Builder
└── 需工厂创建？ → Factory Method
```

---

## 与 GoF 对比

| GoF | Rust 对应 | 差异 |
|-----|-----------|------|
| clone() | Clone::clone | 等价 |
| 原型注册 | HashMap + Clone | 等价 |
| 深拷贝 | 手动 Clone | 等价 |

---

## 边界

| 维度 | 分类 |
|------|------|
| 安全 | 纯 Safe |
| 支持 | 原生 |
| 表达 | 等价 |
