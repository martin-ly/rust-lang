# Decorator 形式化分析

> **创建日期**: 2026-02-12
> **分类**: 结构型
> **安全边界**: 纯 Safe

---

## 形式化定义

**Def 1.1（Decorator 结构）**:

设 $D$ 为装饰器类型，$T$ 为被装饰类型。Decorator 满足：

- $D$ 持有 $T$：$\Omega(D) \supset T$
- $D$ 实现与 $T$ 相同的接口（同一 trait）
- $\mathit{op}(d)$ 可先调用 $\mathit{op}(d.\mathit{inner})$ 再执行额外逻辑，或反之

**Axiom DE1**：装饰器与组件实现同一接口，可叠加。

**Axiom DE2**：委托链：$D_1(D_2(D_3(\cdots)))$，递归委托至最内层。

**定理 DE-T1**：由 [borrow_checker_proof](../../../formal_methods/borrow_checker_proof.md)，委托时 `&self.inner` 借用有效，无数据竞争。

**推论 DE-C1**：Decorator 为纯 Safe；仅用泛型包装、委托、trait impl，无 `unsafe`。由 DE-T1 及 [safe_unsafe_matrix](../../05_boundary_system/safe_unsafe_matrix.md) SBM-T1。

---

## Rust 实现与代码示例

```rust
trait Coffee {
    fn cost(&self) -> f32;
    fn description(&self) -> &str;
}

struct PlainCoffee;
impl Coffee for PlainCoffee {
    fn cost(&self) -> f32 { 2.0 }
    fn description(&self) -> &str { "plain" }
}

struct MilkDecorator<C: Coffee> {
    inner: C,
}

impl<C: Coffee> Coffee for MilkDecorator<C> {
    fn cost(&self) -> f32 {
        self.inner.cost() + 0.5
    }
    fn description(&self) -> &str {
        "milk + "
    }
}

// 使用：叠加装饰
let coffee = MilkDecorator { inner: PlainCoffee };
assert_eq!(coffee.cost(), 2.5);
```

**形式化对应**：`MilkDecorator` 即 $D$；`PlainCoffee` 即 $T$；`cost` 先调用 `inner.cost()` 再加价。

---

## 证明思路

1. **委托**：`&self` 借用 `self`，`&self.inner` 为子借用；调用 `inner.cost()` 无修改 `self` 其他部分。
2. **可叠加**：`MilkDecorator { inner: MilkDecorator { inner: PlainCoffee } }` 合法。

---

## 典型场景

| 场景 | 说明 |
| :--- | :--- |
| 中间件/装饰 | 日志、度量、缓存、重试 |
| I/O 装饰 | 压缩、加密、缓冲 |
| 权限/审计 | 装饰器增加检查逻辑 |

---

## 相关模式

| 模式 | 关系 |
| :--- | :--- |
| [Strategy](../03_behavioral/strategy.md) | 装饰器可持有多态策略 |
| [Adapter](adapter.md) | 同为包装；Decorator 同接口，Adapter 转换接口 |
| [Composite](composite.md) | Decorator 为链式，Composite 为树 |

---

## 实现变体

| 变体 | 说明 | 适用 |
| :--- | :--- | :--- |
| 泛型 `Decorator<C: Component>` | 编译期单态化，零成本 | 装饰链固定 |
| `Box<dyn Component>` | 运行时多态 | 装饰链动态 |
| 宏/派生 | 减少样板；如 `#[derive(Decor)]` | 简单装饰 |

---

## 反例：违反委托链

**错误**：装饰器不委托 inner，直接返回固定值，破坏透明性。

```rust
impl<C: Coffee> Coffee for BadDecorator<C> {
    fn cost(&self) -> f32 { 1.0 }  // 忽略 inner，违反 Axiom DE2
}
```

**后果**：叠加装饰失去意义；与 GoF 语义不一致。

---

## 选型决策树

```text
需要动态扩展行为且保持同接口？
├── 是 → 装饰链可叠加？ → Decorator（泛型或 Box<dyn>）
├── 否 → 需转换接口？ → Adapter
└── 需解耦实现？ → Bridge
```

---

## 与 GoF 对比

| GoF | Rust 对应 | 差异 |
| :--- | :--- | :--- |
| 抽象类 + 具体装饰 | trait + impl | 无继承 |
| 装饰器链 | 泛型嵌套 | 完全等价 |
| 透明性 | 同 trait 接口 | 等价 |

---

## 边界

| 维度 | 分类 |
| :--- | :--- |
| 安全 | 纯 Safe |
| 支持 | 原生 |
| 表达 | 等价 |
