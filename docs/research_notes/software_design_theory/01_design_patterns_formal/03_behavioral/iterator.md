# Iterator 形式化分析

> **创建日期**: 2026-02-12
> **分类**: 行为型
> **安全边界**: 纯 Safe

---

## 形式化定义

**Def 1.1（Iterator 结构）**

设 $I$ 为迭代器类型，$T$ 为元素类型。Iterator 满足：

- $\exists \mathit{next} : \&mut I \to \mathrm{Option}\langle T \rangle$
- 迭代器持有序列状态（位置、引用等）
- 消耗或借用产生元素；每次 `next` 至多产生一个元素

**Axiom IT1**：`next` 最多返回一次每个元素；无重复、无遗漏（由实现保证）。

**Axiom IT2**：迭代器可变借用：`&mut self` 满足借用规则；同时仅一个活跃迭代器或为 FusedIterator。

**定理 IT-T1**：`Iterator` trait 由标准库定义；`for` 糖语法保证类型安全。由 [type_system_foundations](../../../type_theory/type_system_foundations.md)。

**定理 IT-T2**：`&mut self` 可变借用保证迭代器内部状态一致；由 [borrow_checker_proof](../../../formal_methods/borrow_checker_proof.md)。

---

## Rust 实现与代码示例

```rust
struct Counter { count: u32 }

impl Iterator for Counter {
    type Item = u32;
    fn next(&mut self) -> Option<Self::Item> {
        if self.count < 5 {
            let c = self.count;
            self.count += 1;
            Some(c)
        } else {
            None
        }
    }
}

// 使用
for n in Counter { count: 0 } {
    println!("{}", n);  // 0, 1, 2, 3, 4
}
```

**形式化对应**：`Counter` 即 $I$；`Item = u32` 即 $T$；`next(&mut self)` 即 $\mathit{next}$。

---

## 证明思路

1. **类型安全**：`Option<T>` 表示终止；`for` 循环类型检查保证 `Item` 与使用处一致。
2. **所有权**：`next` 返回 `Option<T>`，元素所有权转移至调用者；迭代器持有状态（如 `count`），不持有元素。

---

## 典型场景

| 场景 | 说明 |
|------|------|
| 集合遍历 | `Vec`、`HashMap`、`BTreeMap` 等 |
| 惰性流 | `map`、`filter`、`take` 链式 |
| 自定义序列 | 计数器、生成器、游标 |
| 适配器 | `zip`、`chain`、`enumerate` |

---

## 相关模式

| 模式 | 关系 |
|------|------|
| [Visitor](visitor.md) | 遍历方式不同；Iterator 顺序，Visitor 深度优先 |
| [Composite](../02_structural/composite.md) | 可对 Composite 实现 Iterator |
| [Chain of Responsibility](chain_of_responsibility.md) | 链式传递 vs 迭代消费 |

---

## 反例：迭代中修改集合

**错误**：在 `for x in vec.iter()` 内对 `vec` 执行 `push`/`remove`。

```rust
let mut v = vec![1, 2, 3];
for x in v.iter() {
    v.push(*x);  // 编译错误：同时存在 borrow 与 borrow_mut
}
```

**结论**：Axiom IT2；可变借用互斥；`iter()` 与 `push` 不可同时活跃。

---

## 实现变体

| 变体 | 说明 | 适用 |
|------|------|------|
| 结构体 + next | 自定义迭代器；实现 trait | 新集合类型 |
| 适配器链 | `iter().map().filter()` | 惰性转换 |
| 消费器 | `collect`、`sum`、`fold` | 聚合结果 |

零成本抽象：泛型单态化后，`Iterator` 链无虚调用开销。

---

## 与标准库衔接

`Iterator` trait 为核心抽象；`map`、`filter`、`collect` 等为组合子。所有组合均保持 Safe。

---

## 选型决策树

```
需要顺序遍历集合/序列？
├── 是 → 标准集合？ → iter()/into_iter()
│       └── 自定义序列？ → impl Iterator
├── 需按类型施加不同操作？ → Visitor
└── 需链式传递？ → Chain of Responsibility
```

---

## 边界

| 维度 | 分类 |
|------|------|
| 安全 | 纯 Safe |
| 支持 | 原生 |
| 表达 | 等价 |
