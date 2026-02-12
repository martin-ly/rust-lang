# Memento 形式化分析

> **创建日期**: 2026-02-12
> **分类**: 行为型
> **安全边界**: 纯 Safe

---

## 形式化定义

**Def 1.1（Memento 结构）**

设 $M$ 为备忘类型，$O$ 为原发器类型。Memento 满足：

- $\exists \mathit{save} : O \to M$，捕获 $O$ 状态
- $\exists \mathit{restore} : O \times M \to O$，恢复状态
- $M$ 仅由 $O$ 解读（封装）；或通过 `Clone`/序列化实现

**Axiom MO1**：备忘包含足够状态以恢复；无外部依赖。

**Axiom MO2**：恢复时状态与当前上下文兼容；非法状态会导致不变式违反。

**定理 MO-T1**：`Clone` 或 `serde` 序列化可实现；Rust 无私有访问 OOP 风格，表达为近似。

*证明*：由 Axiom MO1、MO2；`Clone` 生成独立副本，`serde` 序列化/反序列化保证状态可恢复；Rust 无 C++ 友元/私有，$M$ 可被任意代码读取，故为近似表达。∎

**引理 MO-L1（状态一致性）**：若 $M = \mathit{save}(O)$ 且 $O$ 未变，则 $\mathit{restore}(O, M)$ 使 $O$ 回到 $\mathit{save}$ 时状态。

*证明*：由 Def 1.1；$M$ 捕获 $O$ 状态；$\mathit{restore}$ 覆盖 $O$ 为 $M$ 内状态；无外部依赖故一致性成立。∎

**推论 MO-C1**：Memento 与 [expressive_inexpressive_matrix](../../05_boundary_system/expressive_inexpressive_matrix.md) 表一致；$\mathit{ExprB}(\mathrm{Memento}) = \mathrm{Approx}$。

**反例**：若 $M$ 与 $O$ 版本不兼容（如 $O$ 新增字段），`restore` 可能产生非法状态；由 Axiom MO2，需版本兼容或默认值。

---

## Rust 实现与代码示例

```rust
#[derive(Clone)]
struct Memento {
    state: String,
}

struct Originator {
    state: String,
}

impl Originator {
    fn new() -> Self {
        Self { state: String::new() }
    }
    fn save(&self) -> Memento {
        Memento { state: self.state.clone() }
    }
    fn restore(&mut self, m: &Memento) {
        self.state = m.state.clone();
    }
    fn set(&mut self, s: &str) {
        self.state = s.to_string();
    }
}

// 使用
let mut o = Originator::new();
o.set("A");
let m = o.save();
o.set("B");
o.restore(&m);
assert_eq!(o.state, "A");
```

**形式化对应**：`Memento` 即 $M$；`Originator` 即 $O$；`save` 即 $\mathit{save}$；`restore` 即 $\mathit{restore}$。

---

## 证明思路

1. **保存**：`clone()` 产生独立副本；所有权转移至 Memento。
2. **恢复**：`restore` 覆盖 `self.state`；需保证 Memento 与当前 Originator 版本兼容。

---

## 典型场景

| 场景 | 说明 |
| :--- | :--- |
| 撤销/重做 | 编辑器、表单、配置 |
| 快照/检查点 | 游戏存档、事务回滚 |
| 审计日志 | 状态历史、合规 |

---

## 相关模式

| 模式 | 关系 |
| :--- | :--- |
| [Command](command.md) | 撤销需 Memento 保存状态 |
| [State](state.md) | 保存/恢复状态 |
| [Prototype](../01_creational/prototype.md) | Clone 可作 Memento 实现 |

---

## 实现变体

| 变体 | 说明 | 适用 |
| :--- | :--- | :--- |
| `Clone` | 简单结构；内存复制 | 小对象、无环 |
| serde | 序列化/反序列化 | 持久化、跨进程 |
| 快照类型 | 显式 `Snapshot` 结构体 | 版本兼容、校验 |

---

## 反例

**反例**：`restore` 使用非法或过时状态 → 违反领域不变式。需校验 Memento 与当前上下文兼容。

---

## 选型决策树

```
需要保存/恢复状态？
├── 是 → 简单结构？ → Clone
│       └── 需持久化？ → serde
├── 需撤销操作？ → Command + Memento
└── 需状态转换？ → State
```

---

## 与 GoF 对比

| GoF | Rust 对应 | 差异 |
| :--- | :--- | :--- |
| Memento 私有 | 无；Clone/serde 公开 | 近似 |
| Originator 封装 | 快照类型或 Clone | 等价 |
| Caretaker 存储 | Vec<Snapshot> 等 | 等价 |

---

## 边界

| 维度 | 分类 |
| :--- | :--- |
| 安全 | 纯 Safe |
| 支持 | 原生 |
| 表达 | 近似（无私有封装） |
