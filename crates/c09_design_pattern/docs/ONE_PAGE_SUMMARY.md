# C09 设计模式 - 一页纸总结

> **用途**: 快速回顾核心概念、常见坑、学习路径
> **完整文档**: [00_MASTER_INDEX](./00_MASTER_INDEX.md)

---

## 核心概念（4 条）

| 概念 | 说明 |
|------|------|
| **创建型** | Builder、Factory、Singleton；Rust 用 `Default`、`new` 惯用 |
| **结构型** | Adapter、Decorator、Facade；组合优于继承 |
| **行为型** | Strategy、Observer、State；trait 对象或枚举 |
| **Rust 特有** | Newtype、RAII、类型状态机；零成本抽象 |

---

## 常见坑与解决

| 坑 | 解决 |
|----|------|
| 过度设计 | 先满足需求；模式按需引入 |
| OOP 思维照搬 | Rust 用 trait + enum；避免继承层次 |
| 全局可变状态 | 用 `Arc<Mutex<T>>` 或依赖注入 |
| 模式组合复杂 | 参考 [模式组合参考](tier_03_references/04_模式性能评估参考.md) |

---

## 模式速选

| 场景 | 选型 |
|------|------|
| 多步骤构建 | Builder |
| 运行时多态 | `dyn Trait` 或 `enum` |
| 可选扩展 | Decorator / Newtype |
| 状态转换 | 类型状态机 / enum |
| 事件通知 | Observer / channel |

---

## 学习路径

1. **入门** (1–2 周): GoF 创建型 → 结构型 → 行为型
2. **进阶** (2–3 周): Rust 惯用模式 → 模式组合
3. **高级** (持续): 形式化、性能评估、与 C11 互链

---

## 速查与练习

- **速查卡**: [design_patterns_cheatsheet](../../../docs/02_reference/quick_reference/design_patterns_cheatsheet.md)
- **RBE 练习**: [Functional](https://doc.rust-lang.org/rust-by-example/fn.html) · [Structs](https://doc.rust-lang.org/rust-by-example/custom_types/structs.html) · [Enums](https://doc.rust-lang.org/rust-by-example/custom_types/enum.html)
- **Rustlings**: 无设计模式专题；综合运用 07_structs、08_enums、15_traits
