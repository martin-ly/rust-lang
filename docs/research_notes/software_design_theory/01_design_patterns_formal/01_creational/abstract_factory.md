# Abstract Factory 形式化分析

> **创建日期**: 2026-02-12
> **分类**: 创建型
> **安全边界**: 纯 Safe

---

## 形式化定义

**Def 1.1（Abstract Factory 结构）**

设 $\mathcal{F}$ 为抽象工厂族，$T_1, \ldots, T_n$ 为产品类型族。Abstract Factory 满足：

- $\exists \mathit{create}_i : \mathcal{F} \to T_i$，$i \in \{1,\ldots,n\}$
- $\Gamma \vdash \mathit{create}_i(f) : T_i$
- 同一工厂实例 $f$ 创建的产品族风格一致（如暗色主题、亮色主题）

**Axiom AF1**：同一工厂创建的产品族类型一致；不同工厂可产生不同实现族。

**Axiom AF2**：工厂可被拥有或借用；产品所有权转移至调用者。

**定理 AF-T1**：由 [trait_system_formalization](../../../type_theory/trait_system_formalization.md)，trait 解析保证多态工厂调用类型安全。

**定理 AF-T2**：由 [ownership_model](../../../formal_methods/ownership_model.md) T2，产品所有权唯一。

---

## Rust 实现与代码示例

```rust
trait Button { fn render(&self); }
trait Dialog { fn render(&self); }

struct WinDialog;
impl Dialog for WinDialog { fn render(&self) { println!("WinDialog"); } }

struct WinButton;
impl Button for WinButton { fn render(&self) { println!("WinButton"); } }

struct MacButton;
impl Button for MacButton { fn render(&self) { println!("MacButton"); } }

trait GuiFactory {
    type B: Button;
    type D: Dialog;
    fn create_button(&self) -> Self::B;
    fn create_dialog(&self) -> Self::D;
}

struct WinFactory;
impl GuiFactory for WinFactory {
    type B = WinButton;
    type D = WinDialog;
    fn create_button(&self) -> WinButton { WinButton }
    fn create_dialog(&self) -> WinDialog { WinDialog }
}
```

**形式化对应**：`GuiFactory` 为 $\mathcal{F}$；`create_button`、`create_dialog` 为 $\mathit{create}_i$；关联类型 `B`、`D` 保证产品族一致。

---

## 证明思路

1. **产品族一致**：关联类型 `type B`、`type D` 在 impl 中固定；同一 impl 生产的 B 与 D 风格一致。
2. **类型安全**：trait 解析保证调用正确 impl；由 trait_system。

---

## 典型场景

| 场景 | 说明 |
|------|------|
| 跨平台 UI | Win/Mac/Linux 各自 Button、Dialog 族 |
| 主题/皮肤 | 暗色/亮色控件族 |
| 数据库抽象 | 不同驱动产生的 Connection、Statement 族 |
| 序列化格式 | JSON/MessagePack 各自的 Reader/Writer 族 |

---

## 相关模式

| 模式 | 关系 |
|------|------|
| [Factory Method](factory_method.md) | 抽象工厂由多个工厂方法组成 |
| [Builder](builder.md) | 可组合：Builder 由 Factory 创建 |
| [Singleton](singleton.md) | 工厂可为单例 |

---

## 实现变体

| 变体 | 说明 | 适用 |
|------|------|------|
| 关联类型 | `type B: Button; type D: Dialog` | 类型族编译期 |
| 枚举 | `enum Theme { Dark, Light }` + match | 有限主题 |
| trait 对象 | `Box<dyn GuiFactory>` | 运行时选择 |

---

## 反例：混用不同族产品

**错误**：从不同工厂取产品组合，风格不一致。

```rust
let win_factory = WinFactory;
let mac_factory = MacFactory;
// 混用：WinButton + MacDialog → 风格不一致
let ui = (win_factory.create_button(), mac_factory.create_dialog());
```

**结论**：Axiom AF1 要求同一工厂创建族；客户端应仅持有一个工厂实例。

---

## 选型决策树

```
需要创建产品族（风格一致）？
├── 是 → 跨平台/主题/格式族？ → Abstract Factory（关联类型或枚举）
├── 否 → 仅单产品？ → Factory Method
└── 需多步骤构建？ → Builder
```

---

## 与 GoF 对比

| GoF | Rust 对应 | 差异 |
|-----|-----------|------|
| 抽象工厂接口 | trait + 关联类型 | 等价 |
| 具体工厂 | impl for XxxFactory | 等价 |
| 产品族一致 | 关联类型 type B, type D | 编译期保证 |

---

## 边界

| 维度 | 分类 |
|------|------|
| 安全 | 纯 Safe |
| 支持 | 原生 |
| 表达 | 等价 |
