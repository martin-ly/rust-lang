# 充分表达 vs 非充分表达边界矩阵

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-12
> **Rust 版本**: 1.93.0+ (Edition 2024)

---

## 形式化定义与公理

**Def 1.1（表达边界）**

设 $P_{\mathrm{OOP}}$ 为 GoF/OOP 模式 $P$ 的语义，$P_{\mathrm{Rust}}$ 为 Rust 对应实现。定义表达边界函数 $\mathit{ExprB}(P) \in \{\mathrm{Same},\, \mathrm{Approx},\, \mathrm{NoExpr}\}$：

- **等价表达**：$\mathit{ExprB}(P) = \mathrm{Same}$ 当且仅当 $P_{\mathrm{Rust}}$ 与 $P_{\mathrm{OOP}}$ 语义等价（无信息损失、实现路径自然）
- **近似表达**：$\mathit{ExprB}(P) = \mathrm{Approx}$ 当且仅当 $P_{\mathrm{Rust}}$ 可实现核心意图，但实现方式或约束不同，有语义偏移
- **不可表达**：$\mathit{ExprB}(P) = \mathrm{NoExpr}$ 当且仅当 $P_{\mathrm{Rust}}$ 无法表达或需显著变形

**Def 1.2（语义等价）**

$P_{\mathrm{Rust}} \equiv P_{\mathrm{OOP}}$ 当且仅当：对任意输入 $x$，$P_{\mathrm{Rust}}(x)$ 与 $P_{\mathrm{OOP}}(x)$ 行为等价（观察等价）；且类型/约束对应关系一致。

**Axiom EIM1**：Rust 无隐式全局可变；无类继承；无运行时反射。这些限制导致部分 OOP 模式不可直接表达。

**Axiom EIM2**：Rust 的 trait、枚举、所有权、借用可直接对应 OOP 的接口、多态、封装；等价表达模式在语义上无损失。

**定理 EIM-T1**：若模式 $P$ 仅依赖接口、多态、组合、委托，则 $\mathit{ExprB}(P) = \mathrm{Same}$。

*证明*：trait 即接口；`impl Trait for T` 即多态；结构体包装即组合；委托即方法转发。由 [LANGUAGE_SEMANTICS_EXPRESSIVENESS](../../LANGUAGE_SEMANTICS_EXPRESSIVENESS.md) EB1–EB3。对任意输入 $x$，$P_{\mathrm{Rust}}(x)$ 与 $P_{\mathrm{OOP}}(x)$ 行为等价；依 Def 1.2 得 $\mathit{ExprB}(P) = \mathrm{Same}$。∎

**定理 EIM-T2**：若模式 $P$ 依赖全局可变、继承、反射，则 $\mathit{ExprB}(P) \in \{\mathrm{Approx},\, \mathrm{NoExpr}\}$。

*证明*：由 Axiom EIM1；Rust 无隐式全局可变、无类继承、无运行时反射。若 $P$ 核心依赖三者之一，则 $P_{\mathrm{Rust}}$ 必用替代（OnceLock、trait、宏）或无法实现；故 $\mathit{ExprB}(P) \in \{\mathrm{Approx},\, \mathrm{NoExpr}\}$。∎

**引理 EIM-L1**：Singleton 的 $\mathit{ExprB}(\mathrm{Singleton}) = \mathrm{Approx}$，因 GoF 依赖 `static` 可变，Rust 用 OnceLock 替代。

*证明*：由 Axiom EIM1；OnceLock 语义与 static 可变单例等价，但实现路径不同；依 Def 1.1 为 Approx。∎

**推论 EIM-C1**：等价表达模式（Factory Method、Strategy、Adapter 等）满足零成本抽象；近似表达模式可能有额外间接（如 channel）。

**引理 EIM-L2（组合表达边界）**：若 $P_1$、$P_2$ 各自 $\mathit{ExprB}(P_i) \in \{\mathrm{Same},\, \mathrm{Approx}\}$，则组合 $P_1 \circ P_2$ 的 $\mathit{ExprB}(P_1 \circ P_2) \in \{\mathrm{Same},\, \mathrm{Approx}\}$，不退化至 NoExpr。

*证明*：由 Axiom EIM2；trait 组合、委托、结构体嵌套不引入全局可变/继承/反射；最坏为 Approx。∎

**推论 EIM-C2**：等价表达模式在 `no_std` 下仍等价；近似表达模式可能有额外间接（如 channel 需 std）。

---

## 反例：违反表达边界

| 反例 | 后果 | 论证 |
| :--- | :--- | :--- |
| 在 Rust 中实现经典多继承菱形 | 无法表达；无类继承 | 由 Axiom EIM1、定理 EIM-T2 |
| 假设 `dyn Trait` 可向下转型 | 编译错误；无内置反射 | 由 Axiom EIM1 |
| 用 `static mut` 实现 Singleton 且多线程 | UB；违反 Safe 边界 | 见 [safe_unsafe_matrix](safe_unsafe_matrix.md) |

---

## 定义（非形式化对照）

| 分类 | 定义 |
|------|------|
| **等价表达** | 与 GoF/OOP 语义完全等价，无信息损失 |
| **近似表达** | 可实现核心意图，但实现方式或约束不同 |
| **不可表达** | 无法在 Rust 中表达或需显著变形 |

---

## 设计模式 × 表达边界

### 创建型（5）

| 模式 | 表达边界 | 说明 |
| :--- | :--- | :--- |
| Factory Method | 等价表达 | trait 工厂方法，语义一致 |
| Abstract Factory | 等价表达 | 枚举/结构体族 |
| Builder | 等价表达 | 链式构建，类型状态可增强 |
| Prototype | 等价表达 | Clone trait 直接对应 |
| Singleton | 近似表达 | 无全局可变，用 OnceLock 等替代 |

### 结构型（7）

| 模式 | 表达边界 | 说明 |
| :--- | :--- | :--- |
| Adapter | 等价表达 | 包装 + 委托 |
| Bridge | 等价表达 | trait 解耦抽象与实现 |
| Composite | 等价表达 | 枚举递归结构 |
| Decorator | 等价表达 | 结构体包装 |
| Facade | 等价表达 | 模块/结构体 |
| Flyweight | 等价表达 | Arc 共享 |
| Proxy | 等价表达 | 委托、延迟 |

### 行为型（11）

| 模式 | 表达边界 | 说明 |
| :--- | :--- | :--- |
| Chain of Responsibility | 等价表达 | Option/链表传递 |
| Command | 等价表达 | 闭包即命令对象 |
| Interpreter | 近似表达 | 无继承，用枚举+match |
| Iterator | 等价表达 | Iterator trait 原生 |
| Mediator | 等价表达 | 结构体协调 |
| Memento | 近似表达 | 需 Serializable/Clone，无私有状态封装 |
| Observer | 近似表达 | 无继承，用 channel/回调 |
| State | 等价表达 | 枚举/类型状态更严格 |
| Strategy | 等价表达 | trait 即策略 |
| Template Method | 近似表达 | trait 默认方法，无继承 |
| Visitor | 近似表达 | 双重分发用 match 或 trait，风格不同 |

---

## 执行模型 × 表达边界

| 模型 | 表达边界 | 说明 |
| :--- | :--- | :--- |
| 同步 | 等价表达 | 顺序执行，语义一致 |
| 异步 | 等价表达 | Future 模型，await 语义清晰 |
| 并发 | 等价表达 | Send/Sync 提供更强保证 |
| 并行 | 等价表达 | 数据并行、任务并行 |
| 分布式 | 近似表达 | 无内置 RPC，需库支持 |

---

## 近似表达详解

| 模式/模型 | 近似原因 | Rust 替代方案 |
| :--- | :--- | :--- |
| Singleton | 无全局可变；GoF 依赖 static 可变 | OnceLock、LazyLock、依赖注入 |
| Interpreter | 无继承；GoF 用类层次 | 枚举 + match、穷尽匹配 |
| Memento | 无私有状态封装；GoF 有 Originator 私有 | Clone、serde、快照类型 |
| Observer | 无继承；GoF 用 Subject/Observer 继承 | channel、`dyn Fn`、回调 |
| Template Method | 无继承；GoF 用抽象类 | trait 默认方法 |
| Visitor | 双重分发风格不同；GoF 用虚函数 | match、trait、宏 |
| 分布式 | 无内置 RPC | tonic、actix、自定义协议 |

---

## 等价表达示例

**Strategy**：trait 即策略接口，`impl Trait` 即具体策略；语义完全等价。

```rust
trait SortStrategy { fn sort(&self, data: &mut [i32]); }
struct QuickSort; impl SortStrategy for QuickSort { ... }
struct MergeSort; impl SortStrategy for MergeSort { ... }
```

**Iterator**：`Iterator` trait 为语言原生；语义等价且更强（零成本抽象）。

---

## 不可表达边界说明

| 类型 | 示例 | Rust 限制 |
| :--- | :--- | :--- |
| 全局可变隐式共享 | 经典 Singleton 的 static 可变 | 无 `static mut` 安全用法；用 OnceLock |
| 多继承 | 菱形继承、混入 | 仅 trait 多实现；无类继承 |
| 运行时反射 | 动态调用、属性注入 | 无内置反射；用宏或 trait 显式 |
| 任意子类型 | 协变/逆变复杂 | 型变严格；见 [variance_theory](../../type_theory/variance_theory.md) |

---

## 从 OOP 迁移建议

| OOP 概念 | Rust 对应 | 注意 |
| :--- | :--- | :--- |
| 继承 | trait + 组合 | 无类继承；用委托 |
| 多态 | trait + impl / dyn | 对象安全；无向下转型 |
| 全局单例 | OnceLock | 无 static mut |
| 观察者 | channel | 消息传递替代回调 |
| 访问者 | match + trait | 穷尽匹配替代虚函数 |

迁移时优先保证**等价表达**模式；**近似表达**需文档化差异。

---

## Adapter 等价表达示例

```rust
// 目标接口
trait Target { fn request(&self) -> String; }

// 被适配者
struct Adaptee { data: String }

// 适配器：包装 Adaptee，实现 Target
struct Adapter { adaptee: Adaptee }
impl Target for Adapter {
    fn request(&self) -> String {
        self.adaptee.data.clone()
    }
}
```

**形式化对应**：Adapter 持有 `Adaptee`；`impl Target for Adapter` 委托；所有权清晰：`Adapter` 拥有 `Adaptee`。

---

## Composite 等价表达示例

```rust
enum Node {
    Leaf(i32),
    Composite(Vec<Box<Node>>),
}

impl Node {
    fn sum(&self) -> i32 {
        match self {
            Node::Leaf(n) => *n,
            Node::Composite(children) => children.iter().map(|c| c.sum()).sum(),
        }
    }
}
```

**形式化对应**：`Box<Node>` 递归；`Vec` 聚合子节点；穷尽 match 保证所有变体处理。

---

## 不可表达边界说明（扩展）

| 类型 | 示例 | Rust 限制 |
| :--- | :--- | :--- |
| 全局可变隐式共享 | 经典 Singleton 的 static 可变 | 无 `static mut` 安全用法；用 OnceLock |
| 多继承 | 菱形继承、混入 | 仅 trait 多实现；无类继承 |
| 运行时反射 | 动态调用、属性注入 | 无内置反射；用宏或 trait 显式 |
| 任意子类型 | 协变/逆变复杂 | 型变严格；见 [variance_theory](../../type_theory/variance_theory.md) |
| 重载（同名不同签名的函数） | 传统 OOP 多态 | trait 方法 + 泛型；无 ad-hoc 重载 |
| 负约束 | `T: !Trait` | 仅部分支持；RFC 讨论中 |

---

## 引用

- [LANGUAGE_SEMANTICS_EXPRESSIVENESS](../../LANGUAGE_SEMANTICS_EXPRESSIVENESS.md)
- [DESIGN_MECHANISM_RATIONALE](../../DESIGN_MECHANISM_RATIONALE.md)
