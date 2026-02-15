# 组合的形式化定义

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-12
> **Rust 版本**: 1.93.0+ (Edition 2024)

---

## 📊 目录

- [组合的形式化定义](#组合的形式化定义)
  - [定义](#定义)
  - [公理](#公理)
  - [定理与引理（形式化论证）](#定理与引理形式化论证)
  - [Rust 对应](#rust-对应)
  - [设计模式组合示例](#设计模式组合示例)
  - [Crate 组合](#crate-组合)
  - [组合反例](#组合反例)
  - [引用](#引用)

---

## 定义

**Def 1.1（模块）**:

模块 $M$ 为一个命名空间，包含：

- 类型定义：$\mathit{types}(M) = \{T_1, \ldots, T_k\}$
- 函数/方法：$\mathit{fns}(M) = \{f_1, \ldots, f_m\}$
- 可见性：$\mathit{pub}(M) \subseteq \mathit{types}(M) \cup \mathit{fns}(M)$

**Def 1.2（模块依赖）**:

$M_1$ 依赖 $M_2$（记 $M_1 \prec M_2$）当且仅当 $M_1$ 引用 $M_2$ 的 `pub` 项。依赖图 $G = (V, E)$ 其中 $V = \{M_i\}$，$(M_i, M_j) \in E \Leftrightarrow M_i \prec M_j$。

**Def 1.3（组合）**:

组合 $C = M_1 \oplus \cdots \oplus M_n$ 满足：

1. **无环**：$G$ 为 DAG
2. **接口一致**：$M_i$ 使用 $M_j$ 的项时，类型签名匹配
3. **命名无冲突**：$\mathit{pub}(M_i) \cap \mathit{pub}(M_j) = \emptyset$ 当 $i \neq j$（或通过路径隔离）

**Def 1.4（Trait 组合）**:

设 trait $T$ 由 $T_1, \ldots, T_k$ 约束（$T: T_1 + T_2 + \cdots$）。`impl T for A` 的组合满足：

- $A$ 满足 $T_1, \ldots, T_k$ 的约束
- 实现 $T$ 的所有 required 方法

**Def 1.5（泛型组合）**:

设 $F\langle T \rangle$ 为泛型结构。组合满足：

- $T$ 满足 $F$ 的 trait 约束
- 单态化后类型正确；无冲突的 impl

---

## 公理

**Axiom CE1**：组合无命名冲突；模块路径唯一（`crate::module::item`）。

**Axiom CE2**：组合保持类型安全；若各组件良型，则组合良型。

**Axiom CE3**：组合保持所有权与借用规则；跨模块调用不违反规则。

---

## 定理与引理（形式化论证）

**定理 CE-T1（组合保持内存安全）**：若各模块 $M_i$ 满足 [ownership_model](../../formal_methods/ownership_model.md) 定理 T2、T3（所有权唯一性、内存安全），则组合 $C = M_1 \oplus \cdots \oplus M_n$ 满足内存安全。

*证明*：见 [02_effectiveness_proofs](02_effectiveness_proofs.md) CE-T1；归纳基：单模块；归纳步：添加 $M_n$ 时，值传递/所有权转移符合 Def 1.3 接口一致；无新分配模式违反规则。∎

**定理 CE-T2（组合保持数据竞争自由）**：若各模块满足 [borrow_checker_proof](../../formal_methods/borrow_checker_proof.md) 定理 T1，且跨线程传递仅 Send/Sync、共享仅 Sync，则组合保持数据竞争自由。

*证明*：见 [02_effectiveness_proofs](02_effectiveness_proofs.md) CE-T2；Send/Sync 为结构性质；跨模块边界约束不变。∎

**定理 CE-T3（组合保持类型安全）**：若各模块良型，且 [type_system_foundations](../../type_theory/type_system_foundations.md) 进展性 T1、保持性 T2、类型安全 T3 成立，则组合程序良型且类型安全。

*证明*：见 [02_effectiveness_proofs](02_effectiveness_proofs.md) CE-T3；类型环境合并无冲突；跨模块调用保持类型。∎

**引理 CE-L1（模块无环）**：若 $C = M_1 \oplus \cdots \oplus M_n$ 满足 Def 1.3 无环，则依赖图 $G$ 为 DAG；$M_i \prec^* M_j \land M_j \prec^* M_i \Rightarrow \bot$。

*证明*：由 Def 1.3 无环；$\prec^*$ 为传递闭包，环存在则 $M_i \prec^* M_i$，矛盾。∎

**推论 CE-C1**：组合 CE-T1、CE-T2、CE-T3 可组合；若 $C$ 满足 CE-T1、CE-T2、CE-T3，则 $C$ 为 Safe 且良型。

*证明*：由各定理陈述；内存安全 + 数据竞争自由 + 类型安全 ⇒ Safe。∎

**推论 CE-C2（组合反例）**：若 $M_n$ 的 `pub` API 泄漏 `unsafe` 或违反借用规则，则 CE-T1 或 CE-T2 不成立；组合后可能 UB。

*证明*：由 Axiom CE2、CE3；泄漏 unsafe 破坏安全抽象；违反借用规则违反 borrow T1。∎

---

## Rust 对应

```rust
// 模块结构
mod a {
    pub struct A { pub x: i32 }
}
mod b {
    use super::a::A;
    pub fn use_a(a: A) -> i32 { a.x }
}

// 组合：main 使用 a 和 b
fn main() {
    let a = a::A { x: 42 };
    let y = b::use_a(a);  // a 所有权转移
}
```

**形式化对应**：`mod a`、`mod b` 为 $M_1$、$M_2$；`main` 组合两者。依赖：$b \prec a$。

---

## 设计模式组合示例

**Repository + Factory Method**：

```rust
trait Repository<T> { fn find(&self, id: u64) -> Option<T>; fn save(&mut self, t: T); }
trait Product { fn id(&self) -> u64; }
trait ProductFactory { fn create(&self) -> Box<dyn Product>; }

struct Order { id: u64 }
impl Order {
    fn from_product(p: Box<dyn Product>) -> Self { Self { id: p.id() } }
}

struct OrderService<R: Repository<Order>, F: ProductFactory> {
    repo: R,
    factory: F,
}
impl<R: Repository<Order>, F: ProductFactory> OrderService<R, F> {
    fn place_order(&mut self) -> Result<(), String> {
        let product = self.factory.create();
        let order = Order::from_product(product);
        self.repo.save(order);
        Ok(())
    }
}
// 组合满足 CE-T1：各组件 Safe 则组合 Safe
```

**Decorator 链组合**：

```rust
trait Service { fn call(&self) -> i32; }
struct Core;
impl Service for Core { fn call(&self) -> i32 { 42 } }
struct Logging<S: Service>(S);
impl<S: Service> Service for Logging<S> {
    fn call(&self) -> i32 { println!("call"); self.0.call() }
}
// Logging(Core) 或 Logging(Logging(Core))；组合无环
```

---

## Crate 组合

```rust
// crate_a 提供 trait
pub trait Service { fn do_work(&self) -> i32; }

// crate_b 依赖 crate_a，实现 Service
use crate_a::Service;
pub struct MyService;
impl Service for MyService {
    fn do_work(&self) -> i32 { 42 }
}

// crate_c 依赖 a、b，使用组合
use crate_a::Service;
use crate_b::MyService;
fn main() {
    let s = MyService;
    assert_eq!(s.do_work(), 42);
}
```

**Def 1.3 对应**：$M_1 = \mathrm{crate\_a}$，$M_2 = \mathrm{crate\_b}$，$M_3 = \mathrm{crate\_c}$；$M_3 \prec M_2 \prec M_1$；无环。

---

## 组合反例

| 反例 | 后果 |
| :--- | :--- |
| 循环依赖 | 编译失败；`mod a` 用 `b`，`mod b` 用 `a` |
| 泛型约束不一致 | 模块边界类型不匹配 |
| pub 泄漏 unsafe | 破坏组合安全性；CE-T1 不成立 |

---

## 引用

- [type_system_foundations](../../type_theory/type_system_foundations.md)
- [trait_system_formalization](../../type_theory/trait_system_formalization.md)
