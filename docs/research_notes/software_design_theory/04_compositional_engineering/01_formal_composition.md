# 组合的形式化定义

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-12
> **Rust 版本**: 1.93.0+ (Edition 2024)

---

## 定义

**Def 1.1（模块）**

模块 $M$ 为一个命名空间，包含：

- 类型定义：$\mathit{types}(M) = \{T_1, \ldots, T_k\}$
- 函数/方法：$\mathit{fns}(M) = \{f_1, \ldots, f_m\}$
- 可见性：$\mathit{pub}(M) \subseteq \mathit{types}(M) \cup \mathit{fns}(M)$

**Def 1.2（模块依赖）**

$M_1$ 依赖 $M_2$（记 $M_1 \prec M_2$）当且仅当 $M_1$ 引用 $M_2$ 的 `pub` 项。依赖图 $G = (V, E)$ 其中 $V = \{M_i\}$，$(M_i, M_j) \in E \Leftrightarrow M_i \prec M_j$。

**Def 1.3（组合）**

组合 $C = M_1 \oplus \cdots \oplus M_n$ 满足：

1. **无环**：$G$ 为 DAG
2. **接口一致**：$M_i$ 使用 $M_j$ 的项时，类型签名匹配
3. **命名无冲突**：$\mathit{pub}(M_i) \cap \mathit{pub}(M_j) = \emptyset$ 当 $i \neq j$（或通过路径隔离）

**Def 1.4（Trait 组合）**

设 trait $T$ 由 $T_1, \ldots, T_k$ 约束（$T: T_1 + T_2 + \cdots$）。`impl T for A` 的组合满足：

- $A$ 满足 $T_1, \ldots, T_k$ 的约束
- 实现 $T$ 的所有 required 方法

**Def 1.5（泛型组合）**

设 $F\langle T \rangle$ 为泛型结构。组合满足：

- $T$ 满足 $F$ 的 trait 约束
- 单态化后类型正确；无冲突的 impl

---

## 公理

**Axiom CE1**：组合无命名冲突；模块路径唯一（`crate::module::item`）。

**Axiom CE2**：组合保持类型安全；若各组件良型，则组合良型。

**Axiom CE3**：组合保持所有权与借用规则；跨模块调用不违反规则。

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
|------|------|
| 循环依赖 | 编译失败；`mod a` 用 `b`，`mod b` 用 `a` |
| 泛型约束不一致 | 模块边界类型不匹配 |
| pub 泄漏 unsafe | 破坏组合安全性；CE-T1 不成立 |

---

## 引用

- [type_system_foundations](../../type_theory/type_system_foundations.md)
- [trait_system_formalization](../../type_theory/trait_system_formalization.md)
