# Ownership Formalization（所有权形式化）

> **层级**: L4 形式化理论
> **前置概念**: [Ownership](../01_foundation/01_ownership.md) · [Borrowing](../01_foundation/02_borrowing.md) · [Linear Logic](./01_linear_logic.md) · [Type Theory](./02_type_theory.md)
> **后置概念**: [RustBelt](./04_rustbelt.md)
> **主要来源**: [COR: ETH Zurich] · [RustBelt: POPL 2018] · [Aeneas] · [RefinedRust]

---

**变更日志**:

- v1.0 (2026-05-12): 初始版本，完成 COR 形式化、区域类型、分离逻辑、操作语义、思维导图

---

## 一、权威定义（Definition）

### 1.1 COR（Calculus of Ownership and Reference）

> **[COR: ETH Zurich]** We formalize a core of Rust as Calculus of Ownership and Reference (COR), whose design has been affected by the safe layer of λRust in the RustBelt paper. It is a typed procedural language with a Rust-like ownership system.

COR 的核心类型判断：

```text
  Σ; Γ ⊢ e : τ {Σ'}

其中:
  Σ  = 堆状态（heap typing）
  Γ  = 局部变量上下文
  e  = 表达式
  τ  = 类型
  Σ' = 执行后的堆状态
```

### 1.2 RustBelt 形式化

> **[RustBelt: POPL 2018]** RustBelt is the first formal(and machine-checked) foundations for safe encapsulation of unsafe code in a realistic systems language. We present a novel semantic model of Rust based on *Iris*, a higher-order concurrent separation logic framework.

---

## 二、概念属性矩阵

### 2.1 形式化方法对比矩阵

| **项目** | **COR** | **RustBelt (λRust)** | **Aeneas** | **RefinedRust** | **Kani** |
|:---|:---|:---|:---|:---|:---|
| **机构** | ETH Zurich | MPI-SWS | Inria | MPI-SWS | AWS |
| **逻辑基础** | 操作语义 | Iris 分离逻辑 | 纯函数式 Rocq | 分离逻辑 | CBMC 模型检测 |
| **验证目标** | 类型安全 | 内存安全 + 并发 | 功能正确性 | 功能正确性 | 并发路径 |
| **覆盖范围** | Safe Rust 核心 | Safe + Unsafe | Safe Rust | Safe + Unsafe | Safe Rust |
| **工具支持** | 无（纸面） | Coq (Iris) | Rocq/Lean | Coq | 自动化 |
| **工业可用** | 否 | 否 | 学术 | 否 | ✅ 是 |

### 2.2 所有权状态的形式化

| **状态** | **符号** | **可读** | **可写** | **可转移** | **形式化** |
|:---|:---|:---|:---|:---|:---|
| 独有所有权 | `Own(p)` | ✅ | ✅ | ✅ | `p ↦_1 v`（独占指针） |
| 共享借用 | `Shr(p)` | ✅ | ❌ | ❌ | `p ↦_π v`（分数权限 π < 1） |
| 可变借用 | `Mut(p)` | ❌ | ✅ | ❌ | `p ↦_1 v`（临时独占） |
| 已释放 | `Dealloc(p)` | ❌ | ❌ | ❌ | `p ↦ ⊥` |

---

## 三、形式化理论根基

### 3.1 操作语义（Operational Semantics）

```text
赋值（Move）:
  ⟨let y = x, σ⟩ → ⟨skip, σ[y ↦ σ(x)][x ↦ ⊥]⟩
  // x 的值移动到 y，x 标记为未初始化

借用（Borrow）:
  ⟨let r = &x, σ⟩ → ⟨skip, σ[r ↦ &x]⟩
  // r 获得对 x 的共享引用，x 仍有效

可变借用（Mut Borrow）:
  ⟨let r = &mut x, σ⟩ → ⟨skip, σ[r ↦ &mut x]⟩
  // x 在 r 存活期间被冻结

释放（Drop）:
  ⟨drop(x), σ⟩ → ⟨skip, σ[heap.dealloc(x)]⟩
```

### 3.2 分离逻辑中的所有权

```text
分离逻辑断言:
  own(x, T)    —— x 拥有类型 T 的值
  &{π}x        —— x 的分数权限（π = 1 独占，π < 1 共享）
  x ↦ v        —— 堆中 x 指向 v

规则:
  own(x, T) * own(y, U)  →  x 和 y 的堆区域不相交（分离性）
  &{π}x * &{ρ}x  ⇔  π + ρ ≤ 1  （权限可加性）
```

---

## 四、思维导图

```mermaid
graph TD
    A[Ownership Formalization] --> B[COR]
    A --> C[λRust / RustBelt]
    A --> D[分离逻辑]
    A --> E[工具链]

    B --> B1[Σ; Γ ⊢ e : τ {Σ'}]
    B --> B2[堆状态转换]
    B --> B3[Move / Borrow / Drop]

    C --> C1[Iris 高阶逻辑]
    C --> C2[高阶幽灵状态]
    C --> C3[Invariants]

    D --> D1[Own(x, T)]
    D --> D2[Fractional Permissions]
    D --> D3[Separating Conjunction]

    E --> E1[Creusot]
    E --> E2[Verus]
    E --> E3[Kani]
    E --> E4[Aeneas]
```

---

## 五、定理推理链

### 5.1 RustBelt 核心定理

```text
定理 (RustBelt Safety):
前提: 程序在 Safe Rust 中通过编译
    ↓
结论: 程序满足内存安全（无 UAF/DF）+ 数据竞争自由

扩展定理（Unsafe 封装）:
前提: Unsafe 代码满足 Iris 逻辑规约
    ↓
结论: Safe 抽象层保证的安全性在 Unsafe 实现下仍然成立
```

---

## 六、知识来源关系

| **论断** | **来源** | **可信度** |
|:---|:---|:---|
| COR 形式化 Rust 核心 | [COR: ETH Zurich] | ✅ |
| RustBelt 在 Iris 中验证 Rust | [RustBelt: POPL 2018] | ✅ |
| 分离逻辑描述所有权 | [RustBelt] · [Separation Logic] | ✅ |
| Aeneas 翻译到纯函数式 | [Aeneas Paper] | ✅ |
| Kani 模型检测 Rust | [AWS Kani] | ✅ |

---

## 七、待补充

- [ ] **TODO**: 补充 Tree Borrows / Stacked Borrows 内存模型
- [ ] **TODO**: 补充 Creusot/Verus 的功能正确性验证示例
