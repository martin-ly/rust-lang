# 证明树：类型安全定理

> **定理**: 类型安全 = 进展性 (Progress) + 保持性 (Preservation)
> **创建日期**: 2026-02-28
> **状态**: ✅ 完成

---

## 定理陈述

### Thm TY-T1 (类型安全)

对于良型程序 $e$，满足：

1. **进展性**: $e$ 是值，或存在 $e'$ 使得 $e \to e'$
2. **保持性**: 若 $e \to e'$，则 $e'$ 也是良型的

```text
Γ ⊢ e : τ  ⟹  (Value(e) ∨ ∃e'. e → e') ∧ (e → e' ⟹ Γ ⊢ e' : τ)
```

---

## 证明树可视化

```mermaid
graph TD
    subgraph "类型安全定理"
    TS[Thm TY-T1<br/>类型安全] --> PR[进展性 Progress]
    TS --> PS[保持性 Preservation]
    end

    subgraph "进展性证明"
    PR --> PR_Base[基例: 字面量/变量]
    PR --> PR_Ind[归纳步: 复合表达式]

    PR_Base --> PR_B1[整数/布尔/字符串<br/>已是值]
    PR_Base --> PR_B2[变量<br/>查找环境]

    PR_Ind --> PR_App[函数应用]
    PR_Ind --> PR_Match[模式匹配]
    PR_Ind --> PR_Borrow[借用表达式]

    PR_App --> PR_App1[函数可求值?]
    PR_App1 -->|是| PR_App2[参数可求值?]
    PR_App1 -->|否| PR_App3[求值函数]
    PR_App2 -->|是| PR_App4[β归约]
    PR_App2 -->|否| PR_App5[求值参数]
    end

    subgraph "保持性证明"
    PS --> PS_Subst[替换引理]
    PS --> PS_Eval[求值保持]

    PS_Subst --> PS_S1["Γ,x:τ₁ ⊢ e:τ₂<br/>Γ ⊢ v:τ₁<br/>——————<br/>Γ ⊢ [v/x]e:τ₂"]

    PS_Eval --> PS_Beta[β归约保持]
    PS_Eval --> PS_Match[Match归约保持]
    PS_Eval --> PS_Borrow[借用创建保持]

    PS_Beta --> PS_B1["(λx.e) v → [v/x]e<br/>由替换引理保持"]

    PS_Match --> PS_M2["match v { pᵢ ⇒ eᵢ }<br/>选择匹配分支<br/>绑定变量保持类型"]

    PS_Borrow --> PS_B3["&e 创建引用<br/>生命周期 ⊆ e的生命周期<br/>类型保持"]
    end

    subgraph "Rust特定规则"
    RS1[所有权转移保持类型] --> RS1_1[Move语义不改变类型]
    RS2[借用创建子类型] --> RS2_1["&mut T <: &T 不成立"]
    RS3[生命周期子类型] --> RS3_1["'a: 'b → &'a T <: &'b T"]
    end

    PS_B1 --> RS1
    PS_M2 --> RS2
    PS_B3 --> RS3
```

---

## 形式化证明

### 进展性 (Progress)

**定理**: 若 $\Gamma \vdash e : \tau$，则 $e$ 是值或存在 $e'$ 使 $e \to e'$。

**证明** (对推导树结构归纳):

**基例**:

- $e = n$ (整数): 已是值
- $e = b$ (布尔): 已是值
- $e = x$ (变量): 由Γ(x)=τ，运行时查找值

**归纳步**:

**Case**: $e = e_1 \ e_2$ (函数应用)

- 由IH，$e_1$ 是值或可求值
- 若 $e_1$ 可求值，则 $e \to e_1' \ e_2$
- 若 $e_1 = \lambda x.e_3$ 是值:
  - 由IH，$e_2$ 是值或可求值
  - 若 $e_2$ 可求值，则 $e \to (\lambda x.e_3) \ e_2'$
  - 若 $e_2$ 是值，则 $e \to [e_2/x]e_3$ (β归约)

**Case**: $e = \&e_1$ (借用)

- 由IH，$e_1$ 是值或可求值
- 若可求值，则 $e \to \&e_1'$
- 若是值，则 $e$ 是值 (引用值)

### 保持性 (Preservation)

**定理**: 若 $\Gamma \vdash e : \tau$ 且 $e \to e'$，则 $\Gamma \vdash e' : \tau$。

**关键引理** (替换引理):

$$
\frac{\Gamma, x:\tau_1 \vdash e : \tau_2 \quad \Gamma \vdash v : \tau_1}{\Gamma \vdash [v/x]e : \tau_2}
$$

**证明** (对求值关系归纳):

**Case**: β归约 $(\lambda x.e) \ v \to [v/x]e$

- 假设 $\Gamma \vdash (\lambda x.e) \ v : \tau_2$
- 则 $\Gamma \vdash \lambda x.e : \tau_1 \to \tau_2$ 且 $\Gamma \vdash v : \tau_1$
- 由函数类型，$\Gamma, x:\tau_1 \vdash e : \tau_2$
- 由替换引理，$\Gamma \vdash [v/x]e : \tau_2$

**Case**: 借用创建 $\&e \to \&e'$ (其中 $e \to e'$)

- 假设 $\Gamma \vdash \&e : \&'a \tau$
- 则 $\Gamma \vdash e : \tau$ 且 $\text{lft}(e) \subseteq 'a$
- 由IH，$\Gamma \vdash e' : \tau$
- 且 $\text{lft}(e') \subseteq \text{lft}(e) \subseteq 'a$
- 故 $\Gamma \vdash \&e' : \&'a \tau$

---

## Rust特定考虑

### 所有权与类型安全

```rust
// 所有权转移保持类型
let s = String::from("hello");  // s: String
let s2 = s;                      // s2: String, s 失效
// s 的类型仍然是 String，只是不能访问
```

### 借用与类型安全

```rust
// 借用创建子类型关系
let x: i32 = 42;
let r: &i32 = &x;        // &'a i32
let r2: &&i32 = &r;      // &'b &'a i32
// 满足: 'a: 'b 时，&&'a i32 <: &'b &'a i32
```

---

## 与其他定理的关系

```text
类型安全 (TY-T1)
    ├── 所有权唯一性 (OW-T2) ──→ 内存安全
    ├── 借用规则 (BR-T1) ────→ 数据竞争自由
    └── 生命周期有效 (LF-T2) ──→ 引用有效性
```

---

**维护者**: Rust 形式化研究团队
**最后更新**: 2026-02-28
**证明状态**: ✅ L2 完成
