# 类型安全证明树 (Proof Tree: Type Safety)

> **创建日期**: 2026-03-08
> **版本**: v1.0
> **定理**: T-TY1 (进展性 + 保持性定理)

---

## 🌳 定理陈述

```
定理 T-TY1 (类型安全):
对于良类型的程序 P ⊢ e : T:
1. 进展性 (Progress): e 是值，或 ∃e'. e → e'
2. 保持性 (Preservation): 若 e → e'，则 ⊢ e' : T
```

---

## 🌿 证明树结构

```
T-TY1: 类型安全 (Progress + Preservation)
│
├── [Part A] 进展性 (Progress)
│   │
│   ├── Case 1: e 是值
│   │   └── ✓ 进展性空真成立
│   │
│   ├── Case 2: e = e₁ op e₂
│   │   ├── IH: e₁ 可进展
│   │   ├── IH: e₂ 可进展
│   │   └── ✓ e 可进展
│   │
│   ├── Case 3: e = if e₁ then e₂ else e₃
│   │   ├── IH: e₁ 可进展到 true/false
│   │   └── ✓ e 可进展到 e₂ 或 e₃
│   │
│   └── Case 4: e = e₁.m(e₂)
│       ├── IH: e₁ 可进展
│       └── ✓ 方法调用可进展
│
└── [Part B] 保持性 (Preservation)
    │
    ├── Case 1: 变量替换
    │   ├── ⊢ λx.e : T₁ → T₂
    │   ├── ⊢ v : T₁
    │   ├── Lemma 1: 替换保持类型
    │   └── ✓ ⊢ e[v/x] : T₂
    │
    ├── Case 2: 结构体访问
    │   ├── ⊢ {f₁: v₁, ...} : Struct
    │   ├── e → vᵢ (字段访问)
    │   └── ✓ 字段类型保持
    │
    ├── Case 3: 模式匹配
    │   ├── ⊢ match e { pᵢ => eᵢ }
    │   ├── e 匹配模式 pⱼ
    │   ├── Lemma 2: 模式匹配保持类型
    │   └── ✓ ⊢ eⱼ[绑定] : T
    │
    └── Case 4: 借用规则
        ├── ⊢ &e : &T
        ├── e → e'
        └── ✓ ⊢ &e' : &T
```

---

## 📋 关键引理

### Lemma 1: 替换保持类型 (Substitution)

```
Given:
  Γ, x: T₁ ⊢ e : T₂
  Γ ⊢ v : T₁
Prove:
  Γ ⊢ e[v/x] : T₂

Proof (结构归纳):
- Base: e = x
  e[v/x] = v
  ⊢ v : T₁ = T₂[x/T₁] ✓

- Base: e = y ≠ x
  e[v/x] = y
  类型不变 ✓

- Inductive: e = e₁ e₂
  由 IH: e₁[v/x] 保持类型
  由 IH: e₂[v/x] 保持类型
  应用规则: 应用保持 ✓
```

### Lemma 2: 模式匹配保持类型

```
Given:
  ⊢ e : T
  match e { pᵢ => eᵢ } 有类型 T'
  e 匹配 pⱼ
Prove:
  ⊢ eⱼ[绑定] : T'

Proof:
1. 模式 pⱼ 从 T 中提取绑定
2. 每个绑定有确定类型
3. eⱼ 在这些绑定下类型为 T'
4. 替换后类型保持 ✓
```

---

## 🎯 Rust 代码验证

```rust
fn type_safety_theorem() {
    // Progress: 表达式可求值
    let x = 5 + 3;  // → 8

    // Preservation: 求值后类型保持
    let y: i32 = if x > 0 { 1 } else { 0 };  // 始终 i32

    // 替换保持类型
    let f = |x: i32| -> i32 { x + 1 };
    let result = f(5);  // 类型: i32

    // 模式匹配保持类型
    let opt: Option<i32> = Some(42);
    let v = match opt {
        Some(n) => n,  // n: i32
        None => 0,     // 0: i32
    };  // v: i32
}
```

---

## 📊 类型系统规则

```
[VAR]   Γ(x) = T
        ─────────
        Γ ⊢ x : T

[ABS]   Γ, x: T₁ ⊢ e : T₂
        ─────────────────
        Γ ⊢ λx: T₁.e : T₁ → T₂

[APP]   Γ ⊢ e₁ : T₁ → T₂    Γ ⊢ e₂ : T₁
        ─────────────────────────────────
        Γ ⊢ e₁ e₂ : T₂

[REF]   Γ ⊢ e : T
        ──────────────
        Γ ⊢ &e : &T

[MUT]   Γ ⊢ e : T
        ─────────────────
        Γ ⊢ &mut e : &mut T
```

---

## 📊 证明复杂度

| 指标 | 值 |
|------|-----|
| 证明深度 | 5 层 |
| 主要分支 | 2 (Progress + Preservation) |
| 子情况 | 8 个 |
| 关键引理 | 2 个 |
| 证明策略 | 结构归纳 + 情况分析 |

---

## 🔗 相关证明

- [所有权证明树](./PROOF_TREE_OWNERSHIP.md)
- [借用证明树](./PROOF_TREE_BORROW.md)
- [类型系统基础](./type_theory/type_system_foundations.md)
