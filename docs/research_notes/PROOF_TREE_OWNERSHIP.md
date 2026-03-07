# 所有权证明树 (Proof Tree: Ownership)

> **创建日期**: 2026-03-08
> **版本**: v1.0
> **定理**: T-OW1 (所有权唯一性定理)

---

## 🌳 定理陈述

```
定理 T-OW1 (所有权唯一性):
∀资源 r. 在任意时刻 t, owner(r, t) 是唯一的
```

---

## 🌿 证明树结构

```
T-OW1: 所有权唯一性
│
├── [Goal] 证明: owner(r, t) 唯一
│
├── Case 1: 初始状态
│   ├── 前提: r 被创建
│   ├── Def OW1: owner(r, t₀) = creator
│   └── ✓ 唯一性成立
│
├── Case 2: 所有权转移
│   ├── 前提: owner(r, t₁) = A
│   ├── 操作: A move r to B
│   ├── Axiom OW1: move 后 A 失去所有权
│   ├── Def OW2: move 后 owner(r, t₂) = B
│   ├── 归纳假设: t₁ 时刻唯一性成立
│   └── ✓ t₂ 时刻唯一性保持
│
├── Case 3: 借用情况
│   ├── 前提: owner(r, t) = A
│   ├── 操作: A borrow r to B (immutable)
│   ├── Axiom BR1: borrow 不改变所有权
│   ├── 结论: owner(r, t') = A (不变)
│   └── ✓ 唯一性保持
│
└── Case 4: 释放情况
    ├── 前提: owner(r, t) = A
    ├── 操作: r 离开作用域
    ├── Def OW3: Drop trait 被调用
    ├── Axiom OW3: 资源被释放
    ├── 结论: r 不再存在
    └── ✓ 唯一性空真成立
```

---

## 📋 详细证明

### 基础情形 (Base Case)

```rust
// 资源创建时
let r = Resource::new();
// owner(r) = 当前作用域
// 唯一性: ✓ (只有一个所有者)
```

### 归纳步骤 (Inductive Step)

```rust
// 假设: owner(r) = A
let b = a;  // move
// 归纳: owner(r) = B (A 失去所有权)
// 唯一性保持: ✓
```

---

## 🔍 关键引理

### Lemma 1: 移动后原所有者不可用

```
Given: owner(r, t₁) = A
       A move r to B
Prove: A 在 t₂ > t₁ 时不能访问 r

Proof:
1. 根据 Def OW2: move 转移所有权
2. 根据 Axiom OW1: move 后原引用失效
3. Rust 编译器检查: use-after-move error
4. 结论: A 无法访问 r ∎
```

### Lemma 2: 借用不转移所有权

```
Given: owner(r, t) = A
       &r (immutable borrow)
Prove: owner(r, t') = A

Proof:
1. Def BR1: borrow 创建引用，不转移所有权
2. Axiom BR1: 借用期间所有权不变
3. 结论: 所有权保持为 A ∎
```

---

## 🎯 Rust 代码验证

```rust
fn ownership_uniqueness_theorem() {
    // Case 1: 创建
    let r = vec![1, 2, 3];
    // owner(r) = 当前作用域

    // Case 2: 转移
    let s = r;  // move
    // r 不再有效
    // println!("{:?}", r); // ERROR: use of moved value

    // Case 3: 借用
    let t = &s;  // borrow
    // owner(s) 不变
    assert_eq!(s.len(), 3);  // OK: s 仍有效

} // Case 4: 释放 - s 在这里 drop
```

---

## 📊 证明复杂度

| 指标 | 值 |
|------|-----|
| 证明深度 | 4 层 |
| 分支数 | 4 个 |
| 关键引理 | 2 个 |
| 证明策略 | 结构归纳法 |

---

## 🔗 相关证明

- [借用证明树](./PROOF_TREE_BORROW.md)
- [类型安全证明树](./PROOF_TREE_TYPE_SAFETY.md)
- [核心定理完整证明](./CORE_THEOREMS_FULL_PROOFS.md)
