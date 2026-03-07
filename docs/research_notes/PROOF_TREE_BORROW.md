# 借用证明树 (Proof Tree: Borrowing)

> **创建日期**: 2026-03-08
> **版本**: v1.0
> **定理**: T-BR1 (借用安全性定理)

---

## 🌳 定理陈述

```
定理 T-BR1 (借用安全性):
∀引用 &r. 在引用有效期内，被引用数据始终有效且符合借用规则
```

---

## 🌿 证明树结构

```
T-BR1: 借用安全性
│
├── [Goal] 证明: 所有借用都安全
│
├── Rule 1: 不可变借用规则
│   ├── 前提: 存在 &r
│   ├── 条件: 可同时存在多个 &r
│   ├── 限制: 不可存在 &mut r
│   ├── Lemma 1: 读取不修改
│   └── ✓ 安全性: 无数据竞争
│
├── Rule 2: 可变借用规则
│   ├── 前提: 存在 &mut r
│   ├── 条件: 只能有一个 &mut r
│   ├── 限制: 不可同时存在 &r
│   ├── Lemma 2: 独占访问
│   └── ✓ 安全性: 无二义修改
│
├── Rule 3: 生命周期规则
│   ├── 前提: 引用 &r 生命周期为 'a
│   ├── 条件: 'a ⊆ owner(r) 的生命周期
│   ├── Def LT1: 生命周期包含
│   ├── Lemma 3: 悬垂引用预防
│   └── ✓ 安全性: 无悬垂指针
│
└── Rule 4: 嵌套借用规则
    ├── 前提: & &r (引用的引用)
    ├── 条件: 外层生命周期 ⊇ 内层生命周期
    ├── Axiom LT2: 生命周期协变
    └── ✓ 安全性: 传递性保持
```

---

## 📋 详细证明

### Lemma 1: 读取不修改

```
Goal: 不可变借用期间数据不被修改

Proof:
1. 假设存在 &r (immutable borrow)
2. 根据 Rule 2: &mut r 被禁止
3. 因此无主可变访问路径
4. 数据只能通过 &r 读取
5. 结论: 数据不可变 ∎
```

### Lemma 2: 独占访问

```
Goal: 可变借用提供独占访问

Proof:
1. 假设存在 &mut r
2. 根据 Rule 2: 其他 &mut r 和 &r 被禁止
3. 只有一个活跃路径访问数据
4. 修改者身份确定
5. 结论: 独占性保证 ∎
```

### Lemma 3: 悬垂引用预防

```
Goal: 引用永远不会悬垂

Proof:
1. 引用 &r 生命周期为 'a
2. 根据 Rule 3: 'a 必须在 owner(r) 生命周期内
3. 编译时检查: borrow checker 验证
4. 运行时: 数据释放时无活跃引用
5. 结论: 无悬垂引用 ∎
```

---

## 🎯 Rust 代码验证

```rust
fn borrowing_safety_theorem() {
    let mut data = vec![1, 2, 3];

    // Rule 1: 多个不可变借用
    let r1 = &data;
    let r2 = &data;
    println!("{} {}", r1[0], r2[0]);  // OK

    // Rule 2: 可变借用独占
    let r3 = &mut data;
    r3.push(4);  // OK
    // let r4 = &data; // ERROR: cannot borrow as immutable

    // Rule 3: 生命周期检查
    let r;
    {
        let x = 5;
        // r = &x; // ERROR: x does not live long enough
    }
    // println!("{}", r); // ERROR
}
```

---

## 📊 借用检查器算法

```
BorrowCheck(程序 P):
    for each 借用点 b in P:
        if b is &r:
            check 无活跃 &mut r
        if b is &mut r:
            check 无活跃 &r 或 &mut r
        if b 离开作用域:
            释放所有以 b 为起点的借用
    return OK if 所有检查通过
```

---

## 📊 证明复杂度

| 指标 | 值 |
|------|-----|
| 证明深度 | 4 层 |
| 借用规则 | 4 条 |
| 关键引理 | 3 个 |
| 证明策略 | 规则归纳 + 反证 |

---

## 🔗 相关证明

- [所有权证明树](./PROOF_TREE_OWNERSHIP.md)
- [类型安全证明树](./PROOF_TREE_TYPE_SAFETY.md)
- [生命周期形式化](./formal_methods/lifetime_formalization.md)
