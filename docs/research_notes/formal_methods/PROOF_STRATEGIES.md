# 证明策略

> **创建日期**: 2026-02-28
> **最后更新**: 2026-02-28
> **状态**: ✅ 已完成
> **领域**: 形式化证明方法论

---

## 概述

本文档系统梳理形式化证明中常用的策略和技术，为Rust形式化方法的证明提供方法论指导。

---

## 一、归纳证明策略

### 1.1 数学归纳法

**原理**:

```text
证明 P(0)        (基础情形)
证明 ∀n. P(n) → P(n+1)    (归纳步骤)
───────────────────────────────────
       ∀n. P(n)
```

**应用场景**:

- 递归函数终止性
- 迭代次数相关的性质
- 归纳定义的数据结构

**Rust示例 - 列表长度**:

```rust
// 证明: length(append(xs, ys)) = length(xs) + length(ys)

// 基础: xs = []
length(append([], ys)) = length(ys) = 0 + length(ys)

// 归纳: xs = x :: xs'
length(append(x::xs', ys))
= length(x :: append(xs', ys))     // 由append定义
= 1 + length(append(xs', ys))
= 1 + length(xs') + length(ys)     // 归纳假设
= length(x::xs') + length(ys)
```

### 1.2 结构归纳法

**原理**:

```text
对于归纳定义的类型T，证明:
- 对所有基础构造子c，P(c)
- 对所有归纳构造子，若P对子结构成立，则对整体成立
```

**应用场景**:

- 表达式求值
- 抽象语法树遍历
- 类型推导

**Rust示例 - 表达式求值**:

```rust
enum Expr {
    Num(i32),
    Add(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
}

// 证明求值终止
fn eval_terminates(e: &Expr) -> bool {
    match e {
        Num(_) => true,                    // 基础
        Add(e1, e2) => {                   // 归纳
            eval_terminates(e1) &&         // IH: e1终止
            eval_terminates(e2)            // IH: e2终止
        }
        Mul(e1, e2) => eval_terminates(e1) && eval_terminates(e2),
    }
}
```

### 1.3 良基归纳

**原理**:

```text
设 < 是良基关系(无无限下降链)
证明 ∀x. (∀y < x. P(y)) → P(x)
────────────────────────────────
          ∀x. P(x)
```

**应用场景**:

- 递归函数终止性(非结构递归)
- 复杂数据结构遍历

**Rust示例 - 快速排序**:

```rust
fn quicksort<T: Ord>(arr: &mut [T]) {
    if arr.len() <= 1 { return; }

    let pivot = partition(arr);
    let (left, right) = arr.split_at_mut(pivot);

    // 递归在更小的子数组上
    quicksort(left);      // left.len < arr.len
    quicksort(&mut right[1..]);  // right.len < arr.len
}

// 终止性: 基于数组长度的良基归纳
```

---

## 二、共归纳证明策略

### 2.1 共归纳原理

**用于证明**: 最大不动点的性质(如无限行为)

**与归纳的区别**:

- 归纳: 证明最小不动点(有限构造)
- 共归纳: 证明最大不动点(可能无限)

### 2.2 双模拟

**定义**: R是双模拟如果

```text
s₁ R s₂ 且 s₁ → s₁'  ⇒  ∃s₂'. s₂ → s₂' 且 s₁' R s₂'
s₁ R s₂ 且 s₂ → s₂'  ⇒  ∃s₁'. s₁ → s₁' 且 s₁' R s₂'
```

**应用**: 证明程序等价

---

## 三、反证法策略

### 3.1 基本形式

**原理**:

```text
要证: P
假设: ¬P
推出: ⊥ (矛盾)
结论: P
```

### 3.2 在Rust证明中的应用

**示例 - 借用唯一性**:

```text
要证: 不能同时有两个可变借用

反设: ∃r₁, r₂. mutable(r₁) ∧ mutable(r₂) ∧ r₁ ≠ r₂ ∧ valid(r₁) ∧ valid(r₂)

矛盾: 违反借用规则，编译器拒绝

结论: 假设不成立，借用唯一性成立
```

### 3.3 对角线法

**应用**: 证明不可判定性、不可能性结果

---

## 四、构造性证明

### 4.1 存在性构造

**原理**: 要证 ∃x. P(x)，构造具体的witness

**Rust示例**:

```rust
// 证明: 存在满足某性质的类型

// 构造性证明: 给出具体类型
struct MyType { /* ... */ }

impl MyTrait for MyType {
    // 实现所需方法
}

// 证明了: ∃T. T: MyTrait
```

### 4.2 算法构造

**原理**: 构造算法同时证明存在性和计算方法

---

## 五、不变式证明

### 5.1 循环不变式

**定义**: 在循环每次迭代前后都成立的性质

**模板**:

```text
{P}
while b do
    {I ∧ b}  // 不变式且条件成立
    C
    {I}      // 不变式保持
{I ∧ ¬b}     // 不变式且条件不成立 → 目标
```

**Rust示例**:

```rust
// 证明: 二分查找正确
fn binary_search(arr: &[i32], target: i32) -> Option<usize> {
    let mut left = 0;
    let mut right = arr.len();

    // 不变式: target如果在arr中，则在arr[left..right]中
    while left < right {
        let mid = (left + right) / 2;
        match arr[mid].cmp(&target) {
            Equal => return Some(mid),
            Less => left = mid + 1,    // 保持不变式
            Greater => right = mid,    // 保持不变式
        }
    }
    None
}
```

### 5.2 资源不变式

**在分离逻辑中**:

```text
{I * P} C {I * Q}

I是资源不变式，在命令前后都保持
```

---

## 六、抽象与精化

### 6.1 数据抽象

**原理**: 用抽象状态代替具体表示

**Rust示例 - 栈**:

```rust
// 抽象: 栈是元素的序列
// 具体: Vec实现

// 抽象操作
// push(s, x) = s ++ [x]
// pop(s) = (s', x) where s = s' ++ [x]

// 证明: 具体实现满足抽象规范
```

### 6.2 精化关系

**定义**: 具体实现C精化抽象规范A

```text
C ⊑ A  ⟺  C的行为是A行为的子集
```

---

## 七、组合证明

### 7.1 模块化证明

**原理**: 分而治之，分别验证模块，再组合

**Rust示例**:

```rust
// 模块A: 已验证
mod A {
    #[ensures(result > 0)]
    pub fn f(x: i32) -> i32 { /* ... */ }
}

// 模块B: 使用A的规范验证
mod B {
    use A::f;

    #[requires(x > 0)]
    pub fn g(x: i32) -> i32 {
        f(x) + 1  // 由f的规范，f(x) > 0
    }
}
```

### 7.2 组合规则

**顺序组合**:

```text
{P} C₁ {Q}    {Q} C₂ {R}
─────────────────────────
      {P} C₁; C₂ {R}
```

**并行组合** (分离逻辑):

```text
{P₁} C₁ {Q₁}    {P₂} C₂ {Q₂}
────────────────────────────────
{P₁ * P₂} C₁ || C₂ {Q₁ * Q₂}
```

---

## 八、自动化策略

### 8.1 决策过程

**可判定理论**:

- 命题逻辑: SAT求解器
- 线性算术: SMT求解器
- 数组理论: SMT求解器

### 8.2 证明搜索

**策略**:

- 目标驱动 (后向搜索)
- 假设驱动 (前向搜索)
- 中间引理发现

### 8.3 在Rust工具中的应用

| 工具 | 自动化程度 | 策略 |
| :--- | :--- | :--- |
| Kani | 高 | 模型检测 |
| Creusot | 中 | WP + SMT |
| Prusti | 中 | Viper框架 |
| Coq | 低 | 交互式 |

---

## 九、证明策略选择指南

| 问题类型 | 推荐策略 | 工具 |
| :--- | :--- | :--- |
| 递归函数 | 结构归纳 | Coq/Lean |
| 循环程序 | 不变式 | Why3/Dafny |
| 并发程序 | 分离逻辑 | Iris/Viper |
| 内存安全 | 分离逻辑 | VeriFast |
| 程序等价 | 双模拟 | Coq |
| 类型安全 | 进展+保持 | 手写/Coq |

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-28
**状态**: ✅ 证明策略文档完成
