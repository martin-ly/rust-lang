# 仿射类型系统与可判定性

> **权威来源**: Alexei P. Kopylov (2001). *Decidability of Linear Affine Logic*. Information and Computation 164:173-198

## 1. 可判定性定理

### 1.1 核心结果

**定理 (Kopylov, 1995/2001)**: 完整的命题仿射逻辑（Full Propositional Affine Logic）是**可判定的**。

包含的连接词:

- 乘法: ⊗ (tensor), ⅋ (par), ⊸ (linear implication), 1, ⊥
- 加法: & (with), ⊕ (plus), ⊤, 0
- 指数: ! (of course), ? (why not)
- 常量: 全部

判定复杂度: TOWER-Complete (非初等递归，但可判定)

### 1.2 与线性逻辑的对比

| 特性 | 线性逻辑 | 仿射逻辑 |
|------|----------|----------|
| 弱化规则 (Weakening) | 禁止 | 允许 |
| 收缩规则 (Contraction) | 禁止 | 禁止 |
| 可判定性 | 不可判定 | 可判定 |
| 计算解释 | 严格资源管理 | 允许未使用资源 |

## 2. Kopylov的证明方法

### 2.1 证明概述

Kopylov的证明基于三个关键步骤：

1. **归约到正规形式**: 将任意仿射逻辑 sequent 转换为特定正规形式
2. **向量游戏解释**: 扩展Kanovich的计算解释，适应仿射逻辑特性
3. **可终止性**: 证明决策过程必然终止

### 2.2 正规形式

一个sequent被称为正规形式，如果它满足：

- 无冗余公式: 上下文中的每个公式都是"必要"的
- 指数分离: !和?的使用受约束
- 结构约束: 特定的树状结构

形式化: Γ ⊢ Δ 是正规形式，如果满足特定的"平衡"条件

### 2.3 复杂性分析

| 逻辑系统 | 复杂度 |
|----------|--------|
| 命题逻辑 | coNP-Complete |
| 一阶逻辑 | 半可判定 (递归枚举但不可判定) |
| 线性逻辑 (MALL) | PSPACE-Complete |
| 完整线性逻辑 | 不可判定 |
| 完整仿射逻辑 | TOWER-Complete (可判定) |

## 3. 仿射类型与Rust

### 3.1 Rust是仿射语言

```rust
// 1. 资源可以不被使用 (Weakening)
fn unused_resource() {
    let x = String::from("hello");
    // x 被创建但从未使用 - 允许！
    // Drop trait确保最终清理
}

// 2. 资源最多使用一次 (No Contraction)
fn use_once() {
    let x = String::from("hello");
    let y = x;  // x 被移动
    // println!("{}", x);  // 错误! x 已被使用
}

// 3. Copy类型是线性的 (!A)
fn copy_types() {
    let n: i32 = 5;
    let m = n;  // 复制，不是移动
    let p = n;  // 再次复制 - 允许！
    // i32 实现 Copy，所以行为像 !i32
}
```

### 3.2 设计权衡

**严格线性类型系统**:

- 精确资源管理，无隐藏成本
- 编译器可优化
- 但编程繁琐，学习曲线陡峭

**仿射类型系统 (Rust)**:

- 更符合直觉，允许临时变量
- 更好的可用性
- 但需要Drop trait，运行时清理成本

## 4. Rust类型系统的仿射特性

### 4.1 所有权规则的形式化

```text
Rust所有权的仿射解释:

规则1 (Move):  x: T ⊢ let y = x; ...  [x移动到y]
               ───────────────────────
               y: T ⊢ ...              [x不再可用]

规则2 (Borrow): x: T ⊢ let r = &x; ...
                ──────────────────────
                x: T, r: &T ⊢ ...      [x和r都可用]

规则3 (Drop):   x: T ⊢ drop(x); ...
               ─────────────────
               ⊢ ...                  [资源被释放]
```

### 4.2 可判定性对Rust的意义

Rust借用检查器的可判定性:

1. 类型推断: 可判定 (基于Hindley-Milner扩展)
2. 生命周期检查: 可判定 (基于数据流分析)
3. 借用检查: 可判定 (基于NLL算法)
4. 泛型约束求解: 图灵完备 (存在不可判定情况)

关键: Rust的设计确保了核心检查是可判定的

## 5. 参考文献

1. Kopylov, A.P. (2001). Decidability of Linear Affine Logic. *Information and Computation*, 164(1):173-198.
2. Lincoln, P., Mitchell, J., Scedrov, A., & Shankar, N. (1992). Decision Problems for Propositional Linear Logic.
3. Kanovich, M.I. (1994). The Complexity of Horn Fragments of Linear Logic.
