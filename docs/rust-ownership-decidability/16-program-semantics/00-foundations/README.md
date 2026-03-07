# 理论基础 (Foundations)

## 概述

本目录包含编程语言理论的核心理论文档，为理解 Rust 的类型系统、所有权模型和并发语义提供数学基础。

## 文档列表

| 文档 | 主题 | 大小 | 难度 | 前置知识 |
|------|------|------|------|----------|
| [00a-lambda-calculus.md](00a-lambda-calculus.md) | λ演算基础 | 14 KB | 🔴 | 离散数学 |
| [00b-type-theory-basics.md](00b-type-theory-basics.md) | 类型理论基础 | 19 KB | 🔴 | λ演算 |
| [00c-operational-semantics.md](00c-operational-semantics.md) | 操作语义 | 14 KB | 🔴 | 类型理论 |
| [00d-denotational-semantics.md](00d-denotational-semantics.md) | 指称语义 | 12 KB | 🔴 | 操作语义 |
| [00e-axiomatic-semantics.md](00e-axiomatic-semantics.md) | 公理语义 | 13 KB | 🔴 | 一阶逻辑 |

## 学习路径

### 路径A: 理论优先

```
00a (λ演算) → 00b (类型理论) → 00c (操作语义) → 00d (指称语义) → 00e (公理语义)
```

### 路径B: 应用导向

```
00a (基础) → 00b (类型) → 00c (实现) → ../01-rust-core-semantics
```

## 关键公式速查

### λ演算

- β-归约: $(\lambda x.e)\ v \rightarrow e[v/x]$
- α-等价: $\lambda x.e \equiv_\alpha \lambda y.e[y/x]$

### 类型理论

- 函数类型: $\tau_1 \rightarrow \tau_2$
- 多态: $\forall \alpha.\tau$
- 递归: $\mu \alpha.\tau$

### 语义

- 大步: $\langle e, \sigma \rangle \Downarrow \langle v, \sigma' \rangle$
- 小步: $\langle e, \sigma \rangle \rightarrow \langle e', \sigma' \rangle$
- Hoare: $\{P\}\ c\ \{Q\}$

## 与 Rust 的关联

| 理论概念 | Rust对应 |
|----------|----------|
| λ抽象 | 闭包/函数 |
| 参数多态 | 泛型 |
| 递归类型 | 枚举/递归结构 |
| 线性类型 | 所有权系统 |
| 区域类型 | 生命周期 |
| 分离逻辑 | 借用检查 |

## 延伸阅读

1. Pierce, B.C. *Types and Programming Languages* (TAPL)
2. Harper, R. *Practical Foundations for Programming Languages*
3. Winskel, G. *The Formal Semantics of Programming Languages*
4. O'Hearn, P. *Separation Logic* (分离逻辑综述)

## 状态

- [x] λ演算基础
- [x] 类型理论基础
- [x] 操作语义
- [x] 指称语义
- [x] 公理语义

**完成度**: 100% (5/5 文档)
