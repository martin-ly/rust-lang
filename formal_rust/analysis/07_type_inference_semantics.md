# 类型推断语义

## 概述

本文档详细分析Rust类型推断系统的语义，包括Hindley-Milner算法、约束求解和类型推导。

## 1. 类型推断理论基础

### 1.1 Hindley-Milner类型系统

Rust的类型推断基于Hindley-Milner类型系统：

```rust
// 类型变量
type TypeVar = u32;

// 类型表达式
enum Type {
    Var(TypeVar),
    Int,
    Bool,
    Function(Box<Type>, Box<Type>),
    Generic(String, Vec<Type>),
}
```

### 1.2 类型约束

类型推断通过约束求解：

$$
C = \{ \tau_1 = \tau_2, \tau_3 = \tau_4, \ldots \}
$$

其中每个约束表示两个类型必须相等。

## 2. 约束生成

### 2.1 表达式类型推断

对于表达式 $e$，生成约束集 $C$ 和类型 $\tau$：

$$
\frac{\Gamma \vdash e : \tau, C}{\text{infer}(\Gamma, e) = (C, \tau)}
$$

### 2.2 函数类型推断

函数类型推断规则：

$$
\frac{\Gamma, x:\tau_1 \vdash e : \tau_2, C}{\Gamma \vdash \lambda x.e : \tau_1 \rightarrow \tau_2, C}
$$

## 3. 约束求解

### 3.1 统一算法

使用Robinson统一算法求解约束：

```rust
fn unify(t1: &Type, t2: &Type) -> Result<Substitution, TypeError> {
    match (t1, t2) {
        (Type::Var(v), t) | (t, Type::Var(v)) => {
            if occurs_check(v, t) {
                Err(TypeError::OccursCheck)
            } else {
                Ok(Substitution::singleton(*v, t.clone()))
            }
        }
        (Type::Int, Type::Int) => Ok(Substitution::empty()),
        (Type::Function(a1, b1), Type::Function(a2, b2)) => {
            let s1 = unify(a1, a2)?;
            let s2 = unify(&b1.apply(&s1), &b2.apply(&s1))?;
            Ok(s1.compose(&s2))
        }
        _ => Err(TypeError::Mismatch),
    }
}
```

### 3.2 泛型推断

泛型类型推断：

```rust
fn infer_generic<T>(expr: &Expr) -> Result<Type, TypeError> {
    let mut constraints = Vec::new();
    let mut type_vars = HashMap::new();
    
    // 生成约束
    let (c, t) = infer_with_generics(expr, &mut type_vars)?;
    constraints.extend(c);
    
    // 求解约束
    let substitution = solve_constraints(&constraints)?;
    
    // 应用替换
    Ok(t.apply(&substitution))
}
```

## 4. 生命周期推断

### 4.1 生命周期约束

Rust的生命周期推断生成额外的约束：

```rust
struct LifetimeConstraint {
    outlives: (Lifetime, Lifetime),
    source: Span,
}
```

### 4.2 生命周期求解

使用图算法求解生命周期约束：

```rust
fn solve_lifetimes(constraints: &[LifetimeConstraint]) -> Result<LifetimeMap, LifetimeError> {
    let mut graph = Graph::new();
    
    // 构建约束图
    for constraint in constraints {
        graph.add_edge(constraint.outlives.0, constraint.outlives.1);
    }
    
    // 检测循环
    if graph.has_cycle() {
        return Err(LifetimeError::Circular);
    }
    
    // 拓扑排序
    Ok(graph.topological_sort())
}
```

## 5. 形式化证明

### 5.1 类型推断正确性定理

**定理**: 如果 $\Gamma \vdash e : \tau, C$ 且 $C$ 可解，则 $e$ 的类型为 $\tau$。

**证明**: 通过结构归纳法证明约束生成和求解的正确性。

### 5.2 最一般类型定理

**定理**: Hindley-Milner算法产生最一般的类型。

**证明**: 通过反证法证明不存在更一般的类型。

## 6. 工程实现

### 6.1 性能优化

1. **约束缓存**: 缓存已求解的约束
2. **增量推断**: 只重新推断变更的部分
3. **并行求解**: 并行处理独立约束

### 6.2 错误恢复

```rust
fn recover_from_error(error: &TypeError) -> Vec<Suggestion> {
    match error {
        TypeError::Mismatch(t1, t2) => {
            vec![
                Suggestion::Cast(t1.clone(), t2.clone()),
                Suggestion::ChangeType(t1.clone()),
                Suggestion::ChangeType(t2.clone()),
            ]
        }
        TypeError::UnboundVariable(name) => {
            vec![Suggestion::AddBinding(name.clone())]
        }
        _ => vec![],
    }
}
```

## 7. 交叉引用

- [泛型语义分析](./04_generic_semantics.md) - 泛型系统基础
- [生命周期语义](./06_lifetime_semantics.md) - 生命周期约束
- [类型系统理论](./type_system_analysis.md) - 类型系统深度分析

## 8. 参考文献

1. Hindley-Milner Type System
2. Robinson Unification Algorithm
3. Rust Type Inference Implementation
4. Constraint-Based Type Inference
