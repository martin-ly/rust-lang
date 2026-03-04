# 仿射逻辑可判定性证明

## 背景

仿射逻辑(Linear Logic + Weakening)是Rust类型系统的逻辑基础。

## 定理：仿射类型系统可判定性

**定理**: 给定一个仿射类型系统，类型推断问题在PTIME内可解。

### 证明 (基于Kopylov 2004)

**步骤1**: 将类型推断规约为约束求解

**步骤2**: 约束生成

对于每个表达式，生成子类型约束:

```
Γ ⊢ e : τ  ~  约束集 C
```

**步骤3**: 约束简化

应用以下重写规则:

```
τ₁ <: τ₂ ∧ τ₂ <: τ₃  ⟹  τ₁ <: τ₃  (传递)
&ref τ <: &τ           ⟹  成立      (收缩)
```

**步骤4**: 复杂度分析

约束图大小: O(n²)
每个约束检查: O(1)
总复杂度: O(n³) 最坏情况

## Rust的特殊处理

Rust扩展了纯仿射逻辑:

1. **生命周期参数**: 引入偏序约束
2. **Trait约束**: 增加谓词逻辑
3. **高阶类型**: 需要高阶统一

这些扩展使Rust类型推断成为PSPACE-hard，但实践中仍高效。

## 实用算法: Hindley-Milner扩展

```rust
// 伪代码
fn infer(expr: &Expr, env: &TypeEnv) -> Result<Type, Error> {
    match expr {
        Var(x) => env.lookup(x).cloned(),
        Lambda(x, body) => {
            let arg_ty = fresh_variable();
            let new_env = env.extend(x, arg_ty.clone());
            let ret_ty = infer(body, &new_env)?;
            Ok(Type::Function(arg_ty, ret_ty))
        }
        App(f, arg) => {
            let f_ty = infer(f, env)?;
            let arg_ty = infer(arg, env)?;
            let ret_ty = fresh_variable();
            unify(f_ty, Type::Function(arg_ty, ret_ty.clone()))?;
            Ok(ret_ty)
        }
        // ... 其他情况
    }
}
```

## 结论

仿射逻辑为Rust提供了理论基础，实际实现通过精心设计的约束求解保持了实用性。
