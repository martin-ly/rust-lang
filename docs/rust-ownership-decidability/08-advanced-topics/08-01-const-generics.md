# 常量泛型与类型级计算

> **权威来源**: Rust RFC 2000, min_const_generics stabilization

## 1. 常量泛型概述

常量泛型 (Const Generics) 允许类型由常量值参数化。

## 2. 与依赖类型的关系

Rust的常量泛型是受限的依赖类型 (Restricted Dependent Types)。

## 3. 可判定性分析

常量求值涉及停机问题，因此不可判定。Rust通过设置求值步骤限制来处理。

## 4. 实践案例

```rust
struct Array<T, const N: usize> {
    data: [T; N],
}
```
