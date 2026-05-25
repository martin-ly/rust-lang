# Const Trait Preview

> **Bloom 层级**: 分析 → 评价
> **A/S/P 标记**: **S+P** — Structure + Procedure
> **双维定位**: C×Eva — 评价 const trait 的设计权衡
> **前置依赖**: [Trait](../02_intermediate/01_traits.md) · [Const Generics](../02_intermediate/02_generics.md)
> **后置延伸**: [Const Trait Impl](./11_const_trait_impl_preview.md)

> **来源**: [Rust Reference — Const Eval](https://doc.rust-lang.org/reference/const_eval.html) · [RFC 2632](https://rust-lang.github.io/rfcs/2632-const-trait-impl.html)

### 10.4 边界测试：const trait 与泛型 const 求值（编译错误/未来特性）

```rust,ignore
// 概念代码: const trait（开发中）
// const trait Compute {
//     const fn compute() -> i32;
// }

// ❌ 编译错误: const trait 不是当前稳定特性
// 它允许在 const context 中使用 trait bounds

fn main() {
    // 当前限制: 不能在 const fn 中使用 trait 方法
    // const fn double<T: std::ops::Add>(x: T) -> T { x + x } // 错误
}
```

> **修正**: **Const traits** 是 Rust 常量求值的关键扩展：1) `~const Trait` 语法标记"可在 const 上下文中使用的 trait"；2) `const impl Trait for Type` 标记实现支持常量求值；3) 目标：在 `const fn` 中使用泛型 trait bound（如 `T: ~const Add`）。当前状态：部分实现（nightly `const_trait_impl`）， design 迭代中。替代方案：1) `macro_rules!` 生成多份代码；2) `min_specialization` 为常量/非常量分别实现；3) 放弃 const，使用运行时计算。这与 C++ 的 `constexpr`（函数可自动在编译期/运行期使用，无需特殊标记）或 D 的 `CTFE`（Compile Time Function Execution，类似但更灵活）不同——Rust 追求显式控制：const 函数有严格的副作用限制，trait 的 const 支持需显式声明。[来源: [Const Trait RFC](https://rust-lang.github.io/rfcs/2632-const-trait-impl.html)] · [来源: [Const Generics](https://rust-lang.github.io/rfcs/2000-const-generics.html)]
