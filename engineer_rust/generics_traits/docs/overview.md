# 泛型与Trait（Generics & Traits）

## 1. 工程原理与定义（Principle & Definition）

泛型允许类型参数化，提升代码复用与类型安全。Trait定义行为接口，实现多态。Rust 泛型通过单态化实现零成本抽象。
Generics enable type parameterization for code reuse and type safety. Traits define behavioral interfaces for polymorphism. Rust generics achieve zero-cost abstraction via monomorphization.

## 2. Rust 1.88 新特性工程化应用

- `async fn in traits`：trait可直接定义async方法，提升异步多态能力。
- trait对象向上转型：支持trait对象的安全类型提升。
- GATs（Generic Associated Types）：提升trait表达力。

## 3. 典型场景与最佳实践（Typical Scenarios & Best Practices）

- 使用 `impl Trait` 简化返回类型。
- 结合生命周期参数实现安全多态。
- 通过GATs实现高阶抽象。
- 动态trait对象（dyn Trait）与静态泛型的权衡。

**最佳实践：**

- 优先使用泛型实现零成本抽象。
- 复杂多态场景下结合 trait 对象。
- 利用GATs提升trait表达力。
- 结合自动化测试覆盖泛型边界。

## 4. 常见问题 FAQ

- Q: Rust trait对象和泛型的主要区别？
  A: trait对象支持运行时多态，泛型为编译期单态化，性能更优。
- Q: 如何选择 impl Trait 和 dyn Trait？
  A: impl Trait 性能更优，dyn Trait 更灵活。
- Q: GATs 有哪些典型应用？
  A: 适用于高阶trait、异步流等复杂场景。

## 5. 参考与扩展阅读

- [Rust 官方泛型与Trait文档](https://doc.rust-lang.org/book/ch10-00-generics.html)
- [GATs 介绍](https://blog.rust-lang.org/inside-rust/2022/06/08/gats-stabilization.html)
