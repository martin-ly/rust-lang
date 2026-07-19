# 模块化（Modularity）

## 1. 工程原理与国际定义对标（Principle & International Definition）

模块化是指将系统划分为独立、可复用、易维护的模块，提升代码结构清晰度和可扩展性。对标[Wikipedia: Modularity](https://en.wikipedia.org/wiki/Modularity)定义，模块化强调关注点分离与组合优于继承。
Modularity refers to dividing a system into independent, reusable, and maintainable modules, improving code structure clarity and extensibility. According to [Wikipedia: Modularity](https://en.wikipedia.org/wiki/Modularity), modularity emphasizes separation of concerns and composition over inheritance.

## 2. Rust 1.88 新特性工程化应用

- pub(crate)/pub(super)：灵活控制模块可见性。
- inline mod：简化小型模块定义。
- cargo workspaces：多包协作开发。

## 3. 典型惯用法（Idioms）

- 用mod/文件夹组织模块。
- 用pub/pub(crate)控制可见性。
- 用cargo workspace管理多包项目。
- 用trait抽象模块接口。

## 4. 代码示例（含1.88新特性）

```rust
// 见 examples/basic_mod.rs
```

## 5. 工程批判性与哲学思辨

- 关注点分离与边界清晰。
- 警惕模块耦合、接口泄漏与过度分层。
- 组合优于继承的工程论证。

## 6. FAQ

- Q: Rust如何组织模块？
  A: 用mod和文件夹分层组织，pub控制可见性。
- Q: 如何做多包协作？
  A: 用cargo workspace管理多包项目。
- Q: 如何做模块间接口抽象？
  A: 用trait定义统一接口。

## 7. 参考与扩展阅读

- [Rust 模块系统官方文档](https://doc.rust-lang.org/book/ch07-00-modules.html)
- [cargo workspaces 多包管理](https://doc.rust-lang.org/book/ch14-03-cargo-workspaces.html)
- [Wikipedia: Modularity](https://en.wikipedia.org/wiki/Modularity)
