# 模块化（Modularity）

## 1. 定义与软件工程对标

**模块化**是指将系统划分为独立、可组合的模块，提升可维护性和可扩展性。软件工程wiki认为，模块化是大型系统设计的基础。
**Modularity** means dividing a system into independent, composable modules to improve maintainability and scalability. In software engineering, modularity is foundational for large system design.

## 2. Rust 1.88 最新特性

- **mod/ pub/ crate/ super/ self**：灵活的模块系统。
- **trait对象向上转型**：便于抽象模块接口。
- **LazyLock**：全局模块状态缓存。

## 3. 典型惯用法（Idioms）

- 使用mod和pub组织代码结构
- 结合crate和workspace实现多包协作
- 利用trait抽象模块接口和依赖

## 4. 代码示例

```rust
mod utils {
    pub fn add(a: i32, b: i32) -> i32 { a + b }
}
use utils::add;
```

## 5. 软件工程概念对照

- **解耦（Decoupling）**：模块化降低依赖和耦合。
- **可扩展性（Scalability）**：模块独立演进和扩展。
- **可维护性（Maintainability）**：清晰结构便于维护。

## 6. FAQ

- Q: Rust模块化的优势？
  A: 类型安全、灵活结构、生态丰富，适合大型工程。

---
