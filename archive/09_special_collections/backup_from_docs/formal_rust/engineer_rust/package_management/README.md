# 包管理（Package Management）

## 1. 定义与软件工程对标

**包管理**是指通过工具统一管理依赖、版本和分发。软件工程wiki认为，包管理是现代软件生态和可维护性的基础。
**Package management** means managing dependencies, versions, and distribution via tools. In software engineering, package management is foundational for modern software ecosystems and maintainability.

## 2. Rust 1.88 最新特性

- **cargo add/upgrade/outdated**：一站式依赖管理。
- **cargo features**：支持可选依赖和功能切换。
- **trait对象向上转型**：便于抽象多源包管理。

## 3. 典型惯用法（Idioms）

- 使用cargo管理依赖和发布
- 结合cargo-edit自动化升级依赖
- 利用trait抽象包源和分发策略

## 4. 代码示例

```rust
trait PackageSource {
    fn fetch(&self, name: &str) -> Option<Package>;
}
```

## 5. 软件工程概念对照

- **可重用性（Reusability）**：包机制提升代码复用。
- **可维护性（Maintainability）**：依赖管理简化维护。
- **安全性（Security）**：自动化工具检测依赖安全。

## 6. FAQ

- Q: Rust包管理的优势？
  A: 工具链统一、类型安全、生态丰富，适合大规模工程。

---
