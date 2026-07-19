# 测试与验证（Testing & Verification）

## 1. 定义与软件工程对标

**测试与验证**是指通过单元测试、集成测试、属性测试等手段，确保代码正确性和鲁棒性。软件工程wiki认为，测试是高质量软件的保障。
**Testing & verification** means ensuring code correctness and robustness via unit, integration, and property-based tests. In software engineering, testing is the guarantee of high-quality software.

## 2. Rust 1.88 最新特性

- **#[test]属性增强**：支持异步测试和自定义测试运行器。
- **doctest**：文档代码自动测试。
- **trait对象向上转型**：便于测试接口抽象。

## 3. 典型惯用法（Idioms）

- 使用#[test]编写单元测试
- 结合proptest/quickcheck做属性测试
- 利用cargo test自动化测试全流程

## 4. 代码示例

```rust
#[test]
fn test_add() {
    assert_eq!(add(1, 2), 3);
}
```

## 5. 软件工程概念对照

- **可重复性（Repeatability）**：自动化测试保证结果一致。
- **可维护性（Maintainability）**：测试提升代码可维护性。
- **回归防护（Regression Protection）**：测试防止功能回退。

## 6. FAQ

- Q: Rust测试体系的优势？
  A: 自动化、类型安全、支持异步和属性测试，适合高质量工程。

---
