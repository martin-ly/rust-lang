# 测试工程（Testing Engineering）

## 1. 工程原理与定义（Principle & Definition）

测试工程是系统性地设计、实现和自动化执行各种测试（单元、集成、属性、端到端等）以保障软件质量的工程实践。Rust 以类型安全、自动化工具链和丰富的测试生态适合测试工程。
Testing engineering is the systematic practice of designing, implementing, and automating various tests (unit, integration, property-based, end-to-end, etc.) to ensure software quality. Rust's type safety, automation toolchain, and rich testing ecosystem are ideal for testing engineering.

## 2. Rust 1.88 新特性工程化应用

- #[expect]属性：灵活标记预期失败的测试。
- try_blocks：简化测试中的错误处理。
- cargo test增强：支持并发与属性测试。

## 3. 典型场景与最佳实践（Typical Scenarios & Best Practices）

- 用cargo test做单元与集成测试。
- 用proptest/quickcheck做属性测试。
- 用#[test]和#[should_panic]标记测试用例。
- 用CI集成自动化测试。

**最佳实践：**

- 用#[expect]属性标记预期失败。
- 用try_blocks简化测试错误处理。
- 用proptest/quickcheck提升测试覆盖率。
- 用cargo test/CI自动化测试。

## 4. 常见问题 FAQ

- Q: Rust如何做单元测试？
  A: 用#[test]标记测试函数，cargo test自动发现并运行。
- Q: 如何做属性测试？
  A: 用proptest/quickcheck生成随机输入做属性验证。
- Q: 如何集成自动化测试？
  A: 用CI工具自动运行cargo test。

## 5. 参考与扩展阅读

- [cargo test 官方文档](https://doc.rust-lang.org/cargo/commands/cargo-test.html)
- [proptest 属性测试](https://github.com/proptest-rs/proptest)
- [quickcheck 属性测试](https://github.com/BurntSushi/quickcheck)
