# 文档工程（Documentation Engineering）

## 1. 工程原理与定义（Principle & Definition）

文档工程是系统性地编写、维护和自动化生成项目文档的工程实践。Rust 以内置文档注释、自动化工具链和类型安全适合文档工程。
Documentation engineering is the systematic practice of writing, maintaining, and automatically generating project documentation. Rust's built-in doc comments, automation toolchain, and type safety are ideal for documentation engineering.

## 2. Rust 1.88 新特性工程化应用

- rustdoc增强：支持更多注释格式和文档测试。
- mdBook：自动化生成多语言文档。
- #[expect]属性：文档测试中更灵活的错误预期。

## 3. 典型场景与最佳实践（Typical Scenarios & Best Practices）

- 用rustdoc生成API文档。
- 用mdBook编写多语言工程文档。
- 用#[doc]属性自定义模块文档。
- 用cargo test自动化文档测试。

**最佳实践：**

- 用rustdoc自动生成API文档。
- 用mdBook维护多语言文档。
- 用#[expect]属性提升文档测试灵活性。
- 用CI集成文档自动化。

## 4. 常见问题 FAQ

- Q: Rust如何自动生成文档？
  A: 用rustdoc自动提取注释生成API文档。
- Q: 如何做多语言文档？
  A: 用mdBook支持多语言内容。
- Q: 如何做文档测试？
  A: 用cargo test自动运行文档中的代码示例。

## 5. 参考与扩展阅读

- [rustdoc 官方文档](https://doc.rust-lang.org/rustdoc/)
- [mdBook 多语言文档](https://rust-lang.github.io/mdBook/)
- [cargo test 文档测试](https://doc.rust-lang.org/cargo/commands/cargo-test.html)
