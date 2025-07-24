# 宏与元编程（Macro & Metaprogramming）

## 1. 工程原理与定义（Principle & Definition）

宏与元编程是通过代码生成、模板和编译期扩展提升代码复用性和灵活性的工程实践。Rust 以macro_rules!、过程宏和类型系统支持强大的元编程能力。
Macro and metaprogramming are engineering practices that enhance code reuse and flexibility through code generation, templates, and compile-time extensions. Rust's macro_rules!, procedural macros, and type system provide powerful metaprogramming capabilities.

## 2. Rust 1.88 新特性工程化应用

- inline const：宏中支持常量表达式。
- proc_macro增强：更灵活的编译期代码生成。
- syn/quote库：简化过程宏开发。

## 3. 典型场景与最佳实践（Typical Scenarios & Best Practices）

- 用macro_rules!实现通用代码模板。
- 用proc_macro开发自定义派生宏。
- 用syn/quote简化AST处理。
- 用cargo expand调试宏展开。

**最佳实践：**

- 用macro_rules!做零成本模板复用。
- 用proc_macro实现编译期扩展。
- 用syn/quote提升过程宏开发效率。
- 用cargo expand调试宏展开。

## 4. 常见问题 FAQ

- Q: Rust如何定义宏？
  A: 用macro_rules!定义声明式宏，用proc_macro开发过程宏。
- Q: 如何调试宏展开？
  A: 用cargo expand查看宏展开结果。
- Q: 如何做编译期代码生成？
  A: 用proc_macro和syn/quote开发自定义宏。

## 5. 参考与扩展阅读

- [macro_rules! 宏官方文档](https://doc.rust-lang.org/reference/macros-by-example.html)
- [proc_macro 过程宏](https://doc.rust-lang.org/reference/procedural-macros.html)
- [syn/quote AST处理](https://github.com/dtolnay/syn)
