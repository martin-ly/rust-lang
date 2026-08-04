# 宏与元编程（Macro & Metaprogramming）

## 1. 定义与软件工程对标

**宏与元编程**是指通过代码生成和编译期扩展提升开发效率和抽象能力。软件工程wiki认为，宏系统是现代语言高阶抽象的基础。
**Macro & metaprogramming** means generating code and extending behavior at compile time to improve efficiency and abstraction. In software engineering, macros are foundational for high-level abstraction in modern languages.

## 2. Rust 1.88 最新特性

- **macro_rules!增强**：更强的模式匹配和递归能力。
- **proc_macro**：支持自定义属性和派生宏。
- **inline const**：编译期常量表达式嵌入宏。

## 3. 典型惯用法（Idioms）

- 使用macro_rules!定义声明式宏
- 结合proc_macro实现自定义派生和属性宏
- 利用宏生成重复代码和DSL

## 4. 代码示例

```rust
macro_rules! add {
    ($a:expr, $b:expr) => { $a + $b };
}
let sum = add!(1, 2);
```

## 5. 软件工程概念对照

- **抽象能力（Abstraction）**：宏提升代码复用和表达力。
- **类型安全（Type Safety）**：宏系统与类型系统协同。
- **可维护性（Maintainability）**：减少重复代码，提升可维护性。

## 6. FAQ

- Q: Rust宏系统的优势？
  A: 类型安全、编译期扩展、支持DSL，适合高阶抽象和自动化。

---
