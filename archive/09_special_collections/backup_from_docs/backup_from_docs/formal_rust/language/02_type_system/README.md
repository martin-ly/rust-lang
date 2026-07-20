# 类型系统模块总览

## 模块结构体体体

- 理论基础：01_formal_type_system.md
- 生命周期系统：02_lifetime_system.md
- 工程案例：examples/
- 术语与符号：见 concept_dictionary.md、unified_mathematical_symbols.md

## 理论-实践-工具链映射

- 理论：类型系统的形式化定义、定理与证明
- 实践：工程案例、代码片段、自动化验证
- 工具链：concept_checker.rs、symbol_checker.rs、integration_runner.rs

## 交叉引用

- [所有权与借用](../01_ownership_borrowing/00_index.md)
- [控制流](../03_control_flow/00_index.md)
- [泛型](../04_generics/00_index.md)
- [并发](../05_concurrency/00_index.md)
- [术语表](../concept_dictionary.md)
- [全局符号表](../unified_mathematical_symbols.md)

## 术语表（简要）

- 类型（Type）、类型环境、类型推导、子类型、多态、泛型、型变、类型安全、进展性、保持性

## 后续补全提示

- 如需补充理论内容，请参照 01_formal_type_system.md 附录模板。
- 如需补充案例，请在 examples/README.md 登记。
- 交叉引用与术语表建议同步补全。

> 本文档为标准化模板，后续可根据实际内容补充详细说明与交叉引用。
