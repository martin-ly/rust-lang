# 国际化与本地化（i18n & l10n）

## 1. 工程原理与定义（Principle & Definition）

国际化（i18n）与本地化（l10n）是指在全球化背景下，系统通过抽象与分离语言、文化、格式等资源，实现多语言和多文化适配。这体现了软件工程的可移植性与包容性哲学。Rust 以类型系统、资源抽象和生态库支持严谨的国际化工程。
Internationalization (i18n) and localization (l10n) refer to the abstraction and separation of language, culture, and formatting resources to enable multilingual and multicultural adaptation in a global context. This reflects the philosophy of portability and inclusiveness in software engineering. Rust supports rigorous internationalization engineering via its type system, resource abstraction, and ecosystem libraries.

## 2. Rust 1.88 新特性工程化应用

- fluent/unic-langid库：抽象多语言资源与标识。
- serde/yaml/json：灵活管理本地化配置。
- #[expect]属性：本地化测试中的预期异常标注。

## 3. 典型场景与最佳实践（Typical Scenarios & Best Practices）

- 用fluent/unic-langid抽象多语言文本与标识。
- 用serde/yaml/json管理本地化资源。
- 用trait统一国际化接口，提升可移植性。
- 用CI自动化测试多语言适配。

**最佳实践：**

- 抽象语言与文化资源，分离业务逻辑与本地化内容。
- 用fluent/unic-langid提升多语言适配能力。
- 用serde统一配置管理。
- 用自动化测试验证多语言兼容性。

## 4. 常见问题 FAQ

- Q: Rust如何实现多语言适配？
  A: 用fluent/unic-langid抽象文本与标识，serde管理配置。
- Q: 如何保证本地化资源的正确性？
  A: 用类型系统和自动化测试验证资源一致性。
- Q: 如何做多语言自动化测试？
  A: 用CI集成多语言测试用例。

## 5. 参考与扩展阅读

- [fluent 多语言库](https://projectfluent.org/)
- [unic-langid 语言标识](https://github.com/unicode-org/icu4x/tree/main/components/locid)
- [serde 配置解析库](https://serde.rs/)
