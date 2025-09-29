# 国际化与本地化（i18n & l10n, Internationalization & Localization）

## 1. 定义与软件工程对标

**国际化（i18n）**是指为软件适配多语言和多地区环境做准备，**本地化（l10n）**是指针对特定地区进行内容和格式调整。软件工程wiki认为，i18n/l10n是全球化软件的基础。
**Internationalization (i18n)** prepares software for multiple languages and regions, while **localization (l10n)** adapts content and formats for specific locales. In software engineering, i18n/l10n is foundational for global software.

## 2. Rust 1.88 最新特性

- **serde支持多语言数据序列化**
- **trait对象向上转型**：便于多语言适配接口抽象。
- **LazyLock**：全局多语言资源缓存。

## 3. 典型惯用法（Idioms）

- 使用fluent/babel等库管理多语言资源
- 结合serde/json处理多语言内容
- 利用trait抽象本地化适配器

## 4. 代码示例

```rust
trait Localizer {
    fn translate(&self, key: &str, locale: &str) -> String;
}
```

## 5. 软件工程概念对照

- **可移植性（Portability）**：多语言支持提升软件全球适用性。
- **可维护性（Maintainability）**：统一资源管理便于维护。
- **用户体验（User Experience）**：本地化提升用户满意度。

## 6. FAQ

- Q: Rust做i18n/l10n的优势？
  A: 类型安全、生态丰富、易于集成，适合多语言应用。

---
