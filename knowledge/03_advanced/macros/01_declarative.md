# 声明式宏 (Declarative Macros)

> **EN**: Declarative Macros
> **Summary**: 声明式宏 Declarative Macros. (stub/archive redirect)
> **权威来源**: 本主题深度解释见 [concept/03_advanced/03_proc_macros/01_macros.md](../../../concept/03_advanced/03_proc_macros/01_macros.md)。
> **历史版本存档**: [archive/knowledge/03_advanced/macros/01_declarative.md](../../../archive/knowledge/03_advanced/macros/01_declarative.md)
>
> **定位**: 本文件为精简知识卡片，保留核心规则/概念与常见陷阱。详细解释、形式化语义与代码示例请查看权威来源。

---

## 核心概念

1. `macro_rules!` 基于模式匹配与模板替换
2. 捕获类型：`expr`, `ty`, `ident`, `path`, `tt` 等
3. 重复模式 `$(...)*` / `$(...)+` 处理变长参数
4. 卫生系统限制宏内外标识符意外冲突

## 关键区分

| 特性 | 声明式宏 | 过程宏 |
|---|---|---|
| 定义方式 | `macro_rules!` | proc-macro crate |
| 输入 | TokenStream 模式 | TokenStream |
| 能力 | 模式展开 | 自定义 derive/attr |

## 常见陷阱

- 捕获类型选择过宽导致歧义
- 重复分隔符不匹配
- 宏展开后错误信息定位困难

---

**详细内容已迁移**：请点击上方 [concept/03_advanced/03_proc_macros/01_macros.md](../../../concept/03_advanced/03_proc_macros/01_macros.md) 查看最新权威解释。
