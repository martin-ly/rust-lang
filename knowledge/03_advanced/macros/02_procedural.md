# 过程宏 (Procedural Macros)

> **EN**: Procedural Macros
> **Summary**: 过程宏 Procedural Macros. (stub/archive redirect)
> **权威来源**: 本主题深度解释见 [concept/03_advanced/07_proc_macro.md](../../../concept/03_advanced/07_proc_macro.md)。
> **历史版本存档**: [archive/knowledge/03_advanced/macros/02_procedural.md](../../../archive/knowledge/03_advanced/macros/02_procedural.md)
>
> **定位**: 本文件为精简知识卡片，保留核心规则/概念与常见陷阱。详细解释、形式化语义与代码示例请查看权威来源。

---

## 核心概念

1. 在独立 proc-macro crate 中编写，操作 `TokenStream`
2. 三类：自定义 derive、属性宏、函数式宏
3. `syn` 解析 TokenStream，`quote!` 生成代码
4. 保持 span 信息以提供良好编译诊断

## 关键区分

| 类型 | 用途 | 典型场景 |
|---|---|---|
| derive | 为类型自动实现 trait | `#[derive(Debug)]` |
| attribute | 修饰 item 并转换 | `#[route(...)]` |
| function-like | 类似普通宏调用 | `sql!(...)` |

## 常见陷阱

- 未处理属性宏的输入校验
- 生成的代码引用外部路径不稳定
- 编译错误 span 丢失导致诊断质量差

---

**详细内容已迁移**：请点击上方 [concept/03_advanced/07_proc_macro.md](../../../concept/03_advanced/07_proc_macro.md) 查看最新权威解释。
