# Rust 字符串处理 (String Handling)

> **EN**: String Handling
> **Summary**: Rust 字符串处理 String Handling. (stub/archive redirect)
> **权威来源**: 本主题深度解释见 [concept/01_foundation/09_strings_and_text.md](../../concept/01_foundation/09_strings_and_text.md)。
> **历史版本存档**: [archive/knowledge/02_intermediate/05_strings.md](../../archive/knowledge/02_intermediate/05_strings.md)
>
> **定位**: 本文件为精简知识卡片，保留核心规则/概念与常见陷阱。详细解释、形式化语义与代码示例请查看权威来源。

---

## 核心概念

1. `String` 拥有 UTF-8 字节，可变
2. `&str` 是字符串切片，不拥有数据
3. 字符串索引不合法，因为 UTF-8 是变长编码
4. `OsString/CString` 处理非 UTF-8 / C 字符串

## 关键区分

| 类型 | 所有权 | 可变性 | 使用场景 |
|---|---|---|---|
| `String` | 有 | 可变 | 构造/修改 |
| `&str` | 无 | 不可变 | 函数参数/切片 |
| `OsString` | 有 | 可变 | 系统路径 |

## 常见陷阱

- 用整数索引字符串导致编译错误
- `+` 运算会 Move 左操作数
- 混用字节索引与字符边界

---

**详细内容已迁移**：请点击上方 [concept/01_foundation/09_strings_and_text.md](../../concept/01_foundation/09_strings_and_text.md) 查看最新权威解释。
