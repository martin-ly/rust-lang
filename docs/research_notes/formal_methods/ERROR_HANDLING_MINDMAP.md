# 错误处理概念思维导图

> **创建日期**: 2026-02-24
> **级别**: L1/L2
> **类型**: 思维导图

---

## 错误处理层次

```
                            错误处理系统
                                 │
            ┌────────────────────┼────────────────────┐
            │                    │                    │
       【不可恢复】          【可恢复】            【传播机制】
            │                    │                    │
    ┌───────┴───────┐    ┌───────┴───────┐    ┌───────┴───────┐
    │               │    │               │    │               │
   panic!        abort   Result<T, E>    Option  ?操作符       try!
    │               │      │               │      │               │
  栈展开        立即终止  Ok/Err          Some/None  自动传播     早期宏
```

---

## Result类型详解

```
Result<T, E>
│
├── 变体
│   ├── Ok(T) - 成功
│   └── Err(E) - 错误
│
├── 组合子
│   ├── map - 转换Ok值
│   ├── map_err - 转换Err值
│   ├── and_then - 链式操作
│   └── unwrap_or - 默认值
│
└── 转换
    ├── unwrap() - 解包(危险)
    ├── expect() - 带消息解包
    └── unwrap_or_default()
```

| 方法 | 用途 | 安全 |
| :--- | :--- | :--- |
| `is_ok()` | 检查成功 | ✅ |
| `is_err()` | 检查错误 | ✅ |
| `unwrap()` | 强制解包 | ❌ |
| `?` | 传播错误 | ✅ |

---

## Option类型

```
Option<T>
│
├── Some(T) - 有值
├── None - 无值
│
└── 与Result转换
    ├── ok_or()
    ├── ok_or_else()
    └── transpose()
```

---

## 错误类型设计

```
错误类型
│
├── 标准库
│   ├── std::io::Error
│   └── std::fmt::Error
│
├── 自定义错误
│   └── thiserror
│
└── 动态错误
    └── anyhow
```

---

## ?操作符机制

```
?展开
│
├── Result
│   └── Ok(v) → v
│   └── Err(e) → return Err(e.into())
│
└── Option
    └── Some(v) → v
    └── None → return None
```

---

## 最佳实践

```
实践指南
│
├── 使用Result进行错误传播
├── 避免unwrap()生产代码
├── 自定义错误提供上下文
└── 使用?简化错误处理
```

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-24
**状态**: ✅ 已完成 - 思维导图 15/15
