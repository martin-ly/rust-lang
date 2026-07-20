# Error Handling 目录

> **定位**: Rust 错误处理生态的 crate 对比、选型建议与工程实践。
> **Rust 版本**: 1.96.0+ (Edition 2024)

---

## 目录结构

```text
content/ecosystem/error_handling/
├── README.md                 # 本文件
└── anyhow_vs_thiserror.md    # anyhow 与 thiserror 的对比分析
```

---

## 核心 crate

| Crate | 用途 | 适用场景 |
|---|---|---|
| **`anyhow`** | 简单、人体工学的错误处理 | 应用代码、快速原型 |
| **`thiserror`** | 定义结构化错误类型 | 库代码、需要精确错误枚举 |
| **`eyre`** | anyhow 的扩展，支持自定义报告 | 需要自定义错误展示的应用 |
| **`snafu`** | 上下文丰富的错误类型 | 复杂领域错误建模 |

---

## 选型建议

- **写应用**：`anyhow`
- **写库**：`thiserror`
- **需要错误上下文链**：`snafu` 或 `eyre`
