# 行为型设计模式 (Behavioral Patterns)

行为型模式关注对象间的通信和责任分配。

---

## 模式列表
> **[来源: Rust Official Docs]**

| 模式 | 文件 | 描述 | 难度 |
|-----|------|------|------|
| **Observer** | [observer.md](observer.md) | 事件订阅通知 | 🟡 |
| **Strategy** | [strategy.md](strategy.md) | 算法封装 | 🟢 |
| **Command** | [command.md](command.md) | 请求封装 | 🟡 |

---

## 选择指南
> **[来源: Rust Official Docs]**

```
需要对象间的事件通知?
├── 是 → Observer
└── 否 → 需要运行时切换算法?
         ├── 是 → Strategy
         └── 否 → 需要支持撤销操作?
                  ├── 是 → Command
                  └── 否 → 考虑其他模式
```

---

## Rust 特殊考虑
> **[来源: Rust Official Docs]**

- **所有权**: Observer 使用 Weak 引用避免循环
- **闭包**: 可用作轻量级 Command
- **泛型**: Strategy 的零成本抽象
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
