# 行为型设计模式 (Behavioral Patterns)

行为型模式关注对象间的通信和责任分配。

---

## 模式列表

| 模式 | 文件 | 描述 | 难度 |
|-----|------|------|------|
| **Observer** | [observer.md](observer.md) | 事件订阅通知 | 🟡 |
| **Strategy** | [strategy.md](strategy.md) | 算法封装 | 🟢 |
| **Command** | [command.md](command.md) | 请求封装 | 🟡 |

---

## 选择指南

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

- **所有权**: Observer 使用 Weak 引用避免循环
- **闭包**: 可用作轻量级 Command
- **泛型**: Strategy 的零成本抽象
