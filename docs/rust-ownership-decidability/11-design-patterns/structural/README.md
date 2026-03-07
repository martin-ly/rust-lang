# 结构型设计模式 (Structural Patterns)

结构型模式关注如何组合类和对象以形成更大的结构。

---

## 模式列表

| 模式 | 文件 | 描述 | 难度 |
|-----|------|------|------|
| **Adapter** | [adapter.md](adapter.md) | 接口适配 | 🟢 |
| **Decorator** | [decorator.md](decorator.md) | 动态添加功能 | 🟡 |
| **Proxy** | [proxy.md](proxy.md) | 访问控制 | 🟡 |

---

## 选择指南

```
需要改变接口?
├── 是 → Adapter
└── 否 → 需要添加功能而不改变原类?
         ├── 是 → Decorator
         └── 否 → 需要控制访问?
                  ├── 是 → Proxy
                  └── 否 → 直接组合
```

---

## Rust 特性利用

- **泛型**: 零成本装饰者和代理
- **Deref**: 智能指针模式
- **Trait**: 接口抽象
