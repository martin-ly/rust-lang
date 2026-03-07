# 创建型设计模式 (Creational Patterns)

创建型模式关注对象的创建机制，提供创建对象的灵活性。

---

## 模式列表

| 模式 | 文件 | 描述 | 难度 |
|-----|------|------|------|
| **Singleton** | [singleton.md](singleton.md) | 确保全局唯一实例 | 🟡 |
| **Builder** | [builder.md](builder.md) | 逐步构建复杂对象 | 🟡 |
| **Factory** | [factory.md](factory.md) | 封装对象创建逻辑 | 🟢 |

---

## 选择指南

```
需要全局唯一实例?
├── 是 → Singleton
└── 否 → 需要逐步配置对象?
         ├── 是 → Builder
         └── 否 → 需要运行时决定类型?
                  ├── 是 → Factory
                  └── 否 → 直接构造
```

---

## Rust 特殊考虑

- **所有权系统**: 影响单例的可变性设计
- **Type State**: Rust 独特的编译时验证构建者模式
- **零成本抽象**: 泛型工厂避免动态分派开销
