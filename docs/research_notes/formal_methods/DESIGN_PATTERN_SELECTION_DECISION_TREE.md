# 设计模式选择决策树

> **创建日期**: 2026-02-24
> **级别**: L1/L2
> **类型**: 决策树

---

## 决策流程

```
需要解决什么问题？
│
├── 对象创建
│   ├── 需要复杂构造过程
│   │   ├── 需要分步构建 → Builder模式
│   │   └── 需要多种配置 → Factory模式
│   │
│   └── 需要保证唯一性
│       └── Singleton模式 (Rust: const/static)
│
├── 结构组织
│   ├── 需要统一接口
│   │   ├── 不同类实现相同接口 → Adapter模式
│   │   └── 简化复杂系统 → Facade模式
│   │
│   ├── 需要动态添加功能
│   │   └── Decorator模式
│   │
│   └── 需要共享状态
│       └── Flyweight模式
│
└── 行为交互
    ├── 需要解耦请求与处理
    │   └── Command模式
    │
    ├── 需要状态驱动行为
    │   └── State模式
    │
    ├── 需要策略替换
    │   └── Strategy模式
    │
    └── 需要观察者通知
        └── Observer模式
```

---

## 模式速查表

| 模式 | 适用场景 | Rust实现要点 |
| :--- | :--- | :--- |
| Builder | 复杂对象构造 | 消费型builder, typestate模式 |
| Factory | 多种产品创建 | trait对象或泛型 |
| Adapter | 接口适配 | trait实现转换 |
| Decorator | 动态功能叠加 | 泛型包装器 |
| Command | 请求封装 | trait对象或枚举 |
| State | 状态机 | 枚举+方法实现 |
| Strategy | 算法替换 | trait对象 |
| Observer | 事件通知 | 通道或回调 |

---

## Rust特定考虑

```
所有权影响
│
├── 消费型vs借用型
│   ├── self → 消费
│   └── &self / &mut self → 借用
│
├── 生命周期约束
│   └── 确保引用有效
│
└── Send/Sync
    └── 并发安全
```

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-24
**状态**: ✅ 已完成 - 决策树 8/10
