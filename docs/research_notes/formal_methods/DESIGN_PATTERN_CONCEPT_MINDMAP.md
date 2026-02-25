# 设计模式概念族谱 - 思维导图

> **创建日期**: 2026-02-26
> **最后更新**: 2026-02-26
> **状态**: ✅ 新建
> **对应任务**: P1-T10

---

## 全局思维导图

```text
                        设计模式概念族
                               │
        ┌──────────────────────┼──────────────────────┐
        │                      │                      │
   【创建型】              【结构型】              【行为型】
        │                      │                      │
    ├─Singleton           ├─Adapter             ├─Observer
    │  └─OnceLock          │  └─trait+委托       │  └─mpsc/broadcast
    ├─Factory Method      ├─Bridge              ├─Strategy
    │  └─trait fn create   │  └─trait解耦        │  └─trait+impl
    ├─Abstract Factory    ├─Composite           ├─State
    │  └─enum产品族        │  └─enum+Box递归     │  └─enum+match
    ├─Builder             ├─Decorator           ├─Command
    │  └─链式+类型状态     │  └─struct包装       │  └─Box<dyn Fn>
    ├─Prototype           ├─Facade              ├─Iterator
    │  └─Clone trait       ├─Flyweight           ├─Template Method
    └─(Rust扩展)          │  └─Arc共享          ├─Mediator
       └─From/Into        └─Proxy               ├─Chain of Resp.
                           └─trait包装          ├─Visitor
                                                └─Interpreter
```

---

## Rust 实现特点

| 类别 | Rust 特点 | 形式化衔接 |
| :--- | :--- | :--- |
| **创建型** | trait 工厂、enum 产品族、Clone、链式 Builder | ownership_model T2、type_system 保持性 |
| **结构型** | trait 解耦、enum 递归、Arc 共享 | borrow_checker T1、Send/Sync |
| **行为型** | channel 解耦、trait 多态、enum 穷尽 | async_state_machine、trait_system |

---

## 模式组合关系

```text
模式组合
├── Strategy + Factory → 策略由工厂创建
├── Observer + Mediator → 观察者经中介通信
├── State + Strategy → 状态即策略
├── Composite + Visitor → 遍历复合结构
├── Decorator + Builder → 装饰器链式构建
└── Command + Memento → 可撤销命令
```

---

## 与所有权/借用的关系

| 模式 | 所有权 | 借用 |
| :--- | :--- | :--- |
| Chain、Composite | Box 递归、消费 | 无引用则无 'a |
| Observer | channel 转移 | mpsc 无共享可变 |
| Adapter、Decorator | inner 拥有 | &self 借用 |
| Flyweight | Arc 共享 | T: Sync 跨线程 |
| State | 状态拥有上下文 | match 穷尽无悬垂 |

---

## 相关文档

- [01_design_patterns_formal](../software_design_theory/01_design_patterns_formal/README.md) - 23 模式形式化
- [DESIGN_PATTERNS_BOUNDARY_MATRIX](../software_design_theory/01_design_patterns_formal/DESIGN_PATTERNS_BOUNDARY_MATRIX.md) - 等价/近似边界
- [04_expressiveness_boundary](../software_design_theory/02_workflow_safe_complete_models/04_expressiveness_boundary.md) - 表达力边界

---

**维护者**: Rust Formal Methods Research Team
**对应任务**: P1-T10 - 设计模式概念族谱完善
