# C09 设计模式示例

本目录包含 Rust 设计模式的核心示例代码。

---

## 📚 示例列表

### 创建型模式

| 示例 | 描述 | 模式 |
|------|------|------|
| `singleton.rs` | 单例模式 | Singleton |
| `factory.rs` | 工厂模式 | Factory |
| `builder.rs` | 建造者模式 | Builder |
| `prototype.rs` | 原型模式 | Prototype |

### 结构型模式

| 示例 | 描述 | 模式 |
|------|------|------|
| `adapter.rs` | 适配器模式 | Adapter |
| `decorator.rs` | 装饰器模式 | Decorator |
| `composite.rs` | 组合模式 | Composite |
| `proxy.rs` | 代理模式 | Proxy |

### 行为型模式

| 示例 | 描述 | 模式 |
|------|------|------|
| `observer.rs` | 观察者模式 | Observer |
| `strategy.rs` | 策略模式 | Strategy |
| `command.rs` | 命令模式 | Command |
| `state.rs` | 状态模式 | State |

### Rust 特有模式

| 示例 | 描述 | 模式 |
|------|------|------|
| `typestate.rs` | 类型状态模式 | Typestate |
| `visitor_trait.rs` | Trait 访问者 | Visitor |
| `RAII_guard.rs` | RAII 守卫 | RAII |

---

## 🚀 快速开始

```bash
# 运行建造者模式示例
cargo run --example builder

# 运行类型状态模式示例
cargo run --example typestate

# 运行策略模式示例
cargo run --example strategy
```

---

## 🔗 相关文档

- [设计模式指南](../docs/)
- [设计模式概念族谱](../../../docs/research_notes/DESIGN_PATTERN_CONCEPT_MINDMAP.md)

---

*示例基于 Rust 1.94+，Edition 2024*
