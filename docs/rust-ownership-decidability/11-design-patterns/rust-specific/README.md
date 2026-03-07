# Rust 特有设计模式

这些模式利用 Rust 的所有权、生命周期和类型系统特性。

---

## 模式列表

| 模式 | 文件 | 描述 | 难度 |
|-----|------|------|------|
| **RAII Guard** | [raii-guard.md](raii-guard.md) | 资源自动管理 | 🟢 |
| **Newtype** | [newtype.md](newtype.md) | 类型包装 | 🟢 |
| **Type State** | [../11-03-type-state-pattern.md](../11-03-type-state-pattern.md) | 编译时状态机 | 🟡 |

---

## 核心 Rust 特性

- **所有权**: 确保资源管理正确性
- **生命周期**: 编译时引用验证
- **零成本抽象**: 模式无运行时开销
