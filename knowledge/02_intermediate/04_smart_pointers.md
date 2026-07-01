# 智能指针 (Smart Pointers)

> **权威来源**: 本主题深度解释见 [concept/02_intermediate/12_smart_pointers.md](../../concept/02_intermediate/12_smart_pointers.md)。
> **历史版本存档**: [archive/knowledge/02_intermediate/04_smart_pointers.md](../../archive/knowledge/02_intermediate/04_smart_pointers.md)
>
> **定位**: 本文件为精简知识卡片，保留核心规则/概念与常见陷阱。详细解释、形式化语义与代码示例请查看权威来源。

---

## 核心概念

1. `Box<T>` 提供堆分配与唯一所有权
2. `Rc<T>` 共享不可变所有权，基于引用计数
3. `RefCell<T>` 在运行时执行借用检查，提供内部可变性
4. `Arc<T>` 是线程安全的 `Rc`，常与 `Mutex/RwLock` 配合使用

## 关键区分

| 智能指针 | 所有权 | 可变性 | 线程安全 |
|---|---|---|---|
| `Box<T>` | 唯一 | 编译期 | 否（Move） |
| `Rc<T>` | 共享 | 不可变 | 否 |
| `RefCell<T>` | 唯一 | 运行时 | 否 |
| `Arc<T>` | 共享 | 不可变 | 是 |

## 常见陷阱

- `Rc<RefCell<T>>` 循环引用导致内存泄漏
- 在单线程场景无意义地使用 `Arc` 增加开销
- 在 `Rc` 上尝试获取可变引用

---

**详细内容已迁移**：请点击上方 [concept/02_intermediate/12_smart_pointers.md](../../concept/02_intermediate/12_smart_pointers.md) 查看最新权威解释。
