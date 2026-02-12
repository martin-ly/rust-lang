# Singleton 形式化分析

> **创建日期**: 2026-02-12
> **分类**: 创建型
> **安全边界**: 纯 Safe 或 需 unsafe

---

## 形式化定义

**Def 1.1（Singleton 结构）**

设 $T$ 为单例类型。Singleton 满足：

- $\exists \mathit{instance} : () \to \mathrm{Arc}\langle T \rangle$ 或 $\mathit{instance} : () \to \&'static T$
- 全局唯一：$\forall t_1, t_2 \in \mathit{instances},\, t_1 = t_2$（同一引用或 Arc 克隆）
- 惰性初始化：首次访问时构造

**Axiom S1**：实例唯一性；首次访问初始化；线程安全。

**定理 S-T1**：`OnceLock`/`LazyLock` 提供线程安全惰性初始化，无需 unsafe。

*证明*：（1）唯一性：`OnceLock` 内部状态机保证 `get_or_init` 闭包至多执行一次；原子 CAS 或锁序列化首次调用。（2）线程安全：后续 `get` 仅读，无写；Rust 内存模型保证可见性。（3）Safe API：标准库将内部 `unsafe` 封装为安全抽象，对外无 `unsafe` 暴露。由 Axiom S1、[safe_unsafe_matrix](../../05_boundary_system/safe_unsafe_matrix.md) SBM-T1。∎

**定理 S-T2**：传统全局可变需 `unsafe` 或 `Mutex`；后者为 Safe 抽象。

*证明*：`static mut` 多线程访问为 UB；`Mutex` 封装内部 `unsafe`，对外 Safe。见 [safe_unsafe_matrix](../../05_boundary_system/safe_unsafe_matrix.md) SBM-T2。∎

**引理 S-L1**：若用 `OnceLock<T>` 且 $T$ 无 `Send`/`Sync` 要求，则 `get_or_init` 闭包仅执行一次；多线程并发调用时由内部同步序列化。

---

## Rust 实现与代码示例

### 方式一：OnceLock（纯 Safe，推荐）

```rust
use std::sync::OnceLock;

static INSTANCE: OnceLock<String> = OnceLock::new();

fn get_instance() -> &'static String {
    INSTANCE.get_or_init(|| "singleton".to_string())
}
```

### 方式二：LazyLock（纯 Safe）

```rust
use std::sync::LazyLock;

static INSTANCE: LazyLock<String> = LazyLock::new(|| "singleton".to_string());

fn get_instance() -> &'static String {
    &INSTANCE
}
```

### 方式三：带内部可变（Safe）

```rust
use std::sync::{Arc, Mutex, OnceLock};

static INSTANCE: OnceLock<Arc<Mutex<i32>>> = OnceLock::new();

fn get_instance() -> Arc<Mutex<i32>> {
    INSTANCE.get_or_init(|| Arc::new(Mutex::new(0))).clone()
}
```

**形式化对应**：`get_or_init` 保证仅初始化一次；`OnceLock` 内部同步，无数据竞争。

---

## 证明思路

1. **OnceLock**：内部使用 `atomic` 或 `sync`  primitives；`get_or_init` 为 Safe API。
2. **唯一性**：`OnceLock` 保证仅赋值一次；后续 `get` 返回同一引用。

---

## 典型场景

| 场景 | 说明 |
| :--- | :--- |
| 配置/全局设置 | 应用配置、环境变量 |
| 连接池 | 数据库、HTTP 客户端 |
| 日志/追踪 | 全局 logger、tracer |
| 服务定位 | Registry、依赖注入根 |

---

## 相关模式

| 模式 | 关系 |
| :--- | :--- |
| [Abstract Factory](abstract_factory.md) | 工厂常为单例 |
| [Facade](../02_structural/facade.md) | 外观常为单例 |
| Registry（43 完全） | 服务定位即单例；[02_complete_43_catalog](../../02_workflow_safe_complete_models/02_complete_43_catalog.md) |

---

## 实现变体

| 变体 | 说明 | 适用 |
| :--- | :--- | :--- |
| `OnceLock<T>` | 惰性、线程安全；首次 get_or_init | 简单单例 |
| `LazyLock<T>` | 声明时指定初始化；线程安全 | 初始化逻辑简单 |
| `Arc<Mutex<T>>` + OnceLock | 内部可变单例 | 需修改状态 |
| 依赖注入 | 构造时传入；无全局 | 可测试、灵活 |

---

## 反例

**反例**：使用 `static mut` 且多线程访问未同步 → 数据竞争、UB。应使用 `OnceLock`/`LazyLock` 或 `Mutex`。

---

## 边界

| 维度 | 分类 |
| :--- | :--- |
| 安全 | Safe（OnceLock/LazyLock）或 需 unsafe（static mut） |
| 支持 | 原生 |
| 表达 | 近似（无全局可变） |
