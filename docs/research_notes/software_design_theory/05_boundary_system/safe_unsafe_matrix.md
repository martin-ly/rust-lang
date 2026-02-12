# 安全 vs 非安全边界矩阵

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-12
> **Rust 版本**: 1.93.0+ (Edition 2024)

---

## 形式化定义与公理

**Def 1.1（ Safe 边界）**

设 $P$ 为实现某模式/功能的 Rust 程序。定义安全边界函数 $\mathit{SafeB}(P) \in \{\mathrm{Safe},\, \mathrm{Unsafe},\, \mathrm{Inexpr}\}$：

- **纯 Safe**：$\mathit{SafeB}(P) = \mathrm{Safe}$ 当且仅当 $P$ 不含 `unsafe` 块且可完整实现目标
- **需 unsafe**：$\mathit{SafeB}(P) = \mathrm{Unsafe}$ 当且仅当 $P$ 需局部 `unsafe`（FFI、裸指针、transmute），但可封装为对外 Safe 的 API
- **无法表达**：$\mathit{SafeB}(P) = \mathrm{Inexpr}$ 当且仅当无法在 Rust 中表达，或需大量 unsafe 且难以安全封装

**Def 1.2（安全抽象）**

设 $A$ 为封装 unsafe 的 Rust 模块。若 $A$ 对外 API 满足 [borrow_checker_proof](../../formal_methods/borrow_checker_proof.md) 与 [ownership_model](../../formal_methods/ownership_model.md) 的 Safe 规则，则称 $A$ 为**安全抽象**。

**Axiom SBM1**：Safe 代码不触发 UB；违反借用/所有权规则导致编译错误。

**Axiom SBM2**：unsafe 块引入 UB 契约；安全抽象需满足该契约并对外隐藏 unsafe。

**定理 SBM-T1**：若模式 $X$ 仅用 `OnceLock`、`Mutex`、`Channel`、`Arc` 等 Safe 抽象，则 $\mathit{SafeB}(X) = \mathrm{Safe}$。

*证明*：由 [borrow_checker_proof](../../formal_methods/borrow_checker_proof.md) T1、[ownership_model](../../formal_methods/ownership_model.md) T2/T3，Safe API 保证内存安全与无数据竞争。依 Axiom SBM1，Safe 代码不触发 UB；故 $\mathit{SafeB}(X) = \mathrm{Safe}$。∎

**定理 SBM-T2**：若模式 $X$ 需 FFI 或裸指针，则 $\mathit{SafeB}(X) = \mathrm{Unsafe}$；封装为安全抽象后，调用方仍视为 Safe。

*证明*：由 Def 1.1，需 `unsafe` 块则 $\mathit{SafeB}(X) = \mathrm{Unsafe}$。由 Def 1.2、Axiom SBM2，安全抽象对外 API 满足 Safe 规则，调用方无需写 `unsafe`。∎

**引理 SBM-L1**：若 $A$ 为安全抽象，则 $A$ 的 `unsafe` 块需满足其 UB 契约（如 dereference 合法指针、FFI 调用约定）。

*证明*：由 Axiom SBM2；安全抽象需满足契约并对外隐藏 `unsafe`。∎

**推论 SBM-C1**：GoF 23 中 Singleton 用 OnceLock 为 Safe；用 `static mut` 且无同步为 Unsafe 或 Inexpr。

**引理 SBM-L2（反模式边界）**：若 $P$ 用 `static mut` 且多线程无同步，则 $\mathit{SafeB}(P) = \mathrm{Inexpr}$ 或违反 UB 契约。

*证明*：由 Axiom SBM1；`static mut` 多线程写入为数据竞争，违反 borrow T1；依 Def 1.1 无法表达或需大量 unsafe。∎

**推论 SBM-C2**：设计模式与执行模型组合时，若每子组件 Safe，则组合 Safe；由 SBM-T1 与模块组合 CE-T1、CE-T2。

---

## 定义（非形式化对照）

| 分类 | 定义 |
|------|------|
| **纯 Safe** | 仅用安全 API 即可完整实现，无 `unsafe` 块 |
| **需 unsafe** | 实现需局部 `unsafe`（如 FFI、裸指针、transmute），可封装为安全抽象 |
| **无法表达** | 在 Rust 中无法表达或需大量 unsafe 且难以安全封装 |

---

## 安全边界决策树

```text
实现模式 X？
├── X 需全局可变？
│   ├── 是 → 用 OnceLock/LazyLock/Mutex → 纯 Safe
│   └── 否 → 继续
├── X 需共享可变？
│   ├── 是 → 用 Mutex/RefCell/RwLock → 纯 Safe
│   └── 否 → 继续
├── X 需 FFI/裸指针？
│   ├── 是 → 需 unsafe，可封装为安全抽象
│   └── 否 → 纯 Safe
└── 结论：绝大多数 GoF 与扩展模式为纯 Safe
```

---

## 设计模式 × 安全边界

### 创建型（5）

| 模式 | 安全边界 | 实现要点 |
| :--- | :--- | :--- |
| Factory Method | 纯 Safe | Trait + impl，`fn create(&self) -> T` |
| Abstract Factory | 纯 Safe | 关联类型或枚举产品族 |
| Builder | 纯 Safe | 链式 `self` 返回，`build(self)` 消费 |
| Prototype | 纯 Safe | `Clone` trait |
| Singleton | 纯 Safe / 需 unsafe | OnceLock/LazyLock 为 Safe；`static mut` 需 unsafe |

### 结构型（7）

| 模式 | 安全边界 | 实现要点 |
| :--- | :--- | :--- |
| Adapter | 纯 Safe | 结构体包装 `inner: S`，实现目标 trait |
| Bridge | 纯 Safe | `impl Trait` 或 `Box<dyn Trait>` |
| Composite | 纯 Safe | `enum { Leaf(T), Composite(Vec<Node>) }` |
| Decorator | 纯 Safe | 包装 + 委托，同 Adapter |
| Facade | 纯 Safe | 模块或结构体聚合 |
| Flyweight | 纯 Safe | `HashMap<K, Arc<T>>` 缓存 |
| Proxy | 纯 Safe | 持有目标，委托调用 |

### 行为型（11）

| 模式 | 安全边界 | 实现要点 |
| :--- | :--- | :--- |
| Chain of Responsibility | 纯 Safe | `Option<Box<Handler>>` 链 |
| Command | 纯 Safe | `Box<dyn Fn()>` 或 `Fn` trait |
| Interpreter | 纯 Safe | 枚举 AST + match 求值 |
| Iterator | 纯 Safe | `Iterator` trait |
| Mediator | 纯 Safe | 结构体持有多方引用 |
| Memento | 纯 Safe | Clone 或 serde 序列化 |
| Observer | 纯 Safe | mpsc/broadcast channel；或 RefCell<Vec<Callback>> |
| State | 纯 Safe | 枚举或类型状态泛型 |
| Strategy | 纯 Safe | trait + impl |
| Template Method | 纯 Safe | trait 默认方法 |
| Visitor | 纯 Safe | match 或 trait 多态 |

---

## 执行模型 × 安全边界

| 模型 | 安全边界 | 说明 |
|------|----------|------|
| 同步 | 纯 Safe | 顺序执行，默认 |
| 异步 | 纯 Safe | Future + async/await，Pin 由库封装 |
| 并发 | 纯 Safe | Send/Sync + channels/Mutex |
| 并行 | 纯 Safe | Rayon、std::thread |
| 分布式 | 纯 Safe / 需 unsafe | tonic、actix 为 Safe；FFI 绑定需 unsafe |

---

## 扩展模式（43 完全之 20）安全边界

| 模式 | 安全边界 | 说明 |
|------|----------|------|
| Domain Model | 纯 Safe | 结构体 + 方法 |
| Service Layer | 纯 Safe | 模块/结构体 |
| Repository | 纯 Safe | trait + impl |
| Unit of Work | 纯 Safe | 收集变更，批量提交 |
| Data Mapper | 纯 Safe | 转换逻辑 |
| Table Data Gateway | 纯 Safe | 封装数据访问 |
| Active Record | 纯 Safe | 结构体 + 持久化方法 |
| Gateway | 纯 Safe / 需 unsafe | 库封装为 Safe；FFI 需 unsafe |
| MVC、Front Controller | 纯 Safe | 模块分层 |
| DTO、Remote Facade | 纯 Safe | 数据传输结构 |
| Value Object、Registry | 纯 Safe | 值类型、服务定位 |
| Identity Map、Lazy Load | 纯 Safe | HashMap 缓存、按需加载 |
| Plugin、Optimistic Offline Lock | 纯 Safe | 依赖注入、版本检测 |
| Specification、Event Sourcing | 纯 Safe | 谓词组合、事件日志 |

---

## 反例：违反安全边界

| 反例 | 后果 |
|------|------|
| Singleton 用 `static mut` 且多线程无同步 | 数据竞争、UB |
| Observer 回调中修改共享状态无 Mutex | 数据竞争 |
| Gateway 直接 transmute 外部指针 | UB |

---

## 实现检查清单

实现某模式前，确认：

- [ ] 是否需全局可变？→ 用 `OnceLock`/`LazyLock` 而非 `static mut`
- [ ] 是否需共享可变？→ 用 `Mutex`/`RwLock`/`RefCell` 等 Safe 抽象
- [ ] 是否需 FFI？→ 将 unsafe 封装在最小模块内，对外提供 Safe API
- [ ] 跨线程？→ 确保 `Send`/`Sync`；`Arc` 与 `Mutex` 组合

---

## 常见错误与排查

| 错误 | 原因 | 解决 |
| :--- | :--- | :--- |
| 编译错误：`Rc` 不满足 `Send` | 跨线程传递 Rc | 改用 `Arc` |
| 运行时 panic：RefCell borrow 冲突 | 同时 borrow 与 borrow_mut | 缩小借用范围；或改用 Mutex |
| 数据竞争 | 共享可变无同步 | 加 Mutex/RwLock；或改用 channel |
| 悬垂引用 | 生命周期短于借用 | 延长生命周期；或改用所有权 |

---

## 引用

- [SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS](../../SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS.md)
- [THEORETICAL_AND_ARGUMENTATION_SYSTEM_ARCHITECTURE](../../THEORETICAL_AND_ARGUMENTATION_SYSTEM_ARCHITECTURE.md) § 3
