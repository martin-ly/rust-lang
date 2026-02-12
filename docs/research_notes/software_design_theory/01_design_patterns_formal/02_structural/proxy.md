# Proxy 形式化分析

> **创建日期**: 2026-02-12
> **分类**: 结构型
> **安全边界**: 纯 Safe

---

## 形式化定义

**Def 1.1（Proxy 结构）**:

设 $P$ 为代理类型，$T$ 为目标类型。Proxy 满足：

- $P$ 持有或可获取 $T$（延迟加载、缓存等）
- $P$ 实现与 $T$ 相同的接口
- $\mathit{op}(p)$ 可延迟加载、访问控制、日志等，再委托 $p \to T$

**Axiom PR1**：代理与目标接口一致，可透明替换。

**Axiom PR2**：委托时借用/所有权规则满足；无循环依赖。

**定理 PR-T1**：委托时借用/所有权规则保证正确性。由 [borrow_checker_proof](../../../formal_methods/borrow_checker_proof.md)。

**推论 PR-C1**：Proxy 为纯 Safe；`OnceLock` 延迟加载、委托调用，无 `unsafe`。由 PR-T1 及 [safe_unsafe_matrix](../../05_boundary_system/safe_unsafe_matrix.md) SBM-T1。

---

## Rust 实现与代码示例

```rust
trait Subject {
    fn request(&self) -> String;
}

struct RealSubject;
impl Subject for RealSubject {
    fn request(&self) -> String { "real".into() }
}

use std::sync::OnceLock;

struct LazyProxy {
    inner: OnceLock<RealSubject>,
}

impl LazyProxy {
    fn new() -> Self {
        Self { inner: OnceLock::new() }
    }
}

impl Subject for LazyProxy {
    fn request(&self) -> String {
        self.inner.get_or_init(|| RealSubject).request()
    }
}

// 使用：首次调用时初始化
let p = LazyProxy::new();
assert_eq!(p.request(), "real");
```

**虚拟代理（延迟加载）**：

```rust
struct Proxy<T> {
    target: Option<T>,
}

impl<T: Subject> Subject for Proxy<T> {
    fn request(&self) -> String {
        self.target.as_ref().map(|t| t.request()).unwrap_or_default()
    }
}
```

**形式化对应**：`LazyProxy` 即 $P$；`RealSubject` 即 $T$；`request` 延迟加载后委托。

---

## 证明思路

1. **延迟加载**：`OnceLock` 保证仅初始化一次；`get_or_init` 为 Safe。
2. **委托**：`t.request()` 借用 `t`，无冲突。

---

## 典型场景

| 场景 | 说明 |
| :--- | :--- |
| 虚拟代理 | 延迟加载、懒初始化 |
| 保护代理 | 访问控制、权限检查 |
| 远程代理 | 封装 RPC、跨进程调用 |
| 缓存代理 | 缓存结果、减少重复计算 |

---

## 相关模式

| 模式 | 关系 |
| :--- | :--- |
| [Decorator](decorator.md) | 同为包装；Proxy 控制访问，Decorator 扩展行为 |
| [Flyweight](flyweight.md) | Proxy 可包装 Flyweight 做延迟/缓存 |
| [Facade](facade.md) | Proxy 委托单对象；Facade 聚合多对象 |

---

## 实现变体

| 变体 | 说明 | 适用 |
| :--- | :--- | :--- |
| `OnceLock`/`LazyLock` | 虚拟代理；延迟加载 | 耗时初始化 |
| `Arc<Mutex<T>>` | 保护代理；跨线程 | 访问控制 |
| 智能指针 | `Rc`、`Arc` 即引用计数代理 | 共享、生命周期 |

---

## 反例：代理持有 mut 且未同步

**错误**：代理内部用 `RefCell` 缓存，跨线程共享时未用 `Mutex`。

```rust
struct BadProxy {
    cache: std::cell::RefCell<Option<String>>,  // 非 Send
}
// 若跨线程使用 → 编译失败；若单线程滥用 RefCell 写后读 → 运行时 panic
```

**正确**：跨线程用 `Mutex` 或 `RwLock`；单线程用 `RefCell` 需保证借用规则。

---

## 选型决策树

```text
需要控制对目标的访问？
├── 延迟加载？ → OnceLock/LazyLock 代理
├── 访问控制？ → 保护代理（包装 + 检查）
├── 远程调用？ → 远程代理（封装 RPC）
├── 缓存？ → 缓存代理
└── 扩展行为（同接口）？ → Decorator
```

---

## 与 GoF 对比

| GoF | Rust 对应 | 差异 |
| :--- | :--- | :--- |
| 虚拟代理 | OnceLock | 等价 |
| 保护代理 | 包装 + 委托 | 等价 |
| 远程代理 | tonic/HTTP 客户端 | 等价 |

---

## 边界

| 维度 | 分类 |
| :--- | :--- |
| 安全 | 纯 Safe |
| 支持 | 原生 |
| 表达 | 等价 |
