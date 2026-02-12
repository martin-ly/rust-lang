# Facade 形式化分析

> **创建日期**: 2026-02-12
> **分类**: 结构型
> **安全边界**: 纯 Safe

---

## 形式化定义

**Def 1.1（Facade 结构）**

设 $F$ 为外观类型，$S_1, \ldots, S_n$ 为子系统类型。Facade 满足：

- $F$ 持有或可访问 $S_1, \ldots, S_n$
- $\exists \mathit{simplified\_op} : F \to R$，封装对子系统的调用序列
- 客户端仅通过 $F$ 的 `pub` 方法访问；子系统可私有

**Axiom FA1**：外观简化接口，隐藏子系统复杂性。

**Axiom FA2**：外观协调调用顺序；子系统间依赖由 $F$ 管理。

**定理 FA-T1**：模块系统与 `pub` 可见性保证封装边界。由 Rust 模块语义。

---

## Rust 实现与代码示例

```rust
// 子系统（通常为私有模块）
struct SubsystemA;
impl SubsystemA {
    fn operation_a(&self) -> String { "A".into() }
}

struct SubsystemB;
impl SubsystemB {
    fn operation_b(&self, s: &str) -> String {
        format!("B({})", s)
    }
}

// 外观
pub struct Facade {
    a: SubsystemA,
    b: SubsystemB,
}

impl Facade {
    pub fn new() -> Self {
        Self {
            a: SubsystemA,
            b: SubsystemB,
        }
    }
    pub fn simplified_op(&self) -> String {
        let x = self.a.operation_a();
        self.b.operation_b(&x)
    }
}

// 客户端仅使用 Facade
let f = Facade::new();
assert_eq!(f.simplified_op(), "B(A)");
```

**形式化对应**：`Facade` 即 $F$；`SubsystemA`、`SubsystemB` 即 $S_1$、$S_2$；`simplified_op` 即 $\mathit{simplified\_op}$。

---

## 证明思路

1. **封装**：`a`、`b` 为私有字段；客户端仅通过 `simplified_op` 访问。
2. **所有权**：`Facade` 拥有子系统；`&self` 借用，委托调用合法。

---

## 典型场景

| 场景 | 说明 |
|------|------|
| 库/API 简化 | 复杂 SDK 封装为简单入口 |
| 子系统协调 | 编排多个模块的调用顺序 |
| 遗留系统 | 封装旧接口为新接口 |

---

## 相关模式

| 模式 | 关系 |
|------|------|
| [Adapter](adapter.md) | Facade 简化多接口；Adapter 转换单接口 |
| [Mediator](../03_behavioral/mediator.md) | Facade 协调子系统；Mediator 协调同事 |
| [Proxy](proxy.md) | Proxy 委托单对象；Facade 聚合多对象 |

---

## 实现变体

| 变体 | 说明 | 适用 |
|------|------|------|
| 结构体聚合 | `struct Facade { a: A, b: B }` | 持有子系统 |
| 模块 | `mod facade { pub fn op() }` | 函数级简化 |
| trait | `trait Facade { fn op(&self); }` | 多实现 |

---

## 反例：外观暴露子系统细节

**错误**：外观将子系统类型作为 `pub` 字段或方法参数暴露，破坏封装。

```rust
pub struct BadFacade {
    pub a: SubsystemA,  // 暴露内部，客户端可直接操作
}
```

**后果**：客户端依赖子系统，外观失去简化接口的意义；违反 Axiom FA1。

---

## 选型决策树

```
需要简化多子系统调用？
├── 是 → 仅协调调用顺序？ → Facade（结构体聚合）
│       └── 需调解对象间通信？ → Mediator
├── 转换单接口？ → Adapter
└── 委托单对象？ → Proxy
```

---

## 与 GoF 对比

| GoF | Rust 对应 | 差异 |
|-----|-----------|------|
| 外观类 | 结构体或模块 | 等价 |
| 子系统 | 私有字段 | 完全等价 |
| 简化接口 | pub fn | 等价 |

---

## 边界

| 维度 | 分类 |
|------|------|
| 安全 | 纯 Safe |
| 支持 | 原生 |
| 表达 | 等价 |
