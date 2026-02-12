# Flyweight 形式化分析

> **创建日期**: 2026-02-12
> **分类**: 结构型
> **安全边界**: 纯 Safe

---

## 形式化定义

**Def 1.1（Flyweight 结构）**

设 $F$ 为享元类型，$K$ 为键类型。Flyweight 满足：

- $\exists \mathit{get} : K \to \mathrm{Arc}\langle F \rangle$ 或 $\&F$
- 相同 $k$ 返回共享实例；缓存避免重复创建
- 不可变共享：$\mathit{get}(k)$ 为只读引用或 `Arc`；可变状态外置

**Axiom FL1**：共享状态不可变；可变状态外置（如组合为 `(F, Extrinsic)`）。

**Axiom FL2**：缓存键唯一；`HashMap` 保证 $k \mapsto f$ 单射。

**定理 FL-T1**：`Arc` 引用计数保证共享安全；由 [ownership_model](../../../formal_methods/ownership_model.md) 无悬垂。

**定理 FL-T2**：跨线程共享需 `Arc` + `Sync`；单线程可用 `Rc`。

**推论 FL-C1**：Flyweight 为纯 Safe；`Arc`/`Rc` 共享不可变，无 `unsafe`；可变状态外置时用 `Mutex` 等 Safe 抽象。由 FL-T1、FL-T2 及 [safe_unsafe_matrix](../../05_boundary_system/safe_unsafe_matrix.md) SBM-T1。

---

## Rust 实现与代码示例

```rust
use std::collections::HashMap;
use std::sync::Arc;

struct FlyweightFactory {
    cache: HashMap<String, Arc<str>>,
}

impl FlyweightFactory {
    fn new() -> Self {
        Self { cache: HashMap::new() }
    }
    fn get(&mut self, key: &str) -> Arc<str> {
        if let Some(v) = self.cache.get(key) {
            return Arc::clone(v);
        }
        let v = Arc::from(key.to_string().into_boxed_str());
        self.cache.insert(key.to_string(), Arc::clone(&v));
        v
    }
}

// 使用：相同 key 共享
let mut f = FlyweightFactory::new();
let a = f.get("hello");
let b = f.get("hello");
assert!(Arc::ptr_eq(&a, &b));  // 同一实例
```

**形式化对应**：`FlyweightFactory` 为缓存；`get` 即 $\mathit{get}$；`Arc<str>` 为共享不可变。

---

## 证明思路

1. **共享**：`Arc::clone` 增加引用计数；多持有者共享同一堆对象。
2. **不可变**：`Arc<str>` 为共享只读；无数据竞争。

---

## 典型场景

| 场景 | 说明 |
| :--- | :--- |
| 字符/字符串池 | 相同字符串共享 |
| 配置/主题 | 共享只读配置 |
| 图元/纹理 | 游戏、图形共享资源 |
| 类型对象 | 共享元数据 |

---

## 相关模式

| 模式 | 关系 |
| :--- | :--- |
| [Proxy](proxy.md) | Proxy 可包装 Flyweight 做延迟/缓存 |
| [Singleton](../01_creational/singleton.md) | 同为共享；Flyweight 按 key 共享，Singleton 全局唯一 |
| 对象池（扩展） | 共享池；Flyweight 不可变，Pool 可回收 |

---

## 实现变体

| 变体 | 说明 | 适用 |
| :--- | :--- | :--- |
| `HashMap<K, Arc<T>>` | 缓存；跨线程用 Arc | 通用 |
| `Rc` | 单线程共享 | 无 Send 需求 |
| `intern` 字符串 | 相同字符串共享 | 解析器、编译器 |

---

## 反例：共享可变状态

**错误**：享元内部含 `Cell`/`RefCell` 等可变状态，多持有者共享时产生数据竞争或逻辑错误。

```rust
struct BadFlyweight {
    count: std::cell::Cell<u32>,  // 共享可变
}
// 多线程用 Arc<BadFlyweight> → 数据竞争（若单线程则为逻辑错误）
```

**Axiom FL1**：共享状态必须不可变；可变状态外置。

---

## 选型决策树

```text
需要共享不可变实例？
├── 是 → 按 key 共享？ → Flyweight（HashMap + Arc）
│       └── 全局唯一？ → Singleton
├── 需可变共享？ → 非 Flyweight
└── 仅单次使用？ → 普通创建
```

---

## 与 GoF 对比

| GoF | Rust 对应 | 差异 |
| :--- | :--- | :--- |
| 享元工厂 | struct + HashMap | 等价 |
| 共享状态 | Arc<T> | 引用计数 |
| extrinsic | 方法参数 | 等价 |

---

## 边界

| 维度 | 分类 |
| :--- | :--- |
| 安全 | 纯 Safe |
| 支持 | 原生 |
| 表达 | 等价 |
