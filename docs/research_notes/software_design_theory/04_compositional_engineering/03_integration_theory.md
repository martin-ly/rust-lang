# 与 ownership/borrow/trait 的衔接

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-12
> **Rust 版本**: 1.93.0+ (Edition 2024)

---

## 形式化定义与定理

**Def 1.1（跨模块边界）**

设 $M_1$、$M_2$ 为模块，$f : M_1 \to M_2$ 为 `pub fn` 调用。**跨模块边界**指 $f$ 的参数与返回值在 $M_1$ 与 $M_2$ 间传递。

**Def 1.2（性质保持）**

设 $\Phi$ 为性质（如内存安全、无数据竞争、类型安全）。若 $M_1$、$M_2$ 各自满足 $\Phi$，且跨模块调用不破坏 $\Phi$，则称**组合保持 $\Phi$**。

**Axiom IT1**：所有权在跨模块值传递时转移；引用传递遵守借用规则。由 [ownership_model](../../formal_methods/ownership_model.md) 规则 1–3、[borrow_checker_proof](../../formal_methods/borrow_checker_proof.md) 规则 5–8。

**Axiom IT2**：`Send`/`Sync` 为结构性质；若 $T$ 的所有字段为 Send，则 $T$ 为 Send。组合不改变字段类型。

**定理 IT-T1（跨模块所有权保持）**：若 $M_1$ 调用 $M_2$ 的 `pub fn f(x: T)`，则 $x$ 的所有权从 $M_1$ 转移至 $M_2$；规则与模块内一致。

*证明*：由 [02_effectiveness_proofs](02_effectiveness_proofs.md) CE-T1；模块边界仅为 `pub fn` 调用，值/引用传递语义不变。

**定理 IT-T2（跨模块 Send/Sync 传递）**：若 $M_1$ 的 `pub fn` 返回 `impl Future + Send` 且内部持有 $T$，则 $T: \mathrm{Send}$ 为必要条件。

*证明*：由 [async_state_machine](../../formal_methods/async_state_machine.md) T6.1–T6.3；Future 跨 await 点持有时，需 Send 才能跨线程。

---

## 衔接关系图

```text
组合软件工程有效性
        │
        ├── 所有权：[ownership_model](../../formal_methods/ownership_model.md) T2, T3
        │   组合时值传递/移动/借用保持唯一性
        │   跨模块调用：参数为值则移动，为 & 则借用
        │
        ├── 借用：[borrow_checker_proof](../../formal_methods/borrow_checker_proof.md) T1
        │   组合时借用规则跨模块成立
        │   pub fn f(&self, x: &T) 保证 x 与 self 借用互斥
        │
        ├── 生命周期：[lifetime_formalization](../../formal_methods/lifetime_formalization.md) T2
        │   组合时 outlives 关系保持
        │   跨模块引用需满足生命周期约束
        │
        ├── 类型系统：[type_system_foundations](../../type_theory/type_system_foundations.md) T1–T3
        │   组合时类型检查保持
        │   模块边界：实参类型与形参一致
        │
        ├── Trait：[trait_system_formalization](../../type_theory/trait_system_formalization.md)
        │   组合时 impl 解析、对象安全保持
        │   泛型约束跨模块传递
        │
        └── 异步：[async_state_machine](../../formal_methods/async_state_machine.md) T6.1–T6.3
            组合时 Future 状态转换保持
            async 模块组合：await 链保持 Send
```

---

## 组合与所有权

| 传递方式 | 所有权 | 形式化 |
|----------|--------|--------|
| `fn f(x: T)` | 移动 | $\Omega(x) \mapsto \text{callee}$ |
| `fn f(x: &T)` | 不可变借用 | 借用规则 5–6 |
| `fn f(x: &mut T)` | 可变借用 | 借用规则 7–8 |
| `fn f() -> T` | 返回转移 | $\Omega(\text{ret}) \mapsto \text{caller}$ |

组合时上述规则在模块边界不变；`pub fn` 为边界。

---

## 组合与 trait

| 场景 | 衔接 |
|------|------|
| `fn f<T: Trait>(x: T)` | 泛型约束跨模块；单态化后类型确定 |
| `fn f(x: &dyn Trait)` | 对象安全；vtable 正确 |
| `impl Trait for ForeignType` | 孤儿规则； coherence 保证 |

---

## 设计模式组合示例

设计模式可组合使用，例如：

- **Builder + Factory Method**：Builder 作为工厂的产品
- **Decorator + Strategy**：装饰器持有多态策略
- **Observer + Command**：观察者接收命令对象
- **Composite + Visitor**：组合结构配合访问者遍历

组合后由各模式的形式化约束与 CE-T1–T3，保持安全性。

---

## 组合代码示例

```rust
// Builder + Strategy：可配置的排序策略
trait SortStrategy { fn sort(&self, v: &mut [i32]); }
struct QuickSort;
impl SortStrategy for QuickSort { fn sort(&self, v: &mut [i32]) { /* ... */ } }

struct SorterBuilder<S: SortStrategy> { strategy: S }
impl<S: SortStrategy> SorterBuilder<S> {
    fn new(strategy: S) -> Self { Self { strategy } }
    fn sort(&self, v: &mut [i32]) { self.strategy.sort(v); }
}

// Composite + Visitor：树遍历
fn visit<V: Visitor>(v: &mut V, node: &Node) {
    match node {
        Node::Leaf(x) => v.visit_leaf(x),
        Node::Composite(children) => {
            for c in children { visit(v, c); }
            v.visit_composite(children);
        }
    }
}
```

---

## 组合验证清单

组合多模块/多模式时，确认：

- [ ] **CE-T1**：无 `unsafe` 泄漏；跨模块无悬垂、双重释放
- [ ] **CE-T2**：跨线程仅 `Send` 类型；共享仅 `Sync` 类型
- [ ] **CE-T3**：`cargo check` 通过；类型在边界一致
- [ ] **依赖无环**：`mod`/`use` 图无环
- [ ] **接口稳定**：`pub` 变更需考虑消费者

---

## 跨模块 Send/Sync 传递

| 场景 | 约束 |
|------|------|
| `spawn(move || ...)` 捕获模块内类型 | 捕获类型需 `Send` |
| `Arc<T>` 跨线程共享 | `T: Send + Sync` |
| `Mutex<T>` 跨线程 | `T: Send`（Mutex 内部保证 Sync） |
| async 块跨 await | 持有什么类型决定 Future 是否 Send |

组合时：若模块 A 的 `pub fn` 返回 `impl Future` 且内部持有 `T`，则 `T: Send` 才能跨 spawn。

---

## 组合反例

| 反例 | 后果 |
|------|------|
| 循环 mod 依赖 | 编译失败 |
| pub 暴露 unsafe | 破坏 CE-T1 |
| 跨模块传递 `Rc` 到 spawn | 编译错误（非 Send） |
| trait 方法返回 `Self` 做 dyn | 对象安全违规 |

---

## 引用

- [THEORETICAL_AND_ARGUMENTATION_SYSTEM_ARCHITECTURE](../../THEORETICAL_AND_ARGUMENTATION_SYSTEM_ARCHITECTURE.md) § 1.2 理论族依赖
- [COMPREHENSIVE_SYSTEMATIC_OVERVIEW](../../COMPREHENSIVE_SYSTEMATIC_OVERVIEW.md) 概念族谱
