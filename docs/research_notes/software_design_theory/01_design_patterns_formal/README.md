# 设计模式形式分析框架

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-12
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: 100% 完成

---

## 宗旨

对 GoF 23 种设计模式进行形式化分析，建立公理/定义/定理级框架，并与 Rust 形式化基础（ownership、borrow、trait、type_system）衔接。

---

## Rust 实践要点

- **trait 优先**：多数模式用 trait 定义接口；`impl Trait` 或 `dyn Trait` 实现多态
- **枚举优先于继承**：State、Interpreter、Composite 用 `enum` + `match`；穷尽匹配保证完备
- **所有权优先**：链式用 `Box`；共享用 `Arc`；避免 `Rc` 环
- **channel 优先于回调**：Observer 用 `mpsc`/`broadcast` 避免共享可变

---

## 生命周期考虑

| 模式 | 生命周期要点 |
|------|--------------|
| Chain、Composite | `Box` 递归；无引用则无生命周期标注 |
| Observer | channel 转移所有权；无引用生命周期 |
| Adapter、Decorator | `inner` 为拥有；`&self` 借用无 `'a` |
| 含 `&'a T` 的模式 | 需显式 `'a`；保证被引用者 outlives |

---

## 跨线程考虑

| 模式 | Send/Sync 要点 |
|------|----------------|
| Singleton | `OnceLock` 内部同步；`T` 需 `Send` 才可跨线程 |
| Observer | `mpsc`/`broadcast` 需消息 `Send`；回调需 `Sync` |
| Flyweight | 跨线程用 `Arc` 不用 `Rc`；`T` 需 `Sync` |
| Mediator | 同事持有 `Arc` 时需 `Send` |

详见 [01_safe_23_catalog](../02_workflow_safe_complete_models/01_safe_23_catalog.md) 实现约束。

---

## Box / Rc / Arc 选型

| 类型 | 所有权 | 适用 |
|------|--------|------|
| `Box<T>` | 独占 | Chain 的 next、Composite 的 children、递归结构 |
| `Rc<T>` | 共享；单线程 | Flyweight 单线程、Observable 回调 |
| `Arc<T>` | 共享；跨线程 | Flyweight 跨线程、Singleton、Observer channel |

---

## 形式化框架

### 公理与定义

每个模式的形式化分析包含：

1. **Def（定义）**：模式结构的形式化描述（类型、所有权、借用约束）
2. **Axiom（公理）**：模式满足的不变式
3. **定理（Theorem）**：由所有权/借用/类型规则推导的保证

### 依赖引用

形式化分析引用以下已有证明：

| 依赖 | 文档 | 引用定理 |
|------|------|----------|
| 所有权 | [ownership_model](../../formal_methods/ownership_model.md) | T2 唯一性、T3 内存安全 |
| 借用 | [borrow_checker_proof](../../formal_methods/borrow_checker_proof.md) | 数据竞争自由 T1 |
| 生命周期 | [lifetime_formalization](../../formal_methods/lifetime_formalization.md) | 引用有效性 T2 |
| 类型系统 | [type_system_foundations](../../type_theory/type_system_foundations.md) | 进展 T1、保持 T2、类型安全 T3 |
| Trait | [trait_system_formalization](../../type_theory/trait_system_formalization.md) | 对象安全、解析 |

---

## 目录结构

### 01_creational（创建型，5）

| 模式 | 文档 |
|------|------|
| Factory Method | [factory_method](01_creational/factory_method.md) |
| Abstract Factory | [abstract_factory](01_creational/abstract_factory.md) |
| Builder | [builder](01_creational/builder.md) |
| Prototype | [prototype](01_creational/prototype.md) |
| Singleton | [singleton](01_creational/singleton.md) |

### 02_structural（结构型，7）

| 模式 | 文档 |
|------|------|
| Adapter | [adapter](02_structural/adapter.md) |
| Bridge | [bridge](02_structural/bridge.md) |
| Composite | [composite](02_structural/composite.md) |
| Decorator | [decorator](02_structural/decorator.md) |
| Facade | [facade](02_structural/facade.md) |
| Flyweight | [flyweight](02_structural/flyweight.md) |
| Proxy | [proxy](02_structural/proxy.md) |

### 03_behavioral（行为型，11）

| 模式 | 文档 |
|------|------|
| Chain of Responsibility | [chain_of_responsibility](03_behavioral/chain_of_responsibility.md) |
| Command | [command](03_behavioral/command.md) |
| Interpreter | [interpreter](03_behavioral/interpreter.md) |
| Iterator | [iterator](03_behavioral/iterator.md) |
| Mediator | [mediator](03_behavioral/mediator.md) |
| Memento | [memento](03_behavioral/memento.md) |
| Observer | [observer](03_behavioral/observer.md) |
| State | [state](03_behavioral/state.md) |
| Strategy | [strategy](03_behavioral/strategy.md) |
| Template Method | [template_method](03_behavioral/template_method.md) |
| Visitor | [visitor](03_behavioral/visitor.md) |

### 04_boundary_matrix

[04_boundary_matrix](04_boundary_matrix.md)：模式 × 安全/支持/表达边界汇总。

---

## 边界矩阵

详见 [05_boundary_system](../05_boundary_system/README.md)。

---

## 创建型模式对比

| 模式 | 适用场景 | 核心机制 |
|------|----------|----------|
| Factory Method | 单产品、多态创建 | `fn create(&self) -> T` |
| Abstract Factory | 产品族、风格一致 | 关联类型、枚举族 |
| Builder | 多步骤、可选参数 | 链式 + `build(self)` |
| Prototype | 克隆已有对象 | `Clone` |
| Singleton | 全局唯一实例 | `OnceLock` |

---

## 结构型模式对比

| 模式 | 适用场景 | 核心机制 |
|------|----------|----------|
| Adapter | 适配已有接口 | 包装 + `impl Trait for Wrapper` |
| Bridge | 解耦抽象与实现 | trait 解耦 |
| Composite | 树状结构 | 枚举递归、`Vec<Node>` |
| Decorator | 链式扩展行为 | 包装 + 委托 |
| Facade | 简化多接口 | 模块/结构体聚合 |
| Flyweight | 共享不可变 | `Arc` + `HashMap` |
| Proxy | 控制访问、延迟 | 委托、OnceLock |

---

## 行为型模式对比

| 模式 | 适用场景 | 核心机制 |
|------|----------|----------|
| Chain | 请求沿链传递 | `Option<Box<Handler>>` |
| Command | 封装操作、可撤销 | `Fn`、trait |
| Interpreter | 表达式求值 | 枚举 AST + match |
| Iterator | 顺序遍历 | `Iterator` trait |
| Mediator | 多对象协调 | 结构体、channel |
| Memento | 保存/恢复状态 | Clone、serde |
| Observer | 一对多通知 | channel、回调 |
| State | 状态转换 | 枚举、类型状态 |
| Strategy | 可替换算法 | trait |
| Template Method | 算法骨架 | trait 默认方法 |
| Visitor | 树遍历 | match + trait |

---

## 常见模式组合

| 组合 | 说明 |
|------|------|
| Composite + Visitor | 树遍历；[composite](02_structural/composite.md)、[visitor](03_behavioral/visitor.md) |
| Builder + Factory Method | 构建由工厂创建；[builder](01_creational/builder.md)、[factory_method](01_creational/factory_method.md) |
| Decorator + Strategy | 装饰器持有多态策略；[decorator](02_structural/decorator.md)、[strategy](03_behavioral/strategy.md) |
| Observer + Command | 观察者接收命令；[observer](03_behavioral/observer.md)、[command](03_behavioral/command.md) |
| Chain + Command | 链中节点封装为命令；[chain_of_responsibility](03_behavioral/chain_of_responsibility.md)、[command](03_behavioral/command.md) |

---

## 错误处理

| 模式 | Result vs panic |
|------|-----------------|
| Builder | `build() -> Result<T, E>` 推荐；缺必填返回 Err |
| Factory | 可返回 `Option`/`Result`；match 穷尽避免 panic |
| Command | `execute() -> Result` 可传播错误 |
| 一般 | 不可恢复用 panic；可恢复用 Result |

---

## 测试建议

| 模式类型 | 测试要点 |
|----------|----------|
| 创建型 | 产品类型正确；所有权转移 |
| 结构型 | 委托链正确；无遗漏调用 |
| 行为型 | 状态转换；Observer 通知顺序；Chain 委托 |
| 跨线程 | 加 `#[test]` 多线程用例；MIRI 检测 |

---

## 何时不选用

| 模式 | 不适用场景 |
|------|------------|
| Singleton | 需多实例、可测试性优先 |
| Abstract Factory | 仅单产品 → 用 Factory Method |
| Visitor | 结构稳定、操作常变 → 用 match 内联 |
| Chain | 请求总由单处处理 → 直接调用 |
| Observer | 同步紧耦合 → 直接调用 |

---

## 代码审查清单

实现模式后，确认：

- [ ] 满足形式化定义（Def）与公理（Axiom）
- [ ] 无对应反例（见 FORMAL_PROOF_SYSTEM_GUIDE）
- [ ] 错误处理：可恢复用 Result，不可恢复才 panic
- [ ] 跨线程时 Send/Sync 正确
- [ ] 有无不必要的 unsafe

---

## 反例索引

设计模式违反边界时的反例见 [FORMAL_PROOF_SYSTEM_GUIDE](../../FORMAL_PROOF_SYSTEM_GUIDE.md#设计模式反例)：

| 模式 | 反例 |
|------|------|
| Singleton | 全局可变未同步 → 数据竞争 |
| Observer | 共享可变无 Mutex → 数据竞争 |
| Composite | 循环引用 → 所有权无法表达 |
| Builder | build 前必填未设 → 运行时错误 |
| Memento | 恢复非法状态 → 不变式违反 |
| Iterator | 迭代中修改集合 → 借用冲突 |
| Prototype | Clone 浅拷贝共享 → 隐式耦合 |
