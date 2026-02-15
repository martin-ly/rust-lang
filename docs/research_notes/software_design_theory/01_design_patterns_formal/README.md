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
| :--- | :--- |
| Chain、Composite | `Box` 递归；无引用则无生命周期标注 |
| Observer | channel 转移所有权；无引用生命周期 |
| Adapter、Decorator | `inner` 为拥有；`&self` 借用无 `'a` |
| 含 `&'a T` 的模式 | 需显式 `'a`；保证被引用者 outlives |

---

## 跨线程考虑

| 模式 | Send/Sync 要点 |
| :--- | :--- |
| Singleton | `OnceLock` 内部同步；`T` 需 `Send` 才可跨线程 |
| Observer | `mpsc`/`broadcast` 需消息 `Send`；回调需 `Sync` |
| Flyweight | 跨线程用 `Arc` 不用 `Rc`；`T` 需 `Sync` |
| Mediator | 同事持有 `Arc` 时需 `Send` |

详见 [01_safe_23_catalog](../02_workflow_safe_complete_models/01_safe_23_catalog.md) 实现约束。

---

## Box / Rc / Arc 选型

| 类型 | 所有权 | 适用 |
| :--- | :--- | :--- |
| `Box<T>` | 独占 | Chain 的 next、Composite 的 children、递归结构 |
| `Rc<T>` | 共享；单线程 | Flyweight 单线程、Observable 回调 |
| `Arc<T>` | 共享；跨线程 | Flyweight 跨线程、Singleton、Observer channel |

---

## 典型场景与实现变体（实质内容）

每个模式文档均包含：

- **典型场景**：如 Interpreter 的表达式求值、脚本解析、过滤表达式；Observer 的事件通知、多订阅者
- **实现变体**：如 Interpreter 的「枚举 + match」vs「trait 节点」vs「Visitor 分离」；Builder 的「Option + ok_or」vs「类型状态」
- **相关模式**：如 Interpreter 与 Visitor、Composite、Strategy 的关系
- **选型决策树**：按需求反向查模式

**完整场景示例**：创建型 Builder（HTTP 请求）；结构型 Flyweight（字形缓存）、Adapter（HTTP 客户端）、Decorator（日志+重试）、Composite（文件系统树）；行为型 Interpreter（过滤 DSL）、Chain（HTTP 中间件）、Mediator（聊天室）、Observer（订单事件）、Strategy（压缩格式）、Command（可撤销编辑器）、State（订单状态机）、Visitor（AST 美化）；Facade（日志系统）、Template Method（数据导入）等均有完整可运行示例。

---

## 形式化框架

### 公理与定义

每个模式的形式化分析包含：

1. **Def（定义）**：模式结构的形式化描述（类型、所有权、借用约束）
2. **Axiom（公理）**：模式满足的不变式
3. **定理（Theorem）**：由所有权/借用/类型规则推导的保证
4. **推论（Corollary）**：由定理推导的结论（如纯 Safe、与边界矩阵一致等）；23 种模式均已补全

### 依赖引用

形式化分析引用以下已有证明：

| 依赖 | 文档 | 引用定理 |
| :--- | :--- | :--- |
| 所有权 | [ownership_model](../../formal_methods/ownership_model.md) | T2 唯一性、T3 内存安全 |
| 借用 | [borrow_checker_proof](../../formal_methods/borrow_checker_proof.md) | 数据竞争自由 T1 |
| 生命周期 | [lifetime_formalization](../../formal_methods/lifetime_formalization.md) | 引用有效性 T2 |
| 类型系统 | [type_system_foundations](../../type_theory/type_system_foundations.md) | 进展 T1、保持 T2、类型安全 T3 |
| Trait | [trait_system_formalization](../../type_theory/trait_system_formalization.md) | 对象安全、解析 |

---

## 目录结构

### 01_creational（创建型，5）

| 模式 | 文档 |
| :--- | :--- |
| Factory Method | [factory_method](01_creational/factory_method.md) |
| Abstract Factory | [abstract_factory](01_creational/abstract_factory.md) |
| Builder | [builder](01_creational/builder.md) |
| Prototype | [prototype](01_creational/prototype.md) |
| Singleton | [singleton](01_creational/singleton.md) |

### 02_structural（结构型，7）

| 模式 | 文档 |
| :--- | :--- |
| Adapter | [adapter](02_structural/adapter.md) |
| Bridge | [bridge](02_structural/bridge.md) |
| Composite | [composite](02_structural/composite.md) |
| Decorator | [decorator](02_structural/decorator.md) |
| Facade | [facade](02_structural/facade.md) |
| Flyweight | [flyweight](02_structural/flyweight.md) |
| Proxy | [proxy](02_structural/proxy.md) |

### 03_behavioral（行为型，11）

| 模式 | 文档 |
| :--- | :--- |
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
| :--- | :--- | :--- |
| Factory Method | 单产品、多态创建 | `fn create(&self) -> T` |
| Abstract Factory | 产品族、风格一致 | 关联类型、枚举族 |
| Builder | 多步骤、可选参数 | 链式 + `build(self)` |
| Prototype | 克隆已有对象 | `Clone` |
| Singleton | 全局唯一实例 | `OnceLock` |

---

## 结构型模式对比

| 模式 | 适用场景 | 核心机制 |
| :--- | :--- | :--- |
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
| :--- | :--- | :--- |
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

## 23 模式多维对比矩阵

下表为 23 种设计模式的**概念定义/属性关系/表达力**多维对比；每行链接到对应模式文档。用于选型与「文档↔矩阵」双向追溯（见 [HIERARCHICAL_MAPPING_AND_SUMMARY](../../HIERARCHICAL_MAPPING_AND_SUMMARY.md)）。

| 模式 | 所有权特征 | 借用特征 | 安全边界 | 典型场景 | Rust 机制衔接 |
| :--- | :--- | :--- | :--- | :--- | :--- |
| [Factory Method](01_creational/factory_method.md) | 工厂返回拥有 | 多态创建只读/可变 | 纯 Safe | 单产品多态创建 | trait 返回 `impl Trait`/Box |
| [Abstract Factory](01_creational/abstract_factory.md) | 产品族拥有 | 族内一致 | 纯 Safe | 产品族、风格一致 | 关联类型、枚举族 |
| [Builder](01_creational/builder.md) | `build(self)` 消费 | 链式 `self` 移动 | 纯 Safe | 多步骤、可选参数 | 链式 + 所有权消费 |
| [Prototype](01_creational/prototype.md) | 克隆新拥有 | 可借出只读 | 纯 Safe | 克隆已有对象 | `Clone` |
| [Singleton](01_creational/singleton.md) | 全局唯一拥有 | 共享只读/同步可变 | 纯 Safe（OnceLock） | 全局唯一实例 | `OnceLock`、`LazyLock` |
| [Adapter](02_structural/adapter.md) | 包装拥有 inner | 委托 `&self` | 纯 Safe | 适配已有接口 | 包装 + `impl Trait for Wrapper` |
| [Bridge](02_structural/bridge.md) | 抽象持实现 | trait 解耦 | 纯 Safe | 抽象与实现解耦 | trait 对象/泛型 |
| [Composite](02_structural/composite.md) | 树递归拥有 | 遍历借用 | 纯 Safe | 树状结构 | `Vec<Node>`、枚举递归 |
| [Decorator](02_structural/decorator.md) | 包装拥有 inner | 委托 `&self`/`&mut` | 纯 Safe | 链式扩展行为 | 包装 + 委托 |
| [Facade](02_structural/facade.md) | 聚合多子组件 | 内部借用 | 纯 Safe | 简化多接口 | 模块/结构体聚合 |
| [Flyweight](02_structural/flyweight.md) | 共享不可变 | `Arc` 共享读 | 纯 Safe | 共享不可变 | `Arc` + `HashMap` |
| [Proxy](02_structural/proxy.md) | 延迟拥有目标 | 委托访问 | 纯 Safe | 控制访问、延迟 | 委托、OnceLock |
| [Chain](03_behavioral/chain_of_responsibility.md) | 链节点拥有 next | 沿链借用 | 纯 Safe | 请求沿链传递 | `Option<Box<Handler>>` |
| [Command](03_behavioral/command.md) | 封装操作拥有 | 执行时借用 | 纯 Safe | 封装操作、可撤销 | `Fn`、trait |
| [Interpreter](03_behavioral/interpreter.md) | AST 拥有子节点 | 求值只读 | 纯 Safe | 表达式求值 | 枚举 AST + match |
| [Iterator](03_behavioral/iterator.md) | 迭代器持有状态 | `&mut self` next | 纯 Safe | 顺序遍历 | `Iterator` trait |
| [Mediator](03_behavioral/mediator.md) | 中介持同事 | channel/引用 | 纯 Safe | 多对象协调 | 结构体、channel |
| [Memento](03_behavioral/memento.md) | 快照拥有状态 | 恢复时消费 | 纯 Safe | 保存/恢复状态 | Clone、serde |
| [Observer](03_behavioral/observer.md) | 主题/订阅者 | channel 转移所有权 | 纯 Safe | 一对多通知 | channel、回调 |
| [State](03_behavioral/state.md) | 状态机拥有当前 | 转换借用 | 纯 Safe | 状态转换 | 枚举、类型状态 |
| [Strategy](03_behavioral/strategy.md) | 持有策略 trait | 运行时多态 | 纯 Safe | 可替换算法 | trait |
| [Template Method](03_behavioral/template_method.md) | 骨架拥有 | 钩子 `&self` | 纯 Safe | 算法骨架 | trait 默认方法 |
| [Visitor](03_behavioral/visitor.md) | 访问者拥有 | 遍历只读/可变 | 纯 Safe | 树遍历 | match + trait |

*安全边界*：当前 23 模式均为纯 Safe；若某模式扩展使用 `unsafe`，见 [04_boundary_matrix](04_boundary_matrix.md)、[05_boundary_system](../05_boundary_system/README.md)。

**选型决策树（按需求选模式）**：见 [03_semantic_boundary_map §按需求反向查模式](../02_workflow_safe_complete_models/03_semantic_boundary_map.md#按需求反向查模式)（快速查找表 + 决策树精简）；本矩阵与彼处一一对应。

---

## 常见模式组合

| 组合 | 说明 |
| :--- | :--- |
| Composite + Visitor | 树遍历；[composite](02_structural/composite.md)、[visitor](03_behavioral/visitor.md) |
| Builder + Factory Method | 构建由工厂创建；[builder](01_creational/builder.md)、[factory_method](01_creational/factory_method.md) |
| Decorator + Strategy | 装饰器持有多态策略；[decorator](02_structural/decorator.md)、[strategy](03_behavioral/strategy.md) |
| Observer + Command | 观察者接收命令；[observer](03_behavioral/observer.md)、[command](03_behavioral/command.md) |
| Chain + Command | 链中节点封装为命令；[chain_of_responsibility](03_behavioral/chain_of_responsibility.md)、[command](03_behavioral/command.md) |

---

## 错误处理

| 模式 | Result vs panic |
| :--- | :--- |
| Builder | `build() -> Result<T, E>` 推荐；缺必填返回 Err |
| Factory | 可返回 `Option`/`Result`；match 穷尽避免 panic |
| Command | `execute() -> Result` 可传播错误 |
| 一般 | 不可恢复用 panic；可恢复用 Result |

---

## 测试建议

| 模式类型 | 测试要点 |
| :--- | :--- |
| 创建型 | 产品类型正确；所有权转移 |
| 结构型 | 委托链正确；无遗漏调用 |
| 行为型 | 状态转换；Observer 通知顺序；Chain 委托 |
| 跨线程 | 加 `#[test]` 多线程用例；MIRI 检测 |

---

## 何时不选用

| 模式 | 不适用场景 |
| :--- | :--- |
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
| :--- | :--- |
| Singleton | 全局可变未同步 → 数据竞争 |
| Observer | 共享可变无 Mutex → 数据竞争 |
| Composite | 循环引用 → 所有权无法表达 |
| Builder | build 前必填未设 → 运行时错误 |
| Memento | 恢复非法状态 → 不变式违反 |
| Iterator | 迭代中修改集合 → 借用冲突 |
| Prototype | Clone 浅拷贝共享 → 隐式耦合 |

---

## 反例→错误码映射（D1.4）

| 模式反例 | 典型错误码 | 典型信息 | 修复方向 |
| :--- | :--- | :--- | :--- |
| Singleton：Rc 跨线程 | E0378 | `Rc` cannot be sent between threads | 用 `Arc`；`T: Send + Sync` |
| Observer：双重可变借用 | E0499 | cannot borrow as mutable more than once | 用 channel 替代共享可变 |
| Composite：循环引用 | E0382 / 运行时 | borrow of moved value / 引用环 | 用 `Weak` 打破环；或重构 |
| Builder：使用已移动值 | E0382 | borrow of moved value | 链式返回 `self`；`build(self)` 消费 |
| Memento：非法状态恢复 | 运行时 | panic / 不变式违反 | 校验恢复状态；用 `Result` |
| Iterator：迭代中修改 | E0502 | cannot borrow (already borrowed as mutable) | 不用 `&mut`  during iteration |
| Prototype：浅拷贝共享可变 | E0499 / 运行时 | 数据竞争 / 隐式耦合 | 深拷贝 `Clone`；或显式共享 `Arc` |
| Flyweight：Rc 跨线程 | E0378 | `Rc` cannot be sent | 跨线程用 `Arc` |
| Mediator：跨线程传 Rc | E0378 | `Rc` cannot be sent | 用 `Arc<Mutex<T>>` 或 channel |

**引用**：[ERROR_CODE_MAPPING](../../../02_reference/ERROR_CODE_MAPPING.md)、[04_compositional_engineering 组合反例→错误映射](../../04_compositional_engineering/README.md#组合反例编译错误映射ce-t1t2t3)。
