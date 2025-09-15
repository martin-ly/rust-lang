# 设计模式（Design Patterns）索引

## 目的

- 组织经典设计模式在 Rust 环境下的实现与取舍。
- 强调“以类型与所有权为中心”的 Rust 化改造思路。
- 提供示例索引与跨模块导航。

## 分类总览

- 创建型：构建者、工厂方法、抽象工厂、原型、单例（受限）
- 结构型：适配器、装饰器、外观、桥接、组合、代理、享元
- 行为型：策略、观察者、命令、职责链、状态、访问者、解释器、备忘录、迭代器、中介者、模板方法

## Rust 化要点

- 所有权与借用：以 `&`/`&mut`/`Arc`/`Rc` 表达共享与可变性边界。
- 枚举与模式匹配：常以 `enum` 取代层层继承与 RTTI。
- 零成本抽象：`trait` + 泛型 单态化，避免虚调用开销（按需 `dyn`）。
- 不可变优先：通过不可变数据 + 构建者/命令式变更实现可维护性。
- 线程安全：`Send`/`Sync` 标记、`Mutex`/`RwLock` 与无锁结构的权衡。

## 仓库内参考

- 设计模式示例：[crates/c09_design_pattern](../../crates/c09_design_pattern/)
- 控制与函数：[crates/c03_control_fn](../../crates/c03_control_fn/)
- 泛型与 trait：[crates/c04_generic](../../crates/c04_generic/)

## 相关索引

- 类型系统（ADT/状态机建模）：[../01_theoretical_foundations/01_type_system/00_index.md](../01_theoretical_foundations/01_type_system/00_index.md)
- 编程范式（同步/异步）：[../02_programming_paradigms/01_synchronous/00_index.md](../02_programming_paradigms/01_synchronous/00_index.md) ・ [../02_programming_paradigms/02_async/00_index.md](../02_programming_paradigms/02_async/00_index.md)
- 质量保障（模式实现的测试与验证）：[../10_quality_assurance/00_index.md](../10_quality_assurance/00_index.md)

## 推荐阅读路径

1) 先读 Rust 化要点与语言特性支撑。
2) 从创建型→结构型→行为型逐步浏览，实现由浅入深。
3) 关注每个示例中的“类型边界”“错误处理”“可变性隔离”。

## 导航

- 返回根：[`rust-formal-engineering-system/README.md`](../README.md)
- 编程范式：[`02_programming_paradigms/`](../02_programming_paradigms/)
- 质量保障：[`10_quality_assurance/`](../10_quality_assurance/)
- 返回项目根：[`../README.md`](../README.md)
