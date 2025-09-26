# 🦀 Rust设计模式学习模块

**模块类型**: 学习模块  
**学习重点**: Rust设计模式、GoF模式、并发模式  
**适用对象**: Rust中级到高级开发者  

---

## 📋 模块概述

本模块专注于Rust语言中的设计模式实现，包括经典的GoF设计模式和Rust特有的并发、异步模式。通过学习本模块，您将掌握如何在Rust中应用各种设计模式来解决实际问题。

### 🎯 学习目标

- 理解经典设计模式在Rust中的实现
- 掌握Rust特有的并发和异步模式
- 学会在项目中应用适当的设计模式
- 理解模式之间的组合和协作

---

## 🚀 核心学习内容

### 创建型模式

- **单例模式**: 线程安全的单例实现
- **工厂模式**: 使用trait和泛型的工厂设计
- **建造者模式**: 链式调用和类型安全的构建器
- **原型模式**: Clone trait的使用和深拷贝

### 结构型模式

- **适配器模式**: trait适配和类型转换
- **装饰器模式**: 使用组合和trait扩展功能
- **代理模式**: 智能指针和代理实现
- **外观模式**: 简化复杂子系统接口

### 行为型模式

- **观察者模式**: 事件驱动和回调机制
- **策略模式**: trait对象和函数指针
- **命令模式**: 闭包和命令队列
- **状态模式**: 状态机和状态转换

### Rust特有模式

- **所有权模式**: 移动语义和借用模式
- **错误处理模式**: Result和Option的使用
- **并发模式**: 异步编程和消息传递
- **生命周期模式**: 生命周期参数和引用管理

---

## 📚 学习资源

### 基础示例

- **创建型模式示例**: 单例、工厂、建造者的基本实现
- **结构型模式示例**: 适配器、装饰器、代理的使用
- **行为型模式示例**: 观察者、策略、命令的实现
- **Rust模式示例**: 所有权、错误处理、并发模式

### 进阶示例

- **模式组合**: 多个模式的组合使用
- **性能优化**: 零成本抽象和编译时优化
- **异步模式**: async/await和Future的使用
- **错误处理**: 健壮的错误处理策略

---

## 🛠️ 实践练习

### 基础练习

1. **单例模式练习**: 实现线程安全的单例
2. **工厂模式练习**: 创建类型安全的工厂
3. **观察者模式练习**: 实现事件通知系统
4. **策略模式练习**: 实现可插拔的算法

### 进阶练习

1. **模式组合练习**: 组合多个模式解决复杂问题
2. **异步模式练习**: 实现异步的消息处理系统
3. **错误处理练习**: 设计健壮的错误处理机制
4. **性能优化练习**: 优化模式实现的性能

---

## 📖 学习路径

### 第1周：创建型模式

- 学习单例、工厂、建造者模式
- 理解Rust中的对象创建策略
- 练习使用trait和泛型

### 第2周：结构型模式

- 学习适配器、装饰器、代理模式
- 理解组合和继承的区别
- 练习使用智能指针

### 第3周：行为型模式

- 学习观察者、策略、命令模式
- 理解事件驱动编程
- 练习使用闭包和回调

### 第4周：Rust特有模式

- 学习所有权和借用模式
- 理解错误处理模式
- 练习异步和并发模式

---

## 🎯 实践项目

### 初级项目

- **简单工厂**: 实现一个简单的对象工厂
- **观察者系统**: 实现一个事件通知系统
- **策略排序**: 实现可插拔的排序算法

### 中级项目

- **命令模式**: 实现一个可撤销的操作系统
- **状态机**: 实现一个状态转换系统
- **代理模式**: 实现一个缓存代理

### 高级项目

- **异步消息系统**: 实现异步的消息处理系统
- **插件架构**: 实现可扩展的插件系统
- **分布式模式**: 实现分布式系统的设计模式

---

## 🔍 常见问题

### 设计模式问题

- **Q: 什么时候使用设计模式？**
- **A: 当遇到重复出现的设计问题时，使用相应的模式可以提高代码的可维护性和可扩展性。**

- **Q: Rust中的设计模式有什么特点？**
- **A: Rust中的设计模式需要考虑所有权、生命周期和类型安全，通常使用trait和泛型来实现。**

### 并发模式问题

- **Q: 如何在Rust中实现线程安全的单例？**
- **A: 可以使用OnceCell、LazyStatic或者std::sync::Once来实现。**

- **Q: 异步模式与同步模式有什么区别？**
- **A: 异步模式使用Future和async/await，可以处理大量并发连接，而同步模式使用线程和锁。**

### 性能问题

- **Q: 设计模式会影响性能吗？**
- **A: 在Rust中，零成本抽象使得很多设计模式在编译时被优化掉，对运行时性能影响很小。**

- **Q: 如何选择高性能的设计模式？**
- **A: 优先考虑零成本抽象、编译时多态和所有权转移，避免运行时开销。**

---

## 📊 学习进度

### 基础掌握 (第1-2周)

- [ ] 理解创建型和结构型模式
- [ ] 掌握trait和泛型的使用
- [ ] 学会使用智能指针
- [ ] 理解组合优于继承

### 进阶掌握 (第3-4周)

- [ ] 掌握行为型模式
- [ ] 理解事件驱动编程
- [ ] 学会使用闭包和回调
- [ ] 掌握Rust特有模式

### 高级应用 (第5-8周)

- [ ] 在复杂项目中使用设计模式
- [ ] 实现高性能的异步模式
- [ ] 掌握模式组合和协作
- [ ] 能够设计新的模式

---

## 🤝 社区支持

### 获取帮助

- **技术问题**: 通过GitHub Issues反馈
- **学习问题**: 通过社区讨论区提问
- **代码审查**: 请求代码审查和建议
- **项目讨论**: 参与项目相关讨论

### 贡献方式

- **代码贡献**: 提交改进的示例代码
- **文档贡献**: 改进文档和注释
- **测试贡献**: 添加测试用例
- **问题反馈**: 报告发现的问题

---

## 📞 联系信息

### 项目维护

- **维护者**: Rust学习社区
- **更新频率**: 跟随学习进度
- **质量保证**: 持续改进中

### 学习支持

- **学习指导**: 提供学习路径指导
- **问题解答**: 解答学习过程中的问题
- **资源推荐**: 推荐相关学习资源
- **经验分享**: 分享学习经验

---

**模块状态**: 🔄 持续开发中  
**最后更新**: 2025年9月25日  
**适用版本**: Rust 1.90，Edition 2024  

---

*本模块专注于Rust设计模式的学习，提供系统性的学习路径和实践示例。如有任何问题或建议，欢迎反馈。*

---

## 🆕 Rust 1.90 / Edition 2024 采用情况

- let-else：
  - `behavioral/chain_of_responsibility/define.rs` 的 `handle` 方法使用 `let Some(..) else { .. }` 做早退分支。
- return-position impl Trait：
  - `structural/flyweight/define.rs` 的 `OptimizedFlyweightFactory::iter_ids` 返回 `impl Iterator<Item = u32>`。
- RPITIT（trait 方法返回 impl Trait）：
  - `src/rust_190_features.rs::rpitit_demo::TextSource::words` 展示在 trait 方法中返回 `impl Iterator` 的用法。
- dyn 上行转型（dyn upcasting）：
  - `src/rust_190_features.rs::dyn_upcasting_demo` 展示 `&mut dyn Sub` 到 `&mut dyn Super` 的隐式上转型调用场景。
- 其他：
  - 错误处理工具 `error_handling.rs::utils::validate_input` 使用 `let-else` 提升可读性。
  - 全局初始化从 `lazy_static` 迁移为 `std::sync::OnceLock`（见 `error_handling.rs::global_error_monitor`）。

### 示例入口与用法

- 原生 async fn in trait：
  - 模块：`concurrency/asynchronous/native_async_trait`
  - 运行思路：该示例带有单元测试（纯 Rust 栈内 `block_on`），可通过 `cargo test -p c09_design_pattern native_async_trait` 触发。
  - 可选 Tokio 门控：启用 `--features tokio-bench` 可运行基于 Tokio 的延迟处理测试。
- 1.90 汇总示例：
  - 模块：`rust_190_features`
  - API：`highlights::terminate_with_panic() -> !`、`highlights::if_let_chain(..)`、`rpitit_demo::TextSource::words(..)`、`dyn_upcasting_demo`
  - 用途：演示 never 类型与 if-let 链式匹配；可在任意示例/测试中直接调用。
- GATs 借用视图：
  - 模块：`behavioral/observer/define.rs`
  - 类型：`ObserverRef`、`BorrowingObserver`、`BorrowingSubjectString`
  - 要点：通知时借用数据，避免多次克隆，用以展示 GATs 的借用返回。
- 并行流水线（返回位 impl Trait）：
  - 模块：`parallel/pipeline/define.rs`
  - API：`make_pipeline_iter(&[i32]) -> impl Iterator<Item=i32> + Send`
  - 要点：组合 map/filter/map，返回位 impl Trait + Send。

### 运行 examples

```bash
# async trait 示例
cargo run -p c09_design_pattern --example async_trait_demo

# 异步事件总线（背压/取消/超时近似/批处理）
cargo run -p c09_design_pattern --example event_bus_demo

# GATs 观察者示例
cargo run -p c09_design_pattern --example gats_observer_demo

# 流水线迭代器示例
cargo run -p c09_design_pattern --example pipeline_iter_demo

# 启用 Tokio 门控并运行测试
cargo test -p c09_design_pattern --features tokio-bench
```

### Benchmark（Criterion）

```bash
# 运行全部基准
cargo bench -p c09_design_pattern

# 仅运行某组或某项（支持正则）
cargo bench -p c09_design_pattern -- flyweight
cargo bench -p c09_design_pattern -- proxy_request

# 保存当前结果为基线
cargo bench -p c09_design_pattern -- --save-baseline main

# 与已保存的基线对比
cargo bench -p c09_design_pattern -- --baseline main
```

### 新增示例与基准索引

- 示例：
  - `event_bus_demo`: 异步事件总线（async trait + GATs）
  - `async_trait_demo`: 原生 async trait 最小示例
  - `gats_observer_demo`: GATs 借用观察者
  - `pipeline_iter_demo`: 返回位 impl Trait 的流水线

#### 异步事件总线用法提示

- 背压策略：`DropOldest`（保留最新一半示例）、`Block`（逐条处理）、`Batch(n)`（按批处理）
- 取消/超时近似：`run_until_cancel(..., true)`、`run_with_timeout_like(events, max_events)`

示例调用（详见 `examples/event_bus_demo.rs`）：

```rust
let bus = EventBusString::new(StringEventHandler);
let events: Vec<String> = (0..5).map(|i| format!("demo-{}", i)).collect();
block_on(bus.run_with_backpressure(&events));
block_on(bus.run_until_cancel(&events, true));
block_on(bus.run_with_strategy(&events, BackpressureStrategy::Block));
block_on(bus.run_with_strategy(&events, BackpressureStrategy::DropOldest));
block_on(bus.run_with_strategy(&events, BackpressureStrategy::Batch(2)));
block_on(bus.run_with_timeout_like(&events, 3));
```

- 基准：
  - `benches/async_gats_benches.rs`: 异步事件总线与 GATs 观察者基准

后续规划：在不破坏稳定 API 的前提下，逐步引入原生 `async fn` in trait、GATs 等更高级特性到并发与异步子模块（视适用性与依赖生态兼容性推进）。
