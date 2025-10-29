# Rust 系统化学习

[前言](./README.md)

---

# 第一部分：Rust 基础

- [C01: 所有权与借用](./c01_ownership/README.md)
  - [项目概览](./c01_ownership/01_overview.md)
  - [主索引导航](./c01_ownership/02_master_index.md)
  - [FAQ](./c01_ownership/03_faq.md)
  - [术语表](./c01_ownership/04_glossary.md)
  - [快速开始](./c01_ownership/05_quick_start.md)
  - [Tier 1: 基础概念](./c01_ownership/tier1/README.md)
    - [所有权基础](./c01_ownership/tier1/01_ownership_basics.md)
    - [借用与引用](./c01_ownership/tier1/02_borrowing.md)
    - [生命周期](./c01_ownership/tier1/03_lifetimes.md)
  - [Tier 2: 实践指南](./c01_ownership/tier2/README.md)
  - [Tier 3: 参考文档](./c01_ownership/tier3/README.md)
  - [Tier 4: 高级主题](./c01_ownership/tier4/README.md)

- [C02: 类型系统](./c02_type_system/README.md)
  - [项目概览](./c02_type_system/01_overview.md)
  - [主索引导航](./c02_type_system/02_master_index.md)
  - [FAQ](./c02_type_system/03_faq.md)
  - [术语表](./c02_type_system/04_glossary.md)
  - [Tier 1: 基础概念](./c02_type_system/tier1/README.md)
    - [类型基础](./c02_type_system/tier1/01_type_basics.md)
    - [Trait 系统](./c02_type_system/tier1/02_traits.md)
    - [泛型](./c02_type_system/tier1/03_generics.md)
  - [Tier 2: 实践指南](./c02_type_system/tier2/README.md)
  - [Tier 3: 参考文档](./c02_type_system/tier3/README.md)
  - [Tier 4: 高级主题](./c02_type_system/tier4/README.md)

- [C03: 控制流与函数](./c03_control_fn/README.md)
  - [项目概览](./c03_control_fn/01_overview.md)
  - [主索引导航](./c03_control_fn/02_master_index.md)
  - [Tier 1: 基础概念](./c03_control_fn/tier1/README.md)
    - [条件控制](./c03_control_fn/tier1/01_conditionals.md)
    - [模式匹配](./c03_control_fn/tier1/02_pattern_matching.md)
    - [循环](./c03_control_fn/tier1/03_loops.md)
    - [函数](./c03_control_fn/tier1/04_functions.md)
    - [闭包](./c03_control_fn/tier1/05_closures.md)

---

# 第二部分：并发与异步

- [C04: 泛型编程](./c04_generic/README.md)
  - [项目概览](./c04_generic/01_overview.md)
  - [主索引导航](./c04_generic/02_master_index.md)
  - [Tier 1: 高级泛型](./c04_generic/tier1/README.md)
    - [关联类型](./c04_generic/tier1/01_associated_types.md)
    - [高阶 Trait](./c04_generic/tier1/02_higher_ranked_traits.md)
    - [GATs](./c04_generic/tier1/03_gats.md)

- [C05: 线程与并发](./c05_threads/README.md)
  - [项目概览](./c05_threads/01_overview.md)
  - [主索引导航](./c05_threads/02_master_index.md)
  - [Tier 1: 并发基础](./c05_threads/tier1/README.md)
    - [线程](./c05_threads/tier1/01_threads.md)
    - [共享状态](./c05_threads/tier1/02_shared_state.md)
    - [消息传递](./c05_threads/tier1/03_message_passing.md)
    - [原子操作](./c05_threads/tier1/04_atomics.md)

- [C06: 异步编程](./c06_async/README.md)
  - [项目概览](./c06_async/01_overview.md)
  - [主索引导航](./c06_async/02_master_index.md)
  - [Tier 1: 异步基础](./c06_async/tier1/README.md)
    - [async/await](./c06_async/tier1/01_async_await.md)
    - [Future](./c06_async/tier1/02_futures.md)
    - [Runtime](./c06_async/tier1/03_runtime.md)
    - [异步生态](./c06_async/tier1/04_ecosystem.md)

---

# 第三部分：系统与应用

- [C07: 进程管理](./c07_process/README.md)
  - [项目概览](./c07_process/01_overview.md)
  - [主索引导航](./c07_process/02_master_index.md)
  - [Tier 1: 进程基础](./c07_process/tier1/README.md)
    - [进程创建](./c07_process/tier1/01_process_creation.md)
    - [进程间通信](./c07_process/tier1/02_ipc.md)
    - [信号处理](./c07_process/tier1/03_signals.md)

- [C08: 算法与数据结构](./c08_algorithms/README.md)
  - [项目概览](./c08_algorithms/01_overview.md)
  - [主索引导航](./c08_algorithms/02_master_index.md)
  - [Tier 1: 基础算法](./c08_algorithms/tier1/README.md)
    - [排序算法](./c08_algorithms/tier1/01_sorting.md)
    - [搜索算法](./c08_algorithms/tier1/02_searching.md)
    - [图算法](./c08_algorithms/tier1/03_graphs.md)
    - [动态规划](./c08_algorithms/tier1/04_dynamic_programming.md)

- [C09: 设计模式](./c09_design_pattern/README.md)
  - [项目概览](./c09_design_pattern/01_overview.md)
  - [主索引导航](./c09_design_pattern/02_master_index.md)
  - [Tier 1: 经典模式](./c09_design_pattern/tier1/README.md)
    - [创建型模式](./c09_design_pattern/tier1/01_creational.md)
    - [结构型模式](./c09_design_pattern/tier1/02_structural.md)
    - [行为型模式](./c09_design_pattern/tier1/03_behavioral.md)
  - [Tier 2: Rust 特定模式](./c09_design_pattern/tier2/README.md)

- [C10: 网络编程](./c10_networks/README.md)
  - [项目概览](./c10_networks/01_overview.md)
  - [主索引导航](./c10_networks/02_master_index.md)
  - [Tier 1: 网络基础](./c10_networks/tier1/README.md)
    - [TCP/UDP](./c10_networks/tier1/01_tcp_udp.md)
    - [HTTP](./c10_networks/tier1/02_http.md)
    - [WebSocket](./c10_networks/tier1/03_websocket.md)
  - [Tier 2: Web 框架](./c10_networks/tier2/README.md)
    - [Axum](./c10_networks/tier2/01_axum.md)
    - [Actix-web](./c10_networks/tier2/02_actix.md)

---

# 第四部分：生产实践

- [C11: 宏系统](./c11_macro/README.md)
  - [项目概览](./c11_macro/01_overview.md)
  - [主索引导航](./c11_macro/02_master_index.md)
  - [FAQ](./c11_macro/03_faq.md)
  - [术语表](./c11_macro/04_glossary.md)
  - [Tier 1: 声明宏](./c11_macro/tier1/README.md)
    - [宏基础](./c11_macro/tier1/01_macro_basics.md)
    - [模式匹配](./c11_macro/tier1/02_pattern_matching.md)
    - [重复匹配](./c11_macro/tier1/03_repetition.md)
  - [Tier 2: 过程宏](./c11_macro/tier2/README.md)
    - [派生宏](./c11_macro/tier2/01_derive_macros.md)
    - [属性宏](./c11_macro/tier2/02_attribute_macros.md)
    - [函数式宏](./c11_macro/tier2/03_function_like_macros.md)
  - [Tier 3: 最佳实践](./c11_macro/tier3/README.md)

---

# 附录

- [学习路径指南](./appendix/learning_paths.md)
  - [零基础入门路径](./appendix/learning_paths.md#零基础入门)
  - [有经验开发者路径](./appendix/learning_paths.md#有经验开发者)
  - [性能工程师专项](./appendix/learning_paths.md#性能工程师)
  - [安全工程师专项](./appendix/learning_paths.md#安全工程师)

- [跨模块学习资源](./appendix/cross_module.md)
  - [统一知识图谱](./appendix/cross_module.md#知识图谱)
  - [跨模块实战项目](./appendix/cross_module.md#实战项目)
  - [学习进度追踪](./appendix/cross_module.md#进度追踪)

- [参考资料](./appendix/references.md)
  - [官方资源](./appendix/references.md#官方资源)
  - [社区资源](./appendix/references.md#社区资源)
  - [工具链](./appendix/references.md#工具链)

- [术语总表](./appendix/glossary.md)
- [贡献指南](./appendix/contributing.md)
- [更新日志](./appendix/changelog.md)
