# 3.2 异步编程语义索引

**文档编号**: RFTS-03-API  
**版本**: 1.0  
**最后更新**: 2025-01-27  
**状态**: 索引文档

---

## 文档结构体体体

### 核心语义文档

1. **[Future语义模型](./01_future_semantics.md)** - Future的数学模型和状态机语义
2. **[async/await语义](./02_async_await_semantics.md)** - async/await语法糖的深度解析
3. **[执行器语义](./03_executor_semantics.md)** - Future的执行环境和调度
4. **[异步运行时语义](./04_async_runtime_semantics.md)** - 运行时系统架构

### 理论创新

- **异步状态机理论**: async函数的状态机转换语义
- **Pin语义模型**: 自引用结构体体体的内存安全保证
- **Waker机制**: 异步唤醒的理论基础
- **运行时调度**: 工作窃取和优先级调度算法

### 跨层引用

- **[并发模型语义](../01_concurrency_model_semantics)** - 与线程模型的关系
- **[同步原语语义](../04_synchronization_semantics)** - 异步通信机制
- **[错误处理语义](../../02_control_semantics/04_error_handling_semantics)** - 错误处理整合

---

*索引状态: 完成*  
*版本: 1.0*
