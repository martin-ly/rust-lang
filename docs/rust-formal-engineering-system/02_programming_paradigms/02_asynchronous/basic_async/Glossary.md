> ⚠️ **待完善** - 此文件为占位符，内容待完善
> **最后更新**: 2025-10-31
> **预期完成**: 待定

---

﻿# Rust 异步编程术语表（Glossary）

**模块编号**: 06-Glossary  
**主题**: async/await核心术语与工程释义  
**最后更新**: 2024-12-30  
**维护者**: Rust形式化团队

---

| 术语         | 英文/缩写      | 定义/工程意义                                                                 | 交叉引用 |
|--------------|---------------|------------------------------------------------------------------------------|----------|
| 异步/await   | async/await    | Rust用于编写异步代码的语法，async定义异步函数/块，await等待Future完成         | 01_formal_async_system.md |
| Future       | Future         | 表示可能尚未完成的异步计算，核心trait，poll驱动状态移动                      | 01_formal_async_system.md, 04_future_execution.md |
| 状态机       | State Machine  | async/await编译为有限状态机，管理暂停/恢复点                                 | 03_state_machine_theory.md |
| Pin          | Pin            | 智能指针，保证对象在内存中不被移动，防止自引用结构体体体悬垂指针                    | 01_formal_async_system.md |
| Unpin        | Unpin          | 自动trait，标记可安全移动的类型，大多数类型默认Unpin                         | 01_formal_async_system.md |
| Waker        | Waker          | 唤醒器，通知执行器某Future已准备好可继续poll                                  | 04_future_execution.md |
| Context      | Context        | poll方法参数，封装Waker与任务上下文                                          | 04_future_execution.md |
| Poll         | Poll           | poll方法返回值，Ready表示完成，Pending表示等待外部事件                        | 04_future_execution.md |
| 执行器       | Executor       | 驱动Future的核心组件，负责任务调度与poll循环                                 | 05_runtime_system.md |
| 运行时       | Runtime        | 提供执行器、I/O事件、定时器、线程池等异步环境                                | 05_runtime_system.md |
| Stream       | Stream         | 异步迭代器trait，表示异步产生的值序列                                        | 08_concurrency_patterns.md |
| 背压         | Backpressure   | 控制异步流/队列数据速率，防止内存膨胀                                        | 08_concurrency_patterns.md |
| Actor模型    | Actor Model    | 并发模式，每个Actor独立任务，消息异步交互                                    | 08_concurrency_patterns.md |
| Send/Sync    | Send/Sync      | trait，类型系统静态保证跨线程安全                                            | 08_concurrency_patterns.md |
| async-trait  | async-trait    | 宏库，支持trait中定义async fn，自动转换为返回Future的普通函数                 | FAQ.md |
| block_on     | block_on       | 同步阻塞等待异步Future完成，常用于main或测试                                 | FAQ.md |
| spawn_blocking | spawn_blocking | 在异步任务中运行阻塞代码，防止阻塞执行器线程                                 | FAQ.md |
| zero-copy    | Zero-Copy      | 性能优化技术，避免不必要的数据复制，直接在缓冲区操作                          | 07_performance_optimization.md |
| 工作窃取     | Work Stealing  | 多线程任务调度算法，空闲线程可“窃取”他人任务                                 | 05_runtime_system.md |
| 取消/超时    | Cancellation/Timeout | 通过select!、timeout等机制优雅终止/限制异步任务                             | 06_error_handling.md |
| RAII         | RAII           | 资源获取即初始化，结合Drop确保异常/取消下资源安全释放                        | 06_error_handling.md |
| 生态兼容     | Ecosystem Compatibility | 异步库/运行时间的互操作与迁移策略                                    | 09_ecosystem_integration.md |

---

> 本术语表系统梳理Rust异步编程核心概念，便于理论学习与工程查阅，后续将递归细化各专题。

"

---
