# 🎯 Rust 学习检查清单 (Learning Checklist)

> **文档定位**: 系统化学习进度追踪工具  
> **使用方式**: 逐项完成学习任务，标记完成状态  
> **相关文档**: [README](./README.md) | [学习路径](./README.md#学习路径推荐)

**最后更新**: 2025-10-19  
**适用版本**: Rust 1.90+

---

## 📋 如何使用本清单

1. **选择学习路径**: 根据你的背景选择合适的路径
2. **逐项学习**: 按顺序完成各个模块的学习任务
3. **标记完成**: 完成后将 `- [ ]` 改为 `- [x]`
4. **验证理解**: 通过示例和测试验证掌握程度
5. **记录笔记**: 在空白处记录重点和疑问

---

## 🌱 第一阶段：Rust 基础 (2-4周)

### C01 - 所有权与借用 (Ownership & Borrowing)

**学习目标**: 理解 Rust 最核心的特性

#### 基础概念

- [ ] 理解所有权三原则
- [ ] 掌握 Move 语义 vs Copy 语义
- [ ] 理解借用规则（不可变借用 & 可变借用）
- [ ] 掌握引用的使用（`&T` 和 `&mut T`）
- [ ] 理解作用域和 Drop

#### 生命周期

- [ ] 理解生命周期的概念
- [ ] 掌握生命周期标注语法 (`'a`)
- [ ] 理解生命周期省略规则
- [ ] 掌握 `'static` 生命周期
- [ ] 理解结构体中的生命周期

#### 进阶内容

- [ ] 理解智能指针 (`Box<T>`, `Rc<T>`, `Arc<T>`)
- [ ] 掌握内部可变性 (`Cell<T>`, `RefCell<T>`)
- [ ] 理解 Deref trait
- [ ] 防止悬垂指针
- [ ] 理解 RAII 模式

#### 实践任务

- [ ] 运行所有示例代码
- [ ] 完成所有测试
- [ ] 阅读 FAQ 并理解常见问题
- [ ] 能够用所有权系统设计简单程序

**学习资源**:

- 📖 [主索引](./crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md)
- ❓ [FAQ](./crates/c01_ownership_borrow_scope/docs/FAQ.md)
- 📚 [术语表](./crates/c01_ownership_borrow_scope/docs/Glossary.md)

---

### C02 - 类型系统 (Type System)

**学习目标**: 掌握 Rust 强大的类型系统

#### 基础类型

- [ ] 掌握基本类型（整数、浮点、布尔、字符）
- [ ] 理解复合类型（元组、数组）
- [ ] 理解字符串类型 (`String` vs `&str`)
- [ ] 掌握类型推导和类型标注

#### 泛型

- [ ] 理解泛型的概念和使用
- [ ] 掌握泛型函数
- [ ] 掌握泛型结构体和枚举
- [ ] 理解泛型的单态化
- [ ] 掌握生命周期与泛型的结合

#### Trait

- [ ] 理解 Trait 的概念
- [ ] 掌握 Trait 定义和实现
- [ ] 理解 Trait 作为参数 (`impl Trait`)
- [ ] 掌握 Trait 对象 (`dyn Trait`)
- [ ] 理解关联类型 vs 泛型参数
- [ ] 掌握条件 Trait 实现
- [ ] 理解孤儿规则

#### 高级类型

- [ ] 理解 Newtype 模式
- [ ] 掌握 Never 类型 (`!`)
- [ ] 理解 Pin 和 Unpin
- [ ] 掌握 PhantomData
- [ ] 理解零大小类型 (ZST)
- [ ] 掌握 Deref 强制转换

#### 实践任务1

- [ ] 运行所有示例代码
- [ ] 完成所有测试
- [ ] 实现自定义 Trait
- [ ] 使用泛型重构重复代码

**学习资源**:

- 📖 [主索引](./crates/c02_type_system/docs/00_MASTER_INDEX.md)
- ❓ [FAQ](./crates/c02_type_system/docs/FAQ.md)
- 📚 [术语表](./crates/c02_type_system/docs/Glossary.md)

---

### C03 - 控制流与函数 (Control Flow & Functions)

**学习目标**: 掌握控制流和函数式编程

#### 控制流基础

- [ ] 掌握 if/else 表达式
- [ ] 理解 match 表达式和模式匹配
- [ ] 掌握 loop/while/for 循环
- [ ] 理解 if let 和 while let
- [ ] 掌握 let-else 模式 (Rust 1.65+)
- [ ] 理解标签块和带值的 break

#### 函数

- [ ] 掌握函数定义和调用
- [ ] 理解参数和返回值
- [ ] 掌握表达式作为返回值
- [ ] 理解发散函数 (`!` 类型)

#### 闭包

- [ ] 理解闭包的概念和语法
- [ ] 掌握闭包捕获环境的方式
- [ ] 理解 Fn/FnMut/FnOnce trait
- [ ] 掌握高阶函数
- [ ] 理解 move 闭包
- [ ] 掌握返回闭包的方法

#### 错误处理

- [ ] 理解 Result 和 Option
- [ ] 掌握 ? 运算符
- [ ] 理解 panic! vs Result
- [ ] 掌握错误传播
- [ ] 理解自定义错误类型

#### 实践任务2

- [ ] 运行所有示例代码
- [ ] 完成所有测试
- [ ] 使用闭包重构代码
- [ ] 实现完整的错误处理链

**学习资源**:

- 📖 [主索引](./crates/c03_control_fn/docs/00_MASTER_INDEX.md)
- ❓ [FAQ](./crates/c03_control_fn/docs/FAQ.md)
- 📚 [术语表](./crates/c03_control_fn/docs/Glossary.md)

---

## 🚀 第二阶段：并发与异步 (4-8周)

### C04 - 泛型编程 (Generic Programming)

**学习目标**: 深入理解泛型和高级 Trait

#### 高级泛型

- [ ] 掌握泛型约束 (Trait Bounds)
- [ ] 理解 where 子句
- [ ] 掌握关联类型
- [ ] 理解 GATs (Generic Associated Types)
- [ ] 掌握 RPITIT (Return Position Impl Trait In Traits)

#### 实践任务3

- [ ] 设计通用数据结构
- [ ] 实现自定义迭代器
- [ ] 使用 GATs 优化代码

**学习资源**:

- 📖 [主索引](./crates/c04_generic/docs/00_MASTER_INDEX.md)
- ❓ [FAQ](./crates/c04_generic/docs/FAQ.md)
- 📚 [术语表](./crates/c04_generic/docs/Glossary.md)

---

### C05 - 线程与并发 (Threads & Concurrency)

**学习目标**: 掌握多线程编程

#### 线程基础

- [ ] 理解线程的概念
- [ ] 掌握线程创建和 join
- [ ] 理解消息传递 (Channel)
- [ ] 掌握共享状态并发 (Mutex/RwLock)
- [ ] 理解原子类型 (Atomic)

#### 并发模式

- [ ] 理解数据竞争和防护
- [ ] 掌握线程安全 (Send/Sync)
- [ ] 理解 Arc 和 Mutex 组合
- [ ] 掌握 Barrier 和 Condvar
- [ ] 理解线程池

#### 实践任务4

- [ ] 实现多线程计算
- [ ] 使用 Channel 通信
- [ ] 实现生产者-消费者模式

**学习资源**:

- 📖 [主索引](./crates/c05_threads/docs/00_MASTER_INDEX.md)
- ❓ [FAQ](./crates/c05_threads/docs/FAQ.md)
- 📚 [术语表](./crates/c05_threads/docs/Glossary.md)

---

### C06 - 异步编程 (Async Programming)

**学习目标**: 掌握异步编程模型

#### 异步基础

- [ ] 理解 async/await 语法
- [ ] 掌握 Future trait
- [ ] 理解 Runtime (tokio/async-std)
- [ ] 掌握异步函数和异步块
- [ ] 理解 Pin 和自引用结构

#### 异步模式

- [ ] 掌握异步 I/O
- [ ] 理解异步流 (Stream)
- [ ] 掌握异步任务生成
- [ ] 理解 select! 宏
- [ ] 掌握异步取消

#### 实践任务5

- [ ] 实现异步 HTTP 客户端
- [ ] 使用 tokio 构建服务器
- [ ] 实现异步文件操作

**学习资源**:

- 📖 [主索引](./crates/c06_async/docs/00_MASTER_INDEX.md)
- ❓ [FAQ](./crates/c06_async/docs/FAQ.md)
- 📚 [术语表](./crates/c06_async/docs/Glossary.md)

---

## ⚡ 第三阶段：系统与应用 (8-12周)

### C07 - 进程管理 (Process Management)

**学习目标**: 掌握系统编程

- [ ] 理解进程和线程的区别
- [ ] 掌握进程创建和管理
- [ ] 理解 IPC (进程间通信)
- [ ] 掌握信号处理
- [ ] 理解僵尸进程和孤儿进程

**学习资源**:

- 📖 [主索引](./crates/c07_process/docs/00_MASTER_INDEX.md)
- ❓ [FAQ](./crates/c07_process/docs/FAQ.md)
- 📚 [术语表](./crates/c07_process/docs/Glossary.md)

---

### C08 - 算法与数据结构 (Algorithms & Data Structures)

**学习目标**: 巩固基础知识

- [ ] 掌握常见数据结构实现
- [ ] 理解算法复杂度分析
- [ ] 实现经典算法
- [ ] 掌握 Rust 特定优化技巧

**学习资源**:

- 📖 [主索引](./crates/c08_algorithms/docs/00_MASTER_INDEX.md)
- ❓ [FAQ](./crates/c08_algorithms/docs/FAQ.md)
- 📚 [术语表](./crates/c08_algorithms/docs/Glossary.md)

---

### C09 - 设计模式 (Design Patterns)

**学习目标**: 提升架构设计能力

#### GoF 模式

- [ ] 掌握创建型模式 (5种)
- [ ] 掌握结构型模式 (7种)
- [ ] 掌握行为型模式 (11种)

#### Rust 特定模式

- [ ] 理解 Newtype 模式
- [ ] 掌握类型状态模式
- [ ] 理解 RAII 守卫
- [ ] 掌握建造者模式

#### 并发模式6

- [ ] 理解 Actor 模式
- [ ] 掌握 Reactor 模式
- [ ] 理解 CSP (通信顺序进程)

**学习资源**:

- 📖 [主索引](./crates/c09_design_pattern/docs/00_MASTER_INDEX.md)
- ❓ [FAQ](./crates/c09_design_pattern/docs/FAQ.md)
- 📚 [术语表](./crates/c09_design_pattern/docs/Glossary.md)

---

### C10 - 网络编程 (Network Programming)

**学习目标**: 掌握网络应用开发

#### 网络协议

- [ ] 掌握 TCP/UDP 编程
- [ ] 理解 HTTP 协议
- [ ] 掌握 WebSocket
- [ ] 理解 DNS 解析

#### 网络应用

- [ ] 实现 HTTP 客户端
- [ ] 实现 HTTP 服务器
- [ ] 实现 WebSocket 通信
- [ ] 掌握网络安全基础

**学习资源**:

- 📖 [主索引](./crates/c10_networks/docs/00_MASTER_INDEX.md)
- ❓ [FAQ](./crates/c10_networks/docs/FAQ.md)
- 📚 [术语表](./crates/c10_networks/docs/Glossary.md)

---

## 🏆 第四阶段：生产实践 (持续学习)

### C11 - 中间件集成 (Middleware Integration)

**学习目标**: 掌握常见中间件使用

#### 数据库

- [ ] 掌握 Redis 使用
- [ ] 掌握 Postgres 使用
- [ ] 掌握 MySQL 使用
- [ ] 理解 SQLite 使用

#### 消息队列

- [ ] 掌握 NATS 使用
- [ ] 理解 Kafka 使用
- [ ] 掌握 MQTT 使用

**学习资源**:

- 📖 [主索引](./crates/c11_middlewares/docs/00_MASTER_INDEX.md)
- ❓ [FAQ](./crates/c11_middlewares/docs/FAQ.md)
- 📚 [术语表](./crates/c11_middlewares/docs/Glossary.md)

---

### C12 - 模型与架构 (Modeling & Architecture)

**学习目标**: 提升架构设计能力

- [ ] 理解领域建模
- [ ] 掌握架构模式
- [ ] 理解形式化方法
- [ ] 掌握性能模型

**学习资源**:

- 📖 [主索引](./crates/c12_model/docs/00_MASTER_INDEX.md)
- ❓ [FAQ](./crates/c12_model/docs/FAQ.md)
- 📚 [术语表](./crates/c12_model/docs/Glossary.md)

---

### C13 - 可靠性框架 (Reliability Framework)

**学习目标**: 构建可靠系统

#### 容错机制

- [ ] 理解断路器 (Circuit Breaker)
- [ ] 掌握限流 (Rate Limiter)
- [ ] 理解重试策略
- [ ] 掌握超时控制

#### 分布式系统

- [ ] 理解 Raft 共识算法
- [ ] 掌握分布式事务
- [ ] 理解一致性哈希
- [ ] 掌握服务发现

#### 可观测性

- [ ] 掌握日志记录 (tracing)
- [ ] 理解指标监控 (metrics)
- [ ] 掌握分布式追踪

**学习资源**:

- 📖 [主索引](./crates/c13_reliability/docs/00_MASTER_INDEX.md)
- ❓ [FAQ](./crates/c13_reliability/docs/FAQ.md)
- 📚 [术语表](./crates/c13_reliability/docs/Glossary.md)

---

## 🎓 进阶学习

### 实践项目

- [ ] 完成一个完整的 CLI 工具
- [ ] 实现一个 HTTP 服务器
- [ ] 构建一个异步任务系统
- [ ] 开发一个分布式应用

### 贡献项目

- [ ] 阅读 [贡献指南](./CONTRIBUTING.md)
- [ ] 修复一个 Bug
- [ ] 改进文档
- [ ] 添加新示例
- [ ] 提出功能建议

### 持续学习

- [ ] 关注 Rust 版本更新
- [ ] 阅读 Rust RFC
- [ ] 参与社区讨论
- [ ] 分享学习经验
- [ ] 帮助其他学习者

---

## 📊 学习统计

### 我的进度

- **基础阶段**: __ / 3 模块完成
- **并发阶段**: __ / 3 模块完成
- **系统阶段**: __ / 4 模块完成
- **实践阶段**: __ / 3 模块完成

### 时间记录

- **开始日期**: ____-**-**
- **当前进度**: __%
- **预计完成**: ____-**-**

### 学习笔记

```text
记录你的学习心得、重点内容和遇到的问题
```

---

## 🎯 学习建议

### 有效学习策略

1. **循序渐进**: 不要跳过基础模块
2. **动手实践**: 运行所有示例代码
3. **测试验证**: 完成所有测试用例
4. **记录笔记**: 记录重点和疑问
5. **定期复习**: 定期回顾已学内容
6. **参与讨论**: 加入社区交流
7. **实践项目**: 通过项目巩固知识

### 遇到困难时

1. **查看 FAQ**: 每个模块都有常见问题解答
2. **查看术语表**: 快速查找概念定义
3. **搜索 Issues**: 看是否有类似问题
4. **创建 Issue**: 提出你的问题
5. **参与讨论**: 在 Discussions 中交流

---

## 🎉 完成里程碑

### 🌱 基础达成

- 完成 C01-C03 所有模块
- 能够独立编写简单 Rust 程序
- 理解所有权和类型系统

### 🚀 进阶达成

- 完成 C04-C06 所有模块
- 能够编写并发和异步程序
- 掌握高级 Rust 特性

### ⚡ 高级达成

- 完成 C07-C10 所有模块
- 能够开发系统级应用
- 掌握网络编程

### 🏆 专家达成

- 完成 C11-C13 所有模块
- 能够构建生产级系统
- 掌握架构设计和可靠性

---

**开始你的学习之旅吧！** 🚀

从 [C01 所有权与借用](./crates/c01_ownership_borrow_scope/) 开始，逐步完成所有模块的学习！

**最后更新**: 2025-10-19  
**维护团队**: Rust 学习社区  
**版本**: v1.0
