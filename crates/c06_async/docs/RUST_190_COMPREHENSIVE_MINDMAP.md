# 🗺️ Rust 1.90 异步编程 - 综合思维导图

> **版本**: Rust 1.90 Edition 2024  
> **创建日期**: 2025-10-20  
> **适用人群**: 中级到高级开发者

---

## 📋 目录

- [🗺️ Rust 1.90 异步编程 - 综合思维导图](#️-rust-190-异步编程---综合思维导图)
  - [📋 目录](#-目录)
  - [🌳 整体架构](#-整体架构)
  - [⚡ Future 与 async/await](#-future-与-asyncawait)
  - [🔧 异步运行时](#-异步运行时)
  - [📡 异步I/O与并发](#-异步io与并发)
  - [📚 学习路径](#-学习路径)
    - [🌱 初学者路径 (2-3周)](#-初学者路径-2-3周)
    - [⚡ 进阶路径 (2-3周)](#-进阶路径-2-3周)
    - [🎓 专家路径 (3-4周)](#-专家路径-3-4周)
  - [🔍 问题诊断树](#-问题诊断树)
  - [⚖️ 技术选型决策树](#️-技术选型决策树)

---

## 🌳 整体架构

```text
                Rust 异步编程体系
                       │
        ┌──────────────┼──────────────┐
        │              │              │
    Future体系     Runtime系统    并发原语
        │              │              │
    ┌───┴───┐     ┌────┴────┐    ┌───┴───┐
    │       │     │         │    │       │
  async  Future  Tokio  async-std  Channel Select
  await   trait   │         │     JoinSet  spawn
    │       │     │         │        │      │
  Poll   Waker  Executor Reactor  Mutex  Stream
                           
          ┌─────────────────────────┐
          │    零成本异步保证       │
          │                         │
          │ • 编译期状态机生成      │
          │ • 无栈协程              │
          │ • 显式异步              │
          │ • 线程开销可控          │
          └─────────────────────────┘
```

---

## ⚡ Future 与 async/await

```text
Future 核心机制
│
├─ 📝 Future Trait
│  └─ trait Future {
│         type Output;
│         fn poll(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Self::Output>;
│     }
│     • 状态机接口
│     • 惰性求值
│     • 组合式编程
│
├─ 🔄 Poll 枚举
│  ├─ Poll::Ready(value): 完成
│  └─ Poll::Pending: 未完成，等待唤醒
│     • 非阻塞轮询
│     • 手动状态管理
│
├─ ⏰ Waker 机制
│  └─ 唤醒Future继续执行
│     • 事件驱动
│     • 减少轮询开销
│     • Runtime调度核心
│
├─ 📍 Pin 与 Unpin
│  ├─ Pin<P>: 固定内存位置
│  ├─ Unpin: 可安全移动
│  └─ !Unpin: 包含自引用
│     • 防止移动
│     • 保证内存安全
│
├─ ⚡ async/await 语法
│  ├─ async fn foo() -> T
│  │  └─ 等价于 fn foo() -> impl Future<Output = T>
│  │
│  ├─ async block: async { ... }
│  │  └─ 创建匿名Future
│  │
│  └─ await 表达式
│     └─ future.await
│        • 暂停当前async函数
│        • 让出执行权
│        • 自动状态机转换
│
├─ 🎯 async fn in trait (Rust 1.75+)
│  └─ trait AsyncRead {
│         async fn read(&mut self, buf: &mut [u8]) -> Result<usize>;
│     }
│     • Trait中的async方法
│     • RPITIT支持
│     • Rust 1.90: 性能优化
│
└─ 🔒 async closure (Rust 1.90+)
   └─ let f = async |x| { process(x).await };
      • 异步闭包
      • 捕获环境
      • 返回Future
```

---

## 🔧 异步运行时

```text
Runtime 生态系统
│
├─ 🚀 Tokio (主流)
│  ├─ 特性
│  │  ├─ 多线程工作窃取调度器
│  │  ├─ I/O reactor (epoll/kqueue/IOCP)
│  │  ├─ 定时器
│  │  ├─ 完整工具链
│  │  └─ 丰富生态
│  │
│  ├─ 核心组件
│  │  ├─ tokio::spawn: 任务spawn
│  │  ├─ tokio::select!: 多路选择
│  │  ├─ tokio::join!: 并发等待
│  │  ├─ tokio::time: 时间操作
│  │  └─ tokio::sync: 异步同步原语
│  │
│  └─ 适用场景
│     └─ 高并发服务器、网络应用
│
├─ 🌊 async-std
│  ├─ 特性
│  │  ├─ 标准库API风格
│  │  ├─ 跨平台
│  │  ├─ 简洁易用
│  │  └─ 模块化设计
│  │
│  └─ 适用场景
│     └─ 通用异步应用、学习入门
│
├─ 🪶 Smol
│  ├─ 特性
│  │  ├─ 轻量级（~1500 LoC）
│  │  ├─ 单线程/多线程可选
│  │  ├─ 最小依赖
│  │  └─ 灵活组合
│  │
│  └─ 适用场景
│     └─ 嵌入式、资源受限环境
│
├─ ⚡ Glommio / Monoio
│  ├─ 特性
│  │  ├─ io_uring支持
│  │  ├─ NUMA感知
│  │  ├─ thread-per-core
│  │  └─ 极致性能
│  │
│  └─ 适用场景
│     └─ 高性能I/O密集型应用
│
└─ 🎯 Runtime对比
   ├─ 性能: Glommio > Tokio > async-std > Smol
   ├─ 易用: async-std > Tokio > Smol > Glommio
   ├─ 生态: Tokio >>> async-std > others
   └─ 灵活: Smol > async-std > Tokio > Glommio
```

---

## 📡 异步I/O与并发

```text
异步并发原语
│
├─ 📨 Channel (消息传递)
│  ├─ mpsc (多生产者单消费者)
│  │  └─ tokio::sync::mpsc
│  │     • 有界/无界
│  │     • 高效队列
│  │
│  ├─ oneshot (一次性)
│  │  └─ tokio::sync::oneshot
│  │     • 发送单个值
│  │     • 用于请求-响应
│  │
│  └─ broadcast (广播)
│     └─ tokio::sync::broadcast
│        • 多个接收者
│        • 事件通知
│
├─ 🔐 同步原语
│  ├─ Mutex
│  │  └─ tokio::sync::Mutex
│  │     • 异步锁
│  │     • 跨await安全
│  │
│  ├─ RwLock
│  │  └─ tokio::sync::RwLock
│  │     • 读写锁
│  │     • 多读单写
│  │
│  └─ Semaphore
│     └─ tokio::sync::Semaphore
│        • 限制并发数
│        • 资源池管理
│
├─ 🎯 结构化并发
│  ├─ JoinSet (Rust 1.70+)
│  │  └─ tokio::task::JoinSet
│  │     • 动态任务集合
│  │     • 批量等待
│  │     • 自动取消
│  │
│  ├─ select!
│  │  └─ tokio::select! {
│  │         result1 = future1 => { ... }
│  │         result2 = future2 => { ... }
│  │     }
│  │     • 多路选择
│  │     • 首个完成
│  │
│  └─ join! / try_join!
│     └─ tokio::join!(future1, future2)
│        • 并发执行
│        • 全部完成
│
├─ 🌊 Stream (异步迭代器)
│  └─ trait Stream {
│         type Item;
│         fn poll_next(self: Pin<&mut Self>, cx: &mut Context) 
│             -> Poll<Option<Self::Item>>;
│     }
│     • 异步序列
│     • 惰性求值
│     • 组合操作 (map, filter, fold)
│
└─ ⏱️ 时间操作
   ├─ tokio::time::sleep
   ├─ tokio::time::timeout
   ├─ tokio::time::interval
   └─ Instant / Duration
```

---

## 📚 学习路径

### 🌱 初学者路径 (2-3周)

```text
Week 1: async/await基础
│
├─ Day 1-3: Future概念
│  ├─ 理解异步模型
│  ├─ async函数定义
│  ├─ await表达式
│  └─ 实践: 简单async函数
│
└─ Day 4-7: Tokio入门
   ├─ Runtime初始化
   ├─ tokio::spawn
   ├─ 基础I/O
   └─ 实践: HTTP客户端

Week 2: 并发原语
│
├─ Day 1-4: Channel
│  ├─ mpsc使用
│  ├─ oneshot通信
│  └─ 实践: 生产者-消费者
│
└─ Day 5-7: 同步原语
   ├─ Async Mutex
   ├─ Select宏
   └─ 实践: 简单服务器

Week 3: 综合应用
│
└─ 项目实践
   ├─ TCP echo server
   ├─ HTTP服务
   └─ WebSocket chat
```

### ⚡ 进阶路径 (2-3周)

```text
Week 1: 高级并发
│
├─ JoinSet
├─ Stream处理
├─ 背压控制
└─ 实践: 并发爬虫

Week 2: 性能优化
│
├─ Pin详解
├─ 自定义Future
├─ 零拷贝I/O
└─ 实践: 高性能代理

Week 3: Runtime深入
│
├─ 多Runtime对比
├─ io_uring
├─ 错误处理模式
└─ 实践: 微服务框架
```

### 🎓 专家路径 (3-4周)

```text
Week 1-2: 深度理论
│
├─ Future状态机
├─ Waker实现原理
├─ Executor设计
└─ Reactor模式

Week 3-4: 高级应用
│
├─ 自定义Runtime
├─ 异步生态设计
├─ 性能profiling
└─ 项目: 高性能框架
```

---

## 🔍 问题诊断树

```text
遇到异步问题？
│
├─ 编译错误
│  ├─ Future未实现Send
│  │  ├─ 检查: 跨await持有的类型
│  │  └─ 解决: 使用async Mutex或调整生命周期
│  │
│  ├─ Pin相关错误
│  │  ├─ 检查: 是否需要固定位置
│  │  └─ 解决: 使用Box::pin或tokio::pin!
│  │
│  └─ 生命周期错误
│     ├─ 检查: async函数参数生命周期
│     └─ 解决: 添加'static或调整借用
│
├─ 运行时错误
│  ├─ Panic in async context
│  │  ├─ 检查: unwrap的使用
│  │  └─ 解决: 使用? operator
│  │
│  ├─ 死锁
│  │  ├─ 检查: Mutex持有顺序
│  │  └─ 解决: 使用timeout或重构
│  │
│  └─ 内存泄漏
│     ├─ 检查: 未取消的任务
│     └─ 解决: 使用JoinHandle或tokio::select!
│
└─ 性能问题
   ├─ 高CPU使用
   │  ├─ 检查: 是否有忙等待
   │  └─ 解决: 添加yield_now()
   │
   ├─ 高延迟
   │  ├─ 检查: 是否阻塞Runtime
   │  └─ 解决: 使用spawn_blocking
   │
   └─ 低吞吐
      ├─ 检查: 并发度是否足够
      └─ 解决: 增加任务并发数
```

---

## ⚖️ 技术选型决策树

```text
选择哪个Runtime？
│
├─ 通用服务器应用 → Tokio
│  └─ 优点: 成熟生态、文档齐全
│     缺点: 依赖较重
│
├─ 学习/简单应用 → async-std
│  └─ 优点: API简洁、易上手
│     缺点: 生态较小
│
├─ 资源受限 → Smol
│  └─ 优点: 轻量、灵活
│     缺点: 需要手动组合
│
└─ 极致性能 → Glommio/Monoio
   └─ 优点: io_uring、NUMA
      缺点: Linux only、学习曲线陡

并发 vs 并行？
│
├─ I/O密集型 → async (并发)
│  └─ 单线程可处理大量连接
│
└─ CPU密集型 → threads (并行)
   └─ 或spawn_blocking转移到线程池

Channel vs 共享状态？
│
├─ 需要消息传递 → Channel
│  └─ 优点: 避免锁、清晰所有权
│
└─ 需要共享数据 → Mutex/RwLock
   └─ 优点: 直接访问、适合复杂状态

背压控制？
│
├─ 有界Channel → 自动背压
├─ Semaphore → 限制并发数
└─ Stream → 惰性处理
```

---

**文档版本**: v1.0  
**最后更新**: 2025-10-20  
**维护者**: Rust Learning Community

---

🗺️ **掌握异步编程，构建高性能 Rust 应用！** 🚀✨
