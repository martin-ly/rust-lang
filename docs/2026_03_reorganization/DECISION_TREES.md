# Rust 学习项目 - 决策树指南

> 帮助学习者和使用者做出正确选择的决策树

---

## 🎯 1. 学习路径决策树

```text
我应该从哪开始学习 Rust？
│
├─ 我是编程初学者？
│  ├─ 是 → 推荐先学习基础编程概念
│  │       └─ 参考: docs/01_learning/LEARNING_PATH_PLANNING.md
│  │
│  └─ 否 → 我有其他语言经验？
│          │
│          ├─ C/C++ → 重点学习所有权和生命周期
│          │         ├─ 原因: 已有内存管理概念
│          │         └─ 路径: C01 → C04 → C05
│          │
│          ├─ Java/Python/JS → 重点学习所有权和类型系统
│          │                    ├─ 原因: 需理解 Rust 独特之处
│          │                    └─ 路径: C01-C03 → C04-C06
│          │
│          └─ 函数式语言 (Haskell/Scala) → 重点学习生命周期
│                                        ├─ 原因: 已有类型系统基础
│                                        └─ 路径: C01 → C04 → C11
│
├─ 我的学习目标？
│  ├─ 找到工作 →
│  │   ├─ Web 后端: C04 → C06 → C10 → content/ecosystem/web_frameworks
│  │   ├─ 系统编程: C01 → C05 → C07 → content/production/
│  │   ├─ 区块链: C01 → C05 → C08 → content/scenarios/blockchain
│  │   └─ 嵌入式: C01 → C07 → C12 → content/scenarios/embedded
│  │
│  ├─ 个人项目 →
│  │   ├─ CLI 工具: C01-C03 → C07 → examples/cli
│  │   ├─ Web 应用: C01-C06 → C10 → C12
│  │   └─ 系统工具: C01 → C05 → C07
│  │
│  └─ 学术研究 →
│      ├─ 类型理论: C02 → C04 → content/academic/coq_formalization
│      ├─ 形式化验证: C01 → content/academic/rustbelt
│      └─ 编译器: C04 → C11 → content/emerging/
│
└─ 我的时间投入？
   ├─ < 1周 → 快速入门
   │         └─ 阅读: GETTING_STARTED.md + C01-C03 概览
   │
   ├─ 1-4周 → 基础学习
   │         └─ 完成: C01-C06 基础内容
   │
   ├─ 1-3月 → 系统学习
   │         └─ 完成: C01-C12 + 实战项目
   │
   └─ > 3月 → 深度学习
             └─ 完成: 全部内容 + content/ + 贡献开源
```

---

## 🛠️ 2. 技术选型决策树

### 2.1 并发模型选择

```text
我应该使用哪种并发模型？
│
├─ 需要共享大量数据？
│  ├─ 是 → 使用 Arc<Mutex<T>> 或 Arc<RwLock<T>>
│  │       ├─ 读多写少: RwLock
│  │       └─ 读写相当: Mutex
│  │
│  └─ 否 → 使用消息传递
│          ├─ 需要广播? → mpsc::channel 或 tokio::sync::broadcast
│          ├─ 需要单播? → mpsc::channel
│          └─ 需要 oneshot? → oneshot::channel
│
├─ CPU 密集型任务？
│  ├─ 是 → 使用 rayon (数据并行)
│  │       └─ 适合: 数组处理、计算密集型
│  │
│  └─ 否 → IO 密集型
│          ├─ 是 → 使用 async/await + Tokio
│          └─ 否 → 使用标准库线程
│
└─ 需要最高性能？
   ├─ 是 → 考虑 lock-free 数据结构
   │       └─ crossbeam 库
   │
   └─ 否 → 使用标准同步原语
```

### 2.2 异步运行时选择

```text
我应该使用哪个异步运行时？
│
├─ 生产环境？
│  ├─ 是 → Tokio
│  │       ├─ 原因: 生态最成熟，文档最完善
│  │       ├─ 适用: Web 服务、数据库客户端
│  │       └─ 注意: 默认多线程，可配置
│  │
│  └─ 否 → 学习/实验
│          ├─ 需要标准库兼容? → async-std
│          ├─ 需要轻量级? → smol
│          └─ 需要极致性能(Linux)? → Glommio (io_uring)
│
├─ 特定需求？
│  ├─ 嵌入式/资源受限 → embassy
│  ├─ WebAssembly → wasm-bindgen-futures
│  └─ 测试 → tokio::test
│
└─ 兼容性考虑？
   ├─ 已有 Tokio 生态 → 继续使用 Tokio
   └─ 需要通用抽象 → 使用 futures crate
```

### 2.3 Web 框架选择

```text
我应该使用哪个 Web 框架？
│
├─ 项目规模？
│  ├─ 小型项目/微服务 → Axum 或 Actix-web
│  │   ├─ 需要极致性能? → Actix-web
│  │   └─ 需要类型安全? → Axum
│  │
│  ├─ 中型项目 → Axum + Tower
│  │   └─ 原因: 中间件系统完善
│  │
│  └─ 大型项目 → 自定义组合
│      ├─ HTTP: hyper
│      ├─ 路由: axum
│      ├─ 序列化: serde
│      └─ 数据库: sqlx
│
├─ 特定需求？
│  ├─ 需要 GraphQL? → async-graphql
│  ├─ 需要 gRPC? → tonic
│  ├─ 需要 WebSocket? → 所有主流框架都支持
│  └─ 需要实时通信? → 考虑 split + channels
│
└─ 学习曲线？
   ├─ 初学者 → Axum
   │   └─ 原因: 与标准库风格一致
   │
   └─ 有经验 → 根据需求选择
```

---

## 🏗️ 3. 设计模式决策树

### 3.1 创建型模式选择

```text
我需要创建对象，应该使用哪种模式？
│
├─ 需要确保只有一个实例？
│  ├─ 是 → 单例模式 (LazyLock)
│  │       └─ 注意: Rust 中通常用 LazyLock 或 OnceLock
│  │
│  └─ 否 → 继续判断
│
├─ 需要根据不同条件创建不同对象？
│  ├─ 是 → 工厂模式
│  │       ├─ 简单工厂: 函数返回 Box<dyn Trait>
│  │       └─ 抽象工厂: trait Factory { fn create() -> Product }
│  │
│  └─ 否 → 继续判断
│
├─ 需要复杂对象的逐步构建？
│  ├─ 是 → 建造者模式 (Builder Pattern)
│  │       ├─ 类型状态 Builder: 编译时检查
│  │       └─ 普通 Builder: 运行时检查
│  │
│  └─ 否 → 直接创建
```

### 3.2 结构型模式选择

```text
我需要组织代码结构，应该使用哪种模式？
│
├─ 需要适配不兼容接口？
│  ├─ 是 → 适配器模式 (Adapter)
│  │       ├─ 已有类型 → 实现 From/Into
│  │       └─ 外部类型 → Newtype 模式 + Deref
│  │
│  └─ 否 → 继续判断
│
├─ 需要动态添加功能？
│  ├─ 是 → 装饰器模式
│  │       ├─ 组合而非继承
│  │       └─ 使用泛型或 trait object
│  │
│  └─ 否 → 继续判断
│
├─ 需要控制访问？
│  ├─ 是 → 代理模式
│  │       ├─ 延迟初始化 → LazyLock
│  │       ├─ 访问控制 → 自定义代理结构
│  │       └─ 远程代理 → 网络客户端
│  │
│  └─ 否 → 保持简单
```

### 3.3 行为型模式选择

```text
我需要处理对象间交互，应该使用哪种模式？
│
├─ 需要一对多依赖通知？
│  ├─ 是 → 观察者模式
│  │       ├─ 使用 channels (tokio::sync::broadcast)
│  │       └─ 或自定义 EventBus
│  │
│  └─ 否 → 继续判断
│
├─ 需要动态切换算法？
│  ├─ 是 → 策略模式
│  │       └─ trait Strategy { fn execute() }
│  │
│  └─ 否 → 继续判断
│
├─ 需要将请求封装为对象？
│  ├─ 是 → 命令模式
│  │       ├─ 撤销/重做功能
│  │       └─ 请求队列
│  │
│  └─ 否 → 继续判断
│
├─ 需要状态机？
│  ├─ 是 → 状态模式
│  │       ├─ 类型状态: 编译时检查
│  │       └─ 运行时状态: enum + match
│  │
│  └─ 否 → 函数式编程
```

---

## 📦 4. 类型系统设计决策树

```text
我应该如何设计类型系统？
│
├─ 需要运行时多态？
│  ├─ 是 → 使用 trait objects (dyn Trait)
│  │       ├─ 需要集合异构对象? → Vec<Box<dyn Trait>>
│  │       └─ 需要减少编译时间? → dyn Trait
│  │
│  └─ 否 → 使用泛型 (静态分发)
│          ├─ 性能更好
│          └─ 类型安全更强
│
├─ 需要类型级别的状态机？
│  ├─ 是 → 类型状态模式 (PhantomData)
│  │       └─ 编译时状态转换检查
│  │
│  └─ 否 → 使用运行时检查
│
├─ 需要零成本抽象？
│  ├─ 是 → 泛型 + inline
│  │       └─ 单态化生成最优代码
│  │
│  └─ 否 → 可以考虑 dyn Trait
│
└─ 需要处理错误？
   ├─ 可恢复错误 → Result<T, E>
   │              ├─ thiserror (库)
   │              └─ anyhow (应用)
   │
   └─ 不可恢复错误 → panic! 或 unwrap/expect
```

---

## 🔧 5. 工具链决策树

```text
我需要什么开发工具？
│
├─ 代码检查？
│  ├─ 语法检查 → rustc 或 cargo check
│  ├─ 代码风格 → rustfmt
│  ├─ 代码质量 → clippy
│  └─ 测试覆盖 → tarpaulin
│
├─ 调试？
│  ├─ 打印调试 → println! + dbg!
│  ├─ 断点调试 → VSCode + CodeLLDB
│  └─ 远程调试 → GDB/LLDB
│
├─ 性能分析？
│  ├─ 基准测试 → Criterion
│  ├─ 性能分析 → perf (Linux)
│  └─ 内存分析 → valgrind / heaptrack
│
└─ 文档？
   ├─ API 文档 → cargo doc
   ├─ 测试文档 → cargo test --doc
   └─ 书籍 → mdbook
```

---

## 📚 6. 学习资源决策树

```text
我需要什么学习资源？
│
├─ 当前水平？
│  ├─ 初学者 →
│  │   ├─ 官方 Rust Book
│  │   ├─ Rustlings 练习
│  │   └─ 本项目 C01-C03
│  │
│  ├─ 中级 →
│  │   ├─ Rust by Example
│  │   ├─ 本项目 C04-C06
│  │   └─ Programming Rust (书籍)
│  │
│  └─ 高级 →
│      ├─ Rust Reference
│      ├─ The Rustonomicon
│      ├─ 本项目 C07-C12
│      └─ content/academic/
│
├─ 学习方式？
│  ├─ 阅读偏好 → 文档 + 书籍
│  ├─ 实践偏好 → 练习 + 项目
│  ├─ 视频偏好 → YouTube 教程
│  └─ 互动偏好 → Rustlings + Exercism
│
└─ 具体问题？
   ├─ 编译错误 → rustc --explain
   ├─ 概念理解 → 本书对应章节
   ├─ 最佳实践 → docs/05_guides/
   └─ 实际问题 → FAQ.md
```

---

## 🎯 使用建议

1. **从宏观到微观**: 先确定大方向，再深入细节
2. **结合实际**: 根据项目实际需求做选择
3. **保持简单**: 没有银弹，选择最简单的可行方案
4. **迭代优化**: 初始选择不必完美，可随需求演进

---

**本文档提供了 Rust 学习和开发过程中的常见决策树，帮助做出合理选择。**

---

*最后更新: 2026-03-15*
*状态: ✅ 完整*
