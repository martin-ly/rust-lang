# Rust Async 全面专题

> **Rust的核心优势：Zero-Cost Async Programming**
>
> 整合权威来源 | 惯用法 | 设计模式 | 网络 | 嵌入式 | 最佳实践

---

## 专题概览

```text
┌─────────────────────────────────────────────────────────────────┐
│                    Rust Async 全面专题                           │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  📚 权威来源整合                                                  │
│  ├── Tokio官方文档深度解读                                         │
│  ├── Rust Async Book                                              │
│  ├── Embassy Embedded Runtime                                     │
│  └── async-std / smol 生态对比                                    │
│                                                                  │
│  🎨 惯用法 (Idioms)                                               │
│  ├── Future组合与链式调用                                          │
│  ├── 错误处理模式 (? vs match)                                    │
│  ├── 取消与超时处理                                               │
│  └── 资源管理与清理                                               │
│                                                                  │
│  🏗️ 设计模式 (Patterns)                                           │
│  ├── Tower Service Pattern                                        │
│  ├── Actor Pattern                                                │
│  ├── Pipeline / Fan-out Fan-in                                    │
│  ├── Circuit Breaker                                              │
│  └── Backpressure Management                                      │
│                                                                  │
│  🌐 网络编程 (Network)                                            │
│  ├── HTTP服务器模式 (Axum/Actix)                                  │
│  ├── TCP/UDP服务端                                                │
│  ├── WebSocket处理                                                │
│  ├── gRPC (Tonic)                                                 │
│  └── 协议解析状态机                                                │
│                                                                  │
│  🔧 嵌入式 (Embedded)                                             │
│  ├── Embassy框架深度                                               │
│  ├── 无堆async运行时                                               │
│  ├── 中断驱动编程                                                  │
│  └── 实时约束处理                                                  │
│                                                                  │
│  ⭐ 最佳实践 (Practices)                                          │
│  ├── 代码组织结构                                                  │
│  ├── 性能优化技巧                                                  │
│  ├── 调试与可观测性                                                │
│  └── 测试策略                                                     │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

---

## 目录结构

```text
async-specialty/
├── README.md                    # 本文件 - 专题导航
├── authoritative/               # 权威来源整合
│   ├── tokio-deep-dive.md      # Tokio深度解读
│   ├── embassy-runtime.md      # Embassy运行时
│   └── ecosystem-comparison.md # 生态对比
├── patterns/                    # 设计模式
│   ├── service-pattern.md      # Tower Service
│   ├── actor-pattern.md        # Actor模式
│   ├── pipeline-patterns.md    # 流处理模式
│   └── resilience-patterns.md  # 弹性模式
├── network/                     # 网络编程
│   ├── http-server-patterns.md # HTTP服务器
│   ├── tcp-udp-patterns.md     # 底层网络
│   ├── websocket-patterns.md   # WebSocket
│   └── protocol-state-machines.md # 协议解析
├── embedded/                    # 嵌入式
│   ├── embassy-guide.md        # Embassy指南
│   ├── heapless-async.md       # 无堆async
│   ├── interrupt-driven.md     # 中断驱动
│   └── real-time-patterns.md   # 实时模式
└── practices/                   # 最佳实践
    ├── code-organization.md    # 代码组织
    ├── performance-tuning.md   # 性能优化
    ├── debugging-observability.md # 调试
    └── testing-strategies.md   # 测试
```

---

## 核心优势：Why Rust Async?

### 对比其他语言的async

| 特性 | Rust Async | Go Goroutine | Tokio(Node.js) | C# async |
|:-----|:-----------|:-------------|:---------------|:---------|
| **内存安全** | ✅ 编译时保证 | ⚠️ GC | ⚠️ GC | ⚠️ GC |
| **零成本抽象** | ✅ 状态机 | ❌ 2MB栈 | ❌ 事件循环 | ❌ 线程池 |
| **取消安全** | ✅ Drop trait | ❌ | ❌ | ✅ |
| **并发安全** | ✅ Send/Sync | ❌ | ❌ | ⚠️ |
| **嵌入式支持** | ✅ Embassy | ❌ | ❌ | ⚠️ |
| **性能** | ✅ 最优 | △ | △ | △ |

### 关键数据

```text
任务创建:
  Rust Async: ~200ns  █
  Go:          ~2μs   ████
  OS Thread:   ~10μs  ████████████████████

内存占用:
  Rust Async: ~100B   █
  Go:          ~2KB   ████████████████████
  OS Thread:   ~1MB   ████████████████████████████████████████████

最大并发:
  Rust Async: 1M+     ████████████████████████████████████████████
  Go:          ~100K  ████████████████████
  OS Thread:   ~10K   ██
```

---

## 快速开始

### 选择合适的运行时

```rust
// 1. 通用场景 - Tokio (最流行)
[dependencies]
tokio = { version = "1", features = ["full"] }

// 2. 轻量级 - async-std
[dependencies]
async-std = "1.12"

// 3. 嵌入式 - Embassy
[dependencies]
embassy-executor = "0.5"
embassy-time = "0.3"

// 4. 嵌入式裸机 - smol
[dependencies]
smol = "2"
```

### 基础惯用法

```rust
use tokio::time::{sleep, Duration};

// 惯用法1: 顺序执行
async fn sequential() {
    let a = step1().await;
    let b = step2(a).await;
    let c = step3(b).await;
}

// 惯用法2: 并发执行 (join)
async fn concurrent() {
    let (a, b, c) = tokio::join!(
        fetch_data1(),
        fetch_data2(),
        fetch_data3()
    );
}

// 惯用法3: 最先完成 (race)
async fn race() {
    let result = tokio::select! {
        r = source1() => r,
        r = source2() => r,
    };
}

// 惯用法4: 取消与超时
async fn with_timeout() -> Result<Data, TimeoutError> {
    tokio::time::timeout(
        Duration::from_secs(5),
        fetch_data()
    ).await?
}
```

---

## 专题深入

### 1. 权威来源整合

**[Tokio深度解读](./authoritative/tokio-deep-dive.md)**

- Runtime架构详解
- Scheduler实现
- IO Driver (epoll/kqueue/IOCP)
- 与标准库的集成

**[Embassy指南](./embedded/embassy-guide.md)**

- 无堆设计
- 中断集成
- 时间驱动编程
- 硬件抽象层

### 2. 设计模式

**Tower Service Pattern**
> 详见 [Tower Service官方文档](https://docs.rs/tower-service/)

```rust
// 可组合的服务抽象
trait Service<Request> {
    type Response;
    type Future: Future<Output = Self::Response>;
    fn call(&self, req: Request) -> Self::Future;
}
```

**Actor模式**
> 详见 [actor-specialty/README.md](../actor-specialty/README.md)

- 消息传递
- 状态隔离
- 监督策略

### 3. 网络编程

**[HTTP服务器模式](./network/http-server-patterns.md)**

- Axum: 函数式风格
- Actix-web: Actor风格
- 中间件链
- 错误处理策略

**协议解析状态机**
> 使用枚举和模式匹配实现

```rust
enum ProtocolState {
    ReadingHeader { buf: BytesMut },
    ReadingBody { header: Header, remaining: usize },
    Processing { request: Request },
}
```

### 4. 嵌入式

**[Embassy指南](./embedded/embassy-guide.md)**

```rust
#[embassy_executor::main]
async fn main(spawner: Spawner) {
    let p = embassy_stm32::init(Default::default());

    // 并发任务
    spawner.spawn(blink_task(p.PB0)).unwrap();
    spawner.spawn(uart_task(p.USART1)).unwrap();
}

#[embassy_executor::task]
async fn blink_task(pin: PB0) {
    loop {
        pin.set_high();
        Timer::after(Duration::from_millis(300)).await;
        pin.set_low();
        Timer::after(Duration::from_millis(300)).await;
    }
}
```

### 5. 最佳实践

**代码组织**
> 推荐参考 [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)

- 模块边界
- 错误类型设计
- 配置管理

**性能优化**
> 推荐参考 [Tokio性能优化指南](https://docs.rs/tokio/)

- 减少分配
- 批处理
- 零拷贝

---

## 学习路径

### 初学者

1. [Tokio深度解析](./authoritative/tokio-deep-dive.md) - 理解基础
2. [最佳实践](./practices/best-practices.md) - 写出高质量代码

### 进阶开发者

1. [HTTP服务器模式](./network/http-server-patterns.md) - 服务端开发
2. [Tokio深度解析](./authoritative/tokio-deep-dive.md) - 深入理解Runtime

### 嵌入式开发者

1. [Embassy指南](./embedded/embassy-guide.md)
2. [Embassy生态系统](./ecosystem/async-ecosystem-landscape.md)

---

## 参考资源

### 官方文档

- [Tokio Documentation](https://docs.rs/tokio)
- [Rust Async Book](https://rust-lang.github.io/async-book/)
- [Embassy Docs](https://embassy.dev/)

### 社区资源

- [Async Working Group](https://github.com/rust-lang/wg-async)
- [This Week in Rust](https://this-week-in-rust.org/)
- [Rust异步生态](https://github.com/tokio-rs/awesome-tokio)

---

**维护者**: Rust Async Specialty Team
**创建日期**: 2026-03-05
**状态**: 🚧 持续推进中
