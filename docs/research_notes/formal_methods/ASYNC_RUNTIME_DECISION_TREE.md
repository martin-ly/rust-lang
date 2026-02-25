# 异步运行时选型决策树

> **创建日期**: 2026-02-24
> **状态**: ✅ 新建 (Phase 1 Week 8)
> **任务ID**: P1-W8-T5

---

## 决策树概览

```text
需要异步运行时？
│
├── IO密集型任务？
│   ├── 是 → 使用异步
│   │   ├── 需要高并发？
│   │   │   ├── 是 → 选择Tokio
│   │   │   │   ├── 需要Web框架？
│   │   │   │   │   ├── 是 → Axum/Actix-web
│   │   │   │   │   └── 否 → 纯Tokio
│   │   │   │   ├── 需要协议支持？
│   │   │   │   │   ├── HTTP/2, gRPC → tonic
│   │   │   │   │   ├── WebSocket → tokio-tungstenite
│   │   │   │   │   └── 自定义协议 → tokio::net
│   │   │   │   └── 需要调度器定制？
│   │   │   │       ├── 是 → 自定义RuntimeBuilder
│   │   │   │       └── 否 → tokio::main默认
│   │   │   └── 否 → 轻量级异步
│   │   │       ├── 简单任务 → futures + 自定义执行器
│   │   │       └── 嵌入式 → embassy
│   │   └── 需要兼容性？
│   │       ├── 与同步代码混合 → spawn_blocking
│   │       └── 与C集成 → async-std或自定义
│   └── 否 → 使用同步
│       └── 线程池 (rayon/threadpool)
│
├── 延迟敏感度？
│   ├── 极低延迟(μs级) → 禁用yield，CPU亲和性
│   ├── 低延迟(ms级) → work-stealing调度器
│   └── 普通 → 默认配置
│
└── 平台限制？
    ├── no_std → embassy
    ├── WASM → wasm-bindgen-futures
    └── 嵌入式Linux → tokio/rt-multi-thread
```

---

## 主流运行时对比

| 运行时 | 适用场景 | 特点 | 生态 |
| :--- | :--- | :--- | :--- |
| **Tokio** | 通用服务端 | 成熟、功能全、生态好 | ⭐⭐⭐⭐⭐ |
| **async-std** | 标准库兼容 | 类似std API | ⭐⭐⭐ |
| **smol** | 轻量级 | 简单、可组合 | ⭐⭐ |
| **embassy** | 嵌入式 | no_std、实时 | ⭐⭐ |
| **glommio** | 线程-per-core | io_uring、DPDK | ⭐ |

---

## Tokio配置决策

```text
使用Tokio
│
├── 选择运行时类型
│   ├── 多线程 (rt-multi-thread) [推荐]
│   │   └── 适合CPU密集型+IO密集型混合
│   ├── 单线程 (rt-single-thread)
│   │   └── 适合低并发、资源受限
│   └── 当前线程 (rt)
│       └── 测试、特殊场景
│
├── 配置工作线程数
│   ├── 默认: num_cpus
│   ├── CPU密集型: num_cpus
│   └── IO密集型: num_cpus * 2
│
├── 任务调度策略
│   ├── 默认work-stealing [推荐]
│   ├── 局部性优先 → LocalSet
│   └── FIFO → 自定义spawn
│
└── 功能启用
    ├── rt (必需)
    ├── rt-multi-thread
    ├── macros (tokio::main)
    ├── net (TCP/UDP)
    ├── time (定时器)
    ├── process
    ├── fs
    └── sync (Mutex, RwLock, Notify)
```

---

## 代码示例

### 基础Tokio应用

```rust
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 启动TCP服务器
    let listener = tokio::net::TcpListener::bind("127.0.0.1:8080").await?;

    loop {
        let (socket, _) = listener.accept().await?;
        // 为每个连接spawn任务
        tokio::spawn(handle_connection(socket));
    }
}

async fn handle_connection(mut socket: tokio::net::TcpStream) {
    let mut buf = [0; 1024];
    // 异步读写
    let n = socket.read(&mut buf).await.unwrap();
    socket.write_all(&buf[0..n]).await.unwrap();
}
```

### 混合同步/异步代码

```rust
#[tokio::main]
async fn main() {
    // CPU密集型任务放入spawn_blocking
    let result = tokio::task::spawn_blocking(|| {
        heavy_computation()
    }).await.unwrap();

    // IO操作使用async
    let data = tokio::fs::read_to_string("file.txt").await.unwrap();
}
```

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-24
**状态**: ✅ 已完成 - 异步运行时选型决策树
