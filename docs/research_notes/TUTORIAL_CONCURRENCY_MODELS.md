# 教程：并发模型选择

> **创建日期**: 2026-02-24
> **目标受众**: 进阶
> **预计阅读时间**: 25分钟
> **级别**: L1/L2

---

## 引言

Rust提供了多种并发模型。本教程帮助你选择合适的模型。

---

## 第一部分：OS线程

### 何时使用

- CPU密集型任务
- 需要真正的并行
- 阻塞操作

```rust
use std::thread;

let handle = thread::spawn(|| {
    // CPU密集型计算
    heavy_computation()
});

let result = handle.join().unwrap();
```

**限制**: 创建成本高，数量受限(~几百)。

---

## 第二部分：异步/任务

### 何时使用

- IO密集型
- 高并发(数万连接)
- 非阻塞

```rust
#[tokio::main]
async fn main() {
    let listener = tokio::net::TcpListener::bind("127.0.0.1:8080").await.unwrap();

    loop {
        let (socket, _) = listener.accept().await.unwrap();
        tokio::spawn(handle_connection(socket));
    }
}
```

**优势**: 轻量级，可创建数百万任务。

---

## 第三部分：数据并行

### 何时使用

- 数据处理
- 集合操作

```rust
use rayon::prelude::*;

let sum: i32 = (0..1_000_000)
    .into_par_iter()  // 并行迭代器
    .map(|x| x * x)
    .sum();
```

**优势**: 自动工作窃取，负载均衡。

---

## 第四部分：Actor模型

### 何时使用

- 分布式系统
- 容错需求
- 状态封装

```rust
// actix示例
use actix::prelude::*;

struct MyActor;

impl Actor for MyActor {
    type Context = Context<Self>;
}

impl Handler<Message> for MyActor {
    type Result = ();

    fn handle(&mut self, msg: Message, _ctx: &mut Context<Self>) {
        // 处理消息
    }
}
```

---

## 第五部分：选择决策

```
任务类型？
├── CPU密集型
│   ├── 数据并行 → rayon
│   └── 通用并行 → OS线程
│
├── IO密集型
│   └── 异步 → tokio/async-std
│
└── 状态管理
    └── Actor → actix
```

---

## 总结

| 模型 | 适用场景 | 性能 | 复杂度 |
|:---|:---|:---:|:---:|
| OS线程 | CPU密集 | 高 | 低 |
| 异步 | IO密集 | 高 | 中 |
| 数据并行 | 数据处理 | 极高 | 低 |
| Actor | 分布式 | 中 | 高 |

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-24
**状态**: ✅ 已完成 - 教程：并发模型选择 (5/5教程全部完成！)
