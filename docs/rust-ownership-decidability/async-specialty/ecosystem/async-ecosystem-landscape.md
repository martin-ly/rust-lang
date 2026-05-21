# Rust Async 生态系统全景图

> **从嵌入式到io_uring：完整的Async开源生态**

---

## 📑 目录
>
- [Rust Async 生态系统全景图](#rust-async-生态系统全景图)
  - [📑 目录](#-目录)
  - [生态系统总览](#生态系统总览)
  - [1. 嵌入式生态 (Embedded)](#1-嵌入式生态-embedded)
    - [1.1 Embassy生态详解](#11-embassy生态详解)
    - [1.2 RTIC实时框架](#12-rtic实时框架)
  - [2. io\_uring 生态 (Linux高性能)](#2-io_uring-生态-linux高性能)
    - [2.1 tokio-uring](#21-tokio-uring)
    - [2.2 glommio (线程本地io\_uring)](#22-glommio-线程本地io_uring)
    - [2.3 monoio (纯io\_uring)](#23-monoio-纯io_uring)
    - [2.4 io\_uring生态对比](#24-io_uring生态对比)
  - [3. 特色开源库](#3-特色开源库)
    - [3.1 Quinn (QUIC协议)](#31-quinn-quic协议)
    - [3.2 sqlx (编译时检查SQL)](#32-sqlx-编译时检查sql)
    - [3.3 lapin (AMQP/RabbitMQ)](#33-lapin-amqprabbitmq)
  - [4. 生态选择指南](#4-生态选择指南)
    - [4.1 决策树](#41-决策树)
    - [4.2 场景匹配表](#42-场景匹配表)
  - [**更新日期**: 2026-03-05](#更新日期-2026-03-05)
  - [相关概念](#相关概念)

## 生态系统总览
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

```text
┌─────────────────────────────────────────────────────────────────────────────┐
│                        Rust Async 生态系统全景图                              │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  🎯 应用场景分层                                                               │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │  应用层 (Applications)                                               │   │
│  │  ├── Web框架: Axum, Actix-web, Poem, Salvo                          │   │
│  │  ├── 数据库: sqlx, sea-orm, diesel, tokio-postgres                  │   │
│  │  ├── gRPC: Tonic, tarpc                                             │   │
│  │  ├── 消息队列: lapin (AMQP), rdkafka, pulsar                        │   │
│  │  └── 客户端: reqwest, hyper                                         │   │
│  ├─────────────────────────────────────────────────────────────────────┤   │
│  │  运行时层 (Runtimes)                                                 │   │
│  │  ├── 通用: Tokio (默认标准)                                          │   │
│  │  ├── 轻量: async-std, smol, embassy                                 │   │
│  │  ├── io_uring: tokio-uring, glommio, monoio                         │   │
│  │  ├── 嵌入式: Embassy, RTIC                                          │   │
│  │  └── WASM: wasm-bindgen-futures, gloo                               │   │
│  ├─────────────────────────────────────────────────────────────────────┤   │
│  │  抽象层 (Abstractions)                                               │   │
│  │  ├── Future组合: futures, futures-lite                              │   │
│  │  ├── Stream: tokio-stream, async-stream                             │   │
│  │  ├── Service: Tower                                                 │   │
│  │  ├── Actor: Actix, coerce                                           │   │
│  │  └── 并发原语: async-lock, event-listener                           │   │
│  ├─────────────────────────────────────────────────────────────────────┤   │
│  │  系统层 (System)                                                     │   │
│  │  ├── IO多路复用: epoll, kqueue, IOCP, io_uring                      │   │
│  │  ├── 网络协议: quinn (QUIC), async-tls, rustls                      │   │
│  │  ├── 文件系统: tokio-fs, glommio-fs                                 │   │
│  │  └── 进程管理: tokio-process, async-process                         │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 1. 嵌入式生态 (Embedded)
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

### 1.1 Embassy生态详解
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

```rust
#![no_std]
#![no_main]

use embassy_executor::Spawner;
use embassy_time::{Duration, Timer};
use embassy_stm32::gpio::{Level, Output, Speed};

#[embassy_executor::task]
async fn blink_task(mut led: Output<'static>) {
    loop {
        led.set_high();
        Timer::after(Duration::from_millis(300)).await;
        led.set_low();
        Timer::after(Duration::from_millis(300)).await;
    }
}

#[embassy_executor::main]
async fn main(spawner: Spawner) {
    let p = embassy_stm32::init(Default::default());
    let led = Output::new(p.PB0, Level::Low, Speed::Low);
    spawner.spawn(blink_task(led)).unwrap();
}
```

### 1.2 RTIC实时框架

```rust
#[rtic::app(device = stm32f4xx_hal::pac)]
mod app {
    #[shared]
    struct Shared { data: SensorData }

    #[local]
    struct Local { led: PA5<Output<PushPull>> }

    #[init]
    fn init(cx: init::Context) -> (Shared, Local, init::Monotonics) {
        // 初始化硬件
        (Shared { data: SensorData::default() },
         Local { led: cx.device.GPIOA.pa5.into_push_pull_output() },
         init::Monotonics())
    }

    #[task(shared = [data])]
    async fn read_sensor(mut cx: read_sensor::Context) {
        loop {
            let d = read_i2c_sensor().await;
            cx.shared.data.lock(|s| *s = d);
            Systick::delay(1000.millis()).await;
        }
    }
}
```

---

## 2. io_uring 生态 (Linux高性能)

### 2.1 tokio-uring

```rust
use tokio_uring::fs::File;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    tokio_uring::start(async {
        let file = File::create("hello.txt").await?;
        let buf = b"Hello, io_uring!";
        let (result, _) = file.write_at(buf, 0).await;
        result?;

        let buf = vec![0; 16];
        let (result, buf) = file.read_at(buf, 0).await;
        println!("read: {:?}", &buf[..result?]);
        Ok(())
    })
}
```

### 2.2 glommio (线程本地io_uring)

```rust
use glommio::{
    io::{DmaFile, OpenOptions},
    LocalExecutorBuilder, Placement,
};

fn main() {
    let ex = LocalExecutorBuilder::new(Placement::Fixed(0))
        .make()
        .expect("failed to create executor");

    ex.run(async {
        let file = OpenOptions::new()
            .read(true)
            .dma_open("data.bin")
            .await
            .expect("failed to open file");

        let mut buf = file.alloc_dma_buffer(4096);
        let n = file.read_at(&mut buf, 0).await.unwrap();
        println!("read {} bytes", n);
    });
}
```

### 2.3 monoio (纯io_uring)

```rust
use monoio::{
    fs::File,
    io::{AsyncReadRent, AsyncWriteRent},
};

#[monoio::main(driver = "io_uring")]
async fn main() {
    let file = File::open("hello.txt").await.unwrap();
    let buf = Vec::with_capacity(1024);
    let (n, buf) = file.read(buf).await;
    println!("read {} bytes", n.unwrap());
}
```

### 2.4 io_uring生态对比

| 运行时 | io_uring支持 | 性能 | 适用场景 |
|:-------|:-------------|:-----|:---------|
| **tokio-uring** | ✅ 完整 | ⭐⭐⭐ | 通用高性能 |
| **glommio** | ✅ 完整 | ⭐⭐⭐⭐ | 存储密集型 |
| **monoio** | ✅ 纯io_uring | ⭐⭐⭐⭐⭐ | 极致性能 |
| **compio** | ✅ 跨平台 | ⭐⭐⭐ | Windows+Linux |

---

## 3. 特色开源库

### 3.1 Quinn (QUIC协议)

```rust
use quinn::{Endpoint, ServerConfig};

async fn quic_server() {
    let (endpoint, _) = Endpoint::server(
        ServerConfig::with_single_cert(...),
        "0.0.0.0:4433".parse().unwrap()
    ).unwrap();

    while let Some(conn) = endpoint.accept().await {
        tokio::spawn(handle_conn(conn));
    }
}
```

### 3.2 sqlx (编译时检查SQL)

```rust
use sqlx::postgres::PgPool;

async fn query_users(pool: &PgPool) -> Result<Vec<User>, sqlx::Error> {
    let users = sqlx::query_as::<_, User>(
        "SELECT id, name, email FROM users WHERE active = $1"
    )
    .bind(true)
    .fetch_all(pool)
    .await?;

    Ok(users)
}
```

### 3.3 lapin (AMQP/RabbitMQ)

```rust
use lapin::{Connection, ConnectionProperties, options::*};

async fn amqp_consumer() -> Result<(), lapin::Error> {
    let conn = Connection::connect(
        "amqp://guest:guest@localhost:5672/%2f",
        ConnectionProperties::default()
    ).await?;

    let channel = conn.create_channel().await?;
    let mut consumer = channel.basic_consume(
        "my_queue", "consumer_tag",
        BasicConsumeOptions::default(),
        FieldTable::default()
    ).await?;

    while let Some(delivery) = consumer.next().await {
        let delivery = delivery?;
        process(&delivery.data).await;
        delivery.ack(BasicAckOptions::default()).await?;
    }
    Ok(())
}
```

---

## 4. 生态选择指南

### 4.1 决策树

```text
目标平台?
│
├─ 嵌入式 (MCU)
│   ├─ 需要实时保证? → RTIC
│   └─ 通用async → Embassy
│
├─ 服务器 (Linux)
│   ├─ 需要极致IO性能?
│   │   ├─ io_uring可用? → monoio / tokio-uring
│   │   └─ 通用 → Tokio
│   ├─ 需要轻量级? → smol
│   └─ 需要容错Actor? → bastion
│
└─ 跨平台 → Tokio
```

### 4.2 场景匹配表

| 场景 | 推荐运行时 | 理由 |
|:-----|:-----------|:-----|
| Web服务器 | Tokio + Axum | 生态最丰富 |
| 高性能存储 | glommio | DMA支持 |
| 网络密集型 | monoio | 纯io_uring |
| 嵌入式STM32 | Embassy | 硬件抽象完善 |
| 微服务 | Tokio + Tonic | gRPC支持 |

---

**维护者**: Rust Async Ecosystem Team
**更新日期**: 2026-03-05
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [Parent README](../README.md)

---

## 相关概念

- [上级目录](../README.md)


---

## 权威来源索引

> **[来源: Wikipedia - Memory Safety]**

> **[来源: TRPL Ch. 4 - Ownership]**

> **[来源: Rustonomicon - Ownership]**

> **[来源: POPL 2018 - RustBelt]**

> **[来源: Wikipedia - Asynchronous I/O]**

> **[来源: TRPL Ch. 17 - Async]**

> **[来源: Tokio Documentation]**

> **[来源: RFC 2394 - Async/Await]**
