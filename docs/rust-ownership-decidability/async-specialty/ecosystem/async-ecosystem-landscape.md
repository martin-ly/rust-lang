# Rust Async 生态系统全景图

> **从嵌入式到io_uring：完整的Async开源生态**

---

## 生态系统总览

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

### 1.1 Embassy生态详解

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
