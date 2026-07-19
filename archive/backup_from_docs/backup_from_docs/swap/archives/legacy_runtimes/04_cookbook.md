# Async Cookbook：Tokio 与 Smol（可复制片段）

按主题提供最小可运行片段。更完整版本见 `examples/`。

## 目录

- [Async Cookbook：Tokio 与 Smol（可复制片段）](#async-cookbooktokio-与-smol可复制片段)
  - [目录](#目录)
  - [1. 超时与取消（Tokio）](#1-超时与取消tokio)
  - [2. 有界并发抓取（Tokio + reqwest）](#2-有界并发抓取tokio--reqwest)
  - [3. mpsc 背压（Tokio）](#3-mpsc-背压tokio)
  - [4. Smol：最小 HTTP 获取](#4-smol最小-http-获取)
  - [5. Smol：并发任务集（FuturesUnordered）](#5-smol并发任务集futuresunordered)
  - [6. JoinSet + buffer\_unordered（Tokio 组合）](#6-joinset--buffer_unorderedtokio-组合)
  - [7. Notify 用法（Tokio）](#7-notify-用法tokio)
  - [8. Semaphore 进阶：带宽配额](#8-semaphore-进阶带宽配额)

## 1. 超时与取消（Tokio）

```rust
use tokio::time::{timeout, Duration};

async fn slow() { tokio::time::sleep(Duration::from_secs(5)).await; }

#[tokio::main]
async fn main() {
    match timeout(Duration::from_secs(1), slow()).await {
        Ok(_) => println!("done"),
        Err(_) => println!("timeout"),
    }
}
```

## 2. 有界并发抓取（Tokio + reqwest）

```rust
use futures::stream::{StreamExt};

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let urls = ["https://example.com"; 100];
    let client = reqwest::Client::new();
    let bodies = futures::stream::iter(urls)
        .map(|u| async { client.get(u).send().await?.bytes().await })
        .buffer_unordered(32)
        .collect::<Vec<_>>()
        .await;
    println!("{} responses", bodies.len());
    Ok(())
}
```

## 3. mpsc 背压（Tokio）

```rust
use tokio::sync::mpsc;

#[tokio::main]
async fn main() {
    let (tx, mut rx) = mpsc::channel::<u64>(1000);
    let prod = tokio::spawn(async move { for i in 0..10_000 { let _=tx.send(i).await; } });
    let cons = tokio::spawn(async move { while let Some(v)=rx.recv().await { let _=v; } });
    let _ = tokio::join!(prod, cons);
}
```

## 4. Smol：最小 HTTP 获取

```rust
use smol::io::AsyncWriteExt;

fn main() -> anyhow::Result<()> {
    smol::block_on(async move {
        let body = surf::get("https://example.com").recv_string().await?;
        let mut stdout = smol::Unblock::new(std::io::stdout());
        stdout.write_all(body.as_bytes()).await?;
        Ok(())
    })
}
```

## 5. Smol：并发任务集（FuturesUnordered）

## 6. JoinSet + buffer_unordered（Tokio 组合）

```rust
use futures::StreamExt;
use tokio::task::JoinSet;

async fn work(i: usize) -> anyhow::Result<usize> { Ok(i*2) }

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let mut set = JoinSet::new();
    for i in 0..100 { set.spawn(work(i)); }

    let results = futures::stream::unfold(set, |mut set| async move {
        match set.join_next().await { Some(Ok(v)) => Some((v?, set)), _ => None }
    }).buffer_unordered(16).collect::<Vec<_>>().await;

    println!("{} results", results.len());
    Ok(())
}
```

## 7. Notify 用法（Tokio）

```rust
use tokio::sync::Notify;
use std::sync::Arc;

#[tokio::main]
async fn main() {
    let notify = Arc::new(Notify::new());
    let n2 = notify.clone();
    let t = tokio::spawn(async move { n2.notified().await; println!("go"); });
    notify.notify_one();
    let _ = t.await;
}
```

## 8. Semaphore 进阶：带宽配额

```rust
use tokio::sync::Semaphore;
use std::sync::Arc;

#[tokio::main]
async fn main() {
    let sem = Arc::new(Semaphore::new(10));
    for _ in 0..100 {
        let s = sem.clone();
        tokio::spawn(async move { let _p = s.acquire_owned().await.unwrap(); /* do work */ });
    }
    // drain ...
}
```

```rust
use futures::{stream::FuturesUnordered, StreamExt};

async fn compute(i: usize) -> usize { i * 2 }

fn main() {
    smol::block_on(async move {
        let mut futs = FuturesUnordered::new();
        for i in 0..100 { futs.push(async move { compute(i).await }); }
        while let Some(_v) = futs.next().await {}
    });
}
```
