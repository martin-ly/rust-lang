# 异步Rust与所有权

> **权威来源**: Rust Async Book, Pin API RFC

## 1. 异步编程基础

### 1.1 Future trait

```rust
trait Future {
    type Output;
    fn poll(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Self::Output>;
}
```

### 1.2 所有权与异步

```rust
async fn example() {
    let data = String::from("hello");
    let future = async {
        // data 被移动到 async 块
        println!("{}", data);
    };
    // data 在这里不可用
    future.await;
}
```

## 2. Pin 与自引用

### 2.1 Pin 的作用

```rust
// Pin 保证对象在内存中不移动
fn pin_example() {
    let data = String::from("hello");
    let pinned = Box::pin(data);
    // pinned 保证不移动
}
```

### 2.2 自引用结构体

```rust
use std::pin::Pin;
use std::marker::PhantomPinned;

struct SelfReferential {
    data: String,
    ptr_to_data: *const String,
    _pin: PhantomPinned,
}

impl SelfReferential {
    fn new(data: String) -> Pin<Box<Self>> {
        let mut boxed = Box::new(Self {
            data,
            ptr_to_data: std::ptr::null(),
            _pin: PhantomPinned,
        });
        let ptr = &boxed.data as *const String;
        boxed.ptr_to_data = ptr;
        Box::into_pin(boxed)
    }
}
```

## 3. 异步所有权模式

### 3.1 共享所有权

```rust
use std::sync::Arc;

async fn shared_ownership() {
    let data = Arc::new(String::from("shared"));

    let task1 = {
        let data = Arc::clone(&data);
        async move {
            println!("task1: {}", data);
        }
    };

    let task2 = {
        let data = Arc::clone(&data);
        async move {
            println!("task2: {}", data);
        }
    };

    futures::join!(task1, task2);
}
```

### 3.2 借用与生命周期

```rust
async fn borrow_across_await<'a>(data: &'a str) -> usize {
    let len = data.len();
    tokio::time::sleep(Duration::from_secs(1)).await;
    // 'a 必须跨越 await 点
    len
}
```

## 4. 流 (Streams)

```rust
use futures::stream::{self, StreamExt};

async fn stream_example() {
    let mut stream = stream::iter(vec![1, 2, 3]);

    while let Some(value) = stream.next().await {
        println!("{}", value);
    }
}
```
