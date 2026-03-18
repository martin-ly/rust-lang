# async/await 异步编程

> **编写非阻塞异步代码**
> **预计时间**: 8 小时

## 🎯 学习目标

- [ ] 理解 async/await 语法
- [ ] 使用 Future trait
- [ ] 选择合适的运行时
- [ ] 处理异步错误

## 📋 先决条件

- 理解所有权和生命周期
- 了解闭包和 trait

## 🧠 核心概念

### 1. async/await 基础

```rust
async fn say_hello() {
    println!("Hello");
}

#[tokio::main]
async fn main() {
    say_hello().await;
}
```

### 2. 并发执行

```rust
use tokio::join;

async fn fetch_all() {
    let (user, order) = join!(
        fetch_user(),
        fetch_order(),
    );
}
```

### 3. select! 宏

```rust
use tokio::select;

select! {
    result = slow_op() => { }
    _ = timeout() => { }
}
```

## 📖 延伸阅读

- [Async Book](https://rust-lang.github.io/async-book/)
