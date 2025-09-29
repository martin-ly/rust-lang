# 异步编程与Future（Async Programming & Future）  

## 1. 定义与软件工程对标  

**异步编程**允许任务在等待I/O或其他事件时让出控制权，提高资源利用率。软件工程wiki认为，异步是高并发系统的关键能力。  
**Async programming** enables tasks to yield control while waiting for I/O or events, improving resource utilization. In software engineering, async is key for high-concurrency systems.

## 2. Rust 1.88 最新特性  

- **`async fn in traits`**：trait原生支持async方法，极大简化异步抽象。
- **select!宏增强**：多路异步任务调度更灵活。
- **主流运行时tokio/async-std**：生态完善，支持高性能异步。

## 3. 典型惯用法（Idioms）  

- 使用 `async fn`/`await` 编写异步逻辑
- `tokio::spawn`/`async-std::task::spawn` 启动异步任务
- `select!` 宏实现多路复用
- `mpsc`/`oneshot` channel 进行异步通信

## 4. 代码示例（含1.88新特性）  

```rust
// async fn in traits
trait AsyncJob {
    async fn run(&self);
}

// select! 宏
use tokio::select;
async fn foo() {}
async fn bar() {}
select! {
    _ = foo() => println!("foo done"),
    _ = bar() => println!("bar done"),
}
```

## 5. 软件工程概念对照  

- **非阻塞（Non-blocking）**：async/await 保证任务切换无阻塞。
- **事件驱动（Event-driven）**：异步模型天然适合事件驱动架构。
- **高并发（High Concurrency）**：异步+多线程可支撑大规模并发。

## 6. FAQ  

- Q: Rust异步和多线程的区别？  
  A: 异步关注任务切换，多线程关注物理并行，二者可结合。

---
