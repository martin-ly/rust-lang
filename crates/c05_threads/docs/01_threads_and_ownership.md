# 01. 线程与所有权 (Threads and Ownership)

并发 (Concurrency) 是指程序的多个部分独立、无序执行的能力。在 Rust 中，并发编程的基石是操作系统线程，而其安全性的核心保障则来自于所有权系统。

## 目录

- [01. 线程与所有权 (Threads and Ownership)](#01-线程与所有权-threads-and-ownership)
  - [目录](#目录)
  - [1.1. 创建新线程: `thread::spawn`](#11-创建新线程-threadspawn)
  - [1.2. `move` 闭包与所有权](#12-move-闭包与所有权)

## 1.1. 创建新线程: `thread::spawn`

Rust 标准库通过 `std::thread::spawn` 函数提供了创建新线程的 API。`spawn` 函数接受一个闭包 (closure) 作为参数，这个闭包包含了新线程需要执行的代码。

```rust
use std::thread;
use std::time::Duration;

fn main() {
    // 创建一个新线程
    let handle = thread::spawn(|| {
        for i in 1..=5 {
            println!("hi number {} from the spawned thread!", i);
            thread::sleep(Duration::from_millis(1));
        }
    });

    // 主线程的代码会继续执行
    for i in 1..=3 {
        println!("hi number {} from the main thread!", i);
        thread::sleep(Duration::from_millis(1));
    }

    // 等待新线程执行完毕
    handle.join().unwrap();
}
```

`thread::spawn` 会返回一个 `JoinHandle`。这个 `JoinHandle` 是一个拥有所有权的值，调用它的 `join()` 方法可以阻塞当前线程，直到 `spawn` 出来的线程执行结束。

## 1.2. `move` 闭包与所有权

在线程之间传递数据是并发编程的核心挑战。Rust 的所有权系统在这里发挥了至关重要的作用，它能防止数据竞争 (data races) 等常见的并发 bug。

当你尝试在线程中使用来自主线程环境的变量时，必须将这些变量的所有权**移动 (move)** 到新线程中。这是通过在闭包前使用 `move` 关键字来实现的。

**为什么必须 `move`？**
Rust 编译器无法预知新线程会执行多久。如果新线程只是借用 (borrow) 数据，那么在它执行期间，主线程可能会结束，导致被借用的数据被释放，从而产生悬垂引用 (dangling reference)。为了保证内存安全，编译器强制要求将所有权转移给新线程，确保数据在新线程的整个生命周期内都是有效的。

**示例**:

```rust
use std::thread;

fn main() {
    let v = vec![1, 2, 3];

    // 使用 `move` 关键字强制闭包获得 `v` 的所有权
    let handle = thread::spawn(move || {
        // 现在闭包拥有 `v`，可以安全地使用它
        println!("Here's a vector: {:?}", v);
    });

    // 此时 `v` 的所有权已经转移，主线程无法再使用它
    // drop(v); // 这行代码会导致编译错误

    handle.join().unwrap();
}
```

`move` 关键字确保了 `v` 与新线程一同存活，从而在编译时就杜绝了潜在的内存安全问题。这种将所有权与线程生命周期绑定的机制，是 Rust "无畏并发" (Fearless Concurrency) 的核心体现。

---

**章节导航:**

- **下一章 ->** `02_message_passing.md`: 探讨如何使用通道在线程间安全地传递消息。
- **返回目录 ->** `_index.md`
