# 并发程序逻辑

## 1. 并发分离逻辑理论基础

- **并发分离逻辑（Concurrent Separation Logic, CSL）**：扩展分离逻辑以支持多线程程序的局部推理。
- **资源不变式**：每个线程只能访问其拥有的资源，资源转移需满足同步原语约束。
- **原子性**：并发操作要么全部完成，要么全部不做，保证一致性。

## 2. 数据竞争免疫与原子性

- **数据竞争免疫**：类型系统与分离逻辑共同保证同一时刻只有一个线程可写资源，或多个线程只读。
- **原子操作**：如 `AtomicUsize`、`Mutex`，通过类型和同步原语保证原子性。

## 3. Rust并发安全的形式化建模

- **Send/Sync Trait**：类型系统标记线程安全能力。
- **分离逻辑断言**：建模线程间资源分配与同步。
- **RustBelt/Iris**：用高阶并发分离逻辑机械化证明标准库并发原语的安全性。

## 4. 形式化推理与代码示例

```rust
use std::sync::{Arc, Mutex};
use std::thread;

fn main() {
    let counter = Arc::new(Mutex::new(0));
    let mut handles = vec![];
    for _ in 0..10 {
        let counter = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            let mut num = counter.lock().unwrap();
            *num += 1;
        });
        handles.push(handle);
    }
    for handle in handles {
        handle.join().unwrap();
    }
    println!("Result: {}", *counter.lock().unwrap());
}
// 分离逻辑断言：每次加锁后，只有一个线程拥有对num的独占访问权
```

## 5. 工程意义与工具应用

- **优势**：为并发程序的安全性、无数据竞争和原子性提供可验证基础。
- **工具**：RustBelt、Iris、Prusti等支持并发分离逻辑的验证。

## 6. 参考文献

1. O'Hearn, P. W. (2007). Resources, concurrency, and local reasoning. Theoretical Computer Science.
2. Jung, R., Jourdan, J. H., Krebbers, R., & Dreyer, D. (2017). RustBelt: Securing the foundations of the Rust programming language. POPL 2018.
3. Rust官方文档：Concurrency, Send, Sync。 