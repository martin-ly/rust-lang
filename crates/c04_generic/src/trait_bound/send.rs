/*
Send trait 是 Rust 中用于线程间安全传递的重要特征。
它标记一个类型可以安全地跨线程边界转移所有权。

## 定义

Send trait 是一个标记特征：

```rust
pub unsafe trait Send { }
```

## 重要特性

1. **线程安全**: 标记类型可以安全地跨线程传递
2. **所有权转移**: 允许类型的所有权在线程间转移
3. **自动派生**: 大多数类型自动实现 Send
4. **unsafe**: 需要手动实现，编译器无法自动验证安全性

## 实现条件

类型要实现 Send trait，必须满足以下条件：

1. **线程安全**: 类型的所有字段都必须是线程安全的
2. **无内部可变性**: 不能包含非线程安全的内部可变性
3. **无静态引用**: 不能包含非线程安全的静态引用
4. **无原始指针**: 不能包含非线程安全的原始指针

## 实现示例

### 1. 基本类型自动实现 Send

```rust
// 这些类型自动实现 Send
struct SafeType {
    value: i32,
    name: String,
    active: bool,
}

// 编译器自动为 SafeType 实现 Send
// 因为所有字段都实现了 Send
```

### 2. 泛型类型实现 Send

```rust
struct Container<T: Send> {
    value: T,
    metadata: String,
}

// 编译器自动为 Container<T> 实现 Send
// 因为 T: Send 且 String 实现了 Send
```

### 3. 手动实现 Send

```rust
struct CustomType {
    data: Vec<u8>,
    counter: std::sync::atomic::AtomicUsize,
}

// 手动实现 Send（通常是安全的）
unsafe impl Send for CustomType { }
```

## 使用场景

### 1. 线程间数据传递

```rust
use std::thread;

fn main() {
    let data = vec![1, 2, 3, 4, 5];

    // 将数据移动到新线程
    let handle = thread::spawn(move || {
        println!("Received data: {:?}", data);
        // 处理数据
    });

    // 等待线程完成
    handle.join().unwrap();
}
```

### 2. 通道通信

```rust
use std::sync::mpsc;
use std::thread;

fn main() {
    let (tx, rx) = mpsc::channel();

    // 发送线程
    let sender = thread::spawn(move || {
        let data = vec![1, 2, 3, 4, 5];
        tx.send(data).unwrap();
    });

    // 接收线程
    let receiver = thread::spawn(move || {
        let received = rx.recv().unwrap();
        println!("Received: {:?}", received);
    });

    sender.join().unwrap();
    receiver.join().unwrap();
}
```

### 3. 异步任务

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

struct AsyncTask {
    data: Vec<i32>,
}

impl Future for AsyncTask {
    type Output = Vec<i32>;

    fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Self::Output> {
        Poll::Ready(self.data.clone())
    }
}

// AsyncTask 需要实现 Send 才能在异步运行时中使用
unsafe impl Send for AsyncTask { }
```

## 常见不实现 Send 的类型

### 1. Rc<T>

```rust
use std::rc::Rc;

// Rc<T> 不实现 Send，因为引用计数不是线程安全的
// let data = Rc::new(vec![1, 2, 3]);
// thread::spawn(move || {
//     println!("{:?}", data); // 编译错误！
// });
```

### 2. Cell<T> 和 RefCell<T>

```rust
use std::cell::{Cell, RefCell};

// Cell<T> 和 RefCell<T> 不实现 Send
// let data = RefCell::new(vec![1, 2, 3]);
// thread::spawn(move || {
//     data.borrow_mut().push(4); // 编译错误！
// });
```

### 3. 原始指针

```rust
// 原始指针不实现 Send，除非手动实现
// let ptr: *mut i32 = std::ptr::null_mut();
// thread::spawn(move || {
//     // 使用 ptr // 编译错误！
// });
```

## 线程安全替代方案

### 1. Arc<T> 替代 Rc<T>

```rust
use std::sync::Arc;

fn main() {
    let data = Arc::new(vec![1, 2, 3, 4, 5]);

    // 克隆 Arc 引用
    let data_clone = Arc::clone(&data);

    let handle = thread::spawn(move || {
        println!("Data in thread: {:?}", data_clone);
    });

    handle.join().unwrap();
    println!("Original data: {:?}", data);
}
```

### 2. Mutex<T> 替代 RefCell<T>

```rust
use std::sync::Mutex;

fn main() {
    let data = Mutex::new(vec![1, 2, 3]);

    let handle = thread::spawn(move || {
        let mut guard = data.lock().unwrap();
        guard.push(4);
        println!("Modified data: {:?}", guard);
    });

    handle.join().unwrap();
}
```

### 3. Atomic 类型

```rust
use std::sync::atomic::{AtomicUsize, Ordering};

fn main() {
    let counter = AtomicUsize::new(0);

    let handles: Vec<_> = (0..10).map(|_| {
        let counter = &counter;
        thread::spawn(move || {
            for _ in 0..100 {
                counter.fetch_add(1, Ordering::Relaxed);
            }
        })
    }).collect();

    for handle in handles {
        handle.join().unwrap();
    }

    println!("Final count: {}", counter.load(Ordering::Relaxed));
}
```

## 性能考虑

1. **零成本**: Send 标记本身是零成本的
2. **线程安全**: 确保线程安全操作的性能
3. **内存屏障**: 了解原子操作的内存屏障影响
4. **锁竞争**: 避免不必要的锁竞争

## 最佳实践

1. **安全性**: 确保 Send 实现是真正线程安全的
2. **性能**: 使用适当的线程安全原语
3. **测试**: 为多线程场景编写测试
4. **文档**: 明确说明线程安全保证

## 高级用法

### 1. 条件 Send 实现

```rust
struct ConditionalType<T> {
    data: T,
    thread_safe: bool,
}

impl<T> ConditionalType<T> {
    fn new(data: T, thread_safe: bool) -> Self {
        ConditionalType { data, thread_safe }
    }
}

// 只有在 T: Send 时才实现 Send
unsafe impl<T: Send> Send for ConditionalType<T> { }
```

### 2. 组合 Send 类型

```rust
struct CompositeType {
    safe_field: String,
    atomic_field: std::sync::atomic::AtomicBool,
    mutex_field: std::sync::Mutex<i32>,
}

// 手动实现 Send
unsafe impl Send for CompositeType { }
```

### 3. 自定义线程安全类型

```rust
use std::sync::atomic::{AtomicBool, Ordering};

struct CustomAtomic {
    value: AtomicBool,
}

impl CustomAtomic {
    fn new(initial: bool) -> Self {
        CustomAtomic {
            value: AtomicBool::new(initial),
        }
    }

    fn set(&self, value: bool) {
        self.value.store(value, Ordering::Relaxed);
    }

    fn get(&self) -> bool {
        self.value.load(Ordering::Relaxed)
    }
}

// 手动实现 Send
unsafe impl Send for CustomAtomic { }
```

## 总结

Send trait 为 Rust 提供了线程间安全传递的基础。
通过正确实现 Send，可以创建线程安全的代码，
同时需要注意安全性和性能影响。
*/

use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, mpsc};
use std::thread;

// 基本类型自动实现 Send
#[derive(Debug)]
pub struct SendExample {
    pub name: String,
    pub value: i32,
    pub active: bool,
}

// 编译器自动为 SendExample 实现 Send
// 因为所有字段都实现了 Send

// 泛型容器
#[derive(Debug)]
pub struct SendContainer<T: Send> {
    pub value: T,
    pub metadata: String,
}

// 编译器自动为 SendContainer<T> 实现 Send
// 因为 T: Send 且 String 实现了 Send

// 手动实现 Send 的类型
pub struct CustomSendType {
    pub data: Vec<u8>,
    pub counter: AtomicUsize,
    pub flag: AtomicBool,
}

// 手动实现 Send（通常是安全的）
unsafe impl Send for CustomSendType {}

// 线程安全的数据结构
#[derive(Debug)]
pub struct ThreadSafeData {
    pub values: Arc<Vec<i32>>,
    pub counter: AtomicUsize,
    pub active: AtomicBool,
}

// 手动实现 Send
unsafe impl Send for ThreadSafeData {}

impl ThreadSafeData {
    pub fn new(values: Vec<i32>) -> Self {
        ThreadSafeData {
            values: Arc::new(values),
            counter: AtomicUsize::new(0),
            active: AtomicBool::new(true),
        }
    }

    pub fn increment(&self) {
        self.counter.fetch_add(1, Ordering::Relaxed);
    }

    pub fn get_count(&self) -> usize {
        self.counter.load(Ordering::Relaxed)
    }

    pub fn set_active(&self, active: bool) {
        self.active.store(active, Ordering::Relaxed);
    }

    pub fn is_active(&self) -> bool {
        self.active.load(Ordering::Relaxed)
    }
}

// 演示函数
pub fn demonstrate_send() {
    println!("=== Send Trait Demonstration ===\n");

    // 基本线程间数据传递
    demonstrate_basic_threading();

    // 通道通信
    demonstrate_channel_communication();

    // 共享状态
    demonstrate_shared_state();

    // 原子操作
    demonstrate_atomic_operations();

    // 自定义线程安全类型
    demonstrate_custom_send();
}

// 基本线程间数据传递
fn demonstrate_basic_threading() {
    println!("--- Basic Threading ---");

    let data = SendExample {
        name: "Thread Data".to_string(),
        value: 42,
        active: true,
    };

    println!("Original data: {:?}", data);

    // 将数据移动到新线程
    let handle = thread::spawn(move || {
        println!("Data in thread: {:?}", data);
        // 处理数据
    });

    // 等待线程完成
    handle.join().unwrap();
    println!();
}

// 通道通信
fn demonstrate_channel_communication() {
    println!("--- Channel Communication ---");

    let (tx, rx) = mpsc::channel();

    // 发送线程
    let sender = thread::spawn(move || {
        let data = vec![1, 2, 3, 4, 5];
        println!("Sending data: {:?}", data);
        tx.send(data).unwrap();
    });

    // 接收线程
    let receiver = thread::spawn(move || {
        let received = rx.recv().unwrap();
        println!("Received data: {:?}", received);
    });

    sender.join().unwrap();
    receiver.join().unwrap();
    println!();
}

// 共享状态
fn demonstrate_shared_state() {
    println!("--- Shared State ---");

    let shared_data = Arc::new(Mutex::new(vec![1, 2, 3, 4, 5]));

    let handles: Vec<_> = (0..3)
        .map(|id| {
            let data = Arc::clone(&shared_data);
            thread::spawn(move || {
                let mut guard = data.lock().unwrap();
                guard.push(id + 10);
                println!("Thread {} added value, data: {:?}", id, guard);
            })
        })
        .collect();

    for handle in handles {
        handle.join().unwrap();
    }

    let final_data = shared_data.lock().unwrap();
    println!("Final shared data: {:?}", final_data);
    println!();
}

// 原子操作
fn demonstrate_atomic_operations() {
    println!("--- Atomic Operations ---");

    // 使用静态原子计数器来避免生命周期问题
    static COUNTER: AtomicUsize = AtomicUsize::new(0);

    let handles: Vec<_> = (0..5)
        .map(|_| {
            thread::spawn(move || {
                for _ in 0..100 {
                    COUNTER.fetch_add(1, Ordering::Relaxed);
                }
            })
        })
        .collect();

    for handle in handles {
        handle.join().unwrap();
    }

    println!("Final atomic count: {}", COUNTER.load(Ordering::Relaxed));
    println!();
}

// 自定义线程安全类型
fn demonstrate_custom_send() {
    println!("--- Custom Send Types ---");

    let custom_data = CustomSendType {
        data: vec![1, 2, 3, 4, 5],
        counter: AtomicUsize::new(0),
        flag: AtomicBool::new(false),
    };

    let thread_data = custom_data;

    let handle = thread::spawn(move || {
        println!("Custom data in thread:");
        println!("  - Data length: {}", thread_data.data.len());
        println!(
            "  - Counter: {}",
            thread_data.counter.load(Ordering::Relaxed)
        );
        println!("  - Flag: {}", thread_data.flag.load(Ordering::Relaxed));

        // 修改原子字段
        thread_data.counter.fetch_add(10, Ordering::Relaxed);
        thread_data.flag.store(true, Ordering::Relaxed);

        println!("  - After modification:");
        println!(
            "    Counter: {}",
            thread_data.counter.load(Ordering::Relaxed)
        );
        println!("    Flag: {}", thread_data.flag.load(Ordering::Relaxed));
    });

    handle.join().unwrap();
    println!();
}

// 线程安全的数据处理示例
pub fn demonstrate_thread_safe_processing() {
    println!("--- Thread Safe Processing ---");

    let thread_safe_data = ThreadSafeData::new(vec![1, 2, 3, 4, 5]);

    // 创建Arc包装的数据用于在线程间共享
    let shared_data = Arc::new(thread_safe_data);

    let handles: Vec<_> = (0..3)
        .map(|id| {
            let data = Arc::clone(&shared_data);
            thread::spawn(move || {
                println!("Thread {} processing data", id);

                // 访问共享数据
                let values = &data.values;
                println!("  - Values: {:?}", values);

                // 修改原子字段
                data.increment();
                data.set_active(id % 2 == 0);

                println!("  - Counter: {}", data.get_count());
                println!("  - Active: {}", data.is_active());
            })
        })
        .collect();

    for handle in handles {
        handle.join().unwrap();
    }

    // 从Arc中获取数据来访问最终状态
    let final_data = shared_data.as_ref();
    println!("Final state:");
    println!("  - Counter: {}", final_data.get_count());
    println!("  - Active: {}", final_data.is_active());
}

// 测试函数
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_send_example() {
        let data = SendExample {
            name: "Test".to_string(),
            value: 100,
            active: false,
        };

        assert_eq!(data.name, "Test");
        assert_eq!(data.value, 100);
        assert!(!data.active);

        // 测试可以移动到线程
        let handle = thread::spawn(move || {
            assert_eq!(data.name, "Test");
            assert_eq!(data.value, 100);
            assert!(!data.active);
        });

        handle.join().unwrap();
    }

    #[test]
    fn test_send_container() {
        let container = SendContainer {
            value: 42,
            metadata: "Test".to_string(),
        };

        assert_eq!(container.value, 42);
        assert_eq!(container.metadata, "Test");

        // 测试可以移动到线程
        let handle = thread::spawn(move || {
            assert_eq!(container.value, 42);
            assert_eq!(container.metadata, "Test");
        });

        handle.join().unwrap();
    }

    #[test]
    fn test_custom_send_type() {
        let custom = CustomSendType {
            data: vec![1, 2, 3],
            counter: AtomicUsize::new(0),
            flag: AtomicBool::new(false),
        };

        assert_eq!(custom.data.len(), 3);
        assert_eq!(custom.counter.load(Ordering::Relaxed), 0);
        assert!(!custom.flag.load(Ordering::Relaxed));

        // 测试可以移动到线程
        let handle = thread::spawn(move || {
            assert_eq!(custom.data.len(), 3);
            custom.counter.fetch_add(1, Ordering::Relaxed);
            custom.flag.store(true, Ordering::Relaxed);
        });

        handle.join().unwrap();
    }

    #[test]
    fn test_thread_safe_data() {
        let data = ThreadSafeData::new(vec![1, 2, 3]);

        assert_eq!(data.values.len(), 3);
        assert_eq!(data.get_count(), 0);
        assert!(data.is_active());

        // 测试可以移动到线程
        let handle = thread::spawn(move || {
            assert_eq!(data.values.len(), 3);
            data.increment();
            data.set_active(false);
        });

        handle.join().unwrap();
    }
}
