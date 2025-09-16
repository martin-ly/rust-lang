/*
Sync trait 是 Rust 中用于线程间安全共享引用的重要特征。
它标记一个类型可以安全地跨线程边界共享不可变引用。

## 定义

Sync trait 是一个标记特征：

```rust
pub unsafe trait Sync { }
```

## 重要特性

1. **线程安全共享**: 标记类型可以安全地跨线程共享引用
2. **不可变引用**: 允许多个线程同时持有不可变引用
3. **自动派生**: 大多数类型自动实现 Sync
4. **unsafe**: 需要手动实现，编译器无法自动验证安全性

## 实现条件

类型要实现 Sync trait，必须满足以下条件：

1. **线程安全**: 类型的所有字段都必须是线程安全的
2. **无内部可变性**: 不能包含非线程安全的内部可变性
3. **无静态引用**: 不能包含非线程安全的静态引用
4. **无原始指针**: 不能包含非线程安全的原始指针

## 与 Send 的关系

- **Send**: 允许类型的所有权在线程间转移
- **Sync**: 允许类型的引用在线程间共享
- 如果一个类型实现了 Sync，那么 `&T` 必须实现 Send
- 大多数情况下，如果 `T: Send`，那么 `T: Sync`

## 实现示例

### 1. 基本类型自动实现 Sync

```rust
// 这些类型自动实现 Sync
struct SafeType {
    value: i32,
    name: String,
    active: bool,
}

// 编译器自动为 SafeType 实现 Sync
// 因为所有字段都实现了 Sync
```

### 2. 泛型类型实现 Sync

```rust
struct Container<T: Sync> {
    value: T,
    metadata: String,
}

// 编译器自动为 Container<T> 实现 Sync
// 因为 T: Sync 且 String 实现了 Sync
```

### 3. 手动实现 Sync

```rust
struct CustomType {
    data: Vec<u8>,
    counter: std::sync::atomic::AtomicUsize,
}

// 手动实现 Sync（通常是安全的）
unsafe impl Sync for CustomType { }
```

## 使用场景

### 1. 线程间共享不可变数据

```rust
use std::thread;
use std::sync::Arc;

fn main() {
    let data = Arc::new(vec![1, 2, 3, 4, 5]);

    let handles: Vec<_> = (0..3).map(|id| {
        let data = Arc::clone(&data);
        thread::spawn(move || {
            println!("Thread {}: data length = {}", id, data.len());
            // 多个线程可以同时读取 data
        })
    }).collect();

    for handle in handles {
        handle.join().unwrap();
    }
}
```

### 2. 全局配置共享

```rust
use std::sync::Arc;
use std::thread;

struct Config {
    max_threads: usize,
    timeout: u64,
    debug: bool,
}

// 全局配置，多个线程共享
static GLOBAL_CONFIG: once_cell::sync::Lazy<Arc<Config>> =
    once_cell::sync::Lazy::new(|| {
        Arc::new(Config {
            max_threads: 4,
            timeout: 30,
            debug: true,
        })
    });

fn main() {
    let handles: Vec<_> = (0..3).map(|id| {
        let config = Arc::clone(&GLOBAL_CONFIG);
        thread::spawn(move || {
            println!("Thread {}: max_threads = {}", id, config.max_threads);
            println!("Thread {}: timeout = {}", id, config.timeout);
        })
    }).collect();

    for handle in handles {
        handle.join().unwrap();
    }
}
```

### 3. 只读缓存共享

```rust
use std::collections::HashMap;
use std::sync::Arc;
use std::thread;

struct Cache {
    data: HashMap<String, String>,
}

impl Cache {
    fn new() -> Self {
        let mut cache = HashMap::new();
        cache.insert("key1".to_string(), "value1".to_string());
        cache.insert("key2".to_string(), "value2".to_string());
        Cache { data: cache }
    }

    fn get(&self, key: &str) -> Option<&String> {
        self.data.get(key)
    }
}

fn main() {
    let cache = Arc::new(Cache::new());

    let handles: Vec<_> = (0..3).map(|id| {
        let cache = Arc::clone(&cache);
        thread::spawn(move || {
            if let Some(value) = cache.get("key1") {
                println!("Thread {}: key1 = {}", id, value);
            }
            if let Some(value) = cache.get("key2") {
                println!("Thread {}: key2 = {}", id, value);
            }
        })
    }).collect();

    for handle in handles {
        handle.join().unwrap();
    }
}
```

## 常见不实现 Sync 的类型

### 1. Rc<T>

```rust
use std::rc::Rc;

// Rc<T> 不实现 Sync，因为引用计数不是线程安全的
// let data = Rc::new(vec![1, 2, 3]);
// thread::spawn(move || {
//     println!("{:?}", data); // 编译错误！
// });
```

### 2. Cell<T> 和 RefCell<T>

```rust
use std::cell::{Cell, RefCell};

// Cell<T> 和 RefCell<T> 不实现 Sync
// let data = RefCell::new(vec![1, 2, 3]);
// thread::spawn(move || {
//     data.borrow_mut().push(4); // 编译错误！
// });
```

### 3. 原始指针

```rust
// 原始指针不实现 Sync，除非手动实现
// let ptr: *const i32 = std::ptr::null();
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

    let handles: Vec<_> = (0..3).map(|_| {
        let data = Arc::clone(&data);
        thread::spawn(move || {
            println!("Data in thread: {:?}", data);
        })
    }).collect();

    for handle in handles {
        handle.join().unwrap();
    }
}
```

### 2. Mutex<T> 替代 RefCell<T>

```rust
use std::sync::{Arc, Mutex};

fn main() {
    let data = Arc::new(Mutex::new(vec![1, 2, 3]));

    let handles: Vec<_> = (0..3).map(|id| {
        let data = Arc::clone(&data);
        thread::spawn(move || {
            let mut guard = data.lock().unwrap();
            guard.push(id + 10);
            println!("Thread {}: data = {:?}", id, guard);
        })
    }).collect();

    for handle in handles {
        handle.join().unwrap();
    }
}
```

### 3. RwLock<T> 用于读写分离

```rust
use std::sync::{Arc, RwLock};

fn main() {
    let data = Arc::new(RwLock::new(vec![1, 2, 3, 4, 5]));

    // 多个读取线程
    let read_handles: Vec<_> = (0..3).map(|id| {
        let data = Arc::clone(&data);
        thread::spawn(move || {
            let guard = data.read().unwrap();
            println!("Reader {}: data = {:?}", id, *guard);
        })
    }).collect();

    // 一个写入线程
    let write_handle = {
        let data = Arc::clone(&data);
        thread::spawn(move || {
            let mut guard = data.write().unwrap();
            guard.push(100);
            println!("Writer: added 100, data = {:?}", *guard);
        })
    };

    for handle in read_handles {
        handle.join().unwrap();
    }
    write_handle.join().unwrap();
}
```

## 性能考虑

1. **零成本**: Sync 标记本身是零成本的
2. **引用共享**: 允许多个线程同时读取，提高并发性能
3. **内存屏障**: 了解原子操作的内存屏障影响
4. **锁竞争**: 使用适当的锁策略避免竞争

## 最佳实践

1. **安全性**: 确保 Sync 实现是真正线程安全的
2. **性能**: 使用适当的线程安全原语
3. **测试**: 为多线程场景编写测试
4. **文档**: 明确说明线程安全保证

## 高级用法

### 1. 条件 Sync 实现

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

// 只有在 T: Sync 时才实现 Sync
unsafe impl<T: Sync> Sync for ConditionalType<T> { }
```

### 2. 组合 Sync 类型

```rust
struct CompositeType {
    safe_field: String,
    atomic_field: std::sync::atomic::AtomicBool,
    mutex_field: std::sync::Mutex<i32>,
}

// 手动实现 Sync
unsafe impl Sync for CompositeType { }
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

// 手动实现 Sync
unsafe impl Sync for CustomAtomic { }
```

## 总结

Sync trait 为 Rust 提供了线程间安全共享引用的基础。
通过正确实现 Sync，可以创建线程安全的代码，
同时需要注意安全性和性能影响。
*/

use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, RwLock};
use std::thread;

// 基本类型自动实现 Sync
#[derive(Debug)]
pub struct SyncExample {
    pub name: String,
    pub value: i32,
    pub active: bool,
}

// 编译器自动为 SyncExample 实现 Sync
// 因为所有字段都实现了 Sync

// 泛型容器
#[derive(Debug)]
pub struct SyncContainer<T: Sync> {
    pub value: T,
    pub metadata: String,
}

// 编译器自动为 SyncContainer<T> 实现 Sync
// 因为 T: Sync 且 String 实现了 Sync

// 手动实现 Sync 的类型
pub struct CustomSyncType {
    pub data: Vec<u8>,
    pub counter: AtomicUsize,
    pub flag: AtomicBool,
}

// 手动实现 Sync（通常是安全的）
unsafe impl Sync for CustomSyncType {}

// 线程安全的数据结构
#[derive(Debug)]
pub struct ThreadSafeData {
    pub values: Arc<Vec<i32>>,
    pub counter: AtomicUsize,
    pub active: AtomicBool,
}

// 手动实现 Sync
unsafe impl Sync for ThreadSafeData {}

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
pub fn demonstrate_sync() {
    println!("=== Sync Trait Demonstration ===\n");

    // 基本线程间数据共享
    demonstrate_basic_sharing();

    // 只读数据共享
    demonstrate_readonly_sharing();

    // 读写锁使用
    demonstrate_rwlock_usage();

    // 原子操作共享
    demonstrate_atomic_sharing();

    // 自定义线程安全类型
    demonstrate_custom_sync();
}

// 基本线程间数据共享
fn demonstrate_basic_sharing() {
    println!("--- Basic Data Sharing ---");

    let data = Arc::new(SyncExample {
        name: "Shared Data".to_string(),
        value: 42,
        active: true,
    });

    println!("Original data: {:?}", data);

    let handles: Vec<_> = (0..3)
        .map(|id| {
            let data = Arc::clone(&data);
            thread::spawn(move || {
                println!("Thread {}: data = {:?}", id, data);
            })
        })
        .collect();

    for handle in handles {
        handle.join().unwrap();
    }
    println!();
}

// 只读数据共享
fn demonstrate_readonly_sharing() {
    println!("--- Read-Only Data Sharing ---");

    let cache = Arc::new(vec![1, 2, 3, 4, 5]);

    let handles: Vec<_> = (0..3)
        .map(|id| {
            let cache = Arc::clone(&cache);
            thread::spawn(move || {
                println!("Thread {}: cache length = {}", id, cache.len());
                println!("Thread {}: first value = {}", id, cache[0]);
                println!("Thread {}: last value = {}", id, cache[cache.len() - 1]);
            })
        })
        .collect();

    for handle in handles {
        handle.join().unwrap();
    }
    println!();
}

// 读写锁使用
fn demonstrate_rwlock_usage() {
    println!("--- Read-Write Lock Usage ---");

    let data = Arc::new(RwLock::new(vec![1, 2, 3, 4, 5]));

    // 多个读取线程
    let read_handles: Vec<_> = (0..3)
        .map(|id| {
            let data = Arc::clone(&data);
            thread::spawn(move || {
                let guard = data.read().unwrap();
                println!("Reader {}: data = {:?}", id, *guard);
            })
        })
        .collect();

    // 一个写入线程
    let write_handle = {
        let data = Arc::clone(&data);
        thread::spawn(move || {
            let mut guard = data.write().unwrap();
            guard.push(100);
            println!("Writer: added 100, data = {:?}", *guard);
        })
    };

    for handle in read_handles {
        handle.join().unwrap();
    }
    write_handle.join().unwrap();
    println!();
}

// 原子操作共享
fn demonstrate_atomic_sharing() {
    println!("--- Atomic Operations Sharing ---");

    let shared_counter = Arc::new(AtomicUsize::new(0));

    let handles: Vec<_> = (0..5)
        .map(|_| {
            let counter = Arc::clone(&shared_counter);
            thread::spawn(move || {
                for _ in 0..100 {
                    counter.fetch_add(1, Ordering::Relaxed);
                }
            })
        })
        .collect();

    for handle in handles {
        handle.join().unwrap();
    }

    println!(
        "Final shared counter: {}",
        shared_counter.load(Ordering::Relaxed)
    );
    println!();
}

// 自定义线程安全类型
fn demonstrate_custom_sync() {
    println!("--- Custom Sync Types ---");

    let custom_data = CustomSyncType {
        data: vec![1, 2, 3, 4, 5],
        counter: AtomicUsize::new(0),
        flag: AtomicBool::new(false),
    };

    let shared_data = Arc::new(custom_data);

    let handles: Vec<_> = (0..3)
        .map(|id| {
            let data = Arc::clone(&shared_data);
            thread::spawn(move || {
                println!("Thread {}: data length = {}", id, data.data.len());
                println!(
                    "Thread {}: counter = {}",
                    id,
                    data.counter.load(Ordering::Relaxed)
                );
                println!(
                    "Thread {}: flag = {}",
                    id,
                    data.flag.load(Ordering::Relaxed)
                );

                // 修改原子字段
                data.counter.fetch_add(id + 1, Ordering::Relaxed);
                data.flag.store(true, Ordering::Relaxed);
            })
        })
        .collect();

    for handle in handles {
        handle.join().unwrap();
    }

    let final_data = shared_data.as_ref();
    println!("Final state:");
    println!(
        "  - Counter: {}",
        final_data.counter.load(Ordering::Relaxed)
    );
    println!("  - Flag: {}", final_data.flag.load(Ordering::Relaxed));
    println!();
}

// 测试函数
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sync_example() {
        let data = SyncExample {
            name: "Test".to_string(),
            value: 100,
            active: false,
        };

        assert_eq!(data.name, "Test");
        assert_eq!(data.value, 100);
        assert!(!data.active);

        // 测试可以跨线程共享引用
        let shared_data = Arc::new(data);
        let handle = thread::spawn(move || {
            assert_eq!(shared_data.name, "Test");
            assert_eq!(shared_data.value, 100);
            assert!(!shared_data.active);
        });

        handle.join().unwrap();
    }

    #[test]
    fn test_sync_container() {
        let container = SyncContainer {
            value: 42,
            metadata: "Test".to_string(),
        };

        assert_eq!(container.value, 42);
        assert_eq!(container.metadata, "Test");

        // 测试可以跨线程共享引用
        let shared_container = Arc::new(container);
        let handle = thread::spawn(move || {
            assert_eq!(shared_container.value, 42);
            assert_eq!(shared_container.metadata, "Test");
        });

        handle.join().unwrap();
    }

    #[test]
    fn test_custom_sync_type() {
        let custom = CustomSyncType {
            data: vec![1, 2, 3],
            counter: AtomicUsize::new(0),
            flag: AtomicBool::new(false),
        };

        assert_eq!(custom.data.len(), 3);
        assert_eq!(custom.counter.load(Ordering::Relaxed), 0);
        assert!(!custom.flag.load(Ordering::Relaxed));

        // 测试可以跨线程共享引用
        let shared_custom = Arc::new(custom);
        let handle = thread::spawn(move || {
            assert_eq!(shared_custom.data.len(), 3);
            shared_custom.counter.fetch_add(1, Ordering::Relaxed);
            shared_custom.flag.store(true, Ordering::Relaxed);
        });

        handle.join().unwrap();
    }

    #[test]
    fn test_thread_safe_data() {
        let data = ThreadSafeData::new(vec![1, 2, 3]);

        assert_eq!(data.values.len(), 3);
        assert_eq!(data.get_count(), 0);
        assert!(data.is_active());

        // 测试可以跨线程共享引用
        let shared_data = Arc::new(data);
        let handle = thread::spawn(move || {
            assert_eq!(shared_data.values.len(), 3);
            shared_data.increment();
            shared_data.set_active(false);
        });

        handle.join().unwrap();
    }
}
