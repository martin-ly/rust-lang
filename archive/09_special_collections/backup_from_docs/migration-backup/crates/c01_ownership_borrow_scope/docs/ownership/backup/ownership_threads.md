# Rust 多线程环境下的所有权模型与设计模式

## 目录

- [Rust 多线程环境下的所有权模型与设计模式](#rust-多线程环境下的所有权模型与设计模式)
  - [目录](#目录)
  - [1. 所有权模型的综合回顾](#1-所有权模型的综合回顾)
    - [1.1 所有权核心概念总结](#11-所有权核心概念总结)
    - [1.2 借用与所有权转换模式](#12-借用与所有权转换模式)
    - [1.3 容器类型的所有权特性](#13-容器类型的所有权特性)
  - [2. 多线程环境下的所有权挑战](#2-多线程环境下的所有权挑战)
    - [2.1 线程安全性基本问题](#21-线程安全性基本问题)
    - [2.2 多线程所有权转移的特殊性](#22-多线程所有权转移的特殊性)
    - [2.3 线程间数据共享的需求与风险](#23-线程间数据共享的需求与风险)
  - [3. 多线程所有权设计模式分类](#3-多线程所有权设计模式分类)
    - [3.1 消息传递模式](#31-消息传递模式)
    - [3.2 共享状态模式](#32-共享状态模式)
    - [3.3 读写分离模式](#33-读写分离模式)
    - [3.4 所有权分区模式](#34-所有权分区模式)
    - [3.5 工作窃取模式](#35-工作窃取模式)
  - [4. 多线程环境下的所有权转移策略](#4-多线程环境下的所有权转移策略)
    - [4.1 跨线程所有权转移](#41-跨线程所有权转移)
    - [4.2 动态借用转所有权](#42-动态借用转所有权)
    - [4.3 线程本地存储与全局共享](#43-线程本地存储与全局共享)
  - [5. 实际应用案例分析](#5-实际应用案例分析)
    - [5.1 高性能工作池设计](#51-高性能工作池设计)
    - [5.2 并发数据处理管道](#52-并发数据处理管道)
    - [5.3 多线程缓存系统](#53-多线程缓存系统)
    - [5.4 实时事件处理框架](#54-实时事件处理框架)
  - [6. 综合设计权衡分析](#6-综合设计权衡分析)
    - [6.1 性能与安全性权衡](#61-性能与安全性权衡)
      - [锁粒度选择](#锁粒度选择)
      - [锁类型选择](#锁类型选择)
      - [克隆与共享的权衡](#克隆与共享的权衡)
    - [6.2 灵活性与复杂性权衡](#62-灵活性与复杂性权衡)
      - [同步模型选择](#同步模型选择)
      - [线程模型选择](#线程模型选择)
    - [6.3 设计决策指南](#63-设计决策指南)
      - [根据数据访问模式选择所有权模型](#根据数据访问模式选择所有权模型)
      - [根据系统特性选择同步原语](#根据系统特性选择同步原语)
      - [任务分解与并行性策略](#任务分解与并行性策略)
  - [7. 总结与最佳实践](#7-总结与最佳实践)
    - [所有权设计原则](#所有权设计原则)
    - [多线程所有权模式总结](#多线程所有权模式总结)
    - [常见陷阱与规避策略](#常见陷阱与规避策略)
    - [最终建议](#最终建议)

## 1. 所有权模型的综合回顾

### 1.1 所有权核心概念总结

所有权系统是 Rust 最核心的特性，尤其在多线程环境中显得尤为重要。它基于以下几个关键概念：

1. **所有权规则**：每个值有唯一的所有者，当所有者离开作用域时值被丢弃
2. **借用机制**：通过引用临时访问数据而不转移所有权
3. **生命周期**：确保引用不会比其引用的数据存活更长时间
4. **移动语义**：非 `Copy` 类型在赋值或传递时转移所有权
5. **复制语义**：实现 `Copy` trait 的类型在赋值或传递时创建值的副本

在多线程环境中，所有权系统还必须考虑：

```rust
// 在单线程环境中合法
fn single_thread_example() {
    let data = vec![1, 2, 3];
    
    let data_ref = &data;
    println!("引用数据: {:?}", data_ref);
    
    // 在同一函数中，我们可以继续使用原始数据
    println!("原始数据: {:?}", data);
}

// 在多线程环境中需特别处理
fn multi_thread_example() {
    let data = vec![1, 2, 3];
    
    // 错误: 无法确定线程存活时间与 data 生命周期的关系
    // let handle = std::thread::spawn(|| {
    //     println!("线程中使用: {:?}", &data);
    // });
    
    // 正确: 将所有权转移到线程中
    let handle = std::thread::spawn(move || {
        println!("线程中使用: {:?}", data);
    });
    
    // data 的所有权已转移到线程
    // println!("原始数据: {:?}", data); // 错误: data 已被移动
    
    handle.join().unwrap();
}
```

### 1.2 借用与所有权转换模式

在单线程和多线程环境中，借用到所有权的转换有不同的处理方式：

| 转换模式 | 单线程实现 | 多线程实现 | 多线程特殊考量 |
|:----:|:----|:----|:----|
| 借用到克隆 | `data.clone()` | `data.clone()` | 需考虑克隆开销和线程边界 |
| 借用到移动 | `std::mem::take()` | 不直接支持跨线程 | 需要通过通道或共享状态 |
| 延迟所有权转移 | `Cow<T>` | `Arc<T>` + 克隆 | 需要额外同步机制 |
| 动态借用检查 | `RefCell<T>` | `Mutex<T>` | 需要处理死锁和争用 |

### 1.3 容器类型的所有权特性

容器类型在多线程环境中的所有权转移尤为复杂：

```rust
use std::sync::{Arc, Mutex};
use std::thread;

fn main() {
    // 在多线程间共享容器
    let shared_data = Arc::new(Mutex::new(vec![1, 2, 3]));
    
    let mut handles = vec![];
    
    for i in 0..3 {
        let data_clone = Arc::clone(&shared_data);
        let handle = thread::spawn(move || {
            // 获取锁并修改数据
            let mut data = data_clone.lock().unwrap();
            data.push(i + 10);
        });
        handles.push(handle);
    }
    
    // 等待所有线程完成
    for handle in handles {
        handle.join().unwrap();
    }
    
    // 查看最终结果
    let result = shared_data.lock().unwrap();
    println!("最终数据: {:?}", *result);
}
```

## 2. 多线程环境下的所有权挑战

### 2.1 线程安全性基本问题

在多线程环境中，所有权模型面临几个关键挑战：

1. **线程生命周期**：线程可能比创建它的作用域存活更长
2. **数据竞争**：多个线程同时访问同一数据，至少有一个是写操作
3. **死锁**：多个线程互相等待对方持有的资源，形成环路依赖
4. **活锁**：线程不断响应彼此的操作，但无法推进
5. **饥饿**：某些线程无法获得所需资源

Rust 的类型系统通过 `Send` 和 `Sync` trait 来处理这些问题：

- **`Send`**：类型可以安全地在线程间传递所有权
- **`Sync`**：类型可以安全地在线程间共享引用

```rust
// 区分 Send 和 Sync
fn explain_send_sync() {
    // Vec<i32> 是 Send，可以跨线程发送
    let v = vec![1, 2, 3];
    thread::spawn(move || {
        println!("在另一线程: {:?}", v);
    });
    
    // Rc<T> 不是 Send，不能跨线程发送
    // let rc = Rc::new(5);
    // thread::spawn(move || {
    //     println!("在另一线程: {}", rc); // 编译错误
    // });
    
    // Mutex<T> 是 Sync，可以跨线程共享引用
    let mutex = Arc::new(Mutex::new(5));
    let mutex2 = Arc::clone(&mutex);
    thread::spawn(move || {
        let mut num = mutex2.lock().unwrap();
        *num += 1;
    });
    
    // RefCell<T> 不是 Sync，不能跨线程共享引用
    // let ref_cell = Arc::new(RefCell::new(5));
    // let ref_cell2 = Arc::clone(&ref_cell);
    // thread::spawn(move || {
    //     let mut num = ref_cell2.borrow_mut();
    //     *num += 1; // 编译错误
    // });
}
```

### 2.2 多线程所有权转移的特殊性

多线程环境中，所有权转移具有几个特殊性质：

1. **不可逆性**：一旦所有权转移到另一个线程，原线程无法直接取回
2. **生命周期独立**：接收线程的生命周期与发送线程独立
3. **线程边界**：所有权必须穿越线程边界，需要特殊处理
4. **内存序**：多线程访问需要考虑内存顺序保证（Ordering）

```rust
use std::sync::{Arc, Mutex};
use std::thread;

fn ownership_transfer_example() {
    // 单向所有权转移 - 从主线程到工作线程
    let data = vec![1, 2, 3];
    
    let handle = thread::spawn(move || {
        // 工作线程现在拥有 data
        println!("工作线程: {:?}", data);
        // 对数据进行处理...
        data.len()
    });
    
    // 获取处理结果
    let result = handle.join().unwrap();
    println!("结果: {}", result);
    // 注意: data 已经被消费，不能在主线程继续使用
    
    // 双向所有权转移 - 使用通道
    let (tx, rx) = std::sync::mpsc::channel();
    
    let handle2 = thread::spawn(move || {
        // 发送所有权到主线程
        let processed_data = vec![4, 5, 6];
        tx.send(processed_data).unwrap();
        // processed_data 的所有权已转移
    });
    
    // 接收所有权
    let received = rx.recv().unwrap();
    println!("主线程接收: {:?}", received);
    
    handle2.join().unwrap();
}
```

### 2.3 线程间数据共享的需求与风险

多线程程序通常需要共享数据，这带来了所有权管理的复杂性：

```rust
use std::sync::{Arc, Mutex, RwLock};
use std::thread;

fn data_sharing_patterns() {
    // 1. 只读共享 - 使用 Arc 实现多线程间共享所有权
    let shared_data = Arc::new(vec![1, 2, 3]);
    
    let mut handles = vec![];
    for i in 0..3 {
        let data = Arc::clone(&shared_data);
        let handle = thread::spawn(move || {
            println!("线程 {} 读取: {:?}", i, data);
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    // 2. 读写共享 - 使用 Mutex 提供互斥访问
    let mutex_data = Arc::new(Mutex::new(vec![1, 2, 3]));
    
    let mut handles = vec![];
    for i in 0..3 {
        let data = Arc::clone(&mutex_data);
        let handle = thread::spawn(move || {
            let mut guard = data.lock().unwrap();
            guard.push(i + 10);
            println!("线程 {} 修改后: {:?}", i, *guard);
            // guard 在这里释放锁
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    // 3. 读优先共享 - 使用 RwLock 提供读写锁
    let rwlock_data = Arc::new(RwLock::new(vec![1, 2, 3]));
    
    // 启动多个读取线程
    let mut read_handles = vec![];
    for i in 0..3 {
        let data = Arc::clone(&rwlock_data);
        let handle = thread::spawn(move || {
            let guard = data.read().unwrap();
            println!("读线程 {} 读取: {:?}", i, *guard);
            // 模拟长时间读取
            thread::sleep(std::time::Duration::from_millis(50));
        });
        read_handles.push(handle);
    }
    
    // 启动写入线程
    let write_data = Arc::clone(&rwlock_data);
    let write_handle = thread::spawn(move || {
        thread::sleep(std::time::Duration::from_millis(10));
        let mut guard = write_data.write().unwrap();
        guard.push(100);
        println!("写线程修改: {:?}", *guard);
    });
    
    for handle in read_handles {
        handle.join().unwrap();
    }
    write_handle.join().unwrap();
}
```

## 3. 多线程所有权设计模式分类

### 3.1 消息传递模式

**定义**：通过通道在线程间传递数据所有权，而非共享状态。

**特点**：

- 符合 Rust 哲学 "不要通过共享内存来通信，而是通过通信来共享内存"
- 每条数据在任一时刻只有一个所有者，避免数据竞争
- 数据随消息一同移动所有权

**示例**：

```rust
use std::sync::mpsc;
use std::thread;

// 消息定义
enum WorkerMessage {
    Task(Vec<i32>),
    Process(String),
    Terminate,
}

fn message_passing_pattern() {
    // 创建通道
    let (tx, rx) = mpsc::channel();
    
    // 生成多个发送端
    let tx1 = tx.clone();
    let tx2 = tx.clone();
    
    // 工作线程接收任务
    let worker = thread::spawn(move || {
        loop {
            match rx.recv() {
                Ok(WorkerMessage::Task(data)) => {
                    println!("处理任务: {:?}", data);
                    // 数据所有权已转移到工作线程
                }
                Ok(WorkerMessage::Process(text)) => {
                    println!("处理文本: {}", text);
                }
                Ok(WorkerMessage::Terminate) => {
                    println!("工作线程终止");
                    break;
                }
                Err(_) => {
                    println!("通道已关闭");
                    break;
                }
            }
        }
    });
    
    // 发送者线程1
    thread::spawn(move || {
        let data = vec![1, 2, 3, 4];
        tx1.send(WorkerMessage::Task(data)).unwrap();
        // data 所有权已转移
    });
    
    // 发送者线程2
    thread::spawn(move || {
        let text = String::from("处理这段文本");
        tx2.send(WorkerMessage::Process(text)).unwrap();
        // text 所有权已转移
        
        thread::sleep(std::time::Duration::from_millis(100));
        tx2.send(WorkerMessage::Terminate).unwrap();
    });
    
    // 等待工作线程结束
    worker.join().unwrap();
}
```

**优势**：

- 避免共享状态带来的锁竞争和死锁
- 明确的所有权转移语义
- 易于推理的数据流

**挑战**：

- 需要设计消息模型
- 可能需要频繁克隆数据
- 通信开销

### 3.2 共享状态模式

**定义**：通过共享可变状态协调多线程工作，使用同步原语确保安全访问。

**特点**：

- 多线程共享相同数据的访问权
- 使用 `Arc` 共享所有权，使用 `Mutex`/`RwLock` 同步访问
- 适用于需要多线程读写同一数据的场景

**示例**：

```rust
use std::sync::{Arc, Mutex};
use std::thread;

struct SharedDatabase {
    data: Mutex<Vec<String>>,
}

impl SharedDatabase {
    fn new() -> Self {
        SharedDatabase {
            data: Mutex::new(Vec::new()),
        }
    }
    
    fn add(&self, item: String) {
        let mut data = self.data.lock().unwrap();
        data.push(item);
    }
    
    fn get_all(&self) -> Vec<String> {
        let data = self.data.lock().unwrap();
        data.clone()
    }
}

fn shared_state_pattern() {
    let database = Arc::new(SharedDatabase::new());
    
    let mut handles = vec![];
    
    // 多个写入线程
    for i in 0..5 {
        let db = Arc::clone(&database);
        let handle = thread::spawn(move || {
            db.add(format!("数据项 {}", i));
            println!("线程 {} 添加了数据", i);
        });
        handles.push(handle);
    }
    
    // 读取线程
    let db = Arc::clone(&database);
    handles.push(thread::spawn(move || {
        thread::sleep(std::time::Duration::from_millis(50));
        let items = db.get_all();
        println!("读取线程获取所有数据: {:?}", items);
    }));
    
    for handle in handles {
        handle.join().unwrap();
    }
}
```

**高级示例 - 使用细粒度锁**：

```rust
use std::sync::{Arc, Mutex};
use std::collections::HashMap;
use std::thread;

// 使用细粒度锁的缓存系统
struct ShardedCache {
    // 将数据分片存储在多个 Mutex 中以减少锁竞争
    shards: Vec<Mutex<HashMap<String, String>>>,
    shard_count: usize,
}

impl ShardedCache {
    fn new(shard_count: usize) -> Self {
        let mut shards = Vec::with_capacity(shard_count);
        for _ in 0..shard_count {
            shards.push(Mutex::new(HashMap::new()));
        }
        
        ShardedCache {
            shards,
            shard_count,
        }
    }
    
    // 确定键应该在哪个分片
    fn get_shard_index(&self, key: &str) -> usize {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        std::hash::Hash::hash(key, &mut hasher);
        let hash = std::hash::Hasher::finish(&hasher);
        (hash as usize) % self.shard_count
    }
    
    // 插入数据
    fn insert(&self, key: String, value: String) {
        let index = self.get_shard_index(&key);
        let mut shard = self.shards[index].lock().unwrap();
        shard.insert(key, value);
    }
    
    // 获取数据
    fn get(&self, key: &str) -> Option<String> {
        let index = self.get_shard_index(key);
        let shard = self.shards[index].lock().unwrap();
        shard.get(key).cloned()
    }
}

fn fine_grained_locking_example() {
    let cache = Arc::new(ShardedCache::new(16));
    
    let mut handles = vec![];
    
    // 多个写入线程
    for i in 0..100 {
        let c = Arc::clone(&cache);
        let handle = thread::spawn(move || {
            c.insert(format!("key{}", i), format!("value{}", i));
        });
        handles.push(handle);
    }
    
    // 多个读取线程
    for i in 0..100 {
        let c = Arc::clone(&cache);
        let handle = thread::spawn(move || {
            let key = format!("key{}", i % 50);
            if let Some(value) = c.get(&key) {
                println!("线程读取 {}: {}", key, value);
            }
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
}
```

**优势**：

- 允许多线程共享访问相同数据
- 可以根据需要细粒度控制访问权限
- 适合状态需要频繁更新的场景

**挑战**：

- 死锁风险
- 锁竞争影响性能
- 需要精心设计避免长时间持有锁

### 3.3 读写分离模式

**定义**：基于数据访问模式区分读和写操作，优化并发性能。

**特点**：

- 使用 `RwLock` 允许多读单写访问
- 读操作可以并发进行，写操作互斥
- 适用于读多写少的场景

**示例**：

```rust
use std::sync::{Arc, RwLock};
use std::thread;

struct Database {
    data: RwLock<HashMap<String, String>>,
}

impl Database {
    fn new() -> Self {
        Database {
            data: RwLock::new(HashMap::new()),
        }
    }
    
    // 写操作 - 独占
    fn insert(&self, key: String, value: String) {
        let mut data = self.data.write().unwrap();
        data.insert(key, value);
    }
    
    // 读操作 - 共享
    fn get(&self, key: &str) -> Option<String> {
        let data = self.data.read().unwrap();
        data.get(key).cloned()
    }
    
    // 批量读操作 - 共享
    fn get_all(&self) -> Vec<(String, String)> {
        let data = self.data.read().unwrap();
        data.iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect()
    }
}

fn read_write_pattern() {
    let db = Arc::new(Database::new());
    
    // 先填充一些数据
    for i in 0..100 {
        db.insert(format!("key{}", i), format!("value{}", i));
    }
    
    let mut handles = vec![];
    
    // 多个读线程
    for i in 0..10 {
        let db = Arc::clone(&db);
        let handle = thread::spawn(move || {
            for j in 0..10 {
                let key = format!("key{}", i * 10 + j);
                match db.get(&key) {
                    Some(value) => println!("线程 {} 读取: {}={}", i, key, value),
                    None => println!("线程 {} 未找到: {}", i, key),
                }
            }
        });
        handles.push(handle);
    }
    
    // 少量写线程
    for i in 0..2 {
        let db = Arc::clone(&db);
        let handle = thread::spawn(move || {
            for j in 0..5 {
                let key = format!("new_key{}", i * 5 + j);
                let value = format!("new_value{}", i * 5 + j);
                db.insert(key.clone(), value.clone());
                println!("线程 {} 写入: {}={}", i, key, value);
            }
        });
        handles.push(handle);
    }
    
    // 整体读取线程
    let db = Arc::clone(&db);
    handles.push(thread::spawn(move || {
        thread::sleep(std::time::Duration::from_millis(50));
        let all_items = db.get_all();
        println!("总共有 {} 条数据", all_items.len());
    }));
    
    for handle in handles {
        handle.join().unwrap();
    }
}
```

**优势**：

- 允许多个读操作并发进行，提高读取性能
- 保证写操作的互斥性和数据一致性
- 读写意图明确，易于理解

**挑战**：

- 写操作会阻塞所有读操作，可能导致读饥饿
- 持有读锁时间过长会阻塞写操作
- 实现复杂度增加

### 3.4 所有权分区模式

**定义**：将数据分割成多个独立的部分，每个线程负责其中一部分，避免共享。

**特点**：

- 每个线程拥有数据的一个子集的独占所有权
- 尽量减少跨边界数据访问的需求
- 本质上是"划分并征服"的并行处理思想

**示例**：

```rust
use std::thread;

fn ownership_partitioning_pattern() {
    // 原始大数据集
    let data = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12];
    
    // 线程数量
    let thread_count = 3;
    
    // 计算每个线程处理的数据量
    let chunk_size = (data.len() + thread_count - 1) / thread_count;
    
    // 将数据划分给不同线程
    let mut handles = vec![];
    let mut chunked_data = vec![];
    
    // 分割数据
    for chunk in data.chunks(chunk_size) {
        chunked_data.push(chunk.to_vec());
    }
    
    // 启动多个线程，每个处理自己的数据分区
    for (i, chunk) in chunked_data.into_iter().enumerate() {
        let handle = thread::spawn(move || {
            println!("线程 {} 处理数据: {:?}", i, chunk);
            
            // 处理数据
            let sum: i32 = chunk.iter().sum();
            (i, sum)
        });
        handles.push(handle);
    }
    
    // 收集处理结果
    let mut results = vec![];
    for handle in handles {
        results.push(handle.join().unwrap());
    }
    
    // 合并结果
    results.sort_by_key(|&(i, _)| i);
    let total: i32 = results.iter().map(|&(_, sum)| sum).sum();
    
    println!("处理结果: {:?}", results);
    println!("总和: {}", total);
}
```

**高级实现 - 带边界交换**：

```rust
use std::thread;
use std::sync::{Arc, Mutex};

fn ownership_partitioning_with_boundary() {
    let data = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12];
    let thread_count = 3;
    let chunk_size = (data.len() + thread_count - 1) / thread_count;
    
    // 存储处理结果
    let results = Arc::new(Mutex::new(vec![0; data.len()]));
    
    let mut handles = vec![];
    
    // 启动多个线程，每个处理自己的数据分区
    for i in 0..thread_count {
        let start = i * chunk_size;
        let end = std::cmp::min((i + 1) * chunk_size, data.len());
        
        if start >= data.len() {
            break;
        }
        
        // 为每个线程分配数据子集
        let thread_data = data[start..end].to_vec();
        let results_clone = Arc::clone(&results);
        
        let handle = thread::spawn(move || {
            // 处理数据
            let mut processed = vec![];
            for &item in &thread_data {
                processed.push(item * 2); // 简单处理：每个元素翻倍
            }
            
            // 将结果写回共享结果集
            let mut results = results_clone.lock().unwrap();
            for (idx, &value) in processed.iter().enumerate() {
                results[start + idx] = value;
            }
        });
        
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    // 打印结果
    let final_results = results.lock().unwrap();
    println!("最终结果: {:?}", *final_results);
}
```

**优势**：

- 最小化线程间同步需求
- 减少锁竞争，提高并行度
- 降低并发错误风险

**挑战**：

- 数据划分需要仔细设计
- 可能需要额外的边界情况处理
- 不均衡的工作负载可能导致性能瓶颈

### 3.5 工作窃取模式

**定义**：允许空闲线程"窃取"其他线程队列中的任务，实现动态负载均衡。

**特点**：

- 每个线程维护自己的工作队列
- 线程可以从其他线程队列窃取任务
- 动态平衡工作负载，避免线程闲置

**示例**：

```rust
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Duration;
use std::collections::VecDeque;

struct Task {
    id: usize,
    work_amount: usize,
}

impl Task {
    fn execute(&self) {
        println!("执行任务 {}, 工作量: {}", self.id, self.work_amount);
        // 模拟工作
        thread::sleep(Duration::from_millis(self.work_amount as u64));
    }
}

struct WorkStealingPool {
    // 每个工作线程有自己的任务队列
    queues: Vec<Arc<Mutex<VecDeque<Task>>>>,
    thread_count: usize,
}

impl WorkStealingPool {
    fn new(thread_count: usize) -> Self {
        let mut queues = Vec::with_capacity(thread_count);
        for _ in 0..thread_count {
            queues.push(Arc::new(Mutex::new(VecDeque::new())));
        }
        
        WorkStealingPool {
            queues,
            thread_count,
        }
    }
    
    fn submit(&self, task: Task, preferred_thread: usize) {
        let thread_idx = preferred_thread % self.thread_count;
        let mut queue = self.queues[thread_idx].lock().unwrap();
        queue.push_back(task);
    }
    
    fn run(&self) {
        let mut handles = vec![];
        
        for id in 0..self.thread_count {
            let queues = self.queues.clone();
            let thread_count = self.thread_count;
            
            let handle = thread::spawn(move || {
                let mut completed_tasks = 0;
                
                loop {
                    // 尝试从自己的队列获取任务
                    let task = {
                        let mut own_queue = queues[id].lock().unwrap();
                        own_queue.pop_front()
                    };
                    
                    match task {
                        Some(task) => {
                            // 执行任务
                            task.execute();
                            completed_tasks += 1;
                        }
                        None => {
                            // 自己的队列为空，尝试从其他队列窃取任务
                            let mut stolen = false;
                            
                            // 随机选择起始窃取位置
                            let start_steal = (id + 1) % thread_count;
                            for i in 0..thread_count - 1 {
                                let steal_from = (start_steal + i) % thread_count;
                                
                                let stolen_task = {
                                    let mut other_queue = queues[steal_from].lock().unwrap();
                                    other_queue.pop_back() // 从后端窃取
                                };
                                
                                if let Some(task) = stolen_task {
                                    println!("线程 {} 从线程 {} 窃取任务 {}", 
                                             id, steal_from, task.id);
                                    task.execute();
                                    completed_tasks += 1;
                                    stolen = true;
                                    break;
                                }
                            }
                            
                            if !stolen {
                                // 没有任务可窃取，检查是否所有队列都为空
                                let all_empty = queues.iter().all(|q| {
                                    let queue = q.lock().unwrap();
                                    queue.is_empty()
                                });
                                
                                if all_empty {
                                    // 所有工作已完成
                                    break;
                                }
                                
                                // 短暂休眠，避免 CPU 空转
                                thread::sleep(Duration::from_millis(1));
                            }
                        }
                    }
                }
                
                println!("线程 {} 完成 {} 个任务", id, completed_tasks);
            });
            
            handles.push(handle);
        }
        
        for handle in handles {
            handle.join().unwrap();
        }
    }
}

fn work_stealing_pattern() {
    let pool = Arc::new(WorkStealingPool::new(4));
    
    // 创建不平衡的工作负载
    for i in 0..20 {
        let thread_id = i % 4;
        let work_amount = if thread_id == 0 {
            // 线程 0 获得更多工作
            50
        } else {
            10
        };
        
        pool.submit(Task {
            id: i,
            work_amount,
        }, thread_id);
    }
    
    // 运行工作池
    pool.run();
}
```

**优势**：

- 自动负载均衡，提高资源利用率
- 适应性强，适合不均匀工作负载
- 减少线程空闲时间，提高吞吐量

**挑战**：

- 实现复杂度高
- 窃取操作可能引入额外竞争
- 需要仔细设计任务分割策略

## 4. 多线程环境下的所有权转移策略

### 4.1 跨线程所有权转移

在多线程环境中，所有权需要安全地跨越线程边界：

```rust
use std::thread;
use std::sync::mpsc;

enum OwnershipTransfer<T> {
    // 转移所有权
    Move(T),
    // 借用（需要静态生命周期或 Arc）
    Borrow(Arc<T>),
    // 请求返回所有权
    Request,
}

fn cross_thread_ownership() {
    // 1. 使用通道转移所有权
    let (tx, rx) = mpsc::channel();
    
    // 创建资源
    let resource = vec![1, 2, 3, 4, 5];
    
    // 线程1: 发送资源
    let tx1 = tx.clone();
    thread::spawn(move || {
        println!("线程1: 发送资源");
        tx1.send(resource).unwrap();
        // resource 所有权已转移
    });
    
    // 线程2: 接收资源并处理
    let handle = thread::spawn(move || {
        let received = rx.recv().unwrap();
        println!("线程2: 接收资源 {:?}", received);
        
        // 处理后返回新资源
        let processed = received.iter().map(|&x| x * 2).collect::<Vec<_>>();
        processed
    });
    
    // 等待处理结果
    let result = handle.join().unwrap();
    println!("主线程: 获取结果 {:?}", result);
    
    // 2. 使用所有权管理器模式
    let (command_tx, command_rx) = mpsc::channel();
    let (result_tx, result_rx) = mpsc::channel();
    
    // 所有权管理器线程
    thread::spawn(move || {
        let mut resource = String::from("共享资源");
        
        loop {
            match command_rx.recv() {
                Ok(OwnershipTransfer::Request) => {
                    // 返回资源副本
                    result_tx.send(resource.clone()).unwrap();
                }
                Ok(OwnershipTransfer::Move(new_resource)) => {
                    // 更新资源
                    resource = new_resource;
                    println!("资源已更新为: {}", resource);
                }
                Ok(OwnershipTransfer::Borrow(_)) => {
                    // 借用操作（简化示例，实际中会使用 Arc）
                    println!("当前资源: {}", resource);
                }
                Err(_) => {
                    println!("所有发送端已关闭，退出");
                    break;
                }
            }
        }
    });
    
    // 工作线程: 请求并修改资源
    let cmd_tx = command_tx.clone();
    let res_rx = result_rx.clone();
    thread::spawn(move || {
        // 请求资源
        cmd_tx.send(OwnershipTransfer::Request).unwrap();
        
        // 获取资源
        let mut resource = res_rx.recv().unwrap();
        
        // 修改资源
        resource.push_str(" - 已修改");
        
        // 发送回所有权管理器
        cmd_tx.send(OwnershipTransfer::Move(resource)).unwrap();
    });
    
    // 给线程一些时间运行
    thread::sleep(std::time::Duration::from_millis(100));
    
    // 请求查看当前资源
    command_tx.send(OwnershipTransfer::Borrow(Arc::new(()))).unwrap();
}
```

### 4.2 动态借用转所有权

多线程环境中将借用转换为所有权的策略：

```rust
use std::sync::{Arc, Mutex};
use std::thread;

struct DataHolder {
    data: String,
    version: usize,
}

impl DataHolder {
    fn new(data: String) -> Self {
        DataHolder {
            data,
            version: 0,
        }
    }
}

struct DataManager {
    current: Mutex<DataHolder>,
}

impl DataManager {
    fn new(initial_data: String) -> Self {
        DataManager {
            current: Mutex::new(DataHolder::new(initial_data)),
        }
    }
    
    // 获取引用
    fn get_ref(&self) -> String {
        let holder = self.current.lock().unwrap();
        holder.data.clone()
    }
    
    // 根据条件获取所有权（通过克隆）
    fn get_owned_if_needed(&self, predicate: impl Fn(&str) -> bool) -> Option<String> {
        let holder = self.current.lock().unwrap();
        if predicate(&holder.data) {
            Some(holder.data.clone())
        } else {
            None
        }
    }
    
    // 条件性更新 - 检查版本号
    fn update_if_same_version(&self, new_data: String, expected_version: usize) -> bool {
        let mut holder = self.current.lock().unwrap();
        if holder.version == expected_version {
            holder.data = new_data;
            holder.version += 1;
            true
        } else {
            false
        }
    }
    
    // 获取当前版本
    fn get_version(&self) -> usize {
        let holder = self.current.lock().unwrap();
        holder.version
    }
}

fn dynamic_borrow_to_ownership() {
    let manager = Arc::new(DataManager::new("初始数据".to_string()));
    
    let mut handles = vec![];
    
    // 多个读取线程
    for i in 0..3 {
        let mgr = Arc::clone(&manager);
        let handle = thread::spawn(move || {
            // 首先只获取引用
            let data = mgr.get_ref();
            println!("线程 {} 读取: {}", i, data);
            
            // 判断是否需要获取所有权
            if let Some(owned_data) = mgr.get_owned_if_needed(|s| s.contains("初始")) {
                // 获取数据版本
                let version = mgr.get_version();
                
                // 修改数据
                let modified = format!("{} - 线程 {} 修改", owned_data, i);
                
                // 尝试更新回原位置
                let success = mgr.update_if_same_version(modified, version);
                println!("线程 {} 更新{}成功", i, if success { "" } else { "不" });
            }
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    // 查看最终结果
    println!("最终数据: {}", manager.get_ref());
}
```

### 4.3 线程本地存储与全局共享

结合线程本地存储和全局共享模式：

```rust
use std::cell::RefCell;
use std::sync::{Arc, Mutex};
use std::thread;

// 线程本地上下文
thread_local! {
    static LOCAL_CACHE: RefCell<Vec<String>> = RefCell::new(Vec::new());
}

// 全局共享存储
struct GlobalStorage {
    data: Mutex<Vec<String>>,
}

impl GlobalStorage {
    fn new() -> Self {
        GlobalStorage {
            data: Mutex::new(Vec::new()),
        }
    }
    
    fn add(&self, item: String) {
        let mut data = self.data.lock().unwrap();
        data.push(item);
    }
    
    fn get_all(&self) -> Vec<String> {
        let data = self.data.lock().unwrap();
        data.clone()
    }
}

fn thread_local_and_global() {
    let global = Arc::new(GlobalStorage::new());
    
    let mut handles = vec![];
    
    for i in 0..3 {
        let global_clone = Arc::clone(&global);
        let handle = thread::spawn(move || {
            // 使用线程本地存储
            LOCAL_CACHE.with(|cache| {
                // 添加一些线程本地数据
                let mut cache = cache.borrow_mut();
                for j in 0..5 {
                    cache.push(format!("线程 {} 本地项 {}", i, j));
                }
                
                println!("线程 {} 本地缓存大小: {}", i, cache.len());
                
                // 处理本地数据
                for item in cache.iter() {
                    let processed = format!("处理后: {}", item);
                    
                    // 将处理后的数据移动到全局存储
                    global_clone.add(processed);
                }
                
                // 清空本地缓存
                cache.clear();
            });
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    // 查看全局存储
    let all_items = global.get_all();
    println!("全局存储项数: {}", all_items.len());
    for item in all_items.iter().take(5) {
        println!("样本项: {}", item);
    }
}
```

## 5. 实际应用案例分析

### 5.1 高性能工作池设计

设计一个高性能工作池，处理不同类型任务：

```rust
use std::sync::{Arc, Mutex, Condvar};
use std::thread;
use std::time::Duration;
use std::collections::VecDeque;

// 任务特质
trait JobTask: Send + 'static {
    fn execute(&self);
    fn name(&self) -> String;
}

// 具体任务实现
struct ComputeTask {
    id: usize,
    computation: Box<dyn Fn() -> u64 + Send + 'static>,
}

impl ComputeTask {
    fn new(id: usize, computation: Box<dyn Fn() -> u64 + Send + 'static>) -> Self {
        ComputeTask { id, computation }
    }
}

impl JobTask for ComputeTask {
    fn execute(&self) {
        let result = (self.computation)();
        println!("计算任务 {} 结果: {}", self.id, result);
    }
    
    fn name(&self) -> String {
        format!("计算任务 {}", self.id)
    }
}

struct IoTask {
    id: usize,
    io_operation: Box<dyn Fn() + Send + 'static>,
}

impl IoTask {
    fn new(id: usize, io_operation: Box<dyn Fn() + Send + 'static>) -> Self {
        IoTask { id, io_operation }
    }
}

impl JobTask for IoTask {
    fn execute(&self) {
        (self.io_operation)();
        println!("IO任务 {} 完成", self.id);
    }
    
    fn name(&self) -> String {
        format!("IO任务 {}", self.id)
    }
}

// 工作池实现
struct WorkPool {
    queue: Arc<(Mutex<VecDeque<Box<dyn JobTask>>>, Condvar)>,
    workers: Vec<thread::JoinHandle<()>>,
    running: Arc<Mutex<bool>>,
}

impl WorkPool {
    fn new(size: usize) -> Self {
        let queue = Arc::new((Mutex::new(VecDeque::new()), Condvar::new()));
        let running = Arc::new(Mutex::new(true));
        let mut workers = Vec::with_capacity(size);
        
        for id in 0..size {
            let queue_clone = Arc::clone(&queue);
            let running_clone = Arc::clone(&running);
            
            let handle = thread::spawn(move || {
                loop {
                    // 获取任务或等待
                    let task = {
                        let (lock, cvar) = &*queue_clone;
                        let mut queue = lock.lock().unwrap();
                        
                        while queue.is_empty() {
                            let running_guard = running_clone.lock().unwrap();
                            if !*running_guard {
                                return; // 工作池已停止
                            }
                            
                            queue = cvar.wait(queue).unwrap();
                            
                            let running_check = running_clone.lock().unwrap();
                            if !*running_check && queue.is_empty() {
                                return; // 再次检查，避免竞态条件
                            }
                        }
                        
                        queue.pop_front()
                    };
                    
                    // 执行任务
                    if let Some(job) = task {
                        println!("工作线程 {} 开始执行: {}", id, job.name());
                        job.execute();
                    }
                }
            });
            
            workers.push(handle);
        }
        
        WorkPool {
            queue,
            workers,
            running,
        }
    }
    
    fn submit<T: JobTask + 'static>(&self, task: T) {
        let (lock, cvar) = &*self.queue;
        let mut queue = lock.lock().unwrap();
        queue.push_back(Box::new(task));
        cvar.notify_one();
    }
    
    fn shutdown(self) {
        // 设置运行状态为 false
        {
            let mut running = self.running.lock().unwrap();
            *running = false;
        }
        
        // 唤醒所有等待中的工作线程
        let (_, cvar) = &*self.queue;
        cvar.notify_all();
        
        // 等待所有工作线程结束
        for worker in self.workers {
            worker.join().unwrap();
        }
        
        println!("工作池已完全关闭");
    }
}

fn work_pool_example() {
    // 创建工作池
    let pool = WorkPool::new(4);
    
    // 提交计算任务
    for i in 0..10 {
        let task = ComputeTask::new(i, Box::new(move || {
            let n = i + 1;
            thread::sleep(Duration::from_millis(100));
            n as u64 * n as u64
        }));
        pool.submit(task);
    }
    
    // 提交IO任务
    for i in 0..5 {
        let task = IoTask::new(i, Box::new(move || {
            println!("执行IO操作 {}", i);
            thread::sleep(Duration::from_millis(200));
        }));
        pool.submit(task);
    }
    
    // 给任务一些时间执行
    thread::sleep(Duration::from_secs(2));
    
    // 关闭工作池
    pool.shutdown();
}
```

### 5.2 并发数据处理管道

实现一个并发数据处理管道，各阶段分别处理数据：

```rust
use std::sync::{Arc, Mutex};
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

// 定义处理阶段
enum PipelineStage<T, U> {
    // 单线程处理
    SingleThreaded(Box<dyn Fn(T) -> U + Send>),
    // 多线程处理
    MultiThreaded {
        processor: Box<dyn Fn(T) -> U + Send + Sync>,
        threads: usize,
    },
    // 批处理
    Batched {
        processor: Box<dyn Fn(Vec<T>) -> Vec<U> + Send>,
        batch_size: usize,
    },
}

// 管道实现
struct Pipeline<T: Send + 'static, U: Send + 'static> {
    stage: PipelineStage<T, U>,
    next: Option<Box<dyn PipelineConnector<U>>>,
}

// 定义管道连接器特质
trait PipelineConnector<T: Send + 'static>: Send {
    fn process(&self, item: T);
    fn close(&self);
}

// 管道阶段间连接器
impl<T: Send + 'static, U: Send + 'static> PipelineConnector<T> for Pipeline<T, U> {
    fn process(&self, item: T) {
        match &self.stage {
            PipelineStage::SingleThreaded(processor) => {
                let result = processor(item);
                if let Some(next) = &self.next {
                    next.process(result);
                }
            },
            PipelineStage::MultiThreaded { processor, threads: _ } => {
                let processor = Arc::new(processor);
                let next_stage = self.next.as_ref().map(|ns| Arc::new(ns as &dyn PipelineConnector<U>));
                
                let processor_clone = Arc::clone(&processor);
                let next_clone = next_stage.clone();
                
                thread::spawn(move || {
                    let result = processor_clone(item);
                    if let Some(next) = next_clone {
                        next.process(result);
                    }
                });
            },
            PipelineStage::Batched { processor, batch_size } => {
                // 简化实现，实际中应该有一个累积批次的机制
                let mut batch = Vec::with_capacity(*batch_size);
                batch.push(item);
                
                let results = processor(batch);
                if let Some(next) = &self.next {
                    for result in results {
                        next.process(result);
                    }
                }
            }
        }
    }
    
    fn close(&self) {
        // 关闭当前阶段并通知下一阶段
        if let Some(next) = &self.next {
            next.close();
        }
    }
}

impl<T: Send + 'static, U: Send + 'static> Pipeline<T, U> {
    fn new(stage: PipelineStage<T, U>) -> Self {
        Pipeline {
            stage,
            next: None,
        }
    }
    
    fn then<V: Send + 'static>(mut self, next_stage: PipelineStage<U, V>) -> Pipeline<T, V> {
        let next_pipeline = Pipeline::new(next_stage);
        self.next = Some(Box::new(next_pipeline));
        
        // 这里需要从 self.next 中取出 Pipeline<U, V>，但简化实现会略过这步
        // 实际中需要更复杂的连接机制
        todo!("完整实现应返回下一阶段管道")
    }
}

// 使用提供者-消费者模式提供数据源
struct DataSource<T: Send + 'static> {
    sender: mpsc::Sender<Option<T>>,
}

impl<T: Send + 'static> DataSource<T> {
    fn new<P: PipelineConnector<T> + 'static>(pipeline: P) -> Self {
        let (tx, rx) = mpsc::channel();
        
        thread::spawn(move || {
            while let Ok(item) = rx.recv() {
                match item {
                    Some(data) => pipeline.process(data),
                    None => {
                        pipeline.close();
                        break;
                    }
                }
            }
        });
        
        DataSource { sender: tx }
    }
    
    fn send(&self, item: T) {
        self.sender.send(Some(item)).unwrap();
    }
    
    fn close(self) {
        self.sender.send(None).unwrap();
    }
}

// 数据管道示例
fn data_pipeline_example() {
    // 定义处理阶段
    let stage1 = PipelineStage::SingleThreaded(Box::new(|n: i32| {
        println!("阶段1: 处理 {}", n);
        thread::sleep(Duration::from_millis(100));
        n * 2
    }));
    
    let stage2 = PipelineStage::MultiThreaded {
        processor: Box::new(|n: i32| {
            println!("阶段2: 处理 {}", n);
            thread::sleep(Duration::from_millis(150));
            format!("数字: {}", n)
        }),
        threads: 3,
    };
    
    let stage3 = PipelineStage::SingleThreaded(Box::new(|s: String| {
        println!("阶段3: 处理 {}", s);
        thread::sleep(Duration::from_millis(80));
        s.len()
    }));
    
    // 构建管道
    let pipeline = Pipeline::new(stage1);
    // pipeline = pipeline.then(stage2).then(stage3); // 实际实现应该是这样
    
    // 简化实现 - 直接构建阶段1
    let source = DataSource::new(pipeline);
    
    // 发送数据
    for i in 1..=10 {
        source.send(i);
    }
    
    // 关闭数据源
    source.close();
    
    // 等待处理完成
    thread::sleep(Duration::from_secs(3));
}
```

### 5.3 多线程缓存系统

一个带有定时清理功能的多线程缓存系统实现：

```rust
use std::collections::HashMap;
use std::hash::Hash;
use std::sync::{Arc, RwLock, Mutex};
use std::thread;
use std::time::{Duration, Instant};

struct CacheEntry<V> {
    value: V,
    expires_at: Instant,
}

struct ThreadedCache<K, V> {
    data: RwLock<HashMap<K, CacheEntry<V>>>,
    cleanup_interval: Duration,
    cleanup_thread: Mutex<Option<thread::JoinHandle<()>>>,
    running: Arc<RwLock<bool>>,
}

impl<K, V> ThreadedCache<K, V> 
where
    K: Eq + Hash + Clone + Send + Sync + 'static,
    V: Clone + Send + Sync + 'static,
{
    fn new(cleanup_interval: Duration) -> Arc<Self> {
        let cache = Arc::new(ThreadedCache {
            data: RwLock::new(HashMap::new()),
            cleanup_interval,
            cleanup_thread: Mutex::new(None),
            running: Arc::new(RwLock::new(true)),
        });
        
        // 启动清理线程
        cache.start_cleanup_thread();
        
        cache
    }
    
    fn start_cleanup_thread(&self) {
        let cache_ref = Arc::new(self);
        let running = Arc::clone(&self.running);
        
        let handle = thread::spawn(move || {
            while *running.read().unwrap() {
                thread::sleep(cache_ref.cleanup_interval);
                cache_ref.cleanup_expired();
            }
        });
        
        let mut guard = self.cleanup_thread.lock().unwrap();
        *guard = Some(handle);
    }
    
    fn cleanup_expired(&self) {
        let now = Instant::now();
        let mut data = self.data.write().unwrap();
        
        // 收集过期的键
        let expired_keys: Vec<K> = data.iter()
            .filter(|(_, entry)| entry.expires_at <= now)
            .map(|(k, _)| k.clone())
            .collect();
        
        // 移除过期项
        for key in expired_keys {
            data.remove(&key);
            println!("清理了一个过期项");
        }
    }
    
    fn set(&self, key: K, value: V, ttl: Duration) {
        let expires_at = Instant::now() + ttl;
        let mut data = self.data.write().unwrap();
        
        data.insert(key, CacheEntry { value, expires_at });
    }
    
    fn get(&self, key: &K) -> Option<V> {
        let data = self.data.read().unwrap();
        
        data.get(key).and_then(|entry| {
            if entry.expires_at > Instant::now() {
                Some(entry.value.clone())
            } else {
                // 已过期，但尚未清理
                None
            }
        })
    }
    
    fn shutdown(self) {
        // 设置运行标志为 false
        {
            let mut running = self.running.write().unwrap();
            *running = false;
        }
        
        // 等待清理线程结束
        let mut cleanup_thread = self.cleanup_thread.lock().unwrap();
        if let Some(handle) = cleanup_thread.take() {
            handle.join().unwrap();
        }
    }
}

fn threaded_cache_example() {
    // 创建缓存
    let cache = ThreadedCache::new(Duration::from_secs(1));
    
    // 设置一些值，不同的过期时间
    cache.set("key1".to_string(), "value1".to_string(), Duration::from_millis(500));
    cache.set("key2".to_string(), "value2".to_string(), Duration::from_secs(2));
    cache.set("key3".to_string(), "value3".to_string(), Duration::from_secs(5));
    
    // 创建多个线程访问缓存
    let mut handles = vec![];
    
    for i in 0..3 {
        let c = Arc::clone(&cache);
        let handle = thread::spawn(move || {
            // 循环访问缓存
            for j in 0..5 {
                thread::sleep(Duration::from_millis(300));
                
                let key = format!("key{}", (i + j) % 3 + 1);
                match c.get(&key) {
                    Some(value) => println!("线程 {} 读取 {}: {}", i, key, value),
                    None => println!("线程 {} 未找到 {}", i, key),
                }
            }
        });
        handles.push(handle);
    }
    
    // 等待所有访问线程完成
    for handle in handles {
        handle.join().unwrap();
    }
    
    // 给清理线程时间工作
    thread::sleep(Duration::from_secs(3));
    
    // 检查最终状态
    println!("最终状态:");
    for i in 1..=3 {
        let key = format!("key{}", i);
        match cache.get(&key) {
            Some(value) => println!("{}: {}", key, value),
            None => println!("{}: 已过期或不存在", key),
        }
    }
}
```

### 5.4 实时事件处理框架

实现一个实时事件处理框架，支持并发处理：

```rust
use std::sync::{Arc, Mutex, mpsc};
use std::thread;
use std::time::Duration;
use std::collections::HashMap;

// 事件定义
#[derive(Clone, Debug)]
struct Event {
    id: usize,
    event_type: String,
    payload: String,
}

// 事件处理器特质
trait EventHandler: Send + Sync {
    fn handle(&self, event: &Event);
    fn event_types(&self) -> Vec<String>;
}

// 实现一个具体处理器
struct LoggingHandler;
impl EventHandler for LoggingHandler {
    fn handle(&self, event: &Event) {
        println!("日志处理器: 处理事件 {} - {} - {}", 
                 event.id, event.event_type, event.payload);
        thread::sleep(Duration::from_millis(100));
    }
    
    fn event_types(&self) -> Vec<String> {
        vec!["log".to_string(), "error".to_string()]
    }
}

struct AlertHandler;
impl EventHandler for AlertHandler {
    fn handle(&self, event: &Event) {
        println!("警报处理器: 处理事件 {} - {} - {}", 
                 event.id, event.event_type, event.payload);
        thread::sleep(Duration::from_millis(200));
    }
    
    fn event_types(&self) -> Vec<String> {
        vec!["alert".to_string(), "error".to_string()]
    }
}

// 事件分发器
struct EventDispatcher {
    handlers: HashMap<String, Vec<Arc<dyn EventHandler>>>,
    worker_count: usize,
}

impl EventDispatcher {
    fn new(worker_count: usize) -> Self {
        EventDispatcher {
            handlers: HashMap::new(),
            worker_count,
        }
    }
    
    fn register_handler(&mut self, handler: Arc<dyn EventHandler>) {
        for event_type in handler.event_types() {
            self.handlers.entry(event_type)
                .or_insert_with(Vec::new)
                .push(Arc::clone(&handler));
        }
    }
    
    fn start(self) -> EventBus {
        let (sender, receiver) = mpsc::channel();
        let receiver = Arc::new(Mutex::new(receiver));
        
        let handlers = Arc::new(self.handlers);
        let mut workers = vec![];
        
        // 创建工作线程
        for id in 0..self.worker_count {
            let worker_receiver = Arc::clone(&receiver);
            let worker_handlers = Arc::clone(&handlers);
            
            let handle = thread::spawn(move || {
                loop {
                    // 获取事件
                    let event = {
                        let rx = worker_receiver.lock().unwrap();
                        match rx.recv() {
                            Ok(event) => event,
                            Err(_) => break, // 通道已关闭
                        }
                    };
                    
                    // 处理事件
                    if let Some(handlers) = worker_handlers.get(&event.event_type) {
                        println!("工作线程 {} 处理事件 {}", id, event.id);
                        for handler in handlers {
                            handler.handle(&event);
                        }
                    }
                }
                
                println!("工作线程 {} 退出", id);
            });
            
            workers.push(handle);
        }
        
        EventBus {
            sender,
            workers,
        }
    }
}

// 事件总线 - 允许发布事件
struct EventBus {
    sender: mpsc::Sender<Event>,
    workers: Vec<thread::JoinHandle<()>>,
}

impl EventBus {
    fn publish(&self, event: Event) {
        self.sender.send(event).unwrap();
    }
    
    fn shutdown(self) {
        // 关闭发送端会导致接收端的迭代结束
        drop(self.sender);
        
        // 等待所有工作线程退出
        for worker in self.workers {
            worker.join().unwrap();
        }
        
        println!("事件总线已关闭");
    }
}

fn event_framework_example() {
    // 创建事件分发器
    let mut dispatcher = EventDispatcher::new(3);
    
    // 注册处理器
    dispatcher.register_handler(Arc::new(LoggingHandler));
    dispatcher.register_handler(Arc::new(AlertHandler));
    
    // 启动事件总线
    let bus = dispatcher.start();
    
    // 发布一些事件
    for i in 0..10 {
        let event_type = match i % 3 {
            0 => "log",
            1 => "alert",
            _ => "error",
        };
        
        let event = Event {
            id: i,
            event_type: event_type.to_string(),
            payload: format!("事件 {} 的数据", i),
        };
        
        bus.publish(event);
    }
    
    // 给一些时间处理事件
    thread::sleep(Duration::from_secs(3));
    
    // 关闭事件总线
    bus.shutdown();
}
```

## 6. 综合设计权衡分析

### 6.1 性能与安全性权衡

在多线程 Rust 程序中，性能与安全性的权衡常见于以下几方面：

#### 锁粒度选择

细粒度锁可提高并发度，但增加复杂性和死锁风险：

```rust
// 粗粒度锁 - 简单但可能限制并发
struct CoarseGrainedCache {
    data: Mutex<HashMap<String, String>>,
}

// 细粒度锁 - 提高并发但增加复杂性
struct FineGrainedCache {
    shards: Vec<Mutex<HashMap<String, String>>>,
    shard_count: usize,
}

impl FineGrainedCache {
    fn new(shard_count: usize) -> Self {
        let mut shards = Vec::with_capacity(shard_count);
        for _ in 0..shard_count {
            shards.push(Mutex::new(HashMap::new()));
        }
        
        FineGrainedCache {
            shards,
            shard_count,
        }
    }
    
    fn get_shard(&self, key: &str) -> usize {
        // 计算分片索引
        let mut hash = 0;
        for byte in key.bytes() {
            hash = hash.wrapping_mul(31).wrapping_add(byte as usize);
        }
        hash % self.shard_count
    }
}
```

#### 锁类型选择

不同锁类型在性能与功能间有权衡：

| 锁类型 | 优势 | 劣势 | 适用场景 |
|--------|------|------|----------|
| `Mutex` | 简单、支持可变访问 | 没有读并发 | 写操作频繁 |
| `RwLock` | 允许多读单写 | 比 Mutex 开销大 | 读多写少 |
| `parking_lot` 中的锁 | 性能更好、更小 | 非标准库 | 高性能需求 |

#### 克隆与共享的权衡

在线程间传递数据时的克隆与共享权衡：

```rust
fn clone_vs_share_example() {
    let data = vec![1, 2, 3, 4, 5];
    
    // 方案1: 克隆数据给每个线程（无需同步但消耗内存）
    let mut handles = vec![];
    for i in 0..3 {
        let data_clone = data.clone();
        let handle = thread::spawn(move || {
            println!("线程 {} 处理独立数据副本: {:?}", i, data_clone);
        });
        handles.push(handle);
    }
    
    // 方案2: 共享数据（节省内存但需同步）
    let shared_data = Arc::new(data.clone());
    for i in 0..3 {
        let data_ref = Arc::clone(&shared_data);
        let handle = thread::spawn(move || {
            println!("线程 {} 处理共享数据: {:?}", i, data_ref);
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
}
```

### 6.2 灵活性与复杂性权衡

设计多线程系统时在灵活性与复杂性间的权衡：

#### 同步模型选择

选择合适的同步模型影响了系统的灵活性和复杂性：

| 同步模型 | 灵活性 | 复杂性 | 适用场景 |
|----------|--------|--------|----------|
| 通道传递 | 中等 | 低 | 生产者-消费者模式、任务分发 |
| 共享状态 | 高 | 高 | 需要随机访问共享数据的场景 |
| Actor模型 | 高 | 中 | 基于消息的分布式系统 |
| 无锁数据结构 | 低 | 非常高 | 极端性能要求场景 |

```rust
// 示例: 不同同步模型比较
fn synchronization_models() {
    // 1. 通道模型
    let (tx, rx) = mpsc::channel();
    
    thread::spawn(move || {
        for i in 0..5 {
            tx.send(format!("消息 {}", i)).unwrap();
        }
    });
    
    for _ in 0..5 {
        let msg = rx.recv().unwrap();
        println!("接收: {}", msg);
    }
    
    // 2. 共享状态模型
    let counter = Arc::new(Mutex::new(0));
    
    let mut handles = vec![];
    for _ in 0..5 {
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
    
    println!("计数器: {}", *counter.lock().unwrap());
    
    // 3. 类Actor模型（简化版）
    struct Actor {
        receiver: Mutex<mpsc::Receiver<String>>,
        sender: mpsc::Sender<String>,
    }
    
    impl Actor {
        fn new() -> Self {
            let (tx, rx) = mpsc::channel();
            Actor {
                receiver: Mutex::new(rx),
                sender: tx,
            }
        }
        
        fn send(&self, msg: String) {
            self.sender.send(msg).unwrap();
        }
        
        fn process_messages(&self) {
            let rx = self.receiver.lock().unwrap();
            while let Ok(msg) = rx.try_recv() {
                println!("Actor处理: {}", msg);
            }
        }
    }
}
```

#### 线程模型选择

不同的线程模型在灵活性和复杂性方面也存在权衡：

| 线程模型 | 灵活性 | 复杂性 | 资源消耗 |
|----------|--------|--------|----------|
| 每请求一线程 | 高 | 低 | 高 |
| 固定线程池 | 中 | 中 | 中 |
| 工作窃取池 | 高 | 高 | 低 |
| 事件驱动 | 高 | 高 | 低 |

```rust
// 示例: 不同线程模型特点
fn thread_models_comparison() {
    // 1. 每请求一线程
    for i in 0..3 {
        thread::spawn(move || {
            println!("请求 {} 在专用线程中处理", i);
        });
    }
    
    // 2. 固定线程池
    let pool = ThreadPool::new(4); // 假设ThreadPool已定义
    
    for i in 0..10 {
        pool.execute(move || {
            println!("请求 {} 在线程池中处理", i);
        });
    }
    
    // 3. 事件驱动模型（伪代码）
    struct EventLoop {
        queue: VecDeque<Box<dyn FnOnce()>>,
    }
    
    impl EventLoop {
        fn new() -> Self {
            EventLoop { queue: VecDeque::new() }
        }
        
        fn push<F: FnOnce() + 'static>(&mut self, f: F) {
            self.queue.push_back(Box::new(f));
        }
        
        fn run(&mut self) {
            while let Some(task) = self.queue.pop_front() {
                task();
            }
        }
    }
}

// 简化的线程池实现
struct ThreadPool {
    workers: Vec<Worker>,
    sender: mpsc::Sender<Job>,
}

type Job = Box<dyn FnOnce() + Send + 'static>;

impl ThreadPool {
    fn new(size: usize) -> Self {
        let (sender, receiver) = mpsc::channel();
        let receiver = Arc::new(Mutex::new(receiver));
        
        let mut workers = Vec::with_capacity(size);
        for id in 0..size {
            workers.push(Worker::new(id, Arc::clone(&receiver)));
        }
        
        ThreadPool { workers, sender }
    }
    
    fn execute<F>(&self, f: F)
    where
        F: FnOnce() + Send + 'static,
    {
        let job = Box::new(f);
        self.sender.send(job).unwrap();
    }
}

struct Worker {
    id: usize,
    thread: thread::JoinHandle<()>,
}

impl Worker {
    fn new(id: usize, receiver: Arc<Mutex<mpsc::Receiver<Job>>>) -> Self {
        let thread = thread::spawn(move || {
            loop {
                let job = receiver.lock().unwrap().recv().unwrap();
                println!("工作线程 {} 执行任务", id);
                job();
            }
        });
        
        Worker { id, thread }
    }
}
```

### 6.3 设计决策指南

根据上述分析，以下是多线程 Rust 程序中所有权设计决策的指南：

#### 根据数据访问模式选择所有权模型

```rust
fn ownership_model_selection() {
    // 场景1: 独立数据处理 - 使用移动所有权
    let data = vec![1, 2, 3, 4, 5];
    
    thread::spawn(move || {
        // 完全拥有数据所有权
        println!("独占处理: {:?}", data);
    });
    
    // 场景2: 只读共享 - 使用 Arc
    let data = Arc::new(vec![1, 2, 3, 4, 5]);
    
    let data_clone = Arc::clone(&data);
    thread::spawn(move || {
        // 共享不可变访问
        println!("共享只读: {:?}", data_clone);
    });
    
    // 场景3: 读写共享 - 使用 Arc<Mutex>
    let data = Arc::new(Mutex::new(vec![1, 2, 3, 4, 5]));
    
    let data_clone = Arc::clone(&data);
    thread::spawn(move || {
        // 共享可变访问
        let mut guard = data_clone.lock().unwrap();
        guard.push(6);
        println!("共享读写: {:?}", guard);
    });
    
    // 场景4: 分区所有权 - 分割数据
    let mut data = vec![1, 2, 3, 4, 5, 6, 7, 8];
    
    // 取出后半部分所有权
    let second_half = data.split_off(4);
    
    let handle = thread::spawn(move || {
        // 处理后半部分
        println!("处理后半部分: {:?}", second_half);
        
        // 返回处理结果
        second_half.iter().sum::<i32>()
    });
    
    // 主线程处理前半部分
    println!("处理前半部分: {:?}", data);
    let first_sum = data.iter().sum::<i32>();
    
    // 合并结果
    let second_sum = handle.join().unwrap();
    let total = first_sum + second_sum;
    println!("总和: {}", total);
}
```

#### 根据系统特性选择同步原语

```rust
fn synchronization_primitive_selection() {
    // 场景1: 简单的互斥访问
    let counter = Mutex::new(0);
    
    // 场景2: 读多写少
    let database = RwLock::new(HashMap::new());
    
    // 场景3: 一次性初始化
    use std::sync::Once;
    static INIT: Once = Once::new();
    
    INIT.call_once(|| {
        // 只执行一次的初始化代码
        println!("初始化执行一次");
    });
    
    // 场景4: 原子操作 - 无锁计数器
    use std::sync::atomic::{AtomicUsize, Ordering};
    let atomic_counter = AtomicUsize::new(0);
    
    atomic_counter.fetch_add(1, Ordering::SeqCst);
    
    // 场景5: 屏障同步 - 等待多个线程到达同一点
    use std::sync::Barrier;
    let barrier = Arc::new(Barrier::new(3));
    
    for i in 0..3 {
        let b = Arc::clone(&barrier);
        thread::spawn(move || {
            println!("线程 {} 到达屏障前", i);
            b.wait();
            println!("线程 {} 通过屏障", i);
        });
    }
}
```

#### 任务分解与并行性策略

根据任务特性选择合适的并行策略：

```rust
fn parallelism_strategy_selection() {
    // 场景1: 数据并行 - 同样的操作应用于不同数据
    let data = vec![1, 2, 3, 4, 5, 6, 7, 8];
    let chunks = data.chunks(2); // 将数据分成多份
    
    let mut handles = vec![];
    for chunk in chunks {
        let chunk_data = chunk.to_vec();
        let handle = thread::spawn(move || {
            // 每个线程处理一小部分数据
            chunk_data.iter().map(|&x| x * x).collect::<Vec<_>>()
        });
        handles.push(handle);
    }
    
    // 合并结果
    let mut results = vec![];
    for handle in handles {
        let chunk_result = handle.join().unwrap();
        results.extend(chunk_result);
    }
    
    println!("处理结果: {:?}", results);
    
    // 场景2: 任务并行 - 不同操作并行执行
    let (tx1, rx1) = mpsc::channel();
    let (tx2, rx2) = mpsc::channel();
    
    // 任务1: 计算和
    thread::spawn(move || {
        let sum: i32 = (1..=100).sum();
        tx1.send(sum).unwrap();
    });
    
    // 任务2: 计算乘积
    thread::spawn(move || {
        let product: i32 = (1..=10).product();
        tx2.send(product).unwrap();
    });
    
    // 合并结果
    let sum = rx1.recv().unwrap();
    let product = rx2.recv().unwrap();
    
    println!("和: {}, 乘积: {}", sum, product);
    
    // 场景3: 流水线并行 - 多阶段处理
    // (简化版，实际中应使用通道连接各阶段)
    let stages = vec![
        |x: i32| x + 1,     // 阶段1
        |x: i32| x * 2,     // 阶段2
        |x: i32| x.pow(2),  // 阶段3
    ];
    
    let mut results = Vec::new();
    for i in 1..=5 {
        let mut value = i;
        for stage in &stages {
            value = stage(value);
        }
        results.push(value);
    }
    
    println!("流水线结果: {:?}", results);
}
```

## 7. 总结与最佳实践

通过以上深入分析，我们可以总结出 Rust 多线程环境下所有权管理的最佳实践：

### 所有权设计原则

1. **明确所有权边界**：清晰定义每个线程的所有权范围，尽量减少共享
2. **偏好消息传递**：优先考虑消息传递而非共享状态，符合 Rust 哲学
3. **恰当的共享粒度**：共享状态时选择合适的锁粒度，平衡并发度和复杂性
4. **在设计阶段考虑并发**：并发不是事后添加的特性，应在设计时考虑

### 多线程所有权模式总结

| 模式 | 核心机制 | 优势 | 使用场景 |
|:----:|:----|:----|:----|
| 消息传递 | 所有权转移+通道 | 清晰的所有权边界，避免竞争 | 生产者-消费者、任务分发 |
| 共享状态 | Arc+Mutex/RwLock | 高效共享访问 | 共享数据库、缓存系统 |
| 读写分离 | Arc+RwLock | 优化读取性能 | 读多写少的场景 |
| 所有权分区 | 数据分割+独立处理 | 最小化同步需求 | 可并行分解的任务 |
| 工作窃取 | 线程本地队列+窃取 | 负载均衡，避免空闲 | 动态任务系统 |

### 常见陷阱与规避策略

1. **死锁**
   - 规避策略：保持一致的锁获取顺序，尽量减少嵌套锁，使用超时锁
   - 示例：

     ```rust
     // 错误：可能导致死锁的嵌套锁
     fn transfer(from: &Mutex<Account>, to: &Mutex<Account>, amount: u64) {
         let mut from_account = from.lock().unwrap();
         // 如果另一线程以相反顺序获取锁，可能死锁
         let mut to_account = to.lock().unwrap();  
         
         from_account.withdraw(amount);
         to_account.deposit(amount);
     }
     
     // 正确：使用一致的获取顺序
     fn transfer_safe(from: &Mutex<Account>, to: &Mutex<Account>, amount: u64) {
         // 确保以一致顺序获取锁（例如，按地址排序）
         let (first, second) = if std::ptr::addr_of!(*from) < std::ptr::addr_of!(*to) {
             (from, to)
         } else {
             (to, from)
         };
         
         let mut first_account = first.lock().unwrap();
         let mut second_account = second.lock().unwrap();
         
         if std::ptr::eq(first, from) {
             first_account.withdraw(amount);
             second_account.deposit(amount);
         } else {
             second_account.withdraw(amount);
             first_account.deposit(amount);
         }
     }
     ```

2. **数据竞争**
   - 规避策略：使用适当的同步原语，避免在锁外访问受保护数据，使用原子操作
   - 示例：

     ```rust
     // 错误：潜在的数据竞争
     fn process_data(data: &mut Vec<i32>) {
         let mut handles = vec![];
         for i in 0..5 {
             // 错误：多个线程尝试访问同一可变引用
             let handle = thread::spawn(move || {
                 data[i] *= 2;  // 编译错误：无法将 data 移动到多个线程
             });
             handles.push(handle);
         }
     }
     
     // 正确：使用适当的同步
     fn process_data_safe(data: Vec<i32>) -> Vec<i32> {
         let shared_data = Arc::new(Mutex::new(data));
         let mut handles = vec![];
         
         for i in 0..5 {
             let data_clone = Arc::clone(&shared_data);
             let handle = thread::spawn(move || {
                 let mut guard = data_clone.lock().unwrap();
                 if i < guard.len() {
                     guard[i] *= 2;
                 }
             });
             handles.push(handle);
         }
         
         for handle in handles {
             handle.join().unwrap();
         }
         
         // 获取最终结果
         Arc::try_unwrap(shared_data)
             .unwrap()
             .into_inner()
             .unwrap()
     }
     ```

3. **性能瓶颈**
   - 规避策略：避免细粒度同步，减少锁持有时间，使用读写锁分离读写操作
   - 示例：

     ```rust
     // 低效：频繁锁争用
     fn increment_all(counter: &Mutex<Vec<usize>>, iterations: usize) {
         for _ in 0..iterations {
             let mut guard = counter.lock().unwrap();
             for val in guard.iter_mut() {
                 *val += 1;
             }
         }
     }
     
     // 高效：减少锁持有时间
     fn increment_all_efficient(counter: &Mutex<Vec<usize>>, iterations: usize) {
         for _ in 0..iterations {
             let mut temp;
             {
                 // 最小化锁持有时间
                 temp = counter.lock().unwrap().clone();
             }
             
             // 在锁外进行计算
             for val in temp.iter_mut() {
                 *val += 1;
             }
             
             // 仅在需要时获取锁
             let mut guard = counter.lock().unwrap();
             *guard = temp;
         }
     }
     ```

### 最终建议

1. **设计阶段考虑并发**：先明确数据流和线程模型，再编写代码
2. **遵循 Rust 的所有权哲学**：通过通信共享内存，而非通过共享内存通信
3. **始终使用最简单的方案**：从简单方案开始，只在必要时增加复杂性
4. **系统测试**：使用压力测试和并发测试工具验证设计
5. **特殊场景专门处理**：对高性能需求使用特殊技术（无锁数据结构、原子操作）

通过这些分析和最佳实践，
我们可以在 Rust 中构建既安全又高效的多线程系统，
充分利用 Rust 的所有权模型所提供的并发安全保证，同时避免常见的并发陷阱。
Rust 的类型系统和借用检查器成为了并发编程的强大盟友，
让我们能够以更加自信和高效的方式处理复杂的多线程场景。
