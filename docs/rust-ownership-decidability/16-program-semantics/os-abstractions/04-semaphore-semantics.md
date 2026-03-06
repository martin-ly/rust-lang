# 信号量的形式化语义

## 1. 引言

信号量（Semaphore）是由 Edsger Dijkstra 提出的经典同步原语，用于控制对共享资源的访问。与互斥锁不同，信号量可以允许指定数量的线程同时访问资源。本文档从形式化角度定义信号量的语义，包括计数信号量、二进制信号量以及在生产者-消费者模式中的应用。

## 2. 信号量的基本形式化模型

### 2.1 核心定义

```
信号量的形式化结构:

  Semaphore = {
    count: AtomicIsize,  // 当前可用资源数
    max: usize,          // 最大资源数（可选）
  }

  状态:
    count > 0: 有资源可用
    count = 0: 资源耗尽，后续请求将阻塞
    count < 0: 有 |count| 个线程正在等待

  不变式:
    I1: count ≤ max（计数信号量）
    I2: count ∈ {0, 1}（二进制信号量）
```

### 2.2 操作的形式化定义

```
信号量操作:

  acquire(s, n=1):
    前置: n > 0
    原子执行:
      if s.count ≥ n:
        s.count -= n
        return Success
      else:
        将当前线程加入等待队列
        阻塞线程
        return Success（当被唤醒后）

  release(s, n=1):
    前置: n > 0
    原子执行:
      s.count += n
      若有线程在等待:
        唤醒最多 n 个等待的线程

  try_acquire(s, n=1):
    原子执行:
      if s.count ≥ n:
        s.count -= n
        return Success
      else:
        return WouldBlock
```

### 2.3 状态转换图

```
信号量状态转换:

  acquire 成功: (count = k) → (count = k - 1)  if k > 0
  acquire 阻塞: (count = 0) → 线程进入等待队列
  release:      (count = k) → (count = k + n)
                并唤醒等待队列中的线程
```

## 3. 计数信号量的语义

### 3.1 一般计数信号量

```
计数信号量 CountingSemaphore(max):

  初始化:
    count = initial_value, 0 ≤ initial_value ≤ max

  用途:
    - 限制同时访问某资源的线程数
    - 控制连接池大小
    - 限制并发任务数

  形式化性质:
    1. 最多 max 个线程可以同时持有信号量
    2. 若 count < 0，有 |count| 个线程在等待
    3. release 操作可能唤醒等待的线程
```

### 3.2 Rust 代码示例

```rust
use std::sync::Arc;
use std::thread;
use std::time::Duration;

// 使用 tokio 或自定义实现
// 标准库没有直接的 Semaphore，但可以使用 parking_lot 或 tokio

use std::sync::atomic::{AtomicIsize, Ordering};

pub struct Semaphore {
    permits: AtomicIsize,
}

impl Semaphore {
    pub fn new(initial: isize) -> Self {
        Self {
            permits: AtomicIsize::new(initial),
        }
    }

    pub fn acquire(&self) {
        loop {
            let current = self.permits.load(Ordering::Acquire);
            if current > 0 {
                if self.permits.compare_exchange(
                    current,
                    current - 1,
                    Ordering::AcqRel,
                    Ordering::Relaxed
                ).is_ok() {
                    return;
                }
            }
            // 自旋或睡眠等待
            thread::yield_now();
        }
    }

    pub fn release(&self) {
        self.permits.fetch_add(1, Ordering::Release);
    }

    pub fn try_acquire(&self) -> bool {
        let current = self.permits.load(Ordering::Acquire);
        if current > 0 {
            self.permits.compare_exchange(
                current,
                current - 1,
                Ordering::AcqRel,
                Ordering::Relaxed
            ).is_ok()
        } else {
            false
        }
    }
}
```

### 3.3 使用 tokio::sync::Semaphore

```rust
use tokio::sync::Semaphore;
use std::sync::Arc;
use tokio::task;

#[tokio::main]
async fn semaphore_example() {
    // 允许最多 3 个并发任务
    let semaphore = Arc::new(Semaphore::new(3));
    let mut handles = vec![];

    for i in 0..10 {
        let permit = semaphore.clone().acquire_owned().await.unwrap();
        handles.push(task::spawn(async move {
            println!("任务 {} 开始执行", i);
            // 模拟工作
            tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
            println!("任务 {} 完成", i);
            drop(permit);  // 显式释放 permit
        }));
    }

    for handle in handles {
        handle.await.unwrap();
    }
}
```

## 4. 二进制信号量（互斥锁）

### 4.1 二进制信号量的形式化

```
二进制信号量 BinarySemaphore:

  约束:
    count ∈ {0, 1} 始终成立

  等价于:
    互斥锁（但语义略有不同）

  区别:
    - Mutex: 只有持有锁的线程才能释放
    - Binary Semaphore: 任何线程都可以释放

  状态:
    Available: count = 1
    Held: count = 0
```

### 4.2 与互斥锁的比较

```
比较矩阵:

特性              Mutex               Binary Semaphore
---------------------------------------------------------
所有权            有（持有线程专属）    无
释放权限          仅持有者可释放        任何线程可释放
递归获取          通常不支持            不支持
用途              保护临界区            信号通知
```

### 4.3 Rust 代码示例

```rust
use std::sync::Arc;
use std::thread;
use std::time::Duration;

// 使用标准库的 Mutex 作为二进制信号量的替代
// 或使用 parking_lot 的 fair mutex

use std::sync::atomic::{AtomicBool, Ordering};

pub struct BinarySemaphore {
    flag: AtomicBool,
}

impl BinarySemaphore {
    pub fn new(initial: bool) -> Self {
        Self {
            flag: AtomicBool::new(initial),
        }
    }

    pub fn wait(&self) {
        // 等待 flag 变为 true，然后设为 false
        while !self.flag.swap(false, Ordering::Acquire) {
            thread::yield_now();
        }
    }

    pub fn signal(&self) {
        self.flag.store(true, Ordering::Release);
    }

    pub fn try_wait(&self) -> bool {
        self.flag.swap(false, Ordering::Acquire)
    }
}

// 使用示例：两个线程交替执行
fn alternating_example() {
    let sem1 = Arc::new(BinarySemaphore::new(true));
    let sem2 = Arc::new(BinarySemaphore::new(false));

    let sem1_clone = Arc::clone(&sem1);
    let sem2_clone = Arc::clone(&sem2);

    thread::spawn(move || {
        for i in 0..5 {
            sem1_clone.wait();
            println!("线程 A 执行步骤 {}", i);
            sem2_clone.signal();
        }
    });

    for i in 0..5 {
        sem2.wait();
        println!("线程 B 执行步骤 {}", i);
        sem1.signal();
    }
}
```

## 5. 生产者-消费者模式的形式化

### 5.1 有界缓冲区的形式化定义

```
生产者-消费者问题:

  数据结构:
    BoundedBuffer<T> = {
      buffer: Array<T>,
      size: usize,
      empty_slots: Semaphore(n),     // 可用空槽数
      filled_slots: Semaphore(0),    // 已填充槽数
      mutex: Mutex                   // 保护缓冲区访问
    }

  不变式:
    I1: empty_slots.count + filled_slots.count = n（总槽数）
    I2: 0 ≤ 缓冲区中的元素数 ≤ n
    I3: mutex 保护对 buffer 的访问
```

### 5.2 操作语义

```
produce(item):
  1. empty_slots.acquire()   // 等待有空槽
  2. mutex.lock()
  3. buffer.push(item)
  4. mutex.unlock()
  5. filled_slots.release()  // 通知有新数据

consume():
  1. filled_slots.acquire()  // 等待有数据
  2. mutex.lock()
  3. item = buffer.pop()
  4. mutex.unlock()
  5. empty_slots.release()   // 通知有空槽
  6. return item
```

### 5.3 Rust 代码实现

```rust
use std::sync::{Arc, Mutex, Condvar};
use std::thread;
use std::collections::VecDeque;

// 使用 Semaphore 语义实现的有界缓冲区
pub struct SemaphoreBoundedBuffer<T> {
    buffer: Mutex<VecDeque<T>>,
    capacity: usize,
    empty_sem: Condvar,   // 模拟 empty_slots 信号量
    full_sem: Condvar,    // 模拟 filled_slots 信号量
}

impl<T> SemaphoreBoundedBuffer<T> {
    pub fn new(capacity: usize) -> Self {
        Self {
            buffer: Mutex::new(VecDeque::new()),
            capacity,
            empty_sem: Condvar::new(),
            full_sem: Condvar::new(),
        }
    }

    pub fn produce(&self, item: T) {
        let mut buffer = self.buffer.lock().unwrap();

        // 等待有空槽（相当于 empty_slots.acquire()）
        while buffer.len() >= self.capacity {
            buffer = self.empty_sem.wait(buffer).unwrap();
        }

        buffer.push_back(item);

        // 通知消费者有新数据（相当于 filled_slots.release()）
        self.full_sem.notify_one();
    }

    pub fn consume(&self) -> T {
        let mut buffer = self.buffer.lock().unwrap();

        // 等待有数据（相当于 filled_slots.acquire()）
        while buffer.is_empty() {
            buffer = self.full_sem.wait(buffer).unwrap();
        }

        let item = buffer.pop_front().unwrap();

        // 通知生产者有空槽（相当于 empty_slots.release()）
        self.empty_sem.notify_one();

        item
    }
}

// 使用 tokio::sync::Semaphore 的现代实现
#[cfg(feature = "tokio")]
mod modern_impl {
    use tokio::sync::Semaphore;
    use std::sync::Arc;

    pub struct ModernBoundedBuffer<T> {
        buffer: async_channel::Bounded<T>,
        _phantom: std::marker::PhantomData<T>,
    }

    // 或使用标准库的 mpsc
    pub fn mpsc_example() {
        let (tx, rx) = std::sync::mpsc::sync_channel(10);  // 容量为 10

        std::thread::spawn(move || {
            for i in 0..100 {
                tx.send(i).expect("发送失败");
                println!("发送: {}", i);
            }
        });

        for received in rx {
            println!("接收: {}", received);
        }
    }
}
```

## 6. 多资源管理的形式化

### 6.1 资源池的形式化

```
资源池 ResourcePool<R>:

  组成:
    available: Semaphore(n)     // 可用资源计数
    resources: Mutex<Vec<R>>    // 可用资源队列
    in_use: AtomicUsize         // 正在使用的资源数

  操作:
    acquire():
      available.acquire()
      mutex.lock()
      r = resources.pop()
      in_use += 1
      mutex.unlock()
      return r

    release(r):
      mutex.lock()
      resources.push(r)
      in_use -= 1
      mutex.unlock()
      available.release()
```

### 6.2 Rust 实现

```rust
use std::sync::{Arc, Mutex, Semaphore as StdSemaphore};
use std::thread;

pub struct ResourcePool<R> {
    semaphore: StdSemaphore,
    resources: Mutex<Vec<R>>,
}

impl<R> ResourcePool<R> {
    pub fn new(resources: Vec<R>) -> Self {
        let count = resources.len();
        Self {
            semaphore: StdSemaphore::new(count),
            resources: Mutex::new(resources),
        }
    }

    pub fn acquire(&self) -> R {
        self.semaphore.acquire().expect("信号量错误");
        let mut resources = self.resources.lock().unwrap();
        resources.pop().expect("资源池为空但信号量允许获取")
    }

    pub fn release(&self, resource: R) {
        let mut resources = self.resources.lock().unwrap();
        resources.push(resource);
        drop(resources);  // 先释放锁，再释放信号量
        self.semaphore.release();
    }
}

// 使用示例：数据库连接池
struct DbConnection {
    id: usize,
}

fn connection_pool_example() {
    let connections: Vec<DbConnection> = (0..5)
        .map(|i| DbConnection { id: i })
        .collect();

    let pool = Arc::new(ResourcePool::new(connections));
    let mut handles = vec![];

    for i in 0..10 {
        let pool = Arc::clone(&pool);
        handles.push(thread::spawn(move || {
            let conn = pool.acquire();
            println!("线程 {} 获取连接 {}", i, conn.id);
            // 使用连接...
            thread::sleep(std::time::Duration::from_millis(100));
            println!("线程 {} 释放连接 {}", i, conn.id);
            pool.release(conn);
        }));
    }

    for h in handles {
        h.join().unwrap();
    }
}
```

## 7. 信号量的高级模式

### 7.1 读写信号量

```
读写信号量 (多读者单写者):

  结构:
    read_sem: Semaphore(max_readers)
    write_sem: Semaphore(1)
    reader_count: AtomicUsize

  读操作:
    read_sem.acquire()
    if reader_count.fetch_add(1) == 0:
        write_sem.acquire()  // 第一个读者阻止写者
    read_sem.release()
    // 执行读操作
    if reader_count.fetch_sub(1) == 1:
        write_sem.release()  // 最后一个读者允许写者

  写操作:
    write_sem.acquire()
    // 执行写操作
    write_sem.release()
```

### 7.2 屏障信号量

```rust
// 使用信号量实现屏障
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, Condvar};

pub struct SemaphoreBarrier {
    count: AtomicUsize,
    target: usize,
    mutex: Mutex<()>,
    cond: Condvar,
}

impl SemaphoreBarrier {
    pub fn new(count: usize) -> Self {
        Self {
            count: AtomicUsize::new(0),
            target: count,
            mutex: Mutex::new(()),
            cond: Condvar::new(),
        }
    }

    pub fn wait(&self) {
        let mut lock = self.mutex.lock().unwrap();
        let current = self.count.fetch_add(1, Ordering::SeqCst);

        if current + 1 >= self.target {
            // 最后一个到达的线程唤醒所有等待者
            self.count.store(0, Ordering::SeqCst);
            self.cond.notify_all();
        } else {
            // 等待其他线程
            while self.count.load(Ordering::SeqCst) != 0 {
                lock = self.cond.wait(lock).unwrap();
            }
        }
    }
}
```

## 8. 综合安全论证

### 8.1 信号量的正确性定理

```
定理 (信号量不变式):
  对于计数信号量 S，始终满足:
  -S.waiting_count ≤ S.count ≤ S.max

  其中 waiting_count 是正在等待的线程数

定理 (互斥保证):
  对于初始值为 1 的二进制信号量，
  任意时刻最多只有一个线程可以获取它

定理 (有限等待):
  若信号量使用 FIFO 队列管理等待线程，
  则线程等待时间是有限的（无饥饿）
```

### 8.2 不变式总结

```
信号量使用的核心不变式:

I1 (计数非负性):
  信号量的计数值永远不会为负
  （虽然内部实现可能用负数表示等待线程）

I2 (资源守恒):
  每个成功的 acquire 必须对应一个 release

I3 (原子性):
  acquire 和 release 操作是原子的

I4 ( happens-before ):
  release 操作 happens-before 被唤醒的 acquire

I5 (互斥保证 - 二进制信号量):
  最多一个线程可以持有二进制信号量
```

## 9. 总结

本文档完整形式化了信号量的语义：

1. **基本模型**：定义了信号量的结构和核心操作
2. **计数信号量**：允许指定数量的并发访问
3. **二进制信号量**：等效于互斥锁但语义略有不同
4. **生产者-消费者**：展示了信号量在经典问题中的应用
5. **资源池**：演示了信号量在资源管理中的作用
6. **高级模式**：读写信号量和屏障信号量

这些形式化定义确保了 Rust 程序在使用信号量进行并发控制时的正确性和安全性。
