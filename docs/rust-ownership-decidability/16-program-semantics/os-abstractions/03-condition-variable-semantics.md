# 条件变量的形式化语义

## 1. 引言

条件变量（Condition Variable）是同步原语的重要组成部分，用于线程间的协作，允许线程在某个条件不满足时阻塞等待，直到被其他线程通知。Rust 通过 `std::sync::Condvar` 提供了条件变量的实现。本文档从形式化角度定义条件变量的语义，包括 wait/notify 操作、与互斥锁的交互以及虚假唤醒的处理。

## 2. 条件变量的基本形式化模型

### 2.1 核心概念定义

```
条件变量 Condvar 的形式化结构:

  Condvar = {
    wait_queue: Queue<ThreadId>,
    monitor: Monitor
  }

  关联:
    每个 Condvar 必须关联一个 Mutex（监视器模式）

状态:
  CVState ::= Empty | Waiting(℘(ThreadId))
```

### 2.2 操作的形式化定义

```
条件变量操作:

  wait(cv, mutex):
    前置: 当前线程持有 mutex
    执行:
      1. 原子性: 释放 mutex 并加入 cv 的等待队列
      2. 阻塞当前线程
      3. 被唤醒后，重新获取 mutex
    后置: 当前线程持有 mutex

  notify_one(cv):
    执行:
      1. 若 cv.wait_queue 非空
      2. 从队列中移除一个线程 t
      3. 唤醒线程 t

  notify_all(cv):
    执行:
      1. 遍历 cv.wait_queue 中的所有线程
      2. 唤醒所有等待的线程
      3. 清空等待队列
```

## 3. Wait/Notify 的精确语义

### 3.1 Wait 操作的详细语义

```
wait 操作的三阶段原子性:

  阶段 1: 进入等待
    - 验证前置条件: mutex 被当前线程持有
    - 将当前线程加入条件变量的等待队列

  阶段 2: 原子性释放与阻塞
    - 原子操作: release(mutex) AND block(self)
    - 关键点: 这两个操作必须原子性执行，否则可能丢失通知

  阶段 3: 唤醒与重新获取
    - 线程被 notify 唤醒
    - 尝试重新获取 mutex
    - 返回时保证持有 mutex

happens-before 关系:
  notify() → wait() 返回

  这意味着:
  - notify 之前的所有操作对 wait 返回后的操作可见
  - 确保条件变量的正确同步语义
```

### 3.2 Notify 操作的语义

```
notify_one 语义:

  若等待队列非空:
    - 恰好唤醒一个线程
    - 被唤醒的线程从队列中移除
    - 被唤醒的线程进入 Runnable 状态

  若等待队列为空:
    - 操作无效果（通知丢失）

notify_all 语义:

  - 唤醒等待队列中的所有线程
  - 所有被唤醒的线程竞争重新获取 mutex
  - 只有一个线程能获得 mutex 并继续执行
  - 其他线程在 mutex 上阻塞
```

### 3.3 Rust 代码示例

```rust
use std::sync::{Arc, Mutex, Condvar};
use std::thread;
use std::time::Duration;

fn condvar_basic_example() {
    let pair = Arc::new((Mutex::new(false), Condvar::new()));
    let pair_clone = Arc::clone(&pair);

    // 生产者线程
    thread::spawn(move || {
        let (lock, cvar) = &*pair_clone;
        let mut started = lock.lock().unwrap();
        *started = true;
        println!("生产者: 设置 started = true");
        cvar.notify_one();  // 通知等待的线程
    });

    // 消费者线程（主线程）
    let (lock, cvar) = &*pair;
    let mut started = lock.lock().unwrap();

    // 等待条件满足
    while !*started {
        // wait 会自动释放 lock 并阻塞
        // 被唤醒后自动重新获取 lock
        started = cvar.wait(started).unwrap();
    }

    println!("消费者: 检测到 started = true，继续执行");
}
```

## 4. 与互斥锁的交互语义

### 4.1 监视器模式的形式化

```
监视器模式 (Monitor Pattern):

  结构:
    Monitor = Mutex × Condvar(s)

  不变式:
    I1: 访问共享数据必须先获取关联的 mutex
    I2: 调用 wait 时必须先持有 mutex
    I3: wait 返回后自动重新持有 mutex
    I4: 调用 notify 时通常应持有 mutex（保证 happens-before）

  正确性条件:
    ∀对共享数据的访问:
      - 在临界区内（持有 mutex）
      - 条件判断使用 while 循环（处理虚假唤醒）
```

### 4.2 锁所有权转移的形式化

```
wait 操作的所有权转移:

  进入 wait 前:
    线程 T 持有 MutexGuard

  wait 执行中:
    MutexGuard 被暂时释放（所有权返回给 mutex）
    线程 T 进入阻塞状态

  wait 返回后:
    线程 T 重新获得 MutexGuard

  类型系统保证:
    wait 接收 MutexGuard，返回 MutexGuard
    确保所有权始终被正确管理
```

### 4.3 代码示例：生产者-消费者

```rust
use std::sync::{Arc, Mutex, Condvar};
use std::thread;
use std::collections::VecDeque;

struct BoundedBuffer<T> {
    queue: Mutex<VecDeque<T>>,
    not_full: Condvar,
    not_empty: Condvar,
    capacity: usize,
}

impl<T> BoundedBuffer<T> {
    fn new(capacity: usize) -> Self {
        Self {
            queue: Mutex::new(VecDeque::new()),
            not_full: Condvar::new(),
            not_empty: Condvar::new(),
            capacity,
        }
    }

    fn push(&self, item: T) {
        let mut queue = self.queue.lock().unwrap();

        // 等待缓冲区不满
        while queue.len() >= self.capacity {
            queue = self.not_full.wait(queue).unwrap();
        }

        queue.push_back(item);
        self.not_empty.notify_one();
    }

    fn pop(&self) -> T {
        let mut queue = self.queue.lock().unwrap();

        // 等待缓冲区不空
        while queue.is_empty() {
            queue = self.not_empty.wait(queue).unwrap();
        }

        let item = queue.pop_front().unwrap();
        self.not_full.notify_one();
        item
    }
}

fn producer_consumer_example() {
    let buffer = Arc::new(BoundedBuffer::new(10));
    let buffer_consume = Arc::clone(&buffer);

    // 生产者线程
    thread::spawn(move || {
        for i in 0..20 {
            buffer.push(i);
            println!("生产者: 放入 {}", i);
        }
    });

    // 消费者线程
    thread::spawn(move || {
        for _ in 0..20 {
            let item = buffer_consume.pop();
            println!("消费者: 取出 {}", item);
        }
    });
}
```

## 5. 虚假唤醒的处理

### 5.1 虚假唤醒的形式化定义

```
虚假唤醒 (Spurious Wakeup):

  定义:
    线程在没有收到 notify 的情况下从 wait 返回

  原因:
    - 操作系统/硬件层面的信号干扰
    - 某些 POSIX 实现的特性
    - 内核调度器的实现细节

  语义影响:
    调用 wait 返回 ≠ 条件已满足
    必须重新检查条件
```

### 5.2 使用 While 循环的必要性

```
正确使用模式:

  // 错误方式（可能遗漏虚假唤醒）:
  if !condition {
      wait(&condvar, &mutex);  // 危险！
  }

  // 正确方式:
  while !condition {
      wait(&condvar, &mutex);  // 安全
  }

形式化论证:
  设 P 为谓词（需要满足的条件）

  不变式:
    wait 返回后，必须重新验证 P

  证明:
    情况 1: 正常唤醒（notify 触发）
      - 其他线程可能在我们被调度前改变了状态
      - 需要重新检查 P

    情况 2: 虚假唤醒
      - P 可能仍然不成立
      - 必须重新检查 P

    结论: 两种情况下都需要 while 循环
```

### 5.3 安全论证

```
定理: 使用 while 循环的条件变量模式是正确的

证明:
  设线程 T 等待条件 P

  前置条件:
    T 持有 mutex

  循环不变式:
    I: T 持有 mutex ∧ (P ∨ T 在 condvar 的等待队列中)

  初始化:
    第一次检查 P 时，T 持有 mutex
    若 P 不成立，T 进入 wait
    原子操作确保: release(mutex) + 加入队列 是一体的
    因此 I 成立

  保持:
    当 T 从 wait 返回:
      - T 重新获得 mutex
      - 可能情况:
        a) 正常唤醒: 其他线程设置了 P 并调用 notify
           P 可能为真，但也可能被其他线程改变
        b) 虚假唤醒: P 状态未知
      - 重新检查 P，I 保持

  终止:
    假设程序正确，P 最终会被设为真
    当 P 为真时，循环退出

  ∎
```

## 6. 超时等待的语义

### 6.1 WaitTimeout 的形式化定义

```
wait_timeout(cv, mutex, timeout):

  参数:
    timeout: Duration

  执行:
    1. 原子性释放 mutex 并阻塞
    2. 等待条件:
       - 收到 notify，或
       - 超时时间到达
    3. 重新尝试获取 mutex

  返回:
    (MutexGuard, WaitTimeoutResult)

  WaitTimeoutResult:
    - is_timeout(): bool  // true 表示超时，false 表示被 notify

  语义:
    超时返回 ≠ 条件满足
    仍然需要检查条件
```

### 6.2 Rust 代码示例

```rust
use std::sync::{Mutex, Condvar};
use std::time::Duration;

fn timeout_example() {
    let pair = (Mutex::new(false), Condvar::new());

    let (lock, cvar) = &pair;
    let mut guard = lock.lock().unwrap();

    // 带超时的等待
    let timeout = Duration::from_millis(100);

    while !*guard {
        let result = cvar.wait_timeout(guard, timeout).unwrap();
        guard = result.0;

        if result.1.timed_out() {
            println!("等待超时！");
            // 可以选择重试或放弃
            break;
        }
    }

    if *guard {
        println!("条件满足！");
    }
}
```

## 7. 多条件变量的协调

### 7.1 多 Condvar 共享一个 Mutex

```rust
use std::sync::{Mutex, Condvar};

struct ComplexState {
    data_ready: bool,
    processing_done: bool,
}

struct MultiCondvarSystem {
    state: Mutex<ComplexState>,
    data_cond: Condvar,
    processing_cond: Condvar,
}

impl MultiCondvarSystem {
    fn new() -> Self {
        Self {
            state: Mutex::new(ComplexState {
                data_ready: false,
                processing_done: false,
            }),
            data_cond: Condvar::new(),
            processing_cond: Condvar::new(),
        }
    }

    // 数据生产者
    fn produce_data(&self) {
        let mut state = self.state.lock().unwrap();
        // 生成数据...
        state.data_ready = true;
        self.data_cond.notify_one();
    }

    // 数据处理器
    fn wait_and_process(&self) {
        let mut state = self.state.lock().unwrap();

        while !state.data_ready {
            state = self.data_cond.wait(state).unwrap();
        }

        // 处理数据...
        state.processing_done = true;
        self.processing_cond.notify_one();
    }

    // 结果收集者
    fn wait_for_completion(&self) {
        let mut state = self.state.lock().unwrap();

        while !state.processing_done {
            state = self.processing_cond.wait(state).unwrap();
        }

        println!("处理完成！");
    }
}
```

### 7.2 形式化分析

```
多条件变量协调的正确性:

  不变式:
    I1: data_cond 只在 data_ready 改变时 notify
    I2: processing_cond 只在 processing_done 改变时 notify
    I3: 每个条件变量对应一个特定的谓词

  优势:
    - 避免不必要的唤醒（精确通知）
    - 不同等待条件的线程互不干扰

  注意事项:
    - 仍然使用 while 循环检查条件
    - 多个条件变量共享同一个 mutex
```

## 8. 综合安全论证

### 8.1 条件变量的正确性定理

```
定理: 正确使用 Condvar 的程序不会出现以下问题:

  1. 数据竞争:
     - wait 操作确保释放和阻塞是原子的
     - 返回后自动重新持有锁

  2. 信号丢失:
     - 虽然 notify 可能丢失，但 while 循环确保最终会检测到条件

  3. 死锁:
     - 避免在持有多个锁时调用 wait
     - 确保 notify 最终会被调用
```

### 8.2 不变式总结

```
条件变量使用的核心不变式:

I1 (关联性):
  每个 Condvar 应该关联一个明确的互斥锁和条件谓词

I2 (原子性):
  wait 操作的原子性: release(lock) + block 是一个不可分割的操作

I3 (循环检查):
  总是使用 while 循环而不是 if 语句检查条件

I4 ( happens-before ):
  notify 调用 happens-before 对应 wait 的返回

I5 (互斥保证):
  wait 返回后，调用者持有互斥锁
```

## 9. 总结

本文档完整形式化了 Rust 条件变量的语义：

1. **基本模型**：定义了条件变量的状态和操作
2. **Wait/Notify**：详细形式化了等待和通知的语义
3. **互斥锁交互**：阐明了监视器模式和所有权转移
4. **虚假唤醒**：论证了 while 循环的必要性
5. **超时等待**：定义了超时语义和处理方式
6. **多 Condvar**：展示了多个条件变量协调使用的模式

这些形式化定义确保了 Rust 程序在使用条件变量进行线程协作时的正确性和安全性。
