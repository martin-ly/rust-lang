# 屏障的形式化语义

## 1. 引言

屏障（Barrier）是一种同步原语，用于协调多个线程在程序中的特定点汇合。所有到达屏障的线程都必须等待，直到所有参与线程都到达后，才能继续执行。这种"汇合-然后-继续"的模式在并行算法中非常常见。本文档从形式化角度定义屏障的语义。

## 2. 屏障的基本形式化模型

### 2.1 核心概念定义

```
屏障 Barrier 的形式化结构:

  Barrier = {
    capacity: usize,           // 需要等待的线程总数
    arrived: AtomicUsize,      // 已到达的线程数
    generation: AtomicUsize,   // 当前代（用于循环屏障）
    lock: Mutex,               // 保护条件变量
    cond: Condvar              // 用于线程阻塞/唤醒
  }

  状态:
    BarrierState ::= Waiting(n) | Tripped(g)

    Waiting(n): 还有 n 个线程未到达
    Tripped(g): 屏障已触发，正在处理第 g 代
```

### 2.2 屏障操作的形式化定义

```
屏障操作:

  wait(barrier):
    执行:
      1. lock.lock()
      2. arrived += 1
      3. 如果 arrived < capacity:
           // 不是最后一个，等待
           cond.wait()
           lock.unlock()
           return BarrierWaitResult(false)
         否则:
           // 最后一个到达，触发屏障
           arrived = 0
           generation += 1
           cond.notify_all()
           lock.unlock()
           return BarrierWaitResult(true)  // 领导者

  循环屏障 (CyclicBarrier):
    触发后自动重置，可以重复使用
```

### 2.3 状态转换图

```
屏障状态转换:

  初始状态: arrived = 0

  线程到达: arrived = n → arrived = n + 1

  屏障触发条件: arrived = capacity

  触发后:
    - arrived 重置为 0
    - generation 增加
    - 所有等待线程被唤醒

  下一周期开始
```

## 3. 同步屏障的形式化语义

### 3.1 单次屏障的语义

```
单次屏障 SingleBarrier:

  用途:
    一组线程在某点汇合，然后各自继续执行

  形式化性质:
    1. ∀线程 t ∈ 参与者, t 在 wait 处阻塞
    2. 当 |{t: t 已调用 wait}| = capacity 时，屏障触发
    3. 所有线程被唤醒后继续执行

  happens-before 关系:
    ∀t1, t2 ∈ 参与者,
    t1 在 wait 之前的操作 happens-before t2 从 wait 返回后的操作
```

### 3.2 Rust 代码示例

```rust
use std::sync::{Arc, Barrier};
use std::thread;

fn single_barrier_example() {
    // 创建容量为 3 的屏障
    let barrier = Arc::new(Barrier::new(3));
    let mut handles = vec![];

    for i in 0..3 {
        let b = Arc::clone(&barrier);
        handles.push(thread::spawn(move || {
            println!("线程 {} 开始第一阶段", i);
            // 第一阶段工作
            thread::sleep(std::time::Duration::from_millis(i as u64 * 100));

            // 等待所有线程到达
            let result = b.wait();
            if result.is_leader() {
                println!("线程 {} 是领导者", i);
            }

            println!("线程 {} 进入第二阶段", i);
            // 第二阶段工作
        }));
    }

    for h in handles {
        h.join().unwrap();
    }
}
```

### 3.3 安全论证

```
屏障的安全性证明:

定理: 正确使用屏障时，所有参与者都会在屏障点同步

证明:
  设屏障容量为 n

  1. 前 n-1 个调用 wait 的线程:
     - arrived < capacity
     - 在 condvar 上阻塞

  2. 第 n 个调用 wait 的线程:
     - arrived = capacity
     - 触发屏障
     - 唤醒所有等待线程
     - 重置屏障状态

  3. 所有线程继续执行

  因此，所有线程在屏障点完成同步
  ∎
```

## 4. CyclicBarrier 的形式化语义

### 4.1 循环屏障的定义

```
CyclicBarrier:

  与单次屏障的区别:
    - 触发后自动重置
    - 可以重复使用
    - 需要 generation 计数防止旧通知干扰

  形式化结构:
    CyclicBarrier = {
      capacity: usize,
      arrived: AtomicUsize,
      generation: AtomicUsize,  // 关键：区分不同周期
      broken: AtomicBool,       // 屏障是否损坏
      lock: Mutex,
      cond: Condvar
    }
```

### 4.2 Generation 机制的形式化

```
Generation 机制的作用:

  问题:
    线程 A 在第 1 周期等待
    线程 B 在第 2 周期到达并触发屏障
    如果没有 generation，A 会被错误唤醒

  解决方案:
    每个 wait 调用记录当前 generation
    只有 generation 匹配的唤醒才有效

  形式化:
    wait():
      my_gen = generation.load()
      // ... 等待逻辑
      while current_gen == my_gen:
        cond.wait()
      // generation 变化，说明屏障已触发
```

### 4.3 Rust 代码实现

```rust
use std::sync::atomic::{AtomicUsize, AtomicBool, Ordering};
use std::sync::{Mutex, Condvar};

pub struct CyclicBarrier {
    capacity: usize,
    arrived: AtomicUsize,
    generation: AtomicUsize,
    broken: AtomicBool,
    lock: Mutex<()>,
    cond: Condvar,
}

impl CyclicBarrier {
    pub fn new(capacity: usize) -> Self {
        Self {
            capacity,
            arrived: AtomicUsize::new(0),
            generation: AtomicUsize::new(0),
            broken: AtomicBool::new(false),
            lock: Mutex::new(()),
            cond: Condvar::new(),
        }
    }

    pub fn wait(&self) -> Result<bool, ()> {
        let mut lock = self.lock.lock().unwrap();

        if self.broken.load(Ordering::SeqCst) {
            return Err(());
        }

        let my_gen = self.generation.load(Ordering::SeqCst);
        let arrived = self.arrived.fetch_add(1, Ordering::SeqCst) + 1;

        if arrived == self.capacity {
            // 最后一个到达，触发屏障
            self.arrived.store(0, Ordering::SeqCst);
            self.generation.fetch_add(1, Ordering::SeqCst);
            self.cond.notify_all();
            Ok(true)  // 是领导者
        } else {
            // 等待其他线程
            while self.generation.load(Ordering::SeqCst) == my_gen
                  && !self.broken.load(Ordering::SeqCst) {
                lock = self.cond.wait(lock).unwrap();
            }

            if self.broken.load(Ordering::SeqCst) {
                Err(())
            } else {
                Ok(false)
            }
        }
    }

    pub fn reset(&self) {
        let mut lock = self.lock.lock().unwrap();
        self.arrived.store(0, Ordering::SeqCst);
        self.generation.fetch_add(1, Ordering::SeqCst);
        self.broken.store(false, Ordering::SeqCst);
        self.cond.notify_all();
    }
}

// 使用示例
fn cyclic_barrier_example() {
    use std::sync::Arc;
    use std::thread;

    let barrier = Arc::new(CyclicBarrier::new(3));
    let mut handles = vec![];

    for i in 0..3 {
        let b = Arc::clone(&barrier);
        handles.push(thread::spawn(move || {
            for round in 0..3 {
                println!("线程 {} 第 {} 轮开始", i, round);
                thread::sleep(std::time::Duration::from_millis(50));

                let is_leader = b.wait().unwrap();
                if is_leader {
                    println!("  线程 {} 是第 {} 轮的领导者", i, round);
                }

                println!("线程 {} 第 {} 轮继续", i, round);
            }
        }));
    }

    for h in handles {
        h.join().unwrap();
    }
}
```

## 5. 栅栏模式的应用

### 5.1 并行分阶段计算

```
并行分阶段计算模式:

  阶段 1 (并行):
    线程 1 处理数据块 A
    线程 2 处理数据块 B
    线程 3 处理数据块 C

  屏障 1:
    等待所有线程完成阶段 1

  阶段 2 (并行):
    基于阶段 1 的结果继续处理

  形式化:
    ∀i, phase_1_end[i] happens-before phase_2_start[j]
    ∀i, j
```

### 5.2 并行排序示例

```rust
use std::sync::Arc;
use std::thread;

fn parallel_merge_sort_example() {
    // 使用屏障协调多阶段并行排序
    let data = Arc::new(std::sync::Mutex::new(vec![
        9, 3, 7, 1, 5, 2, 8, 4, 6, 0
    ]));

    // 创建多个屏障用于不同阶段的同步
    let barrier1 = Arc::new(std::sync::Barrier::new(2));
    let barrier2 = Arc::new(std::sync::Barrier::new(2));

    let data_clone = Arc::clone(&data);
    let b1_clone = Arc::clone(&barrier1);
    let b2_clone = Arc::clone(&barrier2);

    // 线程 A：处理前半部分
    let handle1 = thread::spawn(move || {
        {
            let mut d = data.lock().unwrap();
            let mid = d.len() / 2;
            d[0..mid].sort();  // 排序前半部分
            println!("线程 A: 前半部分排序完成: {:?}", &d[0..mid]);
        }

        b1_clone.wait();  // 等待线程 B 完成

        // 第二阶段：可以在这里进行合并准备
        println!("线程 A: 进入第二阶段");

        b2_clone.wait();  // 再次同步
    });

    // 线程 B：处理后半部分
    {
        let mut d = data_clone.lock().unwrap();
        let mid = d.len() / 2;
        d[mid..].sort();  // 排序后半部分
        println!("线程 B: 后半部分排序完成: {:?}", &d[mid..]);
    }

    barrier1.wait();  // 等待线程 A 完成第一阶段

    // 第二阶段
    println!("线程 B: 进入第二阶段");

    barrier2.wait();

    // 最终合并
    {
        let mut d = data.lock().unwrap();
        let mid = d.len() / 2;
        let mut result = merge(&d[0..mid], &d[mid..]);
        std::mem::swap(&mut *d, &mut result);
        println!("最终排序结果: {:?}", *d);
    }

    handle1.join().unwrap();
}

fn merge(left: &[i32], right: &[i32]) -> Vec<i32> {
    let mut result = Vec::with_capacity(left.len() + right.len());
    let (mut i, mut j) = (0, 0);

    while i < left.len() && j < right.len() {
        if left[i] <= right[j] {
            result.push(left[i]);
            i += 1;
        } else {
            result.push(right[j]);
            j += 1;
        }
    }

    result.extend_from_slice(&left[i..]);
    result.extend_from_slice(&right[j..]);
    result
}
```

## 6. 屏障与 Happens-Before 关系

### 6.1 同步语义的形式化

```
屏障的 Happens-Before 关系:

  定义:
    设 B 是一个屏障，T = {t1, t2, ..., tn} 是参与者线程

  规则:
    ∀ti ∈ T, 操作 A 在 ti.wait() 之前调用
    ∀tj ∈ T, 操作 B 在 tj.wait() 之后调用

    则: A happens-before B

  意义:
    屏障建立了所有参与者之间的同步点
    确保屏障前的所有操作对所有参与者可见
```

### 6.2 内存序分析

```rust
use std::sync::atomic::{AtomicUsize, Ordering};

// 屏障隐式使用的内存序

// 标准库 Barrier 保证:
// - wait() 调用有 Acquire-Release 语义
// - 所有屏障前的写操作对屏障后的读操作可见

fn memory_ordering_example() {
    use std::sync::{Arc, Barrier};
    use std::thread;
    use std::sync::atomic::AtomicBool;

    let flag = Arc::new(AtomicBool::new(false));
    let barrier = Arc::new(Barrier::new(2));

    let flag_clone = Arc::clone(&flag);
    let barrier_clone = Arc::clone(&barrier);

    thread::spawn(move || {
        // 写操作
        flag_clone.store(true, Ordering::Relaxed);
        println!("线程 1: flag 已设置");

        // 屏障确保写操作在 wait 返回前完成
        barrier_clone.wait();
    });

    barrier.wait();

    // 这里可以安全地读取 flag
    // 屏障建立了 happens-before 关系
    let value = flag.load(Ordering::Relaxed);
    println!("线程 2: flag = {}", value);
    // 保证输出 "flag = true"
}
```

## 7. 屏障的高级模式

### 7.1 可中断屏障

```rust
use std::sync::atomic::{AtomicUsize, AtomicBool, Ordering};
use std::sync::{Mutex, Condvar};

pub struct InterruptibleBarrier {
    capacity: usize,
    arrived: AtomicUsize,
    broken: AtomicBool,
    lock: Mutex<()>,
    cond: Condvar,
}

impl InterruptibleBarrier {
    pub fn new(capacity: usize) -> Self {
        Self {
            capacity,
            arrived: AtomicUsize::new(0),
            broken: AtomicBool::new(false),
            lock: Mutex::new(()),
            cond: Condvar::new(),
        }
    }

    pub fn wait(&self) -> Result<bool, BarrierBrokenError> {
        let mut lock = self.lock.lock().unwrap();

        if self.broken.load(Ordering::SeqCst) {
            return Err(BarrierBrokenError);
        }

        let arrived = self.arrived.fetch_add(1, Ordering::SeqCst) + 1;

        if arrived == self.capacity {
            // 触发屏障
            self.arrived.store(0, Ordering::SeqCst);
            self.cond.notify_all();
            Ok(true)
        } else {
            // 等待，可能被中断
            while self.arrived.load(Ordering::SeqCst) > 0
                  && !self.broken.load(Ordering::SeqCst) {
                let result = self.cond.wait_timeout(
                    lock,
                    std::time::Duration::from_secs(5)
                ).unwrap();
                lock = result.0;

                if result.1.timed_out() {
                    // 超时，破坏屏障
                    self.broken.store(true, Ordering::SeqCst);
                    return Err(BarrierBrokenError);
                }
            }

            if self.broken.load(Ordering::SeqCst) {
                Err(BarrierBrokenError)
            } else {
                Ok(false)
            }
        }
    }

    pub fn interrupt(&self) {
        let _lock = self.lock.lock().unwrap();
        self.broken.store(true, Ordering::SeqCst);
        self.cond.notify_all();
    }
}

#[derive(Debug)]
pub struct BarrierBrokenError;
```

### 7.2 带动作的屏障

```rust
pub struct BarrierWithAction {
    inner: std::sync::Barrier,
    action: Box<dyn Fn() + Send + Sync>,
}

impl BarrierWithAction {
    pub fn new(n: usize, action: Box<dyn Fn() + Send + Sync>) -> Self {
        Self {
            inner: std::sync::Barrier::new(n),
            action,
        }
    }

    pub fn wait(&self) -> std::sync::BarrierWaitResult {
        let result = self.inner.wait();

        // 只有领导者执行动作
        if result.is_leader() {
            (self.action)();
        }

        // 再次等待确保所有线程在动作完成后继续
        if !result.is_leader() {
            self.inner.wait();
        } else {
            // 领导者需要触发第二次等待
            self.inner.wait();
        }

        result
    }
}
```

## 8. 综合安全论证

### 8.1 屏障的正确性定理

```
定理 (屏障同步保证):
  对于容量为 n 的屏障，任意正确实现的屏障满足:

  1. 安全性:
     没有任何线程能在所有 n 个线程都调用 wait 之前
     从 wait 返回

  2. 活性:
     如果所有 n 个线程都调用了 wait，
     那么所有线程最终都会从 wait 返回

  3. 一致性:
     所有线程看到的屏障触发是一致的

  证明概要:
    - 使用计数器跟踪到达线程数
    - 第 n 个线程触发屏障并重置计数器
    - 条件变量确保正确的唤醒语义
    ∎
```

### 8.2 不变式总结

```
屏障使用的核心不变式:

I1 (到达计数):
  0 ≤ arrived < capacity
  或 arrived = capacity（触发瞬间）

I2 (代计数):
  generation 单调递增，用于区分不同周期

I3 (happens-before):
  屏障触发 happens-before 所有等待线程的唤醒

I4 (领导者唯一性):
  每次触发恰好有一个领导者（is_leader = true）

I5 (循环屏障一致性):
  不同代的 wait 调用不会相互干扰
```

## 9. 总结

本文档完整形式化了屏障的语义：

1. **基本模型**：定义了屏障的结构和核心操作
2. **单次屏障**：一组线程在单点同步
3. **CyclicBarrier**：可重复使用的屏障，使用 generation 机制
4. **栅栏模式**：并行分阶段计算和排序示例
5. **Happens-Before**：屏障建立的同步语义
6. **高级模式**：可中断屏障和带动作的屏障

这些形式化定义确保了 Rust 程序在使用屏障进行线程同步时的正确性和安全性。
