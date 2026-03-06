# 锁机制的完整形式化语义

## 1. 引言

锁是并发编程中最基本的同步原语，用于保护共享资源的互斥访问。
Rust 提供了多种锁类型，包括 `Mutex`、`RwLock` 以及底层的自旋锁和顺序锁。
本文档从形式化角度定义这些锁的语义，包括所有权、生命周期和安全保证。

## 2. 锁的基本形式化模型

### 2.1 锁状态定义

```
锁状态机:

  LockState ::= Unlocked | Locked(OwnerId) | Readers(℘(OwnerId))

  其中:
    - Unlocked: 锁未被任何线程持有
    - Locked(o): 锁被线程 o 独占持有
    - Readers(S): 锁被线程集合 S 共享读取
```

### 2.2 状态转换规则

```
互斥锁操作:
  lock:   Unlocked → Locked(self)
  unlock: Locked(o) → Unlocked  if o = self

读写锁操作:
  read_lock:  Unlocked → Readers({self})
              Readers(S) → Readers(S ∪ {self})  if Writers(S) = ∅

  write_lock: Unlocked → Locked(self)

  read_unlock:  Readers(S) → Readers(S \\{self})
  write_unlock: Locked(o) → Unlocked  if o = self
```

## 3. 互斥锁语义的形式化

### 3.1 Mutex 的核心语义

```
Mutex<T> 的形式化定义:

  类型结构:
    Mutex<T> = {
      state: LockState,
      data: UnsafeCell<T>
    }

  不变式:
    I1: state = Locked(o) → data 只能被线程 o 访问
    I2: state = Unlocked → data 不能被任何线程访问
    I3: state 的改变必须通过 lock/unlock 操作

  Send 实现: T: Send → Mutex<T>: Send
  Sync 实现: T: Send → Mutex<T>: Sync
```

### 3.2 MutexGuard 的所有权语义

```
MutexGuard<'a, T> 作为 RAII 守卫:

  生命周期关系:
    lock(m: &Mutex<T>) → MutexGuard<T>
    guard 的生命周期 'a 受限于 m 的引用生命周期

  Deref/DerefMut 语义:
    *guard: &T  /  *guard: &mut T
    解引用仅在 guard 的生命周期内有效

  Drop 语义:
    drop(guard) 隐式调用 unlock

  借用检查器保证:
    持有 guard 期间，其他线程无法获取锁
```

### 3.3 Rust 代码示例

```rust
use std::sync::{Arc, Mutex};
use std::thread;

fn mutex_example() {
    let counter = Arc::new(Mutex::new(0));
    let mut handles = vec![];

    for i in 0..5 {
        let counter = Arc::clone(&counter);
        handles.push(thread::spawn(move || {
            // lock() 获取锁，返回 MutexGuard
            let mut num = counter.lock().unwrap();
            *num += 1;
            println!("线程 {} 增加计数到 {}", i, *num);
            // guard 在此 drop，自动释放锁
        }));
    }

    for handle in handles {
        handle.join().unwrap();
    }

    println!("最终计数: {}", *counter.lock().unwrap());
}
```

### 3.4 安全论证

```
Mutex 的安全性证明:

定理: 正确使用 Mutex 时，对受保护数据的访问是线程安全的

证明:
  1. lock() 操作原子性地获取锁或阻塞
  2. 成功获取锁后，MutexGuard 提供对数据的独占访问
  3. MutexGuard 的 DerefMut 允许修改数据
  4. MutexGuard 的 Drop 确保锁最终释放
  5. 借用检查器防止 guard 越过其作用域
  6. 因此，任意时刻最多只有一个线程可以修改数据
  ∎
```

## 4. 读写锁语义的形式化

### 4.1 RwLock 的形式化定义

```
RwLock<T> 的状态机:

  状态:
    RWState ::= Unlocked
               | ReadLocked(n: ℕ, readers: ℘(ThreadId))
               | WriteLocked(writer: ThreadId)

  状态转换:
    read_lock:
      Unlocked → ReadLocked(1, {self})
      ReadLocked(n, S) → ReadLocked(n+1, S ∪ {self})  if self ∉ S

    write_lock:
      Unlocked → WriteLocked(self)

    read_unlock:
      ReadLocked(n, S) → ReadLocked(n-1, S \\{self})
      ReadLocked(1, S) → Unlocked  if S = {self}

    write_unlock:
      WriteLocked(o) → Unlocked  if o = self

  约束: WriteLocked 与任何 ReadLocked 互斥
```

### 4.2 读者-写者问题形式化

```
读者-写者问题的公平性策略:

1. 读者优先:
   - 新读者可以立即获取锁，即使有写者等待
   - 可能导致写者饥饿

2. 写者优先:
   - 有写者等待时，新读者阻塞
   - 确保写者不会饥饿

3. 公平策略 (Rust 默认):
   - 按请求顺序获取锁
   - 防止读者和写者饥饿
```

### 4.3 Rust 代码示例

```rust
use std::sync::{Arc, RwLock};
use std::thread;

fn rwlock_example() {
    let data = Arc::new(RwLock::new(vec![1, 2, 3]));

    // 多个读线程
    let mut readers = vec![];
    for i in 0..3 {
        let data = Arc::clone(&data);
        readers.push(thread::spawn(move || {
            let read_guard = data.read().unwrap();
            println!("读者 {} 读到: {:?}", i, *read_guard);
            // 多个读锁可以同时持有
        }));
    }

    // 写线程
    let data_write = Arc::clone(&data);
    let writer = thread::spawn(move || {
        let mut write_guard = data_write.write().unwrap();
        write_guard.push(4);
        println!("写者添加元素");
        // 写锁独占，无其他读者或写者
    });

    for r in readers {
        r.join().unwrap();
    }
    writer.join().unwrap();
}
```

## 5. 自旋锁语义的形式化

### 5.1 Spinlock 的形式化定义

```
Spinlock 与 Mutex 的区别:

  阻塞语义:
    Mutex: 获取失败 → 线程阻塞（上下文切换）
    Spinlock: 获取失败 → 忙等待（自旋）

  适用场景:
    Spinlock 适用于:
      - 临界区极短
      - 多核处理器
      - 不允许睡眠的上下文（如中断处理）

  形式化:
    lock_spin:
      while CAS(state, Unlocked, Locked(self)) == false {
        // 忙等待，CPU 空转
        spin_loop_hint();
      }
```

### 5.2 Rust 实现示例

```rust
use std::sync::atomic::{AtomicBool, Ordering};
use std::cell::UnsafeCell;
use std::ops::{Deref, DerefMut};

pub struct SpinLock<T> {
    locked: AtomicBool,
    data: UnsafeCell<T>,
}

unsafe impl<T: Send> Sync for SpinLock<T> {}
unsafe impl<T: Send> Send for SpinLock<T> {}

pub struct SpinGuard<'a, T> {
    lock: &'a SpinLock<T>,
}

impl<T> SpinLock<T> {
    pub const fn new(data: T) -> Self {
        Self {
            locked: AtomicBool::new(false),
            data: UnsafeCell::new(data),
        }
    }

    pub fn lock(&self) -> SpinGuard<T> {
        // 自旋等待
        while self.locked.compare_exchange(
            false,
            true,
            Ordering::Acquire,
            Ordering::Relaxed
        ).is_err() {
            // 提示 CPU 这是一个自旋循环
            std::hint::spin_loop();
        }
        SpinGuard { lock: self }
    }
}

impl<'a, T> Deref for SpinGuard<'a, T> {
    type Target = T;
    fn deref(&self) -> &T {
        unsafe { &*self.lock.data.get() }
    }
}

impl<'a, T> DerefMut for SpinGuard<'a, T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut *self.lock.data.get() }
    }
}

impl<'a, T> Drop for SpinGuard<'a, T> {
    fn drop(&mut self) {
        self.lock.locked.store(false, Ordering::Release);
    }
}
```

## 6. 顺序锁语义的形式化

### 6.1 SeqLock 的形式化定义

```
SeqLock 的设计目标:
  - 允许多个读者并发执行（无锁读取）
  - 写者需要获取锁
  - 读者检测到数据不一致时重试

形式化结构:
  SeqLock<T> = {
    sequence: AtomicUsize,  // 偶数=无写者，奇数=正在写入
    data: UnsafeCell<T>
  }

写操作:
  1. sequence.fetch_add(1)  // 变为奇数
  2. 写入数据
  3. sequence.fetch_add(1)  // 变为偶数

读操作:
  1. seq1 = sequence.load()
  2. 如果 seq1 是奇数，自旋等待
  3. 复制数据
  4. seq2 = sequence.load()
  5. 如果 seq1 ≠ seq2，重试
```

### 6.2 Rust 实现示例

```rust
use std::sync::atomic::{AtomicUsize, Ordering};
use std::cell::UnsafeCell;

pub struct SeqLock<T: Copy> {
    sequence: AtomicUsize,
    data: UnsafeCell<T>,
}

unsafe impl<T: Copy + Send> Send for SeqLock<T> {}
unsafe impl<T: Copy + Send> Sync for SeqLock<T> {}

impl<T: Copy> SeqLock<T> {
    pub const fn new(data: T) -> Self {
        Self {
            sequence: AtomicUsize::new(0),
            data: UnsafeCell::new(data),
        }
    }

    pub fn read(&self) -> T {
        loop {
            let seq1 = self.sequence.load(Ordering::Acquire);

            // 正在写入，等待
            if seq1 % 2 == 1 {
                std::hint::spin_loop();
                continue;
            }

            // 读取数据
            let data = unsafe { *self.data.get() };

            let seq2 = self.sequence.load(Ordering::Acquire);

            // 序列号未变，读取成功
            if seq1 == seq2 {
                return data;
            }
            // 否则重试
        }
    }

    pub fn write(&self, new_data: T) {
        // 开始写入（奇数）
        let seq = self.sequence.fetch_add(1, Ordering::AcqRel);
        assert_eq!(seq % 2, 0);  // 确保之前不是写入状态

        // 写入数据
        unsafe {
            *self.data.get() = new_data;
        }

        // 完成写入（偶数）
        self.sequence.fetch_add(1, Ordering::Release);
    }
}
```

## 7. 死锁避免：锁层次协议

### 7.1 死锁的形式化定义

```
死锁条件 (Coffman 条件):

  1. 互斥: 资源一次只能被一个线程持有
  2. 占有并等待: 线程持有资源的同时等待其他资源
  3. 非抢占: 资源不能被强制释放
  4. 循环等待: 存在线程等待链形成环

形式化:
  死锁 ⟺ ∃线程集合 {t1, t2, ..., tn} 使得
    waits_for(t1, t2) ∧ waits_for(t2, t3) ∧ ... ∧ waits_for(tn, t1)
```

### 7.2 锁层次协议的形式化

```
锁层次协议:

  定义全序关系 <: LockType × LockType

  规则:
    若线程已持有类型 L1 的锁，
    则只能获取 L2 满足 L1 < L2 的锁

  禁止:
    获取 L2 后获取 L1，若 L2 > L1

  效果:
    破坏循环等待条件，防止死锁
```

### 7.3 Rust 代码示例

```rust
use std::sync::Mutex;

// 定义锁的层级
// Level 0: Database Lock（最外层）
// Level 1: Table Lock
// Level 2: Row Lock（最内层）

struct Database {
    tables: Mutex<Vec<Table>>,
}

struct Table {
    rows: Mutex<Vec<Row>>,
}

struct Row {
    data: Mutex<String>,
}

// 遵守锁层次：Database → Table → Row
fn update_row(db: &Database, table_idx: usize, row_idx: usize, new_data: String) {
    // Level 0: 获取 Database 锁
    let tables = db.tables.lock().unwrap();

    // Level 1: 获取 Table 锁
    let rows = tables[table_idx].rows.lock().unwrap();

    // Level 2: 获取 Row 锁
    let mut data = rows[row_idx].data.lock().unwrap();
    *data = new_data;

    // 锁按相反顺序自动释放
}

// 错误示例：违反锁层次（可能导致死锁）
// fn bad_example(t1: &Table, t2: &Table) {
//     let rows1 = t1.rows.lock().unwrap();
//     // 违反层次：在同一层级获取另一个锁
//     let rows2 = t2.rows.lock().unwrap();  // 危险！
// }
```

## 8. 综合安全论证

### 8.1 锁的正确性定理

```
定理 (互斥保证):
  对于任意 Mutex<T> m，在任意时刻最多只有一个线程持有 m 的锁

定理 (数据竞争自由):
  若所有共享可变状态都通过 Mutex/RwLock 保护，
  则程序不存在数据竞争

定理 (死锁自由 - 锁层次):
  若所有线程都遵守锁层次协议，
  则系统不会发生死锁
```

### 8.2 不变式总结

```
锁机制的核心不变式:

I1 (互斥性):
  ∀锁 l, 任意时刻，持有 l 的线程数 ≤ 1 (Mutex)
  或 写者数 + 读者数 ≤ 1 且 写者数 ≤ 1 (RwLock)

I2 (所有权):
  线程 t 持有锁 l ⟺ t 拥有对 l 保护数据的独占访问权

I3 (安全性):
  锁释放 happens-before 后续锁获取

I4 (活性):
  锁最终会释放（无无限期持有）
```

## 9. 总结

本文档完整形式化了 Rust 锁机制的语义：

1. **基本模型**：定义了锁状态机和状态转换规则
2. **Mutex**：RAII 守卫确保安全的独占访问
3. **RwLock**：支持并发读和独占写
4. **Spinlock**：忙等待适用于短临界区
5. **SeqLock**：无锁读取适用于读多写少场景
6. **死锁避免**：锁层次协议破坏循环等待条件

这些形式化定义确保了 Rust 并发程序在使用锁时的安全性和正确性。
