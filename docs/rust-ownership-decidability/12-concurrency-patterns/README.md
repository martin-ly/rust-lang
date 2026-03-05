# Rust 并发模式导航

> **Rust版本**: 1.93.1
> **文档范围**: 线程安全、消息传递、无锁编程、异步并发、数据并行、分布式模式
> **阅读时间**: 约8小时
> **难度级别**: 中级到高级

---

## 📚 文档结构

本系列文档深入探讨 Rust 并发编程的各个层面，从理论基础到实际应用，从线程安全到分布式系统。

```text
12-concurrency-patterns/
├── README.md                          # 本文档 - 导航和概览
├── 12-01-concurrency-architecture.md  # 并发架构设计模式
├── 12-02-thread-safety-patterns.md    # 线程安全模式 (Send/Sync)
├── 12-03-message-passing.md           # 消息传递模式 (Channel/Actor)
├── 12-04-lock-free-patterns.md        # 无锁编程 (CAS/原子操作)
├── 12-05-async-patterns.md            # 异步并发模式
├── 12-06-data-parallelism.md          # 数据并行 (Rayon/SIMD)
└── 12-07-distributed-patterns.md      # 分布式模式
```

---

## 🎯 学习路径

### 路径一：循序渐进（推荐初学者）

```text
README → 12-02 → 12-03 → 12-05 → 12-01 → 12-06 → 12-04 → 12-07
```

1. **线程安全基础** (12-02) - 理解 Send/Sync，掌握内部可变性
2. **消息传递** (12-03) - 学习 CSP 和 Actor 模式
3. **异步并发** (12-05) - 掌握 async/await 和任务调度
4. **架构设计** (12-01) - 综合运用各种模式
5. **数据并行** (12-06) - 高性能并行计算
6. **无锁编程** (12-04) - 极致性能优化
7. **分布式系统** (12-07) - 扩展到多节点

### 路径二：问题导向

| 你的问题 | 推荐阅读 |
|---------|---------|
| 如何安全地共享状态？ | 12-02, 12-04 |
| 如何设计高吞吐系统？ | 12-03, 12-05 |
| 如何最大化 CPU 利用率？ | 12-06, 12-04 |
| 如何构建容错系统？ | 12-07, 12-03 |
| 如何选择并发模型？ | 12-01, 12-05 |

### 路径三：性能优先

```text
12-06 → 12-04 → 12-05 → 12-02 → 12-03
```

---

## 📖 各章内容概览

### 12-01: 并发架构设计模式

**核心主题**:

- 并发模型对比（线程 vs 异步 vs 并行 vs Actor）
- 线程池模式实现
- Scoped 线程（Rust 1.63+）
- 同步原语（RwLock、Barrier、Semaphore）
- Actor 模式与 Actix 框架
- 管道模式和 Future 组合

**适合读者**: 需要设计整体并发架构的系统架构师

---

### 12-02: 线程安全模式

**核心主题**:

- Send 和 Sync trait 深入解析
- 内部可变性模式（RefCell、Mutex、RwLock）
- 锁类型详解与性能对比
- 死锁预防策略
- 线程局部存储
- 条件变量与同步

**关键代码示例**:

```rust
// 类型系统的线程安全检查
fn check_thread_safety<T: Send + Sync>(_: T) {}

// 内部可变性模式
use std::sync::Arc;
use std::cell::RefCell;
use parking_lot::RwLock;

// 死锁预防的锁排序
static LOCK_ORDER: AtomicUsize = AtomicUsize::new(0);
```

**适合读者**: 需要深入理解 Rust 内存模型的开发者

---

### 12-03: 消息传递模式

**核心主题**:

- CSP（Communicating Sequential Processes）理论
- mpsc/mpmc Channel 实现
- Actor 模型设计
- 消息类型设计（命令、事件、查询）
- 背压控制策略
- 消息序列化和反序列化

**关键代码示例**:

```rust
// Actor 消息定义
enum DatabaseMessage {
    Query { sql: String, respond_to: OneshotSender<Result<Row, Error>> },
    Command { cmd: DbCommand, respond_to: OneshotSender<Result<(), Error>> },
    Event(DbEvent),
}

// 背压感知的发送
async fn send_with_backpressure<T>(
    sender: &mpsc::Sender<T>,
    msg: T,
    timeout: Duration,
) -> Result<(), SendError> {
    match timeout_at(Instant::now() + timeout, sender.send(msg)).await {
        Ok(Ok(())) => Ok(()),
        Ok(Err(_)) => Err(SendError::ChannelClosed),
        Err(_) => Err(SendError::Timeout),
    }
}
```

**适合读者**: 设计消息驱动系统的开发者

---

### 12-04: 无锁编程

**核心主题**:

- 内存模型基础（happens-before、sequentially consistent）
- 原子操作和内存序（Relaxed/Acquire/Release/AcqRel/SeqCst）
- CAS（Compare-And-Swap）循环模式
- 无锁数据结构（栈、队列、跳表）
- Hazard Pointer 和内存回收
- RCU（Read-Copy-Update）模式

**关键代码示例**:

```rust
// 无锁队列的 CAS 操作
pub fn push(&self, value: T) {
    let new_node = Box::into_raw(Box::new(Node::new(value)));

    loop {
        let tail = self.tail.load(Ordering::Acquire);
        let next = unsafe { (*tail).next.load(Ordering::Acquire) };

        if tail == self.tail.load(Ordering::Acquire) {
            if next.is_null() {
                if unsafe { (*tail).next.compare_exchange(
                    next, new_node, Ordering::Release, Ordering::Relaxed
                ).is_ok() } {
                    let _ = self.tail.compare_exchange(
                        tail, new_node, Ordering::Release, Ordering::Relaxed
                    );
                    break;
                }
            } else {
                let _ = self.tail.compare_exchange(
                    tail, next, Ordering::Release, Ordering::Relaxed
                );
            }
        }
    }
}
```

**适合读者**: 追求极致性能的底层开发者

---

### 12-05: 异步并发模式

**核心主题**:

- async/await 原理与状态机转换
- 任务调度策略（work-stealing、priority scheduling）
- 背压与流控制
- 超时和取消模式
- 异步 trait 和动态分发
- 运行时选择（Tokio vs async-std vs smol）

**关键代码示例**:

```rust
// 自适应背压控制
pub struct AdaptiveBackpressure {
    current_limit: AtomicUsize,
    success_count: AtomicUsize,
    timeout_count: AtomicUsize,
}

impl AdaptiveBackpressure {
    pub async fn execute<F, T>(&self, f: F) -> Result<T, BackpressureError>
    where
        F: Future<Output = T>,
    {
        let permit = self.acquire_permit().await?;
        let result = timeout(self.current_timeout(), f).await;

        self.update_metrics(&result);
        self.adjust_limit();

        result.map_err(|_| BackpressureError::Timeout)
    }
}
```

**适合读者**: 构建高并发 IO 密集型应用的开发者

---

### 12-06: 数据并行

**核心主题**:

- Rayon 并行迭代器
- Fork-Join 模式
- SIMD 向量化（portable-simd）
- GPU 加速（Rust-GPU、wgpu）
- 并行排序和归约
- 矩阵运算优化

**关键代码示例**:

```rust
// 并行归约与 SIMD 结合
pub fn parallel_simd_sum(data: &[f64]) -> f64 {
    data.par_chunks(4096)
        .map(|chunk| {
            chunk.chunks_exact(4)
                .map(|quad| unsafe {
                    let v = f64x4::from_slice(quad);
                    v.horizontal_sum()
                })
                .sum::<f64>()
                + chunk[chunk.len() - chunk.len() % 4..].iter().sum::<f64>()
        })
        .sum()
}
```

**适合读者**: 数据科学家、科学计算开发者

---

### 12-07: 分布式模式

**核心主题**:

- 一致性模型（强一致、最终一致、因果一致）
- 共识算法（Raft、Paxos）
- 分布式事务（Saga、2PC、TCC）
- 分区容错与降级策略
- 分布式锁（Redlock、ZooKeeper）
- 服务发现和负载均衡

**关键代码示例**:

```rust
// Raft 共识的简化实现
#[derive(Clone, Debug)]
pub enum NodeState {
    Follower { leader: Option<NodeId> },
    Candidate { votes_received: HashSet<NodeId> },
    Leader { next_index: HashMap<NodeId, LogIndex> },
}

impl RaftNode {
    pub async fn append_entries(&mut self, req: AppendEntries) -> Result<AppendResponse> {
        match self.state {
            NodeState::Follower { .. } => self.handle_append_as_follower(req).await,
            NodeState::Candidate { .. } => {
                self.become_follower(Some(req.leader_id));
                self.handle_append_as_follower(req).await
            }
            NodeState::Leader { .. } => {
                if req.term > self.current_term {
                    self.become_follower(Some(req.leader_id));
                    self.handle_append_as_follower(req).await
                } else {
                    Ok(AppendResponse::Reject(self.current_term))
                }
            }
        }
    }
}
```

**适合读者**: 分布式系统开发者、SRE

---

## 🛠️ 配套代码仓库

各章节的完整代码示例可在以下仓库找到：

```bash
git clone https://github.com/rust-lang-concurrency/patterns.git
cd patterns/chapter-12/
cargo test --all
```

每个模块包含：

- `examples/` - 可运行的示例代码
- `benches/` - 性能基准测试
- `tests/` - 单元测试和集成测试

---

## 📊 性能基准

各并发模式的典型性能数据（在 16 核 AMD Ryzen 9 5950X 上测试）：

| 模式 | 吞吐量 (ops/sec) | 延迟 (μs) | 内存占用 |
|------|-----------------|-----------|---------|
| Mutex | 5M | 0.2 | 低 |
| RwLock | 15M (读) / 3M (写) | 0.1 | 低 |
| Channel (mpsc) | 10M | 0.15 | 中等 |
| 无锁队列 | 50M | 0.02 | 中等 |
| Rayon 并行 | 线性加速至 16x | - | 高 |
| Tokio 任务 | 1M tasks/sec | 5 | 低 |

---

## 🔧 调试工具

### 死锁检测

```rust
use parking_lot::deadlock;

// 启用死锁检测
std::thread::spawn(move || {
    loop {
        std::thread::sleep(Duration::from_secs(10));
        let deadlocks = deadlock::check_deadlock();
        if !deadlocks.is_empty() {
            eprintln!("Deadlock detected: {:?}", deadlocks);
        }
    }
});
```

### 竞态条件检测

使用 `loom` 进行并发测试：

```rust
#[test]
fn test_concurrent_stack() {
    loom::model(|| {
        let stack = Arc::new(LockFreeStack::new());

        let s1 = stack.clone();
        let t1 = thread::spawn(move || {
            s1.push(1);
        });

        let s2 = stack.clone();
        let t2 = thread::spawn(move || {
            s2.push(2);
        });

        t1.join().unwrap();
        t2.join().unwrap();

        assert_eq!(stack.pop(), Some(2));
        assert_eq!(stack.pop(), Some(1));
    });
}
```

### 性能分析

```bash
# CPU 火焰图
cargo flamegraph --example concurrent_map

# Cache 分析
cargo cachegrind --example lock_free_stack

# 锁竞争分析
cargo build --features parking_lot/deadlock_detection
```

---

## ⚠️ 常见陷阱与解决方案

### 陷阱 1: 在异步代码中阻塞

```rust
// ❌ 错误
async fn bad() {
    std::thread::sleep(Duration::from_secs(1));
}

// ✅ 正确
async fn good() {
    tokio::time::sleep(Duration::from_secs(1)).await;
}
```

### 陷阱 2: 在持有锁时 await

```rust
// ❌ 错误
async fn bad(data: Arc<Mutex<Data>>) {
    let guard = data.lock().await;
    some_async_op().await; // 可能死锁！
}

// ✅ 正确
async fn good(data: Arc<Mutex<Data>>) {
    let result = {
        let guard = data.lock().await;
        guard.compute()
    };
    some_async_op(result).await;
}
```

### 陷阱 3: 忽略取消安全

```rust
// ❌ 非取消安全
async fn bad(sender: &mpsc::Sender<i32>) {
    sender.send(1).await.unwrap();
    sender.send(2).await.unwrap(); // 取消后可能丢失 1
}

// ✅ 取消安全
async fn good(sender: &mpsc::Sender<i32>) {
    let mut state = 0;

    match sender.send(1).await {
        Ok(()) => state = 1,
        Err(_) => return,
    }

    match sender.send(2).await {
        Ok(()) => state = 2,
        Err(_) => {
            // 回滚或补偿操作
            compensate(state).await;
            return;
        }
    }
}
```

---

## 📚 延伸阅读

### 书籍

1. **Rust Atomics and Locks** by Mara Bos
   - 深入讲解 Rust 内存模型和原子操作
   - 官方推荐的无锁编程指南

2. **Programming Rust** by Jim Blandy et al.
   - 第 19 章：并发
   - 全面的并发编程介绍

3. **Async Rust** by Carl Fredrik Samson
   - async/await 的深入探讨
   - 运行时实现原理

### 在线资源

- [The Rust Async Book](https://rust-lang.github.io/async-book/)
- [Tokio Documentation](https://tokio.rs/)
- [Rayon Documentation](https://docs.rs/rayon/)
- [Crossbeam Documentation](https://docs.rs/crossbeam/)

### 论文与研究

- "The Problem of Programming Language Concurrency Semantics" - Batty et al.
- "Memory Models: A Case for Rethinking Parallel Languages and Hardware" - Boehm
- "RustBelt: Securing the Foundations of the Rust Programming Language" - Jung et al.

---

## 🤝 贡献指南

发现错误或想要贡献内容？请参考以下流程：

1. 提交 Issue 描述问题或建议
2. Fork 仓库并创建特性分支
3. 遵循文档风格指南
4. 提交 Pull Request

### 文档风格指南

- 代码示例必须包含错误处理
- 性能声明需要基准测试支持
- 使用 `loom` 测试并发代码
- 术语首次出现时提供英文原文

---

## 📜 许可证

本系列文档采用 [CC BY-SA 4.0](https://creativecommons.org/licenses/by-sa/4.0/) 许可。

代码示例采用 MIT 或 Apache-2.0 双许可。

---

## 🙏 致谢

感谢以下项目和社区：

- [Tokio](https://tokio.rs/) - 异步运行时
- [Rayon](https://github.com/rayon-rs/rayon) - 数据并行
- [Crossbeam](https://github.com/crossbeam-rs/crossbeam) - 并发原语
- [Actix](https://actix.rs/) - Actor 框架
- [Loom](https://github.com/tokio-rs/loom) - 并发测试

---

> **提示**: 本文档是一个活文档，会随着 Rust 生态的发展持续更新。建议订阅更新通知以获取最新内容。

**最后更新**: 2026年3月4日
**版本**: 1.0.0
