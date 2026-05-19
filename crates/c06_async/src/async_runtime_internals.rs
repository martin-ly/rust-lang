#![forbid(unsafe_code)]

//! 异步运行时内部原理概念解析
//!
//! 本模块以概念形式讲解 Waker、任务队列、Tokio 调度器架构与 Future 状态机。
//! 所有代码均为 safe Rust 概念实现，不使用任何 unsafe。

use std::collections::VecDeque;
use std::future::Future;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

// ============================================================================
// 1. ConceptWaker — Waker 概念实现
// ============================================================================

/// 概念性 Waker 实现
///
/// 真实 Waker 由 `std::task::RawWaker` 和 vtable 构成，需要 unsafe 代码。
/// 这里使用 `Arc<AtomicBool>` 模拟"唤醒标记"的语义。
pub struct ConceptWaker {
    awakened: Arc<AtomicBool>,
}

impl ConceptWaker {
    /// 创建新的 Waker，唤醒标记为 false
    pub fn new() -> Self {
        Self {
            awakened: Arc::new(AtomicBool::new(false)),
        }
    }

    /// 模拟 `wake()`：将唤醒标记设为 true
    pub fn wake(&self) {
        self.awakened.store(true, Ordering::Release);
    }

    /// 检查是否已被唤醒
    pub fn is_awakened(&self) -> bool {
        self.awakened.load(Ordering::Acquire)
    }

    /// 获取底层的 `Arc<AtomicBool>`（用于克隆）
    pub fn inner(&self) -> Arc<AtomicBool> {
        Arc::clone(&self.awakened)
    }

    /// 重置唤醒标记
    pub fn reset(&self) {
        self.awakened.store(false, Ordering::Release);
    }
}

impl Default for ConceptWaker {
    fn default() -> Self {
        Self::new()
    }
}

impl Clone for ConceptWaker {
    fn clone(&self) -> Self {
        Self {
            awakened: Arc::clone(&self.awakened),
        }
    }
}

// ============================================================================
// 2. ConceptTaskQueue — 简单任务队列概念
// ============================================================================

/// 概念性异步任务队列
///
/// 真实运行时（如 Tokio）使用复杂的队列结构（全局注入器 + 本地工作窃取队列）。
/// 这里使用 `VecDeque<Box<dyn Future<Output = ()>>>` 展示最基本的任务缓冲语义。
pub struct ConceptTaskQueue {
    tasks: VecDeque<Box<dyn Future<Output = ()> + 'static>>,
}

impl ConceptTaskQueue {
    /// 创建空任务队列
    pub fn new() -> Self {
        Self {
            tasks: VecDeque::new(),
        }
    }

    /// 向队列尾部追加任务
    pub fn push(&mut self, task: Box<dyn Future<Output = ()> + 'static>) {
        self.tasks.push_back(task);
    }

    /// 从队列头部取出任务
    pub fn pop(&mut self) -> Option<Box<dyn Future<Output = ()> + 'static>> {
        self.tasks.pop_front()
    }

    /// 当前任务数
    pub fn len(&self) -> usize {
        self.tasks.len()
    }

    /// 是否为空
    pub fn is_empty(&self) -> bool {
        self.tasks.is_empty()
    }

    /// 清空队列
    pub fn clear(&mut self) {
        self.tasks.clear();
    }
}

impl Default for ConceptTaskQueue {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// 3. TokioSchedulerArchitecture — Tokio 调度器架构概述
// ============================================================================

/// Tokio 调度器架构概念
pub struct TokioSchedulerArchitecture;

impl TokioSchedulerArchitecture {
    /// 架构总览
    pub fn overview() -> &'static str {
        r#"=== Tokio 调度器架构 ===

Tokio 使用多线程 work-stealing 调度器，核心组件：

1. Global Queue（全局队列）
   - 所有外部任务首先进入全局队列
   - 多线程竞争访问，需要同步（Mutex 或无锁队列）

2. Local Queue（本地队列）
   - 每个工作线程拥有独立的本地队列
   - LIFO 顺序：新任务优先在本地执行，保持缓存友好
   - 无锁访问：只有所属线程能 push/pop

3. Work-Stealing（工作窃取）
   - 当线程本地队列为空时，从其他线程窃取任务
   - 窃取采用 FIFO 顺序，减少竞争
   - 若窃取失败，尝试从全局队列获取

4. I/O Driver
   - 基于 epoll/kqueue/IOCP 的系统调用封装
   - 将就绪的 I/O 事件转换为 Waker 唤醒
"#
    }

    /// Work-Stealing 详解
    pub fn work_stealing() -> &'static str {
        r#"=== Work-Stealing 详解 ===

为什么 Owner 用 LIFO，Thief 用 FIFO？

- Owner LIFO：
  - 递归生成的子任务往往共享数据
  - 后生成的任务更可能命中热缓存
  - 深度优先执行减少任务切换开销

- Thief FIFO：
  - 窃取的是最老的任务，通常粒度更大
  - 减少总窃取次数，降低同步开销

Tokio 的本地队列容量通常为 256，满时任务溢出到全局队列。
"#
    }

    /// 全局队列与本地队列对比
    pub fn global_vs_local() -> &'static str {
        r#"=== 全局队列 vs 本地队列 ===

| 维度       | 全局队列               | 本地队列               |
|------------|----------------------|----------------------|
| 访问者     | 所有线程               | 仅所属线程             |
| 顺序       | FIFO                 | LIFO                 |
| 同步       | 需要锁/原子操作        | 通常无锁               |
| 用途       | 外部任务入口、溢出缓冲 | 线程优先处理的任务     |
| 竞争       | 高                   | 低（仅窃取时竞争）     |

任务生命周期：
spawn -> 全局队列 -> 工作线程获取 -> 本地队列 -> 执行
                \-> 本地队列满 -> 溢出回全局队列
"#
    }
}

// ============================================================================
// 4. FutureStateMachine — Future 状态机概念
// ============================================================================

/// Future 状态机概念图
pub struct FutureStateMachine;

impl FutureStateMachine {
    /// Future 状态机概念
    pub fn concept() -> &'static str {
        r#"=== Future 状态机概念 ===

async fn / async block 会被编译器转换为匿名类型，实现 Future trait。

状态机核心：
```text
enum State {
    Start,           // 初始状态
    Waiting(Pos),    // 等待某个 .await 点
    Completed,       // 已完成
}

struct AsyncFnFuture {
    state: State,
    local_var_1: ...,
    local_var_2: ...,
}
```

poll() 方法：
- 根据当前 state 跳转到对应代码位置
- 遇到 .await 时，调用子 Future 的 poll()
- 若子 Future 返回 Pending，保存状态并返回 Pending
- 若子 Future 返回 Ready，继续执行后续代码

关键点：
- Future 是惰性的：创建时不执行，首次 poll 才开始
- await 点 = 状态保存点 + 子 Future 轮询点
- 编译器自动实现此状态机，无需手写
"#
    }

    /// Future 生命周期
    pub fn lifecycle() -> &'static str {
        r#"=== Future 生命周期 ===

1. 创建（Create）
   - async block / async fn 调用返回一个 Future 对象
   - 此时状态机处于 Start 状态，尚未执行任何代码

2. 轮询（Poll）
   - Executor 调用 Future::poll(cx)
   - cx 提供 Waker，用于通知 Executor 再次 poll
   - 状态机推进到下一个 await 点或完成

3. 挂起（Pending）
   - Future 等待 I/O、定时器或其他异步事件
   - 返回 Poll::Pending，并将 Waker 注册到事件源

4. 唤醒（Wake）
   - 事件完成后，事件源调用 Waker::wake()
   - Executor 将该 Future 重新放入任务队列

5. 完成（Ready）
   - Future 执行完毕，返回 Poll::Ready(T)
   - Executor 将结果传递给调用者，释放任务
"#
    }
}

// ============================================================================
// 测试
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // ---------- ConceptWaker 测试 ----------

    #[test]
    fn test_waker_wake() {
        let waker = ConceptWaker::new();
        assert!(!waker.is_awakened());
        waker.wake();
        assert!(waker.is_awakened());
    }

    #[test]
    fn test_waker_clone() {
        let waker1 = ConceptWaker::new();
        let waker2 = waker1.clone();
        waker1.wake();
        assert!(waker2.is_awakened());
    }

    #[test]
    fn test_waker_reset() {
        let waker = ConceptWaker::new();
        waker.wake();
        assert!(waker.is_awakened());
        waker.reset();
        assert!(!waker.is_awakened());
    }

    // ---------- ConceptTaskQueue 测试 ----------

    #[test]
    fn test_task_queue_push_pop() {
        let mut queue = ConceptTaskQueue::new();
        assert!(queue.is_empty());
        queue.push(Box::new(async {}));
        assert_eq!(queue.len(), 1);
        let task = queue.pop();
        assert!(task.is_some());
        assert!(queue.is_empty());
    }

    #[test]
    fn test_task_queue_multiple_tasks() {
        let mut queue = ConceptTaskQueue::new();
        for _ in 0..5 {
            queue.push(Box::new(async {}));
        }
        assert_eq!(queue.len(), 5);
        queue.clear();
        assert!(queue.is_empty());
    }

    // ---------- Tokio 调度器架构测试 ----------

    #[test]
    fn test_tokio_scheduler_overview() {
        let doc = TokioSchedulerArchitecture::overview();
        assert!(doc.contains("Global Queue"));
        assert!(doc.contains("Local Queue"));
        assert!(doc.contains("Work-Stealing"));
    }

    #[test]
    fn test_tokio_work_stealing_doc() {
        let doc = TokioSchedulerArchitecture::work_stealing();
        assert!(doc.contains("LIFO"));
        assert!(doc.contains("FIFO"));
    }

    #[test]
    fn test_tokio_global_vs_local_doc() {
        let doc = TokioSchedulerArchitecture::global_vs_local();
        assert!(doc.contains("全局队列"));
        assert!(doc.contains("本地队列"));
    }

    // ---------- Future 状态机测试 ----------

    #[test]
    fn test_future_state_machine_concept() {
        let doc = FutureStateMachine::concept();
        assert!(doc.contains("poll()"));
        assert!(doc.contains("Pending"));
        assert!(doc.contains("Ready"));
    }

    #[test]
    fn test_future_lifecycle() {
        let doc = FutureStateMachine::lifecycle();
        assert!(doc.contains("Poll"));
        assert!(doc.contains("Wake"));
        assert!(doc.contains("Ready"));
    }
}
