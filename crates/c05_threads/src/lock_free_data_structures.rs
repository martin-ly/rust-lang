#![forbid(unsafe_code)]

//! 无锁数据结构概念解析
//! lock-free data structure concept

use std::collections::VecDeque;
use std::sync::Mutex;

// ============================================================================
// 1. 内存序概念
// ============================================================================

/// 内存序（Memory Ordering）概念深度解析
/// memory （Memory Ordering）concept
/// 无锁编程的核心在于正确使用原子操作的内存序，以平衡性能与正确性。
/// lock-free core in atomic operation memory ，performance and 。
pub struct MemoryOrderingConcept;

impl MemoryOrderingConcept {
    /// 内存序总览
    /// memory
    pub fn overview() -> &'static str {
        r#"=== 内存序（Memory Ordering）===
        
在 Rust 中，`std::sync::atomic::Ordering` 定义了四种主要内存序：

1. Relaxed — 最弱约束，仅保证原子性，不保证指令重排顺序
2. Acquire — 用于读操作，保证之后的读写不会重排到本次读之前
3. Release — 用于写操作，保证之前的读写不会重排到本次写之后
4. SeqCst — 最强约束，全局顺序一致性，禁止所有重排

选型原则：
- 纯计数器（如引用计数）→ Relaxed
- 消费者读取共享数据 → Acquire
- 生产者释放共享数据 → Release
- 多线程状态机或标志位 → SeqCst
"#
    }

    /// Relaxed and Acquire-Release to比
    pub fn relaxed_vs_acq_rel() -> &'static str {
        r#"=== Relaxed vs Acquire/Release ===

Relaxed:
- 只保证操作本身是原子的
- 编译器和 CPU 可以任意重排周围指令
- 适用场景：简单的计数器、统计信息

Acquire/Release 对：
- 形成 happens-before 关系
- 生产者 Release 写入数据后，消费者 Acquire 读取一定能看到
- 适用场景：单生产者单消费者队列、标志位同步

SeqCst:
- 所有线程以相同顺序观察所有 SeqCst 操作
- 性能开销最大，但推理最简单
- 适用场景：复杂状态机、需要全局一致性的场景
"#
    }
}

// ============================================================================
// 2. ABA 问题
// ============================================================================

/// ABA 问题及其解决方案概念
/// ABA problem and its solution concept
pub struct AbaProblemConcept;

impl AbaProblemConcept {
    /// ABA 问题描述
    /// ABA problemdescription
    /// ABA problem describe
    pub fn explanation() -> &'static str {
        r#"=== ABA 问题 ===

场景：
1. 线程 T1 读取指针 A
2. 线程 T2 将 A 改为 B，再将 B 改回 A
3. T1 的 CAS 操作成功，因为指针值仍是 A
4. 但 A 指向的内容/状态已发生变化，导致逻辑错误

后果：
- 数据结构损坏（如链表断链、栈丢失节点）
- 内存安全问题（如重复释放、访问已释放内存）

=== 解决方案 ===

1. 标签指针（Tagged Pointer）
   - 将指针与单调递增的版本号打包为 64 位整数
   - 每次修改时版本号加 1，即使指针回到 A，版本号也不同

2. Hazard Pointers / Epoch-Based Reclamation
   - 延迟释放被删除的节点
   - 确保没有其他线程正在访问该节点时才真正释放
   - Rust 生态：crossbeam-epoch
"#
    }

    /// 为什么 ABA 在无锁结构中特别危险
    /// as ABA in lock-free structure in
    pub fn why_dangerous() -> &'static str {
        r#"=== 为什么 ABA 特别危险 ===

在 Treiber Stack 的 pop 操作中：
- T1 读取 head = A
- T2 pop A，push B，再 push A（可能是另一个节点，地址相同）
- T1 的 CAS(head, A, A->next) 成功
- 但 A->next 可能已不再是原来的值，导致栈结构损坏

在 Michael-Scott Queue 中：
- tail 指针的 CAS 成功但 next 指针已变
- 可能导致入队节点丢失或队列成环

结论：任何使用 CAS 循环的无锁结构都必须考虑 ABA 防护。
"#
    }
}

// ============================================================================
// 3. TreiberStack — 概念实现（Mutex 模拟）
// ============================================================================

/// 概念性 Treiber 栈
/// concept Treiber stack
/// 这里Use `Mutex<Vec<T>>` 模拟相同 LIFO 语义。
/// Use `Mutex<Vec<T>>` LIFO 。
pub struct TreiberStack<T> {
    inner: Mutex<Vec<T>>,
}

impl<T> TreiberStack<T> {
    /// 创建空栈
    /// Creates空栈
    /// stack
    pub fn new() -> Self {
        Self {
            inner: Mutex::new(Vec::new()),
        }
    }

    /// 压stack（模拟 lock-free push 语义）
    pub fn push(&self, value: T) {
        self.inner.lock().expect("锁不应被 poison").push(value);
    }

    /// 出stack（模拟 lock-free pop 语义）
    pub fn pop(&self) -> Option<T> {
        self.inner.lock().expect("锁不应被 poison").pop()
    }

    /// 是否为空
    /// as
    pub fn is_empty(&self) -> bool {
        self.inner.lock().expect("锁不应被 poison").is_empty()
    }

    /// 当前长度
    /// when before
    pub fn len(&self) -> usize {
        self.inner.lock().expect("锁不应被 poison").len()
    }
}

impl<T> Default for TreiberStack<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// 真实 Treiber Stack 实现差异说明
/// real Treiber Stack explain
/// real Treiber Stack Implementation of差异explain
/// real Treiber Stack Implementation ofdifferenceexplain
pub struct TreiberStackRealImpl;

impl TreiberStackRealImpl {
    /// 真实实现与模拟实现的差异
    /// real and
    pub fn differences() -> &'static str {
        r#"=== 真实 Treiber Stack 实现差异 ===

真实 lock-free 实现：
```text
struct Node<T> {
    data: T,
    next: AtomicPtr<Node<T>>,
}

struct TreiberStack<T> {
    head: AtomicPtr<Node<T>>,
}

push(value):
    new_node = Box::into_raw(Box::new(Node { data: value, next: null }))
    loop:
        old_head = head.load(Acquire)
        new_node.next = old_head
        if head.compare_exchange(old_head, new_node, Release, Relaxed):
            return

pop() -> Option<T>:
    loop:
        old_head = head.load(Acquire)
        if old_head == null: return None
        new_head = (*old_head).next.load(Relaxed)
        if head.compare_exchange(old_head, new_head, Acquire, Relaxed):
            value = read((*old_head).data)
            // 延迟释放 old_node（需要 EBR/Hazard Pointers）
            return Some(value)
```

与当前模拟实现的关键差异：
1. 真实实现使用 AtomicPtr + CAS 循环，无锁争用更低
2. push/pop 的内存序：head 用 Acquire/Release，next 用 Relaxed
3. 出队节点不能立即 free，必须使用 crossbeam-epoch 等延迟回收机制
4. 存在 ABA 风险，需要使用 tagged pointer 或版本号
"#
    }
}

// ============================================================================
// 4. MichaelScottQueue — 概念实现（Mutex 模拟）
// ============================================================================

/// 概念性 Michael-Scott 队列
pub struct MichaelScottQueue<T> {
    inner: Mutex<VecDeque<T>>,
}

impl<T> MichaelScottQueue<T> {
    /// 创建空队列
    /// Creates空队列
    pub fn new() -> Self {
        Self {
            inner: Mutex::new(VecDeque::new()),
        }
    }

    /// 入队（模拟 lock-free enqueue 语义）
    pub fn enqueue(&self, value: T) {
        self.inner.lock().expect("锁不应被 poison").push_back(value);
    }

    /// 出队（模拟 lock-free dequeue 语义）
    pub fn dequeue(&self) -> Option<T> {
        self.inner.lock().expect("锁不应被 poison").pop_front()
    }

    /// 是否为空
    /// as
    pub fn is_empty(&self) -> bool {
        self.inner.lock().expect("锁不应被 poison").is_empty()
    }

    /// 当前长度
    /// when before
    pub fn len(&self) -> usize {
        self.inner.lock().expect("锁不应被 poison").len()
    }
}

impl<T> Default for MichaelScottQueue<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// 真实 Michael-Scott Queue 实现差异说明
/// real Michael-Scott Queue Implementation of差异explain
/// real Michael-Scott Queue Implementation ofdifferenceexplain
pub struct MichaelScottQueueRealImpl;

impl MichaelScottQueueRealImpl {
    /// 真实实现与模拟实现的差异
    /// real and
    pub fn differences() -> &'static str {
        r#"=== 真实 Michael-Scott Queue 实现差异 ===

真实 lock-free 实现：
```text
struct Node<T> {
    data: MaybeUninit<T>,
    next: AtomicPtr<Node<T>>,
}

struct MSQueue<T> {
    head: AtomicPtr<Node<T>>,
    tail: AtomicPtr<Node<T>>,
}

初始化时创建一个 dummy node，head 和 tail 都指向它。

enqueue(value):
    new_node = alloc(Node { data: value, next: null })
    loop:
        tail = self.tail.load(Acquire)
        next = tail.next.load(Acquire)
        if tail == self.tail.load(Relaxed):
            if next == null:
                if tail.next.compare_exchange(next, new_node, Release, Relaxed):
                    let _ = self.tail.compare_exchange(tail, new_node, Release, Relaxed)
                    return
            else:
                let _ = self.tail.compare_exchange(tail, next, Release, Relaxed)

dequeue() -> Option<T>:
    loop:
        head = self.head.load(Acquire)
        tail = self.tail.load(Acquire)
        next = head.next.load(Acquire)
        if head == self.head.load(Relaxed):
            if head == tail:
                if next == null: return None
                let _ = self.tail.compare_exchange(tail, next, Release, Relaxed)
            else:
                value = read(next.data)
                if self.head.compare_exchange(head, next, Release, Relaxed):
                    // 释放旧 dummy 节点需延迟回收
                    return Some(value)
```

与当前模拟实现的关键差异：
1. 分离的 head/tail 指针减少入队/出队之间的竞争
2. 使用 dummy node 简化边界条件
3. 允许"帮忙推进"（helping）：线程发现 tail/head 滞后时主动 CAS 推进
4. 内存回收：出队后的旧 dummy 节点不能立即释放
"#
    }
}

// ============================================================================
// 测试
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    // ---------- 内存序概念测试 ----------

    #[test]
    fn test_memory_ordering_overview() {
        let doc = MemoryOrderingConcept::overview();
        assert!(doc.contains("Relaxed"));
        assert!(doc.contains("Acquire"));
        assert!(doc.contains("Release"));
        assert!(doc.contains("SeqCst"));
    }

    #[test]
    fn test_memory_ordering_relaxed_vs_acq_rel() {
        let doc = MemoryOrderingConcept::relaxed_vs_acq_rel();
        assert!(doc.contains("happens-before"));
    }

    // ---------- ABA 问题测试 ----------

    #[test]
    fn test_aba_explanation() {
        let doc = AbaProblemConcept::explanation();
        assert!(doc.contains("ABA"));
        assert!(doc.contains("Tagged Pointer"));
    }

    #[test]
    fn test_aba_why_dangerous() {
        let doc = AbaProblemConcept::why_dangerous();
        assert!(doc.contains("Treiber Stack"));
    }

    // ---------- TreiberStack 测试 ----------

    #[test]
    fn test_treiber_stack_push_pop() {
        let stack = TreiberStack::new();
        stack.push(1);
        stack.push(2);
        assert_eq!(stack.pop(), Some(2));
        assert_eq!(stack.pop(), Some(1));
        assert_eq!(stack.pop(), None);
    }

    #[test]
    fn test_treiber_stack_is_empty_and_len() {
        let stack: TreiberStack<i32> = TreiberStack::new();
        assert!(stack.is_empty());
        assert_eq!(stack.len(), 0);
        stack.push(42);
        assert!(!stack.is_empty());
        assert_eq!(stack.len(), 1);
    }

    #[test]
    fn test_treiber_stack_concurrent() {
        let stack = Arc::new(TreiberStack::new());
        let mut handles = vec![];
        for i in 0..4 {
            let s = Arc::clone(&stack);
            handles.push(std::thread::spawn(move || {
                for j in 0..100 {
                    s.push(i * 100 + j);
                }
            }));
        }
        for h in handles {
            h.join().unwrap();
        }
        assert_eq!(stack.len(), 400);
    }

    #[test]
    fn test_treiber_stack_real_impl_doc() {
        let doc = TreiberStackRealImpl::differences();
        assert!(doc.contains("AtomicPtr"));
        assert!(doc.contains("CAS"));
    }

    // ---------- MichaelScottQueue 测试 ----------

    #[test]
    fn test_ms_queue_enqueue_dequeue() {
        let queue = MichaelScottQueue::new();
        queue.enqueue(1);
        queue.enqueue(2);
        assert_eq!(queue.dequeue(), Some(1));
        assert_eq!(queue.dequeue(), Some(2));
        assert_eq!(queue.dequeue(), None);
    }

    #[test]
    fn test_ms_queue_is_empty_and_len() {
        let queue: MichaelScottQueue<i32> = MichaelScottQueue::new();
        assert!(queue.is_empty());
        assert_eq!(queue.len(), 0);
        queue.enqueue(42);
        assert!(!queue.is_empty());
        assert_eq!(queue.len(), 1);
    }

    #[test]
    fn test_ms_queue_real_impl_doc() {
        let doc = MichaelScottQueueRealImpl::differences();
        assert!(doc.contains("dummy node"));
        assert!(doc.contains("helping"));
    }
}
