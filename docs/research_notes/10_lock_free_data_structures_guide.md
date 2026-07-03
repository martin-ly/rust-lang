# 无锁数据结构指南 {#无锁数据结构指南}

> **EN**: Lock Free Data Structures Guide
> **Summary**: 无锁数据结构指南 Lock Free Data Structures Guide.
> **内容分级**: [核心级]
>
> **分级**: [A]
> **Bloom 层级**: L4-L6 (分析/评价/创造)
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29
> **Rust 版本**: 1.96.1+ (Edition 2024)
> **状态**: ✅ **已完成**
> **层级**: L4-L6
> **概念族**: 并发安全 / 无锁数据结构
> **权威来源**: [Rust Atomics and Locks](https://marabos.nl/atomics/) (P0) | [The Rust Programming Language - Fearless Concurrency](https://doc.rust-lang.org/book/ch16-00-concurrency.html) (P1) | [crossbeam-epoch documentation](https://docs.rs/crossbeam-epoch) (P2)

---

## 📑 目录 {#目录}

- [无锁数据结构指南 {#无锁数据结构指南}](#无锁数据结构指南-无锁数据结构指南)
  - [📑 目录 {#目录}](#-目录-目录)
  - [一、核心概念 {#一核心概念}](#一核心概念-一核心概念)
    - [1.1 什么是“无锁” {#11-什么是无锁}](#11-什么是无锁-11-什么是无锁)
    - [1.2 为什么需要内存回收 {#12-为什么需要内存回收}](#12-为什么需要内存回收-12-为什么需要内存回收)
  - [二、Treiber Stack {#二treiber-stack}](#二treiber-stack-二treiber-stack)
    - [2.1 算法描述 {#21-算法描述}](#21-算法描述-21-算法描述)
    - [2.2 Rust 实现要点 {#22-rust-实现要点}](#22-rust-实现要点-22-rust-实现要点)
    - [2.3 复杂度 {#23-复杂度}](#23-复杂度-23-复杂度)
  - [三、Michael-Scott Queue {#三michael-scott-queue-1}](#三michael-scott-queue-三michael-scott-queue-1)
    - [三、Michael-Scott Queue {#三michael-scott-queue-1}](#三michael-scott-queue-三michael-scott-queue-1-1)
    - [3.1 算法描述 {#31-算法描述}](#31-算法描述-31-算法描述)
    - [3.2 哨兵节点 {#32-哨兵节点}](#32-哨兵节点-32-哨兵节点)
    - [3.3 Rust 实现要点 {#33-rust-实现要点}](#33-rust-实现要点-33-rust-实现要点)
    - [3.4 复杂度 {#34-复杂度}](#34-复杂度-34-复杂度)
  - [四、Hazard Pointer 与 Epoch-Based Reclamation {#四hazard-pointer-与-epoch-based-reclamation}](#四hazard-pointer-与-epoch-based-reclamation-四hazard-pointer-与-epoch-based-reclamation)
    - [4.1 Hazard Pointer 核心思想 {#41-hazard-pointer-核心思想}](#41-hazard-pointer-核心思想-41-hazard-pointer-核心思想)
    - [4.2 Epoch-Based Reclamation 桥接 {#42-epoch-based-reclamation-桥接}](#42-epoch-based-reclamation-桥接-42-epoch-based-reclamation-桥接)
    - [4.3 选择桥接而非从零实现的原因 {#43-选择桥接而非从零实现的原因}](#43-选择桥接而非从零实现的原因-43-选择桥接而非从零实现的原因)
  - [五、ABA 问题 {#五aba-问题}](#五aba-问题-五aba-问题)
    - [5.1 问题定义 {#51-问题定义}](#51-问题定义-51-问题定义)
    - [5.2 解决方案 {#52-解决方案}](#52-解决方案-52-解决方案)
  - [六、内存序选择 {#六内存序选择}](#六内存序选择-六内存序选择)
    - [6.1 关键原则 {#61-关键原则}](#61-关键原则-61-关键原则)
    - [6.2 本实现的选择 {#62-本实现的选择}](#62-本实现的选择-62-本实现的选择)
  - [七、反例与边界 {#七反例与边界}](#七反例与边界-七反例与边界)
    - [7.1 未实现内存回收的 Treiber Stack {#71-未实现内存回收的-treiber-stack}](#71-未实现内存回收的-treiber-stack-71-未实现内存回收的-treiber-stack)
    - [7.2 错误内存序 {#72-错误内存序}](#72-错误内存序-72-错误内存序)
    - [7.3 忽略 lagging tail {#73-忽略-lagging-tail}](#73-忽略-lagging-tail-73-忽略-lagging-tail)
    - [7.4 弹出后访问已释放数据 {#74-弹出后访问已释放数据}](#74-弹出后访问已释放数据-74-弹出后访问已释放数据)
  - [八、代码锚点 {#八代码锚点}](#八代码锚点-八代码锚点)
  - [九、权威来源索引 {#九权威来源索引}](#九权威来源索引-九权威来源索引)

---

## 一、核心概念 {#一核心概念}

### 1.1 什么是“无锁” {#11-什么是无锁}

无锁（lock-free）数据结构保证：**至少有一个线程**在有限步骤内完成操作，即使其他线程被抢占或崩溃。它不同于：

| 类别 | 阻塞性 | 典型实现 |
|------|--------|----------|
| 阻塞（Blocking） | 高 | `Mutex`、`RwLock` |
| 无锁（Lock-free） | 低 | Treiber Stack、MS Queue、crossbeam 队列 |
| 无等待（Wait-free） | 无 | 理论模型，工程实现较少 |

> **来源**: [Rust Atomics and Locks](https://marabos.nl/atomics/) §2.3

### 1.2 为什么需要内存回收 {#12-为什么需要内存回收}

在无锁结构中，一个节点被逻辑删除后，其他线程可能仍持有指向它的指针。若立即 `free`，则会产生**悬垂指针（dangling pointer）**。因此需要：

- **Hazard Pointers**：每个线程声明自己正在访问的指针。
- **Epoch-Based Reclamation (EBR)**：将删除延迟到所有线程离开当前 epoch。
- **引用计数**：原子引用计数，但可能引入额外竞争。

---

## 二、Treiber Stack {#二treiber-stack}

### 2.1 算法描述 {#21-算法描述}

Treiber Stack 是无锁 LIFO 栈的经典实现：

1. `push(x)`：分配新节点 `n`，令 `n.next = head`，然后 CAS `head = n`。
2. `pop()`：读取 `head`，若为空返回 `None`；否则 CAS `head = head.next`，返回 `head.data`。

### 2.2 Rust 实现要点 {#22-rust-实现要点}

```rust
// 代码锚点: crates/c08_algorithms/src/data_structure/lock_free_stack.rs
pub struct LockFreeStack<T> {
    head: Atomic<Node<T>>,
}
```

- 节点使用 `Option<T>` 存储数据，弹出时 `take()` 避免重复释放。
- 使用 `crossbeam-epoch` 的 `Guard` 保护读取，成功 CAS 后通过 `defer_unchecked` 延迟释放节点。

### 2.3 复杂度 {#23-复杂度}

- 时间：均摊 **O(1)**。
- 空间：每个元素一个节点 + epoch 回收延迟。

---

## 三、Michael-Scott Queue {#三michael-scott-queue-1}

### 三、Michael-Scott Queue {#三michael-scott-queue-1}

### 3.1 算法描述 {#31-算法描述}

Michael-Scott Queue 是无锁 FIFO 队列：

1. `enqueue(x)`：分配新节点 `n`；循环找到真实尾节点 `tail`（处理 lagging tail）；CAS `tail.next = n`；尝试 CAS `tail = n`。
2. `dequeue()`：读取 `head` 与 `head.next`；若 `head == tail` 且 `next` 为空，则队列空；否则 CAS `head = next`，返回 `next.data`。

### 3.2 哨兵节点 {#32-哨兵节点}

使用一个初始哨兵节点，保证 `head` 与 `tail` 永不为空，简化空队列判断。

### 3.3 Rust 实现要点 {#33-rust-实现要点}

```rust
// 代码锚点: crates/c08_algorithms/src/data_structure/lock_free_queue.rs
pub struct LockFreeQueue<T> {
    head: Atomic<Node<T>>,
    tail: Atomic<Node<T>>,
}
```

- `enqueue` 需要帮助推进落后的 `tail`（helping 机制）。
- `dequeue` 移动 `head` 后，旧哨兵节点与新头节点的数据都需要延迟释放。

### 3.4 复杂度 {#34-复杂度}

- 时间：均摊 **O(1)**。
- 空间：每个元素一个节点 + 一个哨兵节点 + 回收延迟。

---

## 四、Hazard Pointer 与 Epoch-Based Reclamation {#四hazard-pointer-与-epoch-based-reclamation}

### 4.1 Hazard Pointer 核心思想 {#41-hazard-pointer-核心思想}

每个线程维护一组“危险指针”：

1. 访问共享节点前，先将指针写入 hazard record。
2. 再次验证该节点仍属于数据结构。
3. 释放内存前，扫描所有 hazard records，确认没有线程保护该指针。

### 4.2 Epoch-Based Reclamation 桥接 {#42-epoch-based-reclamation-桥接}

`crossbeam-epoch` 实现了与 Hazard Pointer 等价的安全保证：

```rust
// 代码锚点: crates/c08_algorithms/src/data_structure/hazard_pointer.rs
pub struct HazardPointer {
    guard: Guard,
}
```

- `pin()`：进入当前 epoch，等效于声明 hazard pointer。
- `Guard` drop：自动 unpin，等效于清除 hazard pointer。
- `defer_unchecked`：将节点延迟到安全 epoch 释放。

### 4.3 选择桥接而非从零实现的原因 {#43-选择桥接而非从零实现的原因}

生产级 Hazard Pointer 需要处理：

- 线程本地 hazard record 分配与回收。
- 全局 hazard list 的扫描（最小化缓存失效）。
- 线程退出时的清理。

`crossbeam-epoch` 已经高效实现这些细节，是 Rust 生态事实标准。

---

## 五、ABA 问题 {#五aba-问题}

### 5.1 问题定义 {#51-问题定义}

ABA 问题：

1. 线程 A 读取 `head = X`。
2. 线程 B 弹出 `X`、弹出 `Y`、再压入一个新节点，其地址恰好复用 `X`。
3. 线程 A 的 CAS `head = X -> Z` 成功，但栈的实际状态已被改变。

在 Treiber Stack 中，ABA 可能导致 `next` 指针指向已释放或错误节点。

### 5.2 解决方案 {#52-解决方案}

| 方案 | 原理 | 适用场景 |
|------|------|----------|
|  tagged pointer | 在指针低位嵌入版本计数 | 64 位系统，指针按字对齐 |
|  Hazard Pointers / EBR | 延迟释放，阻止地址复用 | 通用，与 Rust 的 `crossbeam-epoch` 配合 |
|  RCU | 读侧临界区保护，批量回收 | 读多写少 |

本实现采用 **EBR（crossbeam-epoch）**，因为：

- 无需手动管理 tagged pointer 的位运算。
- 与 Rust 所有权系统兼容，避免裸指针误用。

---

## 六、内存序选择 {#六内存序选择}

### 6.1 关键原则 {#61-关键原则}

无锁算法中，内存序决定操作的可见性顺序：

| 内存序 | 语义 | 典型用途 |
|--------|------|----------|
| `Relaxed` | 无同步保证 | 计数器、局部状态 |
| `Acquire` | 保证读到最新发布的数据 | 读取共享指针（如 `head.load`） |
| `Release` | 保证此前写入对获取侧可见 | 发布共享指针（如 CAS 成功） |
| `AcqRel` | 同时具有 Acquire 与 Release | CAS 读写同一原子变量 |
| `SeqCst` | 全局顺序 | 通常不需要，性能代价高 |

### 6.2 本实现的选择 {#62-本实现的选择}

```rust
// push: 发布新节点
self.head.compare_exchange(head, new, Release, Acquire, guard)

// pop: 读取 head 与 next
let head = self.head.load(Acquire, guard);
let next = head_ref.next.load(Acquire, guard);
```

- `Acquire` 读 `head`：确保看到其他线程 `Release` 写入的完整节点。
- `Release` 写 `head`：确保节点初始化对其他线程可见。
- `next` 在 push 时用 `Relaxed` 存储即可，因为 push 的 `Release` CAS 已经保证了发布顺序。

> **来源**: [Rust Reference - Memory Model](https://doc.rust-lang.org/reference/memory-model.html) (P1)

---

## 七、反例与边界 {#七反例与边界}

### 7.1 未实现内存回收的 Treiber Stack {#71-未实现内存回收的-treiber-stack}

```rust
// 反例：弹出后立即 Box::from_raw 释放
let data = unsafe {
    let boxed = Box::from_raw(current_head);
    boxed.data
};
```

**问题**：其他线程可能仍持有 `current_head` 的 hazard pointer，导致 use-after-free。

**正确做法**：使用 `crossbeam-epoch` 延迟释放。

### 7.2 错误内存序 {#72-错误内存序}

```rust
// 反例：使用 Relaxed 读取 head
let head = self.head.load(Relaxed, guard);
```

**问题**：可能读到未完全初始化的节点（data race）。

**正确做法**：读取共享指针使用 `Acquire`。

### 7.3 忽略 lagging tail {#73-忽略-lagging-tail}

```rust
// 反例：MS Queue 中直接 CAS tail.next，不帮助推进 tail
```

**问题**：若 `tail` 落后，CAS 会反复失败，导致活锁或性能退化。

**正确做法**：enqueue/dequeue 都提供帮助推进逻辑。

### 7.4 弹出后访问已释放数据 {#74-弹出后访问已释放数据}

```rust
// 反例：pop 中先 defer_delete，再读取数据
```

**问题**：`defer_unchecked` 可能在当前线程继续执行前触发回收（虽然 EBR 保证在 Guard 内不回收，但逻辑上仍应避免）。

**正确做法**：在 `Guard` 保护下读取数据，再提交延迟释放。

---

## 八、代码锚点 {#八代码锚点}

| 概念 | 文件 | 关键类型/函数 |
|------|------|---------------|
| Treiber Stack | `crates/c08_algorithms/src/data_structure/lock_free_stack.rs` | `LockFreeStack<T>` |
| Michael-Scott Queue | `crates/c08_algorithms/src/data_structure/lock_free_queue.rs` | `LockFreeQueue<T>` |
| Hazard Pointer / EBR 桥接 | `crates/c08_algorithms/src/data_structure/hazard_pointer.rs` | `HazardPointer`, `defer_delete` |
| 综合示例 | `crates/c08_algorithms/examples/lock_free_data_structures_demo.rs` | `main` |
| 知识图谱 | `docs/research_notes/10_knowledge_graph_index.md` | 无锁数据结构节点与关系边 |

---

## 九、权威来源索引 {#九权威来源索引}

| 级别 | 来源 | 链接 | 对齐内容 |
|------|------|------|----------|
| P0 | *Rust Atomics and Locks* | <https://marabos.nl/atomics/> | Treiber Stack、MS Queue、内存序、ABA |
| P1 | The Rust Programming Language | <https://doc.rust-lang.org/book/ch16-00-concurrency.html> | Send/Sync、并发安全基础 |
| P1 | Rust Reference | <https://doc.rust-lang.org/reference/memory-model.html> | 内存模型与内存序 |
| P2 | crossbeam-epoch docs | <https://docs.rs/crossbeam-epoch> | EBR API、Guard、defer_unchecked |
| P2 | Rustonomicon | <https://doc.rust-lang.org/nomicon/> | unsafe Rust、裸指针、内存回收 |

> **来源: [ACM Digital Library](https://dl.acm.org/)**
> **来源: [IEEE Standards](https://standards.ieee.org/)**
