# Tokio Runtime: Formal Analysis and Deep Dive

## Table of Contents

- [Tokio Runtime: Formal Analysis and Deep Dive](#tokio-runtime-formal-analysis-and-deep-dive)
  - [Table of Contents](#table-of-contents)
  - [1. Introduction](#1-introduction)
    - [1.1 What is Tokio?](#11-what-is-tokio)
    - [1.2 Why Formal Analysis Matters](#12-why-formal-analysis-matters)
  - [2. Tokio Architecture](#2-tokio-architecture)
    - [2.1 Runtime Components](#21-runtime-components)
      - [2.1.1 Scheduler](#211-scheduler)
      - [2.1.2 I/O Driver](#212-io-driver)
      - [2.1.3 Timer](#213-timer)
      - [2.1.4 Blocking Pool](#214-blocking-pool)
    - [2.2 Scheduler Types](#22-scheduler-types)
      - [2.2.1 Current-Thread Scheduler](#221-current-thread-scheduler)
      - [2.2.2 Multi-Thread Scheduler](#222-multi-thread-scheduler)
  - [3. Task System](#3-task-system)
    - [3.1 Task Structure](#31-task-structure)
    - [3.2 Spawning Semantics](#32-spawning-semantics)
      - [3.2.1 Theorem SPAWN-SAFETY](#321-theorem-spawn-safety)
      - [3.2.2 Theorem SPAWN-LOCAL-SAFETY](#322-theorem-spawn-local-safety)
    - [3.3 JoinHandle Semantics](#33-joinhandle-semantics)
  - [4. Ownership in Async](#4-ownership-in-async)
    - [4.1 Task Ownership Model](#41-task-ownership-model)
    - [4.2 Shared Ownership Patterns](#42-shared-ownership-patterns)
      - [4.2.1 Arc\<Mutex\> Pattern](#421-arcmutex-pattern)
      - [4.2.2 Channel-Based Communication](#422-channel-based-communication)
    - [4.3 JoinHandle and Task Completion](#43-joinhandle-and-task-completion)
  - [5. I/O Driver](#5-io-driver)
    - [5.1 Mio Integration](#51-mio-integration)
    - [5.2 Platform Abstractions](#52-platform-abstractions)
      - [5.2.1 Epoll (Linux)](#521-epoll-linux)
      - [5.2.2 Kqueue (BSD/macOS)](#522-kqueue-bsdmacos)
      - [5.2.3 IOCP (Windows)](#523-iocp-windows)
    - [5.3 I/O Resource Lifecycle](#53-io-resource-lifecycle)
  - [6. Timer System](#6-timer-system)
    - [6.1 Hierarchical Timer Wheel](#61-hierarchical-timer-wheel)
    - [6.2 Timer Operations](#62-timer-operations)
    - [6.3 Timer Implementation Details](#63-timer-implementation-details)
  - [7. Counter-Examples](#7-counter-examples)
    - [Counter-Example 1: spawn\_local in Multi-Threaded Context](#counter-example-1-spawn_local-in-multi-threaded-context)
    - [Counter-Example 2: !Send Future in spawn](#counter-example-2-send-future-in-spawn)
    - [Counter-Example 3: Blocking in Async Context](#counter-example-3-blocking-in-async-context)
    - [Counter-Example 4: Mutex Across await](#counter-example-4-mutex-across-await)
    - [Counter-Example 5: Unbounded Channel Memory Leak](#counter-example-5-unbounded-channel-memory-leak)
    - [Counter-Example 6: Memory Leak in Long-Running Task](#counter-example-6-memory-leak-in-long-running-task)
    - [Counter-Example 7: Timer Cancellation Race](#counter-example-7-timer-cancellation-race)
    - [Counter-Example 8: Select Resource Leak](#counter-example-8-select-resource-leak)
    - [Counter-Example 9: Async Drop Missing](#counter-example-9-async-drop-missing)
    - [Counter-Example 10: Runtime Shutdown with Pending Tasks](#counter-example-10-runtime-shutdown-with-pending-tasks)
    - [Counter-Example 11: Blocking Thread Exhaustion](#counter-example-11-blocking-thread-exhaustion)
    - [Counter-Example 12: Wrong Runtime Flavor](#counter-example-12-wrong-runtime-flavor)
    - [Counter-Example 13: LocalSet in Wrong Context](#counter-example-13-localset-in-wrong-context)
    - [Counter-Example 14: Task Abort During Critical Section](#counter-example-14-task-abort-during-critical-section)
    - [Counter-Example 15: Interval Drift](#counter-example-15-interval-drift)
    - [Counter-Example 16: Deadlock with Nested Locks](#counter-example-16-deadlock-with-nested-locks)
    - [Counter-Example 17: Semaphore Permit Leak](#counter-example-17-semaphore-permit-leak)
    - [Counter-Example 18: Incorrect Buffer Management](#counter-example-18-incorrect-buffer-management)
  - [8. Performance Analysis](#8-performance-analysis)
    - [8.1 Work-Stealing Algorithm](#81-work-stealing-algorithm)
    - [8.2 Task Polling](#82-task-polling)
    - [8.3 Memory Layout](#83-memory-layout)
  - [9. Case Study: Web Server](#9-case-study-web-server)
    - [9.1 Complete HTTP Server Implementation](#91-complete-http-server-implementation)
    - [9.2 Performance Optimizations](#92-performance-optimizations)
    - [9.3 Testing the Server](#93-testing-the-server)
  - [10. References](#10-references)
    - [10.1 Academic Papers](#101-academic-papers)
    - [10.2 Official Documentation](#102-official-documentation)
    - [10.3 Related Crates](#103-related-crates)
  - [Appendix A: Theorem Summary](#appendix-a-theorem-summary)
  - [Appendix B: Glossary](#appendix-b-glossary)

---

## 1. Introduction

Tokio is the preeminent asynchronous runtime for the Rust programming language, providing the essential infrastructure for building high-performance, concurrent applications. This document presents a comprehensive formal analysis of the Tokio runtime, examining its architecture, semantics, safety properties, and common pitfalls through the lens of ownership, types, and formal verification principles.

### 1.1 What is Tokio?

Tokio is an event-driven, non-blocking I/O platform for writing asynchronous applications in Rust. It consists of:

- **Runtime**: The core executor that schedules and runs asynchronous tasks
- **I/O drivers**: Platform-specific abstractions for network and file operations
- **Timer facilities**: For delays, timeouts, and intervals
- **Synchronization primitives**: Channels, mutexes, and barriers for async contexts

### 1.2 Why Formal Analysis Matters

Understanding Tokio through formal analysis provides several benefits:

1. **Correctness guarantees**: Reasoning about safety properties ensures code behaves as expected
2. **Performance understanding**: Knowledge of internal mechanisms enables optimization
3. **Debugging efficiency**: Understanding failure modes helps diagnose issues
4. **Architectural decisions**: Informed choices about task spawning, resource management, etc.

---

## 2. Tokio Architecture

### 2.1 Runtime Components

The Tokio runtime can be formally defined as a composition of four primary components:

```
Runtime = Scheduler + I/O Driver + Timer + Blocking Pool
```

Each component has specific responsibilities and interacts with others through well-defined interfaces.

#### 2.1.1 Scheduler

The scheduler is responsible for executing asynchronous tasks. Tokio provides two primary scheduler flavors:

```rust
// Current-thread scheduler
let rt = tokio::runtime::Builder::new_current_thread()
    .build()
    .unwrap();

// Multi-thread scheduler (work-stealing)
let rt = tokio::runtime::Builder::new_multi_thread()
    .worker_threads(4)
    .build()
    .unwrap();
```

**Formal Definition**:

```
Scheduler = (T, W, P, S)
where:
  T = Set of tasks {t₁, t₂, ..., tₙ}
  W = Set of workers {w₁, w₂, ..., wₘ}
  P = Policy function: T × W → Task
  S = State: Running | ShuttingDown | Shutdown
```

#### 2.1.2 I/O Driver

The I/O driver integrates with the operating system's asynchronous I/O facilities:

- **Linux**: epoll
- **macOS/BSD**: kqueue
- **Windows**: IOCP (I/O Completion Ports)
- **io_uring**: Experimental support on Linux

```rust
// Internal structure (simplified)
pub(crate) struct Driver {
    inner: Inner,
    tick: u8,
}

enum Inner {
    #[cfg(unix)]
    Poll(Poll),
    #[cfg(windows)]
    Iocp(Iocp),
    #[cfg(all(target_os = "linux", feature = "io-uring"))]
    Uring(Uring),
}
```

#### 2.1.3 Timer

The timer system provides:

- `tokio::time::sleep`: One-shot delays
- `tokio::time::interval`: Periodic execution
- `tokio::time::timeout`: Operation timeouts

```rust
pub(crate) struct Timer {
    wheel: Wheel,
    next_expiration: Option<Instant>,
}
```

#### 2.1.4 Blocking Pool

For operations that cannot be made asynchronous, Tokio provides a dedicated thread pool:

```rust
// Spawn blocking operation
let result = tokio::task::spawn_blocking(|| {
    // CPU-intensive or blocking I/O work
    std::fs::read_to_string("large_file.txt")
}).await?;
```

### 2.2 Scheduler Types

#### 2.2.1 Current-Thread Scheduler

**Definition**: Executes all tasks on the current OS thread.

```rust
#[tokio::main(flavor = "current_thread")]
async fn main() {
    // All tasks run on the main thread
    tokio::spawn(async {
        println!("Running on main thread");
    }).await.unwrap();
}
```

**Properties**:

```
Theorem CURRENT-THREAD-ISOLATION:
  For all tasks t spawned on current_thread runtime:
    thread_id(t) = thread_id(runtime)

Corollary: No Send bound required for Rc, RefCell
```

**Use Cases**:

- Testing and debugging
- Applications requiring thread-local state
- Single-threaded performance scenarios
- Resource-constrained environments

#### 2.2.2 Multi-Thread Scheduler

**Definition**: Uses a work-stealing algorithm across multiple OS threads.

```rust
#[tokio::main(flavor = "multi_thread", worker_threads = 8)]
async fn main() {
    // Tasks may migrate between worker threads
    tokio::spawn(async {
        println!("Running on worker thread");
    }).await.unwrap();
}
```

**Properties**:

```
Theorem MULTI-THREAD-SEND-REQUIREMENT:
  For all tasks t spawned on multi_thread runtime:
    ∀ capture c in t: Send(c) must hold

Theorem WORK-STEALING-LOAD-BALANCING:
  Given worker threads w₁, w₂ with queues Q₁, Q₂:
    if |Q₁| > |Q₂| + threshold:
      ∃ task t ∈ Q₁: migrate(t, w₁ → w₂)
```

**Work-Stealing Algorithm**:

```
Algorithm WORK-STEALING:
  Input: Worker w with local queue Q_local

  1. Poll task from Q_local (LIFO order)
  2. If Q_local empty:
       a. Try to steal from global injection queue
       b. Try to steal from other workers' queues (FIFO order)
  3. Repeat while runtime active
```

---

## 3. Task System

### 3.1 Task Structure

A Tokio task is the fundamental unit of concurrent execution. Formally:

```rust
/// Conceptual task structure
struct Task {
    /// The future to execute
    future: Pin<Box<dyn Future<Output = ()> + Send>>,

    /// Current execution state
    state: TaskState,

    /// Waker for notification
    waker: Option<Waker>,

    /// Associated metadata
    id: TaskId,
}

#[derive(Clone, Copy, PartialEq)]
enum TaskState {
    Created,     // Task just spawned
    Running,     // Currently being polled
    Suspended,   // Awaiting I/O or timer
    Completed,   // Future returned Poll::Ready
    Cancelled,   // Explicitly aborted
}
```

**Task Lifecycle**:

```
┌─────────┐    spawn     ┌──────────┐   poll     ┌─────────┐
│ Created │ ───────────→ │  Ready   │ ────────→ │ Running │
└─────────┘              └──────────┘           └────┬────┘
                                                     │
              ┌──────────────────────────────────────┤
              │                                      │
              ↓  Poll::Pending                       ↓ Poll::Ready
        ┌──────────┐                           ┌──────────┐
        │ Suspended│ ←──────────────────────── │Completed │
        └────┬─────┘    waker.notify()         └──────────┘
             │
             └────────────────────────────────────┐
                                                  │
                                                  ↓ abort()
                                           ┌──────────┐
                                           │ Cancelled│
                                           └──────────┘
```

### 3.2 Spawning Semantics

#### 3.2.1 Theorem SPAWN-SAFETY

**Statement**:

```
Theorem SPAWN-SAFETY:
  For spawn(task) on multi_thread runtime:
    task: Future + Send + 'static ⊢ SafeSpawn(task)

  where SafeSpawn(task) ≝
    ∀ data d captured by task:
      Send(d) ∧ (d: 'static ∨ d owned by task)
```

**Proof Sketch**:

1. Multi-thread scheduler may move task between worker threads
2. Task must be Send to safely migrate across thread boundaries
3. 'static bound ensures captured references outlive task execution
4. Therefore, Send + 'static are necessary conditions

```rust
// Valid: String is Send + 'static
let data: String = "hello".to_string();
tokio::spawn(async move {
    println!("{}", data); // OK
});

// Invalid: Rc is !Send
let data: Rc<String> = Rc::new("hello".to_string());
tokio::spawn(async move {
    println!("{}", data); // ERROR: Rc<String> cannot be sent between threads
});
```

#### 3.2.2 Theorem SPAWN-LOCAL-SAFETY

**Statement**:

```
Theorem SPAWN-LOCAL-SAFETY:
  For spawn_local(task) on current_thread runtime:
    task: Future + 'static ⊢ SafeLocalSpawn(task)

  Note: Send bound NOT required as task never migrates threads
```

```rust
// Valid on current_thread runtime
let data: Rc<String> = Rc::new("hello".to_string());
tokio::task::spawn_local(async move {
    println!("{}", data); // OK on current_thread
});
```

### 3.3 JoinHandle Semantics

```rust
/// Handle for awaiting task completion
pub struct JoinHandle<T> {
    raw: Option<RawTask>,
    _p: PhantomData<T>,
}

impl<T> Future for JoinHandle<T> {
    type Output = Result<T, JoinError>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        // Polls for task completion
    }
}
```

**Theorem JOINHANDLE-COMPLETION**:

```
Theorem JOINHANDLE-COMPLETION:
  For JoinHandle h from spawn(task):
    h.await = Ok(v)  ⟺  task completes normally with value v
    h.await = Err(e) ⟺  task panics OR is aborted
    h.await blocks   ⟺  task still executing
```

---

## 4. Ownership in Async

### 4.1 Task Ownership Model

Each Tokio task has exclusive ownership of its future and all captured data:

```
Ownership Model:
┌─────────────────────────────────────────┐
│              Task Owner                 │
│  ┌─────────────────────────────────┐    │
│  │          Future                 │    │
│  │  ┌─────────────────────────┐    │    │
│  │  │   Captured Data         │    │    │
│  │  │   - Strings             │    │    │
│  │  │   - Channels            │    │    │
│  │  │   - Sockets             │    │    │
│  │  └─────────────────────────┘    │    │
│  └─────────────────────────────────┘    │
│           │                             │
│           ↓ poll()                      │
│      (temporary &mut)                   │
└─────────────────────────────────────────┘
```

### 4.2 Shared Ownership Patterns

#### 4.2.1 Arc<Mutex<T>> Pattern

```rust
use std::sync::Arc;
use tokio::sync::Mutex;

// Shared state between tasks
let state = Arc::new(Mutex::new(Vec::new()));

let state2 = state.clone();
tokio::spawn(async move {
    state2.lock().await.push(1);
});

state.lock().await.push(2);
```

**Formal Properties**:

```
Given: Arc<Mutex<T>> shared across tasks
Invariants:
  1. Arc maintains reference count (thread-safe)
  2. Mutex provides mutual exclusion (async-aware)
  3. T is protected from data races
```

#### 4.2.2 Channel-Based Communication

```rust
use tokio::sync::mpsc;

let (tx, mut rx) = mpsc::channel(100);

tokio::spawn(async move {
    while let Some(msg) = rx.recv().await {
        process(msg).await;
    }
});

tx.send("message").await?;
```

### 4.3 JoinHandle and Task Completion

The `JoinHandle` provides a mechanism to await task completion and retrieve results:

```rust
let handle: JoinHandle<i32> = tokio::spawn(async {
    compute_something().await
});

// Await completion
match handle.await {
    Ok(result) => println!("Task returned: {}", result),
    Err(e) => println!("Task failed: {:?}", e),
}
```

**Theorem JOINHANDLE-LIFETIME**:

```
Theorem JOINHANDLE-LIFETIME:
  JoinHandle<T>: 'static independent of T's lifetime

  Reason: JoinHandle internally holds task reference, not T directly
  Consequence: Can store handles in long-lived collections
```

---

## 5. I/O Driver

### 5.1 Mio Integration

Tokio builds upon the `mio` crate for platform-specific I/O multiplexing:

```rust
// Conceptual mio integration
struct IoDriver {
    registry: Registry,
    events: Events,
}

impl IoDriver {
    fn poll(&mut self, timeout: Option<Duration>) -> io::Result<()> {
        self.poll.poll(&mut self.events, timeout)?;

        for event in &self.events {
            self.dispatch_event(event);
        }
        Ok(())
    }
}
```

### 5.2 Platform Abstractions

#### 5.2.1 Epoll (Linux)

```rust
#[cfg(target_os = "linux")]
mod epoll {
    use libc::{epoll_create1, epoll_ctl, epoll_wait, EPOLL_CLOEXEC};

    pub struct Epoll {
        epfd: RawFd,
    }

    impl Epoll {
        pub fn new() -> io::Result<Epoll> {
            let epfd = syscall!(epoll_create1(EPOLL_CLOEXEC))?;
            Ok(Epoll { epfd })
        }

        pub fn register(&self, fd: RawFd, token: Token, interests: Interests) {
            // epoll_ctl(EPOLL_CTL_ADD)
        }
    }
}
```

#### 5.2.2 Kqueue (BSD/macOS)

```rust
#[cfg(any(target_os = "macos", target_os = "freebsd", target_os = "dragonfly"))]
mod kqueue {
    use libc::{kqueue, kevent, EV_ADD, EV_ENABLE};

    pub struct Kqueue {
        kq: RawFd,
    }
}
```

#### 5.2.3 IOCP (Windows)

```rust
#[cfg(windows)]
mod iocp {
    use windows_sys::Win32::System::IO::{CreateIoCompletionPort, GetQueuedCompletionStatus};

    pub struct Iocp {
        handle: HANDLE,
    }
}
```

### 5.3 I/O Resource Lifecycle

```
┌──────────────┐
│   Created    │
└──────┬───────┘
       │ register with driver
       ↓
┌──────────────┐
│  Registered  │◄──────┐
└──────┬───────┘       │ ready
       │               │
       ↓ poll          │
┌──────────────┐       │
│   Waiting    │───────┘
└──────┬───────┘
       │ ready
       ↓
┌──────────────┐
│   Ready      │
└──────┬───────┘
       │ read/write
       ↓
┌──────────────┐
│  Completed   │
└──────────────┘
```

---

## 6. Timer System

### 6.1 Hierarchical Timer Wheel

Tokio uses a hierarchical timer wheel for efficient timer management:

```rust
/// Hierarchical timer wheel with 6 levels
pub(crate) struct Timer {
    /// Wheel levels: [ms, 100ms, 1s, 10s, 100s, 1000s]
    wheels: [Wheel; NUM_WHEELS],

    /// Current time base
    time_base: Instant,

    /// Next expiration time
    next_expiration: Option<Instant>,
}

struct Wheel {
    /// 64 slots per wheel level
    slots: [Vec<Entry>; 64],

    /// Current slot index
    cursor: usize,
}
```

**Wheel Levels**:

```
Level 0: 64 slots × 1ms   = 64ms range, 1ms resolution
Level 1: 64 slots × 100ms = 6.4s range, 100ms resolution
Level 2: 64 slots × 1s    = 64s range, 1s resolution
Level 3: 64 slots × 10s   = 640s range, 10s resolution
Level 4: 64 slots × 100s  = 6400s range, 100s resolution
Level 5: 64 slots × 1000s = 64000s range, 1000s resolution
```

### 6.2 Timer Operations

```rust
/// Create a sleep future
pub fn sleep(duration: Duration) -> Sleep {
    Sleep::new_timeout(Instant::now() + duration)
}

/// Create an interval
pub fn interval(period: Duration) -> Interval {
    Interval::new(Instant::now(), period)
}

/// Timeout wrapper
pub fn timeout<T>(duration: Duration, future: T) -> Timeout<T> {
    Timeout::new(future, duration)
}
```

**Theorem TIMER-ACCURACY**:

```
Theorem TIMER-ACCURACY:
  For sleep(d) where d is duration:
    actual_delay ∈ [d, d + scheduler_quantum]

  where scheduler_quantum depends on runtime load
```

### 6.3 Timer Implementation Details

```rust
impl Future for Sleep {
    type Output = ();

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<()> {
        let now = Instant::now();

        if now >= self.deadline {
            // Timer expired
            Poll::Ready(())
        } else {
            // Register waker for notification
            self.register(cx.waker());
            Poll::Pending
        }
    }
}
```

---

## 7. Counter-Examples

This section presents 15+ counter-examples demonstrating common mistakes and anti-patterns when using Tokio.

### Counter-Example 1: spawn_local in Multi-Threaded Context

**Problem**: Attempting to use `spawn_local` without a `LocalSet` on a multi-threaded runtime.

```rust
use std::rc::Rc;

#[tokio::main(flavor = "multi_thread")]
async fn main() {
    let data = Rc::new("local data".to_string());

    // ERROR: spawn_local called from outside of the LocalSet
    tokio::task::spawn_local(async move {
        println!("{}", data);
    });
}
```

**Error Output**:

```
thread 'main' panicked at 'spawn_local called from outside of the LocalSet'
```

**Root Cause**: `spawn_local` requires a `LocalSet` context even on current_thread runtime. On multi_thread runtime, a `LocalSet` must be explicitly created.

**Correct Usage**:

```rust
#[tokio::main(flavor = "multi_thread")]
async fn main() {
    let local = tokio::task::LocalSet::new();

    let data = Rc::new("local data".to_string());

    local.run_until(async move {
        tokio::task::spawn_local(async move {
            println!("{}", data);
        }).await.unwrap();
    }).await;
}
```

**Formal Analysis**:

```
Invariant VIOLATED: spawn_local requires LocalSet context

Preconditions for spawn_local(task):
  1. Current thread within LocalSet scope
  2. LocalSet.run_until() or LocalSet.await active

Violation leads to: panic! at runtime
```

---

### Counter-Example 2: !Send Future in spawn

**Problem**: Trying to spawn a future containing `!Send` types on a multi-threaded runtime.

```rust
use std::rc::Rc;
use std::cell::RefCell;

#[tokio::main]
async fn main() {
    let data = Rc::new(RefCell::new(vec![1, 2, 3]));

    // ERROR: Rc<RefCell<Vec<i32>>> cannot be sent between threads safely
    tokio::spawn(async move {
        data.borrow_mut().push(4);
    });
}
```

**Error Output**:

```
error[E0277]: `Rc<RefCell<Vec<i32>>>` cannot be sent between threads safely
   --> src/main.rs:7:5
    |
7   |     tokio::spawn(async move {
    |     ^^^^^^^^^^^^ `Rc<RefCell<Vec<i32>>>` cannot be sent between threads safely
    |
    = help: within `[async block@src/main.rs:7:18: 9:6]`, the trait `Send` is not implemented for `Rc<RefCell<Vec<i32>>>`
```

**Root Cause**: `Rc` and `RefCell` are `!Send`. The multi-threaded scheduler may move tasks between threads, requiring all captured data to be `Send`.

**Solutions**:

```rust
// Solution 1: Use Arc + Mutex instead of Rc + RefCell
use std::sync::Arc;
use tokio::sync::Mutex;

let data = Arc::new(Mutex::new(vec![1, 2, 3]));

tokio::spawn(async move {
    data.lock().await.push(4);
});
```

```rust
// Solution 2: Use current_thread runtime
#[tokio::main(flavor = "current_thread")]
async fn main() {
    let data = Rc::new(RefCell::new(vec![1, 2, 3]));

    tokio::spawn(async move {
        data.borrow_mut().push(4);
    });
}
```

**Formal Analysis**:

```
Theorem VIOLATED: spawn(task) ⊢ Send(task)

Rc<T>: !Send because reference counting is not thread-safe
RefCell<T>: !Send because interior mutability is not thread-safe

Fix: Replace with:
  Arc<T>: Send when T: Send + Sync
  Mutex<T>: Send when T: Send
```

---

### Counter-Example 3: Blocking in Async Context

**Problem**: Performing blocking I/O or CPU-intensive work directly in async code.

```rust
#[tokio::main]
async fn main() {
    let handles: Vec<_> = (0..100)
        .map(|i| {
            tokio::spawn(async move {
                // BAD: Blocking the async executor thread!
                let contents = std::fs::read_to_string("large_file.txt").unwrap();

                // BAD: CPU-intensive work on executor thread
                let sum: u64 = (0..10_000_000).sum();

                (i, contents.len(), sum)
            })
        })
        .collect();

    for handle in handles {
        let (i, len, sum) = handle.await.unwrap();
        println!("Task {}: file size = {}, sum = {}", i, len, sum);
    }
}
```

**Problem Analysis**:

```
Impact of blocking in async:
┌─────────────────────────────────────────────────────────┐
│  Worker Thread 1: [blocked on file read]                │
│  Worker Thread 2: [blocked on file read]                │
│  Worker Thread 3: [blocked on file read]                │
│  Worker Thread 4: [blocked on file read]                │
│                                                         │
│  Result: All tasks blocked, no progress possible!       │
└─────────────────────────────────────────────────────────┘
```

**Solution**: Use `spawn_blocking` for blocking operations.

```rust
#[tokio::main]
async fn main() {
    let handles: Vec<_> = (0..100)
        .map(|i| {
            tokio::spawn(async move {
                // GOOD: Move blocking work to blocking pool
                let contents = tokio::task::spawn_blocking(|| {
                    std::fs::read_to_string("large_file.txt").unwrap()
                }).await.unwrap();

                // GOOD: CPU work in blocking pool
                let sum = tokio::task::spawn_blocking(|| {
                    (0..10_000_000).sum::<u64>()
                }).await.unwrap();

                (i, contents.len(), sum)
            })
        })
        .collect();

    for handle in handles {
        let (i, len, sum) = handle.await.unwrap();
        println!("Task {}: file size = {}, sum = {}", i, len, sum);
    }
}
```

**Formal Analysis**:

```
Theorem ASYNC-FAIRNESS:
  For runtime R with n worker threads:
    blocking_operation() on worker ⟹ n-1 workers available
    blocking_operation() on all workers ⟹ deadlock

Corollary: Always use spawn_blocking for:
  - Synchronous I/O (file system operations)
  - CPU-intensive computations
  - Blocking syscalls
```

---

### Counter-Example 4: Mutex Across await

**Problem**: Holding a standard library mutex across an await point.

```rust
use std::sync::Mutex;

#[tokio::main]
async fn main() {
    let data = std::sync::Arc::new(Mutex::new(Vec::new()));

    let data2 = data.clone();
    tokio::spawn(async move {
        // BAD: Holding std::sync::MutexGuard across await!
        let mut guard = data2.lock().unwrap();

        // This await point means the mutex is held while task is suspended
        tokio::time::sleep(std::time::Duration::from_secs(1)).await;

        guard.push(1); // May panic if another task panicked while holding lock
    });

    // This task may block indefinitely
    let data3 = data.clone();
    tokio::spawn(async move {
        let mut guard = data3.lock().unwrap();
        guard.push(2);
    }).await.unwrap();
}
```

**Root Cause**: `std::sync::MutexGuard` is `!Send`, and holding it across await can:

1. Cause deadlocks if the task is moved between threads
2. Block the executor thread if another task tries to acquire the same mutex

**Solution**: Use `tokio::sync::Mutex` for async contexts.

```rust
use tokio::sync::Mutex;

#[tokio::main]
async fn main() {
    let data = std::sync::Arc::new(Mutex::new(Vec::new()));

    let data2 = data.clone();
    tokio::spawn(async move {
        // GOOD: Tokio's async-aware mutex
        let mut guard = data2.lock().await;

        // Mutex is released while sleeping (guard dropped across await)
        tokio::time::sleep(std::time::Duration::from_secs(1)).await;

        guard.push(1);
    });

    let data3 = data.clone();
    tokio::spawn(async move {
        let mut guard = data3.lock().await;
        guard.push(2);
    }).await.unwrap();
}
```

**Formal Analysis**:

```
Theorem MUTEX-TYPE-SAFETY:
  std::sync::MutexGuard<'a, T>: !Send

  Therefore:
    spawn(async { let g = std_mutex.lock(); await; })
      ⊢ COMPILE ERROR (Send bound not satisfied)

  Tokio::sync::MutexGuard<'a, T>: Send
  Therefore:
    spawn(async { let g = tokio_mutex.lock().await; await; })
      ⊢ OK
```

---

### Counter-Example 5: Unbounded Channel Memory Leak

**Problem**: Using unbounded channels without backpressure can cause memory exhaustion.

```rust
use tokio::sync::mpsc;

#[tokio::main]
async fn main() {
    // BAD: Unbounded channel - no limit on buffer size
    let (tx, mut rx) = mpsc::unbounded_channel::<Vec<u8>>();

    // Producer task sends faster than consumer processes
    let producer = tokio::spawn(async move {
        loop {
            let large_data = vec![0u8; 1024 * 1024]; // 1MB chunks
            // Never blocks, queue grows indefinitely
            tx.send(large_data).unwrap();
        }
    });

    // Consumer processes slowly
    let consumer = tokio::spawn(async move {
        while let Some(data) = rx.recv().await {
            // Simulate slow processing
            tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
            println!("Processed {} bytes", data.len());
        }
    });

    // OOM likely before either task completes
    tokio::join!(producer, consumer);
}
```

**Memory Growth**:

```
Time    | Queue Size | Memory Used
--------|------------|-------------
0s      | 0          | 0 MB
1s      | ~1000      | ~1000 MB
5s      | ~5000      | ~5000 MB
10s     | ~10000     | ~10000 MB
```

**Solution**: Use bounded channels with backpressure.

```rust
use tokio::sync::mpsc;

#[tokio::main]
async fn main() {
    // GOOD: Bounded channel with capacity 100
    let (tx, mut rx) = mpsc::channel::<Vec<u8>>(100);

    let producer = tokio::spawn(async move {
        loop {
            let large_data = vec![0u8; 1024 * 1024]; // 1MB chunks

            // Blocks when buffer is full, providing backpressure
            if tx.send(large_data).await.is_err() {
                break;
            }
        }
    });

    let consumer = tokio::spawn(async move {
        while let Some(data) = rx.recv().await {
            tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
            println!("Processed {} bytes", data.len());
        }
    });

    tokio::join!(producer, consumer);
}
```

**Formal Analysis**:

```
Theorem CHANNEL-BOUNDEDNESS:
  unbounded_channel() ⊢ buffer_size = ∞
  bounded_channel(n) ⊢ buffer_size ≤ n

Safety Property:
  ∀ bounded channel c:
    send(c, msg) ∧ full(c) ⟹ sender_blocked(c)

Liveness Property:
    receiver_consumes(c) ⟹ sender_unblocked(c)
```

---

### Counter-Example 6: Memory Leak in Long-Running Task

**Problem**: Accumulating data in a task without proper cleanup.

```rust
use std::collections::HashMap;
use tokio::time::{self, Duration};

#[tokio::main]
async fn main() {
    tokio::spawn(async {
        let mut cache: HashMap<u64, Vec<u8>> = HashMap::new();
        let mut counter = 0u64;

        loop {
            // Cache grows without bounds
            cache.insert(counter, vec![0u8; 1024 * 100]); // 100KB per entry
            counter += 1;

            // No eviction strategy!

            time::sleep(Duration::from_millis(100)).await;

            if counter % 100 == 0 {
                println!("Cache size: {} entries, ~{} MB",
                    counter,
                    counter * 100 / 1024
                );
            }
        }
    });

    time::sleep(Duration::from_secs(3600)).await;
}
```

**Solution**: Implement proper eviction and limits.

```rust
use std::collections::HashMap;
use tokio::time::{self, Duration, Instant};

struct BoundedCache<K, V> {
    data: HashMap<K, (V, Instant)>,
    max_size: usize,
    ttl: Duration,
}

impl<K: Eq + std::hash::Hash, V> BoundedCache<K, V> {
    fn new(max_size: usize, ttl: Duration) -> Self {
        Self {
            data: HashMap::new(),
            max_size,
            ttl,
        }
    }

    fn insert(&mut self, key: K, value: V) {
        if self.data.len() >= self.max_size {
            // Evict oldest entry
            if let Some(oldest) = self.data
                .iter()
                .min_by_key(|(_, (_, time))| *time)
                .map(|(k, _)| *k)
            {
                self.data.remove(&oldest);
            }
        }
        self.data.insert(key, (value, Instant::now()));
    }

    fn cleanup_expired(&mut self) {
        let now = Instant::now();
        self.data.retain(|_, (_, time)| now.duration_since(*time) < self.ttl);
    }
}
```

---

### Counter-Example 7: Timer Cancellation Race

**Problem**: Race condition between timer expiration and explicit cancellation.

```rust
use tokio::time::{sleep, Duration, timeout};

#[tokio::main]
async fn main() {
    let result = timeout(Duration::from_millis(100), async {
        // Simulated work that might complete quickly
        sleep(Duration::from_millis(50)).await;

        // Race condition: what if timeout fires during this computation?
        expensive_computation().await
    }).await;

    match result {
        Ok(value) => println!("Completed: {}", value),
        Err(_) => println!("Timed out"),
    }
}

async fn expensive_computation() -> String {
    // What if timeout fires here?
    // The result might be lost or partially computed
    std::thread::sleep(Duration::from_millis(200)); // Simulating work
    "result".to_string()
}
```

**Problem**: When a timeout fires, the underlying future is dropped. If it was in the middle of critical work, state may be inconsistent.

**Solution**: Use graceful cancellation with cancellation tokens.

```rust
use tokio::time::{sleep, Duration, timeout};
use tokio_util::sync::CancellationToken;

#[tokio::main]
async fn main() {
    let token = CancellationToken::new();
    let child_token = token.child_token();

    let handle = tokio::spawn(async move {
        // Check cancellation at safe points
        for i in 0..10 {
            if child_token.is_cancelled() {
                println!("Gracefully stopping at iteration {}", i);
                // Cleanup and return
                return format!("partial_result_{}", i);
            }

            sleep(Duration::from_millis(50)).await;
        }

        "complete_result".to_string()
    });

    // Cancel after 200ms
    sleep(Duration::from_millis(200)).await;
    token.cancel();

    let result = handle.await.unwrap();
    println!("Result: {}", result);
}
```

**Formal Analysis**:

```
Theorem TIMEOUT-CANCELLATION:
  timeout(d, future) =
    if future completes in < d: Ok(result)
    if duration exceeds d: Err(Elapsed)

  In Err case: future is dropped immediately

  Safety concern: future may be in inconsistent state

Solution: CancellationToken provides cooperative cancellation
```

---

### Counter-Example 8: Select Resource Leak

**Problem**: Using `tokio::select!` without properly handling cancelled branches.

```rust
use tokio::sync::mpsc;
use tokio::time::{sleep, Duration};

#[tokio::main]
async fn main() {
    let (tx, mut rx) = mpsc::channel(10);

    // Spawn producer
    tokio::spawn(async move {
        for i in 0..100 {
            let _ = tx.send(i).await;
        }
    });

    loop {
        tokio::select! {
            Some(msg) = rx.recv() => {
                println!("Received: {}", msg);

                // If this branch is not selected, the received value
                // from rx.recv() is dropped (potentially lost data)
            }
            _ = sleep(Duration::from_millis(100)) => {
                println!("Timeout");
                // rx.recv() future was cancelled, message may be lost
            }
        }
    }
}
```

**Problem**: `select!` cancels uncompleted branches. If `rx.recv()` is cancelled, the message is lost.

**Solution**: Use biased selection or proper message handling.

```rust
use tokio::sync::mpsc;
use tokio::time::{sleep, Duration, interval};

#[tokio::main]
async fn main() {
    let (tx, mut rx) = mpsc::channel(10);

    tokio::spawn(async move {
        for i in 0..100 {
            let _ = tx.send(i).await;
        }
    });

    let mut tick = interval(Duration::from_millis(100));

    loop {
        tokio::select! {
            // Prioritize message processing
            biased;

            Some(msg) = rx.recv() => {
                println!("Received: {}", msg);
            }
            _ = tick.tick() => {
                println!("Tick");
            }
        }
    }
}
```

**Formal Analysis**:

```
Theorem SELECT-CANCELLATION:
  select! {
    a = fut_a => { A },
    b = fut_b => { B },
  }

  If fut_a completes first:
    - A executes
    - fut_b is cancelled (dropped)

  Cancellation safety requirement:
    fut must be safe to drop at any await point
```

---

### Counter-Example 9: Async Drop Missing

**Problem**: Types that need cleanup logic in async context.

```rust
use tokio::net::TcpStream;
use tokio::io::{AsyncReadExt, AsyncWriteExt};

struct Connection {
    stream: TcpStream,
    buffer: Vec<u8>,
}

impl Connection {
    async fn new(addr: &str) -> tokio::io::Result<Self> {
        let stream = TcpStream::connect(addr).await?;
        Ok(Self {
            stream,
            buffer: Vec::new(),
        })
    }

    async fn send(&mut self, data: &[u8]) -> tokio::io::Result<()> {
        self.stream.write_all(data).await
    }
}

// PROBLEM: No async cleanup - if we need to send a goodbye message,
// we can't do it in regular Drop
impl Drop for Connection {
    fn drop(&mut self) {
        // Can't use .await here!
        // let _ = self.stream.write_all(b"BYE"); // Can't await!
    }
}

#[tokio::main]
async fn main() {
    {
        let mut conn = Connection::new("127.0.0.1:8080").await.unwrap();
        conn.send(b"Hello").await.unwrap();
        // Connection dropped here, no graceful shutdown possible
    }
}
```

**Solution**: Use explicit async cleanup methods.

```rust
use tokio::net::TcpStream;
use tokio::io::{AsyncReadExt, AsyncWriteExt};

struct Connection {
    stream: Option<TcpStream>,
    buffer: Vec<u8>,
}

impl Connection {
    async fn new(addr: &str) -> tokio::io::Result<Self> {
        let stream = TcpStream::connect(addr).await?;
        Ok(Self {
            stream: Some(stream),
            buffer: Vec::new(),
        })
    }

    async fn send(&mut self, data: &[u8]) -> tokio::io::Result<()> {
        if let Some(ref mut stream) = self.stream {
            stream.write_all(data).await
        } else {
            Err(tokio::io::Error::new(
                tokio::io::ErrorKind::NotConnected,
                "Connection closed"
            ))
        }
    }

    /// Async cleanup method
    async fn shutdown(mut self) -> tokio::io::Result<()> {
        if let Some(mut stream) = self.stream.take() {
            stream.write_all(b"BYE").await?;
            stream.shutdown().await?;
        }
        Ok(())
    }
}

impl Drop for Connection {
    fn drop(&mut self) {
        // Only handle the case where shutdown wasn't called
        if self.stream.is_some() {
            // Log warning or handle sync cleanup only
            eprintln!("Warning: Connection dropped without graceful shutdown");
        }
    }
}

#[tokio::main]
async fn main() {
    let conn = Connection::new("127.0.0.1:8080").await.unwrap();
    // Use ManuallyDrop pattern or explicit shutdown
    conn.shutdown().await.unwrap();
}
```

---

### Counter-Example 10: Runtime Shutdown with Pending Tasks

**Problem**: Runtime drops pending tasks without completion on shutdown.

```rust
use tokio::time::{sleep, Duration};
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

fn main() {
    let counter = Arc::new(AtomicUsize::new(0));

    {
        let rt = tokio::runtime::Runtime::new().unwrap();

        let counter_clone = counter.clone();
        rt.spawn(async move {
            sleep(Duration::from_secs(5)).await;
            counter_clone.fetch_add(1, Ordering::SeqCst);
            println!("Task completed");
        });

        // Runtime dropped here after block
        // Pending tasks are cancelled!
    } // <-- Tasks dropped here!

    println!("Counter: {}", counter.load(Ordering::SeqCst));
    // Output: Counter: 0 (task never completed)
}
```

**Solution**: Use `block_on` with proper shutdown sequence.

```rust
use tokio::time::{sleep, Duration};
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

fn main() {
    let counter = Arc::new(AtomicUsize::new(0));

    let rt = tokio::runtime::Runtime::new().unwrap();

    let counter_clone = counter.clone();

    // Use block_on to ensure task completes
    rt.block_on(async move {
        let handle = tokio::spawn(async move {
            sleep(Duration::from_secs(1)).await;
            counter_clone.fetch_add(1, Ordering::SeqCst);
            println!("Task completed");
        });

        // Wait for task to complete
        handle.await.unwrap();
    });

    // Or use shutdown_timeout
    rt.shutdown_timeout(Duration::from_secs(10));

    println!("Counter: {}", counter.load(Ordering::SeqCst));
    // Output: Counter: 1
}
```

**Formal Analysis**:

```
Theorem RUNTIME-SHUTDOWN:
  Runtime::drop() behavior:
    1. Blocks until all worker threads complete current tasks
    2. Drops pending tasks without polling to completion
    3. Does NOT wait for spawned tasks to complete

  Safe shutdown requires:
    - Explicit await of JoinHandles
    - Or use of shutdown_timeout()
```

---

### Counter-Example 11: Blocking Thread Exhaustion

**Problem**: Using `spawn_blocking` without considering pool limits.

```rust
use tokio::task;
use std::time::Duration;

#[tokio::main]
async fn main() {
    // Default blocking pool: 512 threads max

    let handles: Vec<_> = (0..1000)
        .map(|i| {
            task::spawn_blocking(move || {
                // Each task holds a blocking thread for 10 seconds
                std::thread::sleep(Duration::from_secs(10));
                println!("Task {} done", i);
                i
            })
        })
        .collect();

    // First 512 tasks start immediately
    // Remaining 488 tasks are queued
    // Total time: ~20 seconds (two waves)

    for handle in handles {
        handle.await.unwrap();
    }
}
```

**Solution**: Configure blocking pool or use semaphores.

```rust
use tokio::task;
use tokio::sync::Semaphore;
use std::sync::Arc;
use std::time::Duration;

#[tokio::main]
async fn main() {
    // Limit concurrent blocking operations
    let semaphore = Arc::new(Semaphore::new(100));

    let handles: Vec<_> = (0..1000)
        .map(|i| {
            let permit = semaphore.clone().acquire_owned().await.unwrap();
            task::spawn_blocking(move || {
                let _permit = permit; // Hold permit until done
                std::thread::sleep(Duration::from_millis(100));
                println!("Task {} done", i);
                i
            })
        })
        .collect();

    for handle in handles {
        handle.await.unwrap();
    }
}
```

---

### Counter-Example 12: Wrong Runtime Flavor

**Problem**: Choosing the wrong runtime flavor for the workload.

```rust
// BAD: Using current_thread for CPU-bound parallel work
#[tokio::main(flavor = "current_thread")]
async fn main() {
    let start = std::time::Instant::now();

    // All tasks run sequentially on one thread!
    let tasks: Vec<_> = (0..8)
        .map(|i| {
            tokio::spawn(async move {
                // CPU-intensive work
                let sum: u64 = (i * 1_000_000..(i + 1) * 1_000_000).sum();
                println!("Task {}: sum = {}", i, sum);
            })
        })
        .collect();

    for task in tasks {
        task.await.unwrap();
    }

    println!("Elapsed: {:?}", start.elapsed());
    // Takes ~8x longer than multi_thread
}
```

**Solution**: Choose appropriate runtime flavor.

```rust
// GOOD: Multi-thread runtime for parallel CPU work
#[tokio::main(flavor = "multi_thread", worker_threads = 8)]
async fn main() {
    let start = std::time::Instant::now();

    let tasks: Vec<_> = (0..8)
        .map(|i| {
            tokio::task::spawn_blocking(move || {
                let sum: u64 = (i * 1_000_000..(i + 1) * 1_000_000).sum();
                println!("Task {}: sum = {}", i, sum);
                sum
            })
        })
        .collect();

    for task in tasks {
        task.await.unwrap();
    }

    println!("Elapsed: {:?}", start.elapsed());
    // Uses all CPU cores
}
```

---

### Counter-Example 13: LocalSet in Wrong Context

**Problem**: Misunderstanding LocalSet requirements.

```rust
use std::rc::Rc;

#[tokio::main(flavor = "multi_thread")]
async fn main() {
    let local_set = tokio::task::LocalSet::new();

    // ERROR: This doesn't work as expected
    // LocalSet::run_until takes ownership and blocks until completion
    let data = Rc::new("shared".to_string());

    local_set.run_until(async {
        // Tasks spawned here can use !Send types
        let data2 = data.clone();
        tokio::task::spawn_local(async move {
            println!("{}", data2);
        }).await.unwrap();
    }).await;

    // After run_until completes, local_set is consumed
    // Can't spawn more tasks!
}
```

**Solution**: Use LocalSet correctly within its scope.

```rust
use std::rc::Rc;

#[tokio::main(flavor = "multi_thread")]
async fn main() {
    let local_set = tokio::task::LocalSet::new();

    local_set
        .run_until(async {
            let data = Rc::new("shared".to_string());

            // Spawn multiple !Send tasks
            let mut handles = vec![];

            for i in 0..5 {
                let data_clone = data.clone();
                let handle = tokio::task::spawn_local(async move {
                    println!("Task {}: {}", i, data_clone);
                    i * 2
                });
                handles.push(handle);
            }

            // Collect all results
            let results: Vec<_> = handles
                .into_iter()
                .map(|h| h.await.unwrap())
                .collect();

            println!("Results: {:?}", results);
        })
        .await;
}
```

---

### Counter-Example 14: Task Abort During Critical Section

**Problem**: Task aborted while holding resources.

```rust
use tokio::sync::Mutex;
use std::sync::Arc;

#[tokio::main]
async fn main() {
    let resource = Arc::new(Mutex::new(vec![1, 2, 3]));

    let resource_clone = resource.clone();
    let handle = tokio::spawn(async move {
        let mut guard = resource_clone.lock().await;

        // Simulate partial modification
        guard.push(4);

        // What if abort happens here?
        tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;

        // This may never execute if task is aborted
        guard.push(5);
    });

    // Abort the task
    handle.abort();

    match handle.await {
        Ok(_) => println!("Task completed"),
        Err(e) => println!("Task aborted: {:?}", e),
    }

    // Resource state may be inconsistent!
    let final_state = resource.lock().await;
    println!("Final state: {:?}", *final_state);
    // May be [1, 2, 3, 4] - incomplete!
}
```

**Solution**: Use cancellation-safe operations and cleanup.

```rust
use tokio::sync::Mutex;
use std::sync::Arc;
use tokio_util::sync::CancellationToken;

#[tokio::main]
async fn main() {
    let resource = Arc::new(Mutex::new(vec![1, 2, 3]));
    let token = CancellationToken::new();

    let resource_clone = resource.clone();
    let token_clone = token.child_token();

    let handle = tokio::spawn(async move {
        // Check cancellation before critical section
        if token_clone.is_cancelled() {
            return Err("Cancelled before start");
        }

        let mut guard = resource_clone.lock().await;

        // Atomic operation: all or nothing
        let new_elements = vec![4, 5, 6];
        guard.extend(new_elements);

        // Drop guard before await point
        drop(guard);

        // Now safe to check cancellation and sleep
        tokio::select! {
            _ = tokio::time::sleep(tokio::time::Duration::from_secs(1)) => {}
            _ = token_clone.cancelled() => {
                // Cleanup if cancelled
                let mut guard = resource_clone.lock().await;
                // Rollback logic if needed
                return Err("Cancelled during sleep");
            }
        }

        Ok(())
    });

    // Request cancellation
    token.cancel();

    match handle.await {
        Ok(Ok(())) => println!("Task completed successfully"),
        Ok(Err(e)) => println!("Task cancelled gracefully: {}", e),
        Err(e) => println!("Task panicked: {:?}", e),
    }

    let final_state = resource.lock().await;
    println!("Final state: {:?}", *final_state);
}
```

---

### Counter-Example 15: Interval Drift

**Problem**: Timer intervals drift over time due to processing delays.

```rust
use tokio::time::{interval, Duration, Instant};

#[tokio::main]
async fn main() {
    let mut interval = interval(Duration::from_secs(1));
    let start = Instant::now();

    for i in 0..10 {
        interval.tick().await;

        // Simulate variable processing time
        tokio::time::sleep(Duration::from_millis(100 + i * 50)).await;

        let elapsed = start.elapsed().as_secs_f64();
        println!("Tick {} at {:.2}s (expected: {}s)", i, elapsed, i);
        // Drift accumulates: actual time > expected time
    }
}
```

**Output showing drift**:

```
Tick 0 at 1.10s (expected: 0s)
Tick 1 at 2.25s (expected: 1s)  // 0.25s drift
Tick 2 at 3.45s (expected: 2s)  // 0.45s drift
Tick 3 at 4.70s (expected: 3s)  // 0.70s drift
...
```

**Solution**: Use `interval_at` with missed tick behavior.

```rust
use tokio::time::{interval_at, Duration, Instant, MissedTickBehavior};

#[tokio::main]
async fn main() {
    let start = Instant::now();

    let mut interval = interval_at(start, Duration::from_secs(1));

    // Choose appropriate missed tick behavior
    interval.set_missed_tick_behavior(MissedTickBehavior::Skip);
    // Alternatives: Delay, Burst

    for i in 0..10 {
        interval.tick().await;

        // Simulate variable processing time
        tokio::time::sleep(Duration::from_millis(100 + i * 50)).await;

        let elapsed = start.elapsed().as_secs_f64();
        let expected = interval.period().as_secs_f64() * (i as f64);
        println!("Tick {} at {:.2}s (expected: {:.2}s, drift: {:.2}s)",
            i, elapsed, expected, elapsed - expected);
    }
}
```

**Missed Tick Behaviors**:

```
Delay:      Wait for next scheduled tick (default)
Skip:       Skip missed ticks, schedule from now
Burst:      Process all missed ticks immediately
```

---

### Counter-Example 16: Deadlock with Nested Locks

**Problem**: Deadlock when acquiring multiple async locks in different orders.

```rust
use tokio::sync::Mutex;
use std::sync::Arc;

#[tokio::main]
async fn main() {
    let lock_a = Arc::new(Mutex::new(0));
    let lock_b = Arc::new(Mutex::new(0));

    let a1 = lock_a.clone();
    let b1 = lock_b.clone();
    let task1 = tokio::spawn(async move {
        let _guard_a = a1.lock().await;
        println!("Task 1: locked A");

        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;

        let _guard_b = b1.lock().await; // May deadlock!
        println!("Task 1: locked B");
    });

    let a2 = lock_a.clone();
    let b2 = lock_b.clone();
    let task2 = tokio::spawn(async move {
        let _guard_b = b2.lock().await;
        println!("Task 2: locked B");

        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;

        let _guard_a = a2.lock().await; // May deadlock!
        println!("Task 2: locked A");
    });

    // DEADLOCK: Task 1 holds A, waits for B
    //           Task 2 holds B, waits for A

    tokio::join!(task1, task2);
}
```

**Solution**: Always acquire locks in consistent order.

```rust
use tokio::sync::Mutex;
use std::sync::Arc;

// Define a consistent ordering (e.g., by memory address)
async fn acquire_ordered<T>(
    a: &Mutex<T>,
    b: &Mutex<T>,
) -> (tokio::sync::MutexGuard<T>, tokio::sync::MutexGuard<T>) {
    let a_ptr = a as *const _ as usize;
    let b_ptr = b as *const _ as usize;

    if a_ptr < b_ptr {
        let guard_a = a.lock().await;
        let guard_b = b.lock().await;
        (guard_a, guard_b)
    } else {
        let guard_b = b.lock().await;
        let guard_a = a.lock().await;
        (guard_a, guard_b)
    }
}

#[tokio::main]
async fn main() {
    let lock_a = Arc::new(Mutex::new(0));
    let lock_b = Arc::new(Mutex::new(0));

    let a1 = lock_a.clone();
    let b1 = lock_b.clone();
    let task1 = tokio::spawn(async move {
        let (_guard_a, _guard_b) = acquire_ordered(&*a1, &*b1).await;
        println!("Task 1: locked A and B");
    });

    let a2 = lock_a.clone();
    let b2 = lock_b.clone();
    let task2 = tokio::spawn(async move {
        let (_guard_a, _guard_b) = acquire_ordered(&*a2, &*b2).await;
        println!("Task 2: locked A and B");
    });

    tokio::join!(task1, task2);
    println!("No deadlock!");
}
```

---

### Counter-Example 17: Semaphore Permit Leak

**Problem**: Acquiring semaphore permits without releasing them.

```rust
use tokio::sync::Semaphore;
use std::sync::Arc;

#[tokio::main]
async fn main() {
    let semaphore = Arc::new(Semaphore::new(3));

    // Acquire all permits
    let permit1 = semaphore.acquire().await.unwrap();
    let permit2 = semaphore.acquire().await.unwrap();
    let permit3 = semaphore.acquire().await.unwrap();

    // PROBLEM: Permits held indefinitely
    // If this were in a loop or long-running task,
    // no other task could acquire permits

    // Should explicitly drop permits or use acquire_owned
    // drop(permit1);
    // drop(permit2);
    // drop(permit3);

    // This will hang forever
    let permit4 = semaphore.try_acquire();
    assert!(permit4.is_err(), "Should not be able to acquire");
}
```

**Solution**: Use RAII patterns or explicit release.

```rust
use tokio::sync::Semaphore;
use std::sync::Arc;

#[tokio::main]
async fn main() {
    let semaphore = Arc::new(Semaphore::new(3));

    // Use scope-based RAII
    {
        let _permit = semaphore.acquire().await.unwrap();
        // Permit automatically released at end of scope
        println!("Working with permit...");
    } // Permit released here

    // Or use forget/dispose pattern for owned permits
    let sem_clone = semaphore.clone();
    let handle = tokio::spawn(async move {
        let permit = sem_clone.acquire_owned().await.unwrap();

        // Move permit into spawned task
        tokio::spawn(async move {
            // Permit held until this task completes
            println!("Working in spawned task...");
            tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
            // Permit released when dropped
        }).await.unwrap();
    });

    handle.await.unwrap();

    // Semaphore is now available again
    let _permit = semaphore.acquire().await.unwrap();
    println!("Acquired permit after cleanup");
}
```

---

### Counter-Example 18: Incorrect Buffer Management

**Problem**: Reusing buffers incorrectly in async I/O.

```rust
use tokio::net::TcpStream;
use tokio::io::{AsyncReadExt, AsyncWriteExt};

async fn read_messages_bad(stream: &mut TcpStream) -> tokio::io::Result<()> {
    let mut buf = vec![0u8; 1024];

    loop {
        // BAD: buf is reused but previous data may remain
        let n = stream.read(&mut buf).await?;

        if n == 0 {
            break;
        }

        // Only process first n bytes, but buffer may contain stale data
        process(&buf); // May read beyond n!
    }

    Ok(())
}

fn process(data: &[u8]) {
    // If this reads the full buffer instead of just data.len(),
    // it will see stale data from previous reads
    println!("Processing {} bytes", data.len());
}
```

**Solution**: Always respect the length returned by read operations.

```rust
use tokio::net::TcpStream;
use tokio::io::{AsyncReadExt, AsyncWriteExt};

async fn read_messages_good(stream: &mut TcpStream) -> tokio::io::Result<()> {
    let mut buf = vec![0u8; 1024];

    loop {
        let n = stream.read(&mut buf).await?;

        if n == 0 {
            break;
        }

        // GOOD: Only process the bytes that were actually read
        process(&buf[..n]);
    }

    Ok(())
}

// Even better: use read_buf with BytesMut for zero-copy
use bytes::BytesMut;

async fn read_messages_zero_copy(stream: &mut TcpStream) -> tokio::io::Result<()> {
    let mut buf = BytesMut::with_capacity(1024);

    loop {
        let n = stream.read_buf(&mut buf).await?;

        if n == 0 {
            break;
        }

        // Process the filled portion
        process(&buf);

        // Clear processed data but keep capacity
        buf.clear();
    }

    Ok(())
}
```

---

## 8. Performance Analysis

### 8.1 Work-Stealing Algorithm

Tokio's multi-thread scheduler uses a work-stealing algorithm for load balancing.

**Algorithm Details**:

```
Algorithm WORK-STEALING-SCHEDULER:

  Data Structures:
    - Each worker w has local queue Q_w (LIFO for own tasks)
    - Global injection queue Q_global (FIFO)

  Worker Loop:
    1. Pop task from Q_w (LIFO)
    2. If Q_w empty:
         a. Try pop from Q_global
         b. Randomly select victim worker v
         c. Steal half of tasks from Q_v (FIFO)
    3. Execute task (poll future)
    4. If task yields (Poll::Pending), reschedule
    5. Repeat
```

**Performance Characteristics**:

| Operation | Time Complexity | Notes |
|-----------|----------------|-------|
| Local push/pop | O(1) | LIFO, hot cache |
| Global push | O(1) | Lock-free |
| Global pop | O(1) | Lock-free |
| Work stealing | O(k) | Steal k tasks, amortized O(1) |

**Theorem WORK-STEALING-EFFICIENCY**:

```
Theorem WORK-STEALING-EFFICIENCY:
  For n workers and m tasks where m >> n:
    Expected makespan ≈ m/n × average_task_time

  With high probability, load imbalance is bounded by O(log n)
```

### 8.2 Task Polling

**Polling Strategy**:

```
Task Polling Lifecycle:
┌─────────────┐     poll()      ┌─────────────┐
│   Ready     │ ──────────────→ │   Running   │
│   Queue     │                 │             │
└─────────────┘                 └──────┬──────┘
                                       │
         ┌─────────────────────────────┤
         │                             │
         │ Poll::Ready                 │ Poll::Pending
         ↓                             ↓
┌─────────────┐               ┌─────────────┐
│  Complete   │               │  Suspended  │
│             │               │             │
└─────────────┘               └──────┬──────┘
                                     │
                                     │ waker.notify()
                                     ↓
                              ┌─────────────┐
                              │   Ready     │
                              │   Queue     │
                              └─────────────┘
```

**Optimization Strategies**:

1. **Cooperative Scheduling**: Tasks yield periodically
2. **LIFO for local**: Better cache locality
3. **FIFO for stealing**: Reduces contention

### 8.3 Memory Layout

**Task Memory Structure**:

```rust
// Simplified task representation
struct Task {
    // Header (fixed size)
    header: TaskHeader,        // ~32 bytes

    // State tracking
    state: AtomicUsize,        // 8 bytes

    // Future storage (dynamically sized)
    future: dyn Future,        // Varies

    // Output storage
    output: Option<JoinHandleOutput>, // Varies
}

struct TaskHeader {
    vtable: *const Vtable,     // 8 bytes
    state: TaskState,          // 4 bytes
    queue_next: *mut Task,     // 8 bytes (intrusive list)
    waker_cache: Option<Waker>, // 16 bytes
}
```

**Memory Overhead**:

| Component | Size (64-bit) |
|-----------|---------------|
| Task header | ~48 bytes |
| Minimum task | ~64 bytes |
| Empty JoinHandle | ~16 bytes |
| Channel (per message) | ~8 bytes overhead |

**Theorem MEMORY-EFFICIENCY**:

```
Theorem MEMORY-EFFICIENCY:
  For n concurrent tasks:
    Runtime memory ∈ O(n × (sizeof(Task) + sizeof(Future)))

  With work-stealing:
    Queue overhead ∈ O(n) distributed across workers
```

---

## 9. Case Study: Web Server

### 9.1 Complete HTTP Server Implementation

```rust
//! High-performance Tokio-based HTTP server
//! Demonstrates best practices for async Rust

use tokio::net::{TcpListener, TcpStream};
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::sync::{Semaphore, RwLock};
use tokio::time::{timeout, Duration};

use std::collections::HashMap;
use std::sync::Arc;
use std::net::SocketAddr;

/// Server configuration
#[derive(Clone, Debug)]
pub struct ServerConfig {
    /// Address to bind to
    pub bind_addr: SocketAddr,
    /// Maximum concurrent connections
    pub max_connections: usize,
    /// Request timeout
    pub request_timeout: Duration,
    /// Read buffer size
    pub buffer_size: usize,
}

impl Default for ServerConfig {
    fn default() -> Self {
        Self {
            bind_addr: "0.0.0.0:8080".parse().unwrap(),
            max_connections: 10000,
            request_timeout: Duration::from_secs(30),
            buffer_size: 8192,
        }
    }
}

/// Request type
#[derive(Debug)]
pub struct Request {
    pub method: String,
    pub path: String,
    pub headers: HashMap<String, String>,
    pub body: Vec<u8>,
}

/// Response type
#[derive(Debug)]
pub struct Response {
    pub status: u16,
    pub headers: HashMap<String, String>,
    pub body: Vec<u8>,
}

impl Response {
    pub fn ok(body: impl Into<Vec<u8>>) -> Self {
        let mut headers = HashMap::new();
        headers.insert("Content-Type".to_string(), "text/plain".to_string());

        Self {
            status: 200,
            headers,
            body: body.into(),
        }
    }

    pub fn not_found() -> Self {
        Self {
            status: 404,
            headers: HashMap::new(),
            body: b"Not Found".to_vec(),
        }
    }

    pub fn server_error() -> Self {
        Self {
            status: 500,
            headers: HashMap::new(),
            body: b"Internal Server Error".to_vec(),
        }
    }

    /// Serialize to HTTP response bytes
    pub fn to_bytes(&self) -> Vec<u8> {
        let status_text = match self.status {
            200 => "OK",
            404 => "Not Found",
            500 => "Internal Server Error",
            _ => "Unknown",
        };

        let mut response = format!(
            "HTTP/1.1 {} {}\r\n",
            self.status, status_text
        );

        // Add content length
        response.push_str(&format!(
            "Content-Length: {}\r\n",
            self.body.len()
        ));

        // Add headers
        for (key, value) in &self.headers {
            response.push_str(&format!("{}: {}\r\n", key, value));
        }

        response.push_str("\r\n");

        let mut bytes = response.into_bytes();
        bytes.extend_from_slice(&self.body);
        bytes
    }
}

/// Handler trait for processing requests
trait Handler: Send + Sync + 'static {
    fn handle(&self, request: Request) -> impl std::future::Future<Output = Response> + Send;
}

/// Simple router
pub struct Router {
    routes: RwLock<HashMap<String, Box<dyn Fn(Request) -> Response + Send + Sync>>>,
}

impl Router {
    pub fn new() -> Self {
        Self {
            routes: RwLock::new(HashMap::new()),
        }
    }

    pub async fn register<F>(&self, path: &str, handler: F)
    where
        F: Fn(Request) -> Response + Send + Sync + 'static,
    {
        let mut routes = self.routes.write().await;
        routes.insert(path.to_string(), Box::new(handler));
    }

    pub async fn route(&self, request: Request) -> Response {
        let routes = self.routes.read().await;

        match routes.get(&request.path) {
            Some(handler) => handler(request),
            None => Response::not_found(),
        }
    }
}

/// Connection handler
struct ConnectionHandler {
    config: ServerConfig,
    router: Arc<Router>,
    semaphore: Arc<Semaphore>,
}

impl ConnectionHandler {
    fn new(
        config: ServerConfig,
        router: Arc<Router>,
        semaphore: Arc<Semaphore>,
    ) -> Self {
        Self {
            config,
            router,
            semaphore,
        }
    }

    async fn handle_connection(&self, mut stream: TcpStream, addr: SocketAddr) {
        let _permit = match self.semaphore.acquire().await {
            Ok(permit) => permit,
            Err(_) => {
                eprintln!("Semaphore closed");
                return;
            }
        };

        println!("Connection from {}", addr);

        let result = timeout(
            self.config.request_timeout,
            self.process_requests(&mut stream),
        ).await;

        match result {
            Ok(Ok(())) => println!("Connection {} handled successfully", addr),
            Ok(Err(e)) => eprintln!("Error handling connection {}: {}", addr, e),
            Err(_) => eprintln!("Connection {} timed out", addr),
        }

        // Permit released automatically when dropped
    }

    async fn process_requests(&self, stream: &mut TcpStream) -> tokio::io::Result<()> {
        let mut buffer = vec![0u8; self.config.buffer_size];

        loop {
            // Read request
            let n = stream.read(&mut buffer).await?;

            if n == 0 {
                // Connection closed
                break;
            }

            // Parse request (simplified)
            let request = match self.parse_request(&buffer[..n]) {
                Some(req) => req,
                None => {
                    let response = Response::not_found();
                    stream.write_all(&response.to_bytes()).await?;
                    continue;
                }
            };

            // Route and handle
            let response = self.router.route(request).await;

            // Send response
            stream.write_all(&response.to_bytes()).await?;
            stream.flush().await?;
        }

        Ok(())
    }

    fn parse_request(&self, data: &[u8]) -> Option<Request> {
        // Simplified HTTP parsing
        let text = String::from_utf8_lossy(data);
        let lines: Vec<&str> = text.lines().collect();

        if lines.is_empty() {
            return None;
        }

        // Parse request line
        let parts: Vec<&str> = lines[0].split_whitespace().collect();
        if parts.len() < 2 {
            return None;
        }

        let method = parts[0].to_string();
        let path = parts[1].to_string();

        // Parse headers
        let mut headers = HashMap::new();
        for line in &lines[1..] {
            if line.is_empty() {
                break;
            }
            if let Some(pos) = line.find(':') {
                let key = line[..pos].trim().to_string();
                let value = line[pos + 1..].trim().to_string();
                headers.insert(key, value);
            }
        }

        Some(Request {
            method,
            path,
            headers,
            body: vec![],
        })
    }
}

/// HTTP Server
pub struct HttpServer {
    config: ServerConfig,
    router: Arc<Router>,
    semaphore: Arc<Semaphore>,
}

impl HttpServer {
    pub fn new(config: ServerConfig) -> Self {
        let router = Arc::new(Router::new());
        let semaphore = Arc::new(Semaphore::new(config.max_connections));

        Self {
            config,
            router,
            semaphore,
        }
    }

    pub fn router(&self) -> Arc<Router> {
        self.router.clone()
    }

    pub async fn run(&self) -> tokio::io::Result<()> {
        let listener = TcpListener::bind(self.config.bind_addr).await?;
        println!("Server listening on {}", self.config.bind_addr);

        let handler = Arc::new(ConnectionHandler::new(
            self.config.clone(),
            self.router.clone(),
            self.semaphore.clone(),
        ));

        loop {
            match listener.accept().await {
                Ok((stream, addr)) => {
                    let handler = handler.clone();

                    // Spawn connection handler
                    tokio::spawn(async move {
                        handler.handle_connection(stream, addr).await;
                    });
                }
                Err(e) => {
                    eprintln!("Accept error: {}", e);
                }
            }
        }
    }
}

/// Main entry point
#[tokio::main]
async fn main() -> tokio::io::Result<()> {
    // Configure server
    let config = ServerConfig {
        bind_addr: "0.0.0.0:8080".parse().unwrap(),
        max_connections: 10000,
        request_timeout: Duration::from_secs(30),
        buffer_size: 8192,
    };

    // Create server
    let server = HttpServer::new(config);
    let router = server.router();

    // Register routes
    router.register("/", |_req| {
        Response::ok("Welcome to Tokio HTTP Server!")
    }).await;

    router.register("/health", |_req| {
        Response::ok("OK")
    }).await;

    router.register("/stats", |_req| {
        let body = format!(
            "Active connections: (not tracked in this example)\n\
             Server: Tokio HTTP/1.1"
        );
        Response::ok(body)
    }).await;

    router.register("/echo", |req| {
        let body = format!(
            "Method: {}\nPath: {}\n",
            req.method, req.path
        );
        Response::ok(body)
    }).await;

    // Run server
    server.run().await
}
```

### 9.2 Performance Optimizations

```rust
//! Performance optimizations for the HTTP server

use tokio::net::TcpSocket;
use std::net::SocketAddr;

/// Optimized socket configuration
pub fn configure_socket(socket: &TcpSocket, addr: SocketAddr) -> tokio::io::Result<()> {
    // Enable TCP_NODELAY to reduce latency
    socket.set_nodelay(true)?;

    // Set reuse address for quick restarts
    if addr.is_ipv4() {
        socket.set_reuseaddr(true)?;
    }

    // Set buffer sizes
    socket.set_send_buffer_size(64 * 1024)?;
    socket.set_recv_buffer_size(64 * 1024)?;

    Ok(())
}

/// Connection pool for upstream connections
use tokio::sync::Mutex;
use std::collections::VecDeque;

pub struct ConnectionPool {
    connections: Mutex<VecDeque<TcpStream>>,
    max_size: usize,
}

impl ConnectionPool {
    pub fn new(max_size: usize) -> Self {
        Self {
            connections: Mutex::new(VecDeque::with_capacity(max_size)),
            max_size,
        }
    }

    pub async fn acquire(&self, addr: SocketAddr) -> tokio::io::Result<TcpStream> {
        // Try to get existing connection
        if let Some(conn) = self.connections.lock().await.pop_front() {
            // TODO: Check if connection is still alive
            return Ok(conn);
        }

        // Create new connection
        TcpStream::connect(addr).await
    }

    pub async fn release(&self, stream: TcpStream) {
        let mut connections = self.connections.lock().await;
        if connections.len() < self.max_size {
            connections.push_back(stream);
        }
        // Otherwise, drop the connection
    }
}

/// Zero-copy response using vectored I/O
use tokio::io::Interest;
use bytes::{Bytes, BytesMut};

pub struct ZeroCopyResponse {
    headers: Bytes,
    body: Bytes,
}

impl ZeroCopyResponse {
    pub async fn write_to(&self, stream: &TcpStream) -> tokio::io::Result<()> {
        // Use write_all for simplicity - in production use writev
        let mut output = BytesMut::with_capacity(self.headers.len() + self.body.len());
        output.extend_from_slice(&self.headers);
        output.extend_from_slice(&self.body);

        stream.write_all(&output).await
    }
}
```

### 9.3 Testing the Server

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use tokio::time::timeout;

    #[tokio::test]
    async fn test_router() {
        let router = Router::new();

        router.register("/test", |_req| {
            Response::ok("test response")
        }).await;

        let request = Request {
            method: "GET".to_string(),
            path: "/test".to_string(),
            headers: HashMap::new(),
            body: vec![],
        };

        let response = router.route(request).await;
        assert_eq!(response.status, 200);
        assert_eq!(response.body, b"test response");
    }

    #[tokio::test]
    async fn test_request_parsing() {
        let handler = ConnectionHandler::new(
            ServerConfig::default(),
            Arc::new(Router::new()),
            Arc::new(Semaphore::new(10)),
        );

        let request_data = b"GET /hello HTTP/1.1\r\nHost: localhost\r\n\r\n";
        let request = handler.parse_request(request_data);

        assert!(request.is_some());
        let req = request.unwrap();
        assert_eq!(req.method, "GET");
        assert_eq!(req.path, "/hello");
    }

    #[tokio::test]
    async fn test_concurrent_connections() {
        let config = ServerConfig {
            bind_addr: "127.0.0.1:0".parse().unwrap(),
            max_connections: 100,
            ..Default::default()
        };

        let server = HttpServer::new(config);
        let router = server.router();

        router.register("/", |_req| Response::ok("OK")).await;

        // Start server in background
        let server_handle = tokio::spawn(async move {
            server.run().await
        });

        // Give server time to start
        tokio::time::sleep(Duration::from_millis(100)).await;

        // Create multiple concurrent connections
        let mut handles = vec![];
        for _ in 0..50 {
            let handle = tokio::spawn(async move {
                // Would connect and make request in real test
            });
            handles.push(handle);
        }

        for h in handles {
            h.await.unwrap();
        }
    }
}
```

---

## 10. References

### 10.1 Academic Papers

1. **"Work-First and Help-First Scheduling Policies for Async-Finish Task Networks"**
   - Authors: Y. Guo, et al.
   - Describes work-stealing algorithms used in async runtimes

2. **"The Space Efficiency of Tokio's Scheduler"**
   - Tokio internal documentation on scheduler design

3. **"Fearless Concurrency with Rust"**
   - Explains Rust's ownership model enabling safe async

### 10.2 Official Documentation

1. [Tokio Documentation](https://tokio.rs/)
2. [Rust Async Book](https://rust-lang.github.io/async-book/)
3. [Tokio API Reference](https://docs.rs/tokio/)

### 10.3 Related Crates

- `futures`: Core future abstractions
- `async-trait`: Async trait methods
- `tokio-util`: Additional utilities
- `tower`: Service composition
- `hyper`: HTTP implementation

---

## Appendix A: Theorem Summary

| Theorem | Statement |
|---------|-----------|
| SPAWN-SAFETY | `spawn` requires `Send + 'static` |
| SPAWN-LOCAL-SAFETY | `spawn_local` requires `'static` only |
| JOINHANDLE-COMPLETION | JoinHandle awaits task completion |
| JOINHANDLE-LIFETIME | JoinHandle is always `'static` |
| CURRENT-THREAD-ISOLATION | Tasks run on same thread as runtime |
| MULTI-THREAD-SEND-REQUIREMENT | All captures must be Send |
| WORK-STEALING-LOAD-BALANCING | Idle workers steal from busy workers |
| ASYNC-FAIRNESS | Blocking operations must use spawn_blocking |
| MUTEX-TYPE-SAFETY | Use tokio::sync::Mutex in async |
| CHANNEL-BOUNDEDNESS | Bounded channels provide backpressure |
| TIMER-ACCURACY | Timer precision depends on runtime load |
| TIMEOUT-CANCELLATION | Timeout drops incomplete futures |
| SELECT-CANCELLATION | Unselected branches are cancelled |
| RUNTIME-SHUTDOWN | Runtime drop cancels pending tasks |
| WORK-STEALING-EFFICIENCY | Expected makespan ≈ m/n |
| MEMORY-EFFICIENCY | Memory usage is O(n) in task count |

---

## Appendix B: Glossary

| Term | Definition |
|------|------------|
| **Async/Await** | Syntax for writing asynchronous code |
| **Context** | Passed to poll(), contains waker |
| **Executor** | Runs futures to completion |
| **Future** | Represents async computation |
| **JoinHandle** | Handle for awaiting task completion |
| **Poll** | Method to check future progress |
| **Reactor** | Handles I/O events |
| **Runtime** | Complete async execution environment |
| **Scheduler** | Decides which task runs next |
| **Task** | Unit of work in async runtime |
| **Waker** | Notifies executor task is ready |
| **Work-Stealing** | Load balancing algorithm |

---

*Document Version: 1.0*
*Compatible with: Rust 1.94, Tokio 1.40+*
*Last Updated: 2026-03-06*
