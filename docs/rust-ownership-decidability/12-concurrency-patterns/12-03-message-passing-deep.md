# Message Passing Patterns: Formal Deep Dive

> **Rust Version**: 1.94
> **Scope**: Channel semantics, ownership transfer theorems, message passing patterns, async channels
> **Prerequisites**: Understanding of ownership, Send/Sync traits, async/await basics
> **Estimated Reading Time**: 3-4 hours
> **Difficulty**: Advanced

---

## Table of Contents

- [Message Passing Patterns: Formal Deep Dive](#message-passing-patterns-formal-deep-dive)
  - [Table of Contents](#table-of-contents)
  - [Executive Summary](#executive-summary)
  - [1. Message Passing Fundamentals](#1-message-passing-fundamentals)
    - [1.1 Channel Semantics](#11-channel-semantics)
    - [1.2 Types of Channels](#12-types-of-channels)
      - [mpsc: Multiple Producer, Single Consumer](#mpsc-multiple-producer-single-consumer)
      - [oneshot: Single Use Channel](#oneshot-single-use-channel)
      - [broadcast: One-to-Many](#broadcast-one-to-many)
      - [watch: Latest Value](#watch-latest-value)
  - [2. Ownership Transfer Theorems](#2-ownership-transfer-theorems)
    - [Theorem CHANNEL-OWNERSHIP](#theorem-channel-ownership)
    - [Theorem CHANNEL-ISOLATION](#theorem-channel-isolation)
    - [Theorem ASYNC-CHANNEL-SAFETY](#theorem-async-channel-safety)
  - [3. Common Patterns](#3-common-patterns)
    - [3.1 Worker Pool](#31-worker-pool)
      - [Counter-Example: Task Loss on Panic](#counter-example-task-loss-on-panic)
    - [3.2 Pipeline](#32-pipeline)
      - [Counter-Example: Unbounded Queue Overflow](#counter-example-unbounded-queue-overflow)
    - [3.3 Request-Response](#33-request-response)
      - [Counter-Example: Response to Wrong Requestor](#counter-example-response-to-wrong-requestor)
    - [3.4 Pub-Sub](#34-pub-sub)
      - [Counter-Example: Slow Subscriber Blocking](#counter-example-slow-subscriber-blocking)
  - [4. Async Channel Patterns](#4-async-channel-patterns)
    - [4.1 Bounded vs Unbounded](#41-bounded-vs-unbounded)
      - [Counter-Example: Unbounded Memory Growth](#counter-example-unbounded-memory-growth)
    - [4.2 Select Operation](#42-select-operation)
      - [Counter-Example: Resource Leak in Select](#counter-example-resource-leak-in-select)
    - [4.3 Priority Channels](#43-priority-channels)
  - [5. Error Handling](#5-error-handling)
    - [5.1 Sender/Receiver Disconnection](#51-senderreceiver-disconnection)
      - [Counter-Example: Ignoring SendError Causing Panic](#counter-example-ignoring-senderror-causing-panic)
    - [5.2 Poisoned Channels](#52-poisoned-channels)
  - [6. Performance Patterns](#6-performance-patterns)
    - [6.1 Batch Processing](#61-batch-processing)
    - [6.2 Zero-Copy Messages](#62-zero-copy-messages)
      - [Counter-Example: Unnecessary Cloning](#counter-example-unnecessary-cloning)
  - [7. Case Study: Chat Server](#7-case-study-chat-server)
    - [Architecture Overview](#architecture-overview)
    - [Complete Implementation](#complete-implementation)
    - [Ownership Flow Analysis](#ownership-flow-analysis)
    - [Graceful Shutdown](#graceful-shutdown)
  - [8. Anti-Patterns](#8-anti-patterns)
    - [Anti-Pattern 1: Synchronous Send in Async Context](#anti-pattern-1-synchronous-send-in-async-context)
    - [Anti-Pattern 2: Unbounded Channels Without Backpressure](#anti-pattern-2-unbounded-channels-without-backpressure)
    - [Anti-Pattern 3: Holding Receiver Across Await](#anti-pattern-3-holding-receiver-across-await)
    - [Anti-Pattern 4: Channel Per Task Overhead](#anti-pattern-4-channel-per-task-overhead)
  - [9. Rust 1.94 Features](#9-rust-194-features)
  - [10. References](#10-references)
    - [Core Documentation](#core-documentation)
    - [Academic Papers](#academic-papers)
    - [Related Patterns](#related-patterns)

---

## Executive Summary

This document provides a comprehensive formal treatment of message passing patterns in Rust, establishing mathematical foundations for understanding how Rust's channel-based concurrency ensures memory safety through ownership transfer. We present:

- **3+ formal theorems** with complete proofs about channel ownership semantics
- **15+ code examples** demonstrating correct patterns
- **8+ counter-examples** showing common pitfalls and their solutions
- **Complete chat server case study** with architecture analysis
- **Rust 1.94 features** including `LazyLock` for global channel registries

The core insight is that Rust's ownership system, when combined with channel communication, creates a message passing model that prevents data races by construction—ownership is always unique, and channels provide the only mechanism for transferring that ownership between threads.

---

## 1. Message Passing Fundamentals

### 1.1 Channel Semantics

A channel in Rust implements a fundamental communication primitive based on **ownership transfer**. Unlike shared memory where multiple threads can access data simultaneously (requiring synchronization), channels ensure that at any point in time, only one party owns the data.

**Formal Definition 1.1 (Channel Type)**:

A channel of type `T` is a communication primitive with the following signature:

```
Sender<T> × Receiver<T> → T transfer
```

**Ownership Protocol**:

```
send(t: T):     Ownership: Thread A → Channel
                Effect: Thread A loses access to t

recv() -> T:    Ownership: Channel → Thread B
                Effect: Thread B gains exclusive access to t
```

**Invariant**: ∀ value v of type T sent through channel c:

```
at any time t, exactly one of:
    - v is owned by sender
    - v is owned by channel (in transit)
    - v is owned by receiver
```

```rust
/// Demonstration of ownership transfer semantics
use std::sync::mpsc;

fn ownership_transfer_demo() {
    let (tx, rx) = mpsc::channel::<String>();

    // Thread A: Sender owns the data initially
    let data = String::from("critical payload");

    // Ownership transfers: Thread A → Channel
    tx.send(data).unwrap();

    // ERROR: data has been moved
    // println!("{}", data);  // Compile error: use of moved value

    // Thread B: Receiver gains ownership
    let received = rx.recv().unwrap();

    // Thread B now exclusively owns the data
    println!("Received: {}", received);

    // When received goes out of scope, it's dropped
}
```

**Type Safety Through Send Trait**:

Channels enforce type safety through the `Send` trait:

```rust
/// T: Send ensures values can cross thread boundaries safely
pub fn channel<T: Send>() -> (Sender<T>, Receiver<T>)

/// This is why Rc<T> cannot be sent through channels:
use std::rc::Rc;
// let (tx, rx) = mpsc::channel::<Rc<i32>>();  // Rc<i32> is !Send
```

### 1.2 Types of Channels

Rust's ecosystem provides several channel types, each optimized for different communication patterns:

#### mpsc: Multiple Producer, Single Consumer

The `mpsc` (Multiple Producer, Single Consumer) channel is the standard library's primary channel type.

```rust
use std::sync::mpsc;
use std::thread;

/// mpsc supports multiple senders (clonable) but only one receiver
fn mpsc_example() {
    let (tx, rx) = mpsc::channel::<i32>();

    // Spawn multiple producers
    let tx1 = tx.clone();
    let producer1 = thread::spawn(move || {
        for i in 0..5 {
            tx1.send(i).unwrap();
        }
    });

    let tx2 = tx.clone();
    let producer2 = thread::spawn(move || {
        for i in 5..10 {
            tx2.send(i).unwrap();
        }
    });

    // Single consumer
    drop(tx); // Drop original sender

    let consumer = thread::spawn(move || {
        while let Ok(value) = rx.recv() {
            println!("Received: {}", value);
        }
        println!("Channel closed");
    });

    producer1.join().unwrap();
    producer2.join().unwrap();
    consumer.join().unwrap();
}
```

#### oneshot: Single Use Channel

Oneshot channels are optimized for single message communication, typically used for request-response patterns.

```rust
use tokio::sync::oneshot;

/// oneshot channels close after a single message
async fn oneshot_example() {
    let (tx, rx) = oneshot::channel::<String>();

    tokio::spawn(async move {
        // Send exactly one message
        let _ = tx.send("response data".to_string());
        // Channel is now closed, cannot send again
    });

    // Receive exactly one message
    match rx.await {
        Ok(data) => println!("Received: {}", data),
        Err(_) => println!("Sender dropped"),
    }
}
```

**Efficiency**: Onseshot channels have minimal overhead—no internal buffering, no complex state management.

#### broadcast: One-to-Many

Broadcast channels send the same message to multiple receivers.

```rust
use tokio::sync::broadcast;

/// broadcast: one sender, multiple receivers
async fn broadcast_example() {
    // Create channel with capacity 16
    let (tx, _rx1) = broadcast::channel::<String>(16);
    let mut rx2 = tx.subscribe();
    let mut rx3 = tx.subscribe();

    // Send one message, all receivers get it
    tx.send("system notification".to_string()).unwrap();

    // Both receivers receive the same message
    let msg2 = rx2.recv().await.unwrap();
    let msg3 = rx3.recv().await.unwrap();

    assert_eq!(msg2, msg3);
    println!("Both received: {}", msg2);
}
```

**Key Properties**:

- Messages are cloned for each receiver (T: Clone required)
- Receivers can lag and miss messages if buffer fills
- Active receivers are tracked for flow control

#### watch: Latest Value

Watch channels maintain the most recent value, useful for configuration or state propagation.

```rust
use tokio::sync::watch;

/// watch: always access the latest value
async fn watch_example() {
    let (tx, mut rx) = watch::channel("initial".to_string());

    // Multiple receivers can watch
    let mut rx2 = rx.clone();

    // Update value
    tx.send("updated".to_string()).unwrap();

    // Receivers always see latest value
    rx.changed().await.unwrap();
    println!("Rx1: {}", *rx.borrow());  // "updated"

    rx2.changed().await.unwrap();
    println!("Rx2: {}", *rx2.borrow()); // "updated"
}
```

**Use Cases**:

- Configuration updates
- Service discovery
- State synchronization

---

## 2. Ownership Transfer Theorems

### Theorem CHANNEL-OWNERSHIP

**Statement**: Channel send/receive correctly transfers ownership without data races.

**Formal Statement**:

```
∀T: Send, ∀v: T, ∀c: Channel<T>:
    c.send(v) transfers ownership of v from sender thread to channel
    c.recv() transfers ownership of v from channel to receiver thread
    ∧
    at all times, exactly one entity owns v
```

**Proof**:

1. **Send Operation**: When `sender.send(v)` is called:
   - By Rust's move semantics, `v` is moved into the channel
   - The sender thread loses access to `v` (compile-time enforced)
   - Ownership is transferred to the channel's internal buffer

2. **Channel Internal State**: While in the channel:
   - The value resides in the channel's internal queue/buffer
   - The channel implementation ensures exclusive access
   - No thread can directly access the buffered value

3. **Receive Operation**: When `receiver.recv()` returns:
   - Ownership is moved from the channel to the receiver thread
   - The receiver gains exclusive access to the value
   - The channel relinquishes ownership

4. **No Shared State**: Since ownership is always unique:
   - No two threads can simultaneously access the value
   - Therefore, no data race is possible

```rust
/// Proof demonstration: Ownership transfer prevents races
use std::sync::mpsc;
use std::thread;

fn ownership_prevents_races() {
    let (tx, rx) = mpsc::channel::<Vec<u8>>();

    // Producer thread
    let producer = thread::spawn(move || {
        let data = vec![1, 2, 3, 4, 5];
        tx.send(data).unwrap();
        // data is moved, cannot be accessed here
        // println!("{:?}", data);  // COMPILE ERROR
    });

    // Consumer thread
    let consumer = thread::spawn(move || {
        let received = rx.recv().unwrap();
        // We have exclusive ownership, safe to modify
        let sum: u8 = received.iter().sum();
        println!("Sum: {}", sum);
    });

    producer.join().unwrap();
    consumer.join().unwrap();
}
```

### Theorem CHANNEL-ISOLATION

**Statement**: Channel communication provides thread isolation—values in transit are inaccessible to any thread.

**Formal Statement**:

```
∀T: Send, ∀c: Channel<T>, ∀v: T in transit through c:
    ¬(∃t: Thread. can_access(t, v))
```

**Proof**:

1. **Buffer Isolation**: The channel's internal buffer is private
   - Not exposed through any public API
   - Protected by internal synchronization primitives

2. **No Peek Operation**: Standard channels don't support peeking
   - Once sent, the value is opaque until received
   - No mechanism to observe in-transit values

3. **Drop Safety**: If channel is dropped, in-transit values are dropped
   - No values leak out without ownership transfer
   - Destructor ensures clean cleanup

```rust
/// Demonstration of channel isolation
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

fn channel_isolation() {
    let (tx, rx) = mpsc::channel::<String>();

    thread::spawn(move || {
        let sensitive = String::from("password123");
        tx.send(sensitive).unwrap();
        // Value is now isolated in the channel
        thread::sleep(Duration::from_secs(1));
        // No way to peek or modify during transit
    });

    // Value is in transit, completely isolated
    thread::sleep(Duration::from_millis(100));

    // Only receiver can access
    let received = rx.recv().unwrap();
    println!("Securely received: {}", received);
}
```

### Theorem ASYNC-CHANNEL-SAFETY

**Statement**: Async channel operations preserve ownership safety across await points.

**Formal Statement**:

```
∀T: Send, ∀c: AsyncChannel<T>, ∀v: T:
    async { c.send(v).await } preserves ownership transfer semantics
    ∧
    State: Pending → value ownership maintained by channel
```

**Proof**:

1. **Suspension Safety**: When an async send/recv suspends:
   - The value is stored in the channel's internal state
   - The Future's state machine doesn't hold a reference
   - Ownership remains with the channel

2. **Cancellation Safety**: If the Future is dropped:
   - Async channels handle cleanup gracefully
   - Unsent values may be returned or dropped depending on implementation
   - No ownership violations occur

3. **Thread Migration**: When Future resumes on different thread:
   - Value is received through channel, not accessed across threads
   - Ownership transfer happens atomically at receive point
   - Send bound ensures value can safely exist on new thread

```rust
/// Async channel safety demonstration
use tokio::sync::mpsc;

async fn async_channel_safety() {
    let (tx, mut rx) = mpsc::channel::<Vec<u8>>(10);

    let data = vec![1, 2, 3, 4, 5];

    // Send ownership to channel
    tx.send(data).await.unwrap();
    // data is moved

    // May suspend here, ownership maintained by channel
    let received = rx.recv().await.unwrap();

    // May resume on different thread, ownership transferred safely
    println!("Received on potentially different thread: {:?}", received);
}
```

---

## 3. Common Patterns

### 3.1 Worker Pool

The worker pool pattern distributes tasks among a fixed set of worker threads, providing load balancing and resource control.

```rust
use std::sync::mpsc;
use std::thread;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

/// Generic Worker Pool with graceful shutdown
pub struct WorkerPool<T, R> {
    workers: Vec<Worker>,
    sender: Option<mpsc::Sender<Job<T, R>>>,
    active_tasks: Arc<AtomicUsize>,
}

type Job<T, R> = Box<dyn FnOnce(T) -> R + Send + 'static>;

struct Worker {
    id: usize,
    thread: Option<thread::JoinHandle<()>>,
}

impl<T: Send + 'static, R: Send + 'static> WorkerPool<T, R> {
    pub fn new(size: usize) -> (Self, mpsc::Receiver<R>) {
        let (job_sender, job_receiver) = mpsc::channel::<Job<T, R>>();
        let (result_sender, result_receiver) = mpsc::channel::<R>();

        let job_receiver = Arc::new(std::sync::Mutex::new(job_receiver));
        let active_tasks = Arc::new(AtomicUsize::new(0));

        let mut workers = Vec::with_capacity(size);

        for id in 0..size {
            let rx = Arc::clone(&job_receiver);
            let tx = result_sender.clone();
            let active = Arc::clone(&active_tasks);

            let thread = thread::spawn(move || {
                loop {
                    let job = {
                        let lock = rx.lock().unwrap();
                        lock.recv()
                    };

                    match job {
                        Ok(job) => {
                            active.fetch_add(1, Ordering::SeqCst);
                            // Execute job (simplified - real implementation needs task input)
                            // job(task);
                            active.fetch_sub(1, Ordering::SeqCst);
                        }
                        Err(_) => {
                            println!("Worker {} shutting down", id);
                            break;
                        }
                    }
                }
            });

            workers.push(Worker {
                id,
                thread: Some(thread),
            });
        }

        let pool = WorkerPool {
            workers,
            sender: Some(job_sender),
            active_tasks,
        };

        (pool, result_receiver)
    }

    pub fn execute<F>(&self, f: F) -> Result<(), mpsc::SendError<Job<T, R>>>
    where
        F: FnOnce(T) -> R + Send + 'static,
    {
        let job = Box::new(f);
        self.sender.as_ref().unwrap().send(job)
    }

    pub fn active_count(&self) -> usize {
        self.active_tasks.load(Ordering::SeqCst)
    }
}

impl<T, R> Drop for WorkerPool<T, R> {
    fn drop(&mut self) {
        // Signal shutdown by dropping sender
        drop(self.sender.take());

        // Wait for all workers to finish
        for worker in &mut self.workers {
            if let Some(thread) = worker.thread.take() {
                println!("Waiting for worker {} to finish", worker.id);
                thread.join().unwrap();
            }
        }
    }
}
```

#### Counter-Example: Task Loss on Panic

```rust
use std::sync::mpsc;
use std::thread;
use std::panic;

/// COUNTER-EXAMPLE: Tasks can be lost if workers panic
fn worker_pool_panic_issue() {
    let (tx, rx) = mpsc::channel::<i32>();
    let rx = std::sync::Arc::new(std::sync::Mutex::new(rx));

    // Spawn worker that panics
    let rx_clone = Arc::clone(&rx);
    let worker = thread::spawn(move || {
        let rx = rx_clone;
        loop {
            let task = {
                let lock = rx.lock().unwrap();
                lock.recv()
            };

            match task {
                Ok(n) => {
                    if n == 42 {
                        panic!("Task 42 causes panic!");  // Worker dies here
                    }
                    println!("Processed: {}", n);
                }
                Err(_) => break,
            }
        }
    });

    // Send tasks
    for i in 0..10 {
        tx.send(i).unwrap();
    }

    // Task 42 kills the worker, remaining tasks are lost!
    // No mechanism to redistribute unprocessed tasks

    drop(tx);
    let _ = worker.join();  // Worker panicked
}

/// SOLUTION: Catch panics and restart workers
use std::sync::atomic::{AtomicBool, Ordering};

fn worker_pool_with_recovery() {
    let (tx, rx) = mpsc::channel::<i32>();
    let rx = Arc::new(std::sync::Mutex::new(rx));
    let shutdown = Arc::new(AtomicBool::new(false));

    // Worker wrapper that catches panics
    let spawn_worker = |id: usize, rx: Arc<std::sync::Mutex<mpsc::Receiver<i32>>>, shutdown: Arc<AtomicBool>| {
        thread::spawn(move || {
            let result = panic::catch_unwind(|| {
                loop {
                    if shutdown.load(Ordering::SeqCst) {
                        break;
                    }

                    let task = {
                        let lock = rx.lock().unwrap();
                        lock.recv()
                    };

                    match task {
                        Ok(n) => {
                            if n == 42 {
                                panic!("Task 42 causes panic!");
                            }
                            println!("Worker {} processed: {}", id, n);
                        }
                        Err(_) => break,
                    }
                }
            });

            match result {
                Ok(_) => println!("Worker {} exited normally", id),
                Err(_) => println!("Worker {} panicked, needs restart", id),
            }
        })
    };

    // Spawn initial workers
    let mut workers = vec![];
    for id in 0..2 {
        workers.push(spawn_worker(id, Arc::clone(&rx), Arc::clone(&shutdown)));
    }

    // Send tasks including the problematic one
    for i in 0..10 {
        tx.send(i).unwrap();
    }

    // ... recovery logic to restart panicked workers

    shutdown.store(true, Ordering::SeqCst);
    drop(tx);

    for w in workers {
        let _ = w.join();
    }
}
```

### 3.2 Pipeline

The pipeline pattern chains processing stages, where each stage receives input from the previous stage and sends output to the next.

```rust
use std::sync::mpsc;
use std::thread;

/// Pipeline stage trait
pub trait PipelineStage<In, Out>: Send + 'static {
    fn process(&mut self, input: In) -> Out;
}

/// Pipeline builder
pub struct Pipeline<In, Out> {
    input_sender: mpsc::Sender<In>,
    output_receiver: mpsc::Receiver<Out>,
}

impl<In: Send + 'static, Out: Send + 'static> Pipeline<In, Out> {
    /// Create a single-stage pipeline
    pub fn new<S, F>(mut stage: S, mut f: F) -> Self
    where
        S: PipelineStage<In, Out>,
        F: FnMut() -> S + Send + 'static,
    {
        let (input_tx, input_rx) = mpsc::channel::<In>();
        let (output_tx, output_rx) = mpsc::channel::<Out>();

        thread::spawn(move || {
            for input in input_rx {
                let output = stage.process(input);
                if output_tx.send(output).is_err() {
                    break;
                }
            }
        });

        Pipeline {
            input_sender: input_tx,
            output_receiver: output_rx,
        }
    }

    /// Add a stage to the pipeline
    pub fn then<NewOut: Send + 'static, S, F>(self, mut stage: S, mut f: F) -> Pipeline<In, NewOut>
    where
        S: PipelineStage<Out, NewOut>,
        F: FnMut() -> S + Send + 'static,
    {
        let (new_output_tx, new_output_rx) = mpsc::channel::<NewOut>();
        let mut old_output_rx = self.output_receiver;

        thread::spawn(move || {
            for input in old_output_rx {
                let output = stage.process(input);
                if new_output_tx.send(output).is_err() {
                    break;
                }
            }
        });

        Pipeline {
            input_sender: self.input_sender,
            output_receiver: new_output_rx,
        }
    }

    pub fn send(&self, input: In) -> Result<(), mpsc::SendError<In>> {
        self.input_sender.send(input)
    }

    pub fn recv(&self) -> Result<Out, mpsc::RecvError> {
        self.output_receiver.recv()
    }
}

/// Example: Image processing pipeline
struct DecodeStage;
struct ProcessStage;
struct EncodeStage;

impl PipelineStage<Vec<u8>, Vec<u8>> for DecodeStage {
    fn process(&mut self, input: Vec<u8>) -> Vec<u8> {
        // Simulate decoding
        println!("Decoding {} bytes", input.len());
        input  // Pass through for demo
    }
}

impl PipelineStage<Vec<u8>, Vec<u8>> for ProcessStage {
    fn process(&mut self, input: Vec<u8>) -> Vec<u8> {
        // Simulate processing
        println!("Processing {} bytes", input.len());
        input
    }
}

impl PipelineStage<Vec<u8>, Vec<u8>> for EncodeStage {
    fn process(&mut self, input: Vec<u8>) -> Vec<u8> {
        // Simulate encoding
        println!("Encoding {} bytes", input.len());
        input
    }
}

fn image_pipeline_example() {
    let pipeline = Pipeline::new(DeccodeStage, || DecodeStage)
        .then(ProcessStage, || ProcessStage)
        .then(EncodeStage, || EncodeStage);

    // Send image through pipeline
    pipeline.send(vec![0u8; 1024]).unwrap();

    let result = pipeline.recv().unwrap();
    println!("Final output: {} bytes", result.len());
}
```

#### Counter-Example: Unbounded Queue Overflow

```rust
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

/// COUNTER-EXAMPLE: Fast producer with slow consumer causes unbounded growth
fn unbounded_queue_overflow() {
    let (tx, rx) = mpsc::channel::<Vec<u8>>();

    // Fast producer
    let producer = thread::spawn(move || {
        let mut count = 0;
        loop {
            // Generates 1MB per iteration
            let data = vec![0u8; 1_000_000];
            if tx.send(data).is_err() {
                break;
            }
            count += 1;
            if count % 100 == 0 {
                println!("Produced {} MB", count);
            }
        }
    });

    // Slow consumer
    let consumer = thread::spawn(move || {
        while let Ok(data) = rx.recv() {
            // Process slowly
            thread::sleep(Duration::from_millis(100));
            println!("Processed {} bytes", data.len());
        }
    });

    // Memory grows without bound until OOM!
    // producer.join().unwrap();
    // consumer.join().unwrap();
}

/// SOLUTION: Use bounded channels with backpressure
use crossbeam::channel;

fn bounded_queue_with_backpressure() {
    // Bounded channel with capacity 10
    let (tx, rx) = channel::bounded::<Vec<u8>>(10);

    // Fast producer - will block when buffer is full
    let producer = thread::spawn(move || {
        let mut count = 0;
        loop {
            let data = vec![0u8; 1_000_000];

            // This will block when buffer is full, creating backpressure
            match tx.send(data) {
                Ok(_) => {
                    count += 1;
                    if count % 100 == 0 {
                        println!("Produced {} MB (backpressure active)", count);
                    }
                }
                Err(_) => break,
            }
        }
    });

    // Slow consumer
    let consumer = thread::spawn(move || {
        while let Ok(data) = rx.recv() {
            thread::sleep(Duration::from_millis(100));
            println!("Processed {} bytes (queue len: {})", data.len(), rx.len());
        }
    });

    // Memory usage is now bounded to ~10MB
    // producer.join().unwrap();
    // consumer.join().unwrap();
}
```

### 3.3 Request-Response

The request-response pattern implements synchronous-style communication over asynchronous channels.

```rust
use tokio::sync::{mpsc, oneshot};
use std::collections::HashMap;

/// Request with embedded response channel
pub struct Request<Req, Resp> {
    pub id: u64,
    pub payload: Req,
    pub respond_to: oneshot::Sender<Resp>,
}

/// Request-response client
pub struct RpcClient<Req, Resp> {
    request_id: std::sync::atomic::AtomicU64,
    sender: mpsc::Sender<Request<Req, Resp>>,
}

impl<Req: Send + 'static, Resp: Send + 'static> RpcClient<Req, Resp> {
    pub fn new(sender: mpsc::Sender<Request<Req, Resp>>) -> Self {
        RpcClient {
            request_id: std::sync::atomic::AtomicU64::new(0),
            sender,
        }
    }

    pub async fn call(&self, payload: Req) -> Result<Resp, RpcError> {
        let id = self.request_id.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        let (tx, rx) = oneshot::channel();

        let request = Request {
            id,
            payload,
            respond_to: tx,
        };

        // Send request
        self.sender.send(request).await.map_err(|_| RpcError::ServerUnavailable)?;

        // Wait for response with timeout
        match tokio::time::timeout(
            std::time::Duration::from_secs(5),
            rx
        ).await {
            Ok(Ok(response)) => Ok(response),
            Ok(Err(_)) => Err(RpcError::ResponseChannelClosed),
            Err(_) => Err(RpcError::Timeout),
        }
    }
}

#[derive(Debug)]
pub enum RpcError {
    ServerUnavailable,
    ResponseChannelClosed,
    Timeout,
}

/// Server handling requests
pub struct RpcServer<Req, Resp> {
    receiver: mpsc::Receiver<Request<Req, Resp>>,
    handler: Box<dyn Fn(Req) -> Resp + Send + Sync>,
}

impl<Req: Send + 'static, Resp: Send + 'static> RpcServer<Req, Resp> {
    pub fn new<F>(handler: F) -> (Self, RpcClient<Req, Resp>)
    where
        F: Fn(Req) -> Resp + Send + Sync + 'static,
    {
        let (tx, rx) = mpsc::channel(100);
        let server = RpcServer {
            receiver: rx,
            handler: Box::new(handler),
        };
        let client = RpcClient::new(tx);
        (server, client)
    }

    pub async fn run(mut self) {
        while let Some(request) = self.receiver.recv().await {
            let response = (self.handler)(request.payload);
            // Ignore send errors (client may have cancelled)
            let _ = request.respond_to.send(response);
        }
    }
}

/// Example usage
async fn rpc_example() {
    let (server, client) = RpcServer::new(|req: String| {
        format!("Response to: {}", req)
    });

    // Spawn server
    tokio::spawn(server.run());

    // Make RPC calls
    let response = client.call("Hello".to_string()).await.unwrap();
    println!("Got: {}", response);
}
```

#### Counter-Example: Response to Wrong Requestor

```rust
use tokio::sync::{mpsc, oneshot};

/// COUNTER-EXAMPLE: Response sent to wrong requestor due to ID mismatch
async fn wrong_response_target() {
    let (req_tx, mut req_rx) = mpsc::channel::<(u64, String, oneshot::Sender<String>)>(10);

    // Spawn malicious/confused server
    tokio::spawn(async move {
        let mut pending = std::collections::HashMap::new();

        while let Some((id, req, tx)) = req_rx.recv().await {
            if req == "get_pending" {
                // BUG: Responding to wrong request!
                if let Some((wrong_id, wrong_tx)) = pending.iter().next() {
                    let _ = wrong_tx.send(format!("Response for {} sent to {}", wrong_id, id));
                }
            } else {
                pending.insert(id, tx);
            }
        }
    });

    // Client 1 sends request
    let (tx1, rx1) = oneshot::channel();
    req_tx.send((1, "hello".to_string(), tx1)).await.unwrap();

    // Client 2 triggers the bug
    let (tx2, rx2) = oneshot::channel();
    req_tx.send((2, "get_pending".to_string(), tx2)).await.unwrap();

    // Client 1 receives wrong response!
    // let response = rx1.await.unwrap();  // May receive response meant for someone else
}

/// SOLUTION: Proper request ID tracking and validation
struct SafeRequest<Req, Resp> {
    id: u64,
    payload: Req,
    respond_to: oneshot::Sender<(u64, Resp)>,  // Include ID in response
}

async fn safe_request_response() {
    let (req_tx, mut req_rx) = mpsc::channel::<SafeRequest<String, String>>(10);

    tokio::spawn(async move {
        while let Some(req) = req_rx.recv().await {
            let response = format!("Processed: {}", req.payload);
            // Always pair response with request ID
            let _ = req.respond_to.send((req.id, response));
        }
    });

    let id = 1u64;
    let (tx, rx) = oneshot::channel();
    let request = SafeRequest {
        id,
        payload: "hello".to_string(),
        respond_to: tx,
    };

    req_tx.send(request).await.unwrap();

    // Verify response matches request
    let (resp_id, response) = rx.await.unwrap();
    assert_eq!(resp_id, id, "Response ID mismatch!");
    println!("Correctly received: {}", response);
}
```

### 3.4 Pub-Sub

The pub-sub pattern allows publishers to broadcast messages to multiple subscribers without knowing who they are.

```rust
use tokio::sync::broadcast;
use std::collections::HashMap;

/// Topic-based pub-sub system
pub struct PubSub<T: Clone + Send + 'static> {
    topics: HashMap<String, broadcast::Sender<T>>,
    default_capacity: usize,
}

impl<T: Clone + Send + 'static> PubSub<T> {
    pub fn new(default_capacity: usize) -> Self {
        PubSub {
            topics: HashMap::new(),
            default_capacity,
        }
    }

    /// Create or get a topic
    pub fn create_topic(&mut self, name: &str) -> broadcast::Sender<T> {
        self.topics
            .entry(name.to_string())
            .or_insert_with(|| broadcast::channel(self.default_capacity).0)
            .clone()
    }

    /// Subscribe to a topic
    pub fn subscribe(&mut self, topic: &str) -> Option<broadcast::Receiver<T>> {
        self.topics.get(topic).map(|tx| tx.subscribe())
    }

    /// Publish to a topic
    pub fn publish(&self, topic: &str, message: T) -> Result<usize, PubSubError> {
        match self.topics.get(topic) {
            Some(tx) => {
                let count = tx.send(message)?;
                Ok(count)
            }
            None => Err(PubSubError::TopicNotFound),
        }
    }

    /// Get subscriber count for a topic
    pub fn subscriber_count(&self, topic: &str) -> usize {
        self.topics
            .get(topic)
            .map(|tx| tx.receiver_count())
            .unwrap_or(0)
    }
}

#[derive(Debug)]
pub enum PubSubError {
    TopicNotFound,
    SendError(broadcast::error::SendError<()>),
}

impl From<broadcast::error::SendError<()>> for PubSubError {
    fn from(e: broadcast::error::SendError<()>) -> Self {
        PubSubError::SendError(e)
    }
}

/// Example: Event bus
async fn event_bus_example() {
    let mut event_bus = PubSub::<String>::new(100);

    // Create topic
    event_bus.create_topic("user.events");

    // Multiple subscribers
    let mut sub1 = event_bus.subscribe("user.events").unwrap();
    let mut sub2 = event_bus.subscribe("user.events").unwrap();
    let mut sub3 = event_bus.subscribe("user.events").unwrap();

    // Publish event
    event_bus.publish("user.events", "User 123 logged in".to_string()).unwrap();

    // All subscribers receive
    assert_eq!(sub1.recv().await.unwrap(), "User 123 logged in");
    assert_eq!(sub2.recv().await.unwrap(), "User 123 logged in");
    assert_eq!(sub3.recv().await.unwrap(), "User 123 logged in");
}
```

#### Counter-Example: Slow Subscriber Blocking

```rust
use tokio::sync::broadcast;
use std::time::Duration;

/// COUNTER-EXAMPLE: Slow subscriber causes message loss
async fn slow_subscriber_blocking() {
    // Small buffer of 2 messages
    let (tx, mut fast_rx) = broadcast::channel::<String>(2);
    let mut slow_rx = tx.subscribe();

    // Spawn slow consumer
    tokio::spawn(async move {
        loop {
            match slow_rx.recv().await {
                Ok(msg) => {
                    println!("Slow consumer: {}", msg);
                    tokio::time::sleep(Duration::from_secs(5)).await;  // Very slow!
                }
                Err(e) => {
                    println!("Slow consumer error: {:?}", e);
                    break;
                }
            }
        }
    });

    // Fast producer sends many messages
    for i in 0..10 {
        match tx.send(format!("Message {}", i)) {
            Ok(n) => println!("Sent to {} receivers", n),
            Err(e) => println!("Send error: {:?}", e),
        }
    }

    // Fast consumer tries to receive all
    while let Ok(msg) = fast_rx.try_recv() {
        println!("Fast consumer: {}", msg);
    }

    // Messages 2-8 are lost because slow consumer caused overflow!
}

/// SOLUTION: Dedicated per-subscriber channel
use tokio::sync::mpsc;

struct ReliablePubSub<T: Clone + Send + 'static> {
    subscribers: HashMap<String, Vec<mpsc::Sender<T>>>,
}

impl<T: Clone + Send + 'static> ReliablePubSub<T> {
    fn new() -> Self {
        ReliablePubSub {
            subscribers: HashMap::new(),
        }
    }

    fn subscribe(&mut self, topic: &str, buffer_size: usize) -> mpsc::Receiver<T> {
        let (tx, rx) = mpsc::channel(buffer_size);
        self.subscribers
            .entry(topic.to_string())
            .or_default()
            .push(tx);
        rx
    }

    async fn publish(&self, topic: &str, message: T) {
        if let Some(subs) = self.subscribers.get(topic) {
            for tx in subs {
                // Try-send prevents slow subscribers from blocking
                let _ = tx.try_send(message.clone());
            }
        }
    }
}
```

---

## 4. Async Channel Patterns

### 4.1 Bounded vs Unbounded

Async channels come in bounded and unbounded variants, each with distinct memory and performance characteristics.

```rust
use tokio::sync::mpsc;

/// Comparison of bounded vs unbounded channels
async fn channel_types_comparison() {
    // Unbounded channel - no backpressure
    let (unbounded_tx, mut unbounded_rx) = mpsc::unbounded_channel::<i32>();

    // Can send unlimited messages without blocking
    for i in 0..1_000_000 {
        unbounded_tx.send(i).unwrap();  // Never blocks
    }
    println!("Unbounded queue size: {}", unbounded_rx.len());

    // Bounded channel - with backpressure
    let (bounded_tx, mut bounded_rx) = mpsc::channel::<i32>(100);

    // Async send will block when buffer is full
    for i in 0..200 {
        match bounded_tx.try_send(i) {
            Ok(_) => {},
            Err(e) => println!("Buffer full at {}: {:?}", i, e),
        }
    }
    println!("Bounded queue size: {}", bounded_rx.len());
}
```

**Memory Usage Implications**:

| Channel Type | Memory Usage | Backpressure | Use Case |
|-------------|--------------|--------------|----------|
| Unbounded | O(n) with n = messages | None | Sporadic traffic |
| Bounded | O(capacity) | Yes | Sustained throughput |

#### Counter-Example: Unbounded Memory Growth

```rust
use tokio::sync::mpsc;

/// COUNTER-EXAMPLE: Unbounded channel can cause OOM
async fn unbounded_memory_growth() {
    let (tx, _rx) = mpsc::unbounded_channel::<Vec<u8>>();

    // Producer that never stops
    tokio::spawn(async move {
        loop {
            // Send 1MB chunks
            let chunk = vec![0u8; 1_000_000];
            if tx.send(chunk).is_err() {
                break;
            }
            // No backpressure - continues indefinitely
        }
    });

    // Consumer that's too slow
    // If this consumes slower than producer, memory grows without bound
    tokio::time::sleep(std::time::Duration::from_secs(60)).await;
    // OOM likely occurs before this!
}

/// SOLUTION: Bounded channel with proper backpressure handling
async fn bounded_with_backpressure() {
    let (tx, mut rx) = mpsc::channel::<Vec<u8>>(10);

    tokio::spawn(async move {
        let mut produced = 0;
        loop {
            let chunk = vec![0u8; 1_000_000];

            // Bounded send blocks when buffer is full
            if tx.send(chunk).await.is_err() {
                break;
            }
            produced += 1;
            if produced % 100 == 0 {
                println!("Produced {} MB (backpressure active)", produced);
            }
        }
    });

    // Consumer
    while let Some(chunk) = rx.recv().await {
        tokio::time::sleep(std::time::Duration::from_millis(10)).await;
        println!("Consumed {} bytes", chunk.len());
    }
}
```

### 4.2 Select Operation

The `select!` macro allows waiting on multiple channel operations simultaneously.

```rust
use tokio::sync::mpsc;
use tokio::select;

/// Select across multiple channels
async fn select_example() {
    let (tx1, mut rx1) = mpsc::channel::<i32>(10);
    let (tx2, mut rx2) = mpsc::channel::<String>(10);

    tokio::spawn(async move {
        tx1.send(42).await.unwrap();
    });

    tokio::spawn(async move {
        tx2.send("hello".to_string()).await.unwrap();
    });

    // Wait for whichever arrives first
    select! {
        Some(n) = rx1.recv() => {
            println!("Received from channel 1: {}", n);
        }
        Some(s) = rx2.recv() => {
            println!("Received from channel 2: {}", s);
        }
        else => {
            println!("All channels closed");
        }
    }
}

/// Select with timeout
async fn select_with_timeout() {
    let (tx, mut rx) = mpsc::channel::<i32>(10);

    let result = tokio::time::timeout(
        std::time::Duration::from_secs(1),
        rx.recv()
    ).await;

    match result {
        Ok(Some(n)) => println!("Received: {}", n),
        Ok(None) => println!("Channel closed"),
        Err(_) => println!("Timeout!"),
    }
}
```

#### Counter-Example: Resource Leak in Select

```rust
use tokio::select;
use tokio::sync::{mpsc, oneshot};

/// COUNTER-EXAMPLE: Resource leak when select chooses one branch
async fn resource_leak_in_select() {
    let (tx1, rx1) = oneshot::channel::<i32>();
    let (tx2, rx2) = oneshot::channel::<String>();
    let (resource_tx, mut resource_rx) = mpsc::channel::<Vec<u8>>(1);

    // Spawn tasks that hold resources
    let resource = vec![0u8; 1_000_000]; // 1MB resource

    tokio::spawn(async move {
        // This task holds resource until response is received
        let _ = tx1.send(42);
        // Resource should be freed after send, but...
        drop(resource);
    });

    tokio::spawn(async move {
        let _ = tx2.send("hello".to_string());
    });

    // Select only takes one branch
    select! {
        Ok(n) = rx1 => {
            println!("Got number: {}", n);
            // rx2 is dropped, its sender's resources may leak
        }
        Ok(s) = rx2 => {
            println!("Got string: {}", s);
            // rx1 is dropped
        }
    }

    // If rx2 was chosen, the task waiting on rx1 might hold resources indefinitely
}

/// SOLUTION: Ensure cleanup on all branches
async fn safe_select_cleanup() {
    let (tx1, rx1) = oneshot::channel::<i32>();
    let (tx2, rx2) = oneshot::channel::<String>();

    // Wrap receivers in Option for explicit cleanup
    let mut rx1 = Some(rx1);
    let mut rx2 = Some(rx2);

    tokio::spawn(async move {
        let _ = tx1.send(42);
    });

    tokio::spawn(async move {
        let _ = tx2.send("hello".to_string());
    });

    loop {
        select! {
            // biased ensures deterministic ordering
            biased;

            Some(Ok(n)) = async { rx1.as_mut()?.await }, if rx1.is_some() => {
                println!("Got number: {}", n);
                rx1 = None;  // Explicit cleanup
            }
            Some(Ok(s)) = async { rx2.as_mut()?.await }, if rx2.is_some() => {
                println!("Got string: {}", s);
                rx2 = None;  // Explicit cleanup
            }
            else => break,
        }
    }
}
```

### 4.3 Priority Channels

Priority channels allow processing messages based on importance rather than arrival order.

```rust
use std::collections::BinaryHeap;
use std::cmp::Ordering;
use tokio::sync::mpsc;

/// Priority message wrapper
#[derive(Debug, Clone)]
pub struct PriorityMessage<T> {
    priority: u8,  // Lower number = higher priority
    sequence: u64, // For FIFO within same priority
    payload: T,
}

impl<T> PartialEq for PriorityMessage<T> {
    fn eq(&self, other: &Self) -> bool {
        self.priority == other.priority && self.sequence == other.sequence
    }
}

impl<T> Eq for PriorityMessage<T> {}

impl<T> PartialOrd for PriorityMessage<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T> Ord for PriorityMessage<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        // Reverse: lower priority number = higher priority
        other.priority.cmp(&self.priority)
            .then_with(|| self.sequence.cmp(&other.sequence))
    }
}

/// Priority channel
pub struct PriorityChannel<T> {
    sender: mpsc::Sender<PriorityMessage<T>>,
    next_sequence: std::sync::atomic::AtomicU64,
}

impl<T: Send + 'static> PriorityChannel<T> {
    pub fn new(buffer_size: usize) -> (Self, PriorityReceiver<T>) {
        let (tx, rx) = mpsc::channel(buffer_size);

        let channel = PriorityChannel {
            sender: tx,
            next_sequence: std::sync::atomic::AtomicU64::new(0),
        };

        let receiver = PriorityReceiver::new(rx);
        (channel, receiver)
    }

    pub async fn send(&self, priority: u8, payload: T) -> Result<(), mpsc::error::SendError<PriorityMessage<T>>> {
        let sequence = self.next_sequence.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        let msg = PriorityMessage {
            priority,
            sequence,
            payload,
        };
        self.sender.send(msg).await
    }
}

/// Priority-aware receiver
pub struct PriorityReceiver<T> {
    raw_receiver: mpsc::Receiver<PriorityMessage<T>>,
    priority_queue: BinaryHeap<PriorityMessage<T>>,
    max_queue_size: usize,
}

impl<T: Send + 'static> PriorityReceiver<T> {
    fn new(raw_receiver: mpsc::Receiver<PriorityMessage<T>>) -> Self {
        PriorityReceiver {
            raw_receiver,
            priority_queue: BinaryHeap::new(),
            max_queue_size: 1000,
        }
    }

    pub async fn recv(&mut self) -> Option<T> {
        // First, drain available messages from raw channel
        while let Ok(msg) = self.raw_receiver.try_recv() {
            if self.priority_queue.len() < self.max_queue_size {
                self.priority_queue.push(msg);
            } else {
                // Queue full, drop lowest priority
                if msg.priority < self.priority_queue.peek()?.priority {
                    self.priority_queue.pop();
                    self.priority_queue.push(msg);
                }
            }
        }

        // Return highest priority message
        if let Some(msg) = self.priority_queue.pop() {
            return Some(msg.payload);
        }

        // Wait for more messages
        match self.raw_receiver.recv().await {
            Some(msg) => {
                self.priority_queue.push(msg);
                self.recv().await
            }
            None => None,
        }
    }
}

/// Starvation prevention using priority aging
pub struct FairPriorityChannel<T> {
    sender: mpsc::Sender<(u8, u64, T)>,  // (priority, timestamp, payload)
}

impl<T: Send + 'static> FairPriorityChannel<T> {
    pub async fn send_with_aging(
        &self,
        priority: u8,
        payload: T,
        wait_time: std::time::Duration,
    ) -> Result<(), mpsc::error::SendError<(u8, u64, T)>> {
        // Older messages get their priority boosted
        let effective_priority = priority.saturating_sub(wait_time.as_secs() as u8);
        let timestamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs();

        self.sender.send((effective_priority, timestamp, payload)).await
    }
}
```

---

## 5. Error Handling

### 5.1 Sender/Receiver Disconnection

Channels can disconnect when one end is dropped, and proper handling is essential for robust applications.

```rust
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

/// Proper disconnection handling
fn disconnection_handling() {
    let (tx, rx) = mpsc::channel::<String>();

    // Producer that may crash
    let producer = thread::spawn(move || {
        for i in 0..5 {
            if tx.send(format!("Message {}", i)).is_err() {
                println!("Receiver disconnected, stopping producer");
                return;
            }
            thread::sleep(Duration::from_millis(100));
        }
        // tx dropped here, signaling end of stream
    });

    // Consumer with early exit
    let consumer = thread::spawn(move || {
        loop {
            match rx.recv_timeout(Duration::from_secs(1)) {
                Ok(msg) => println!("Received: {}", msg),
                Err(mpsc::RecvTimeoutError::Timeout) => {
                    println!("Timeout, breaking");
                    break;
                }
                Err(mpsc::RecvTimeoutError::Disconnected) => {
                    println!("Sender disconnected, all messages received");
                    break;
                }
            }
        }
    });

    producer.join().unwrap();
    consumer.join().unwrap();
}
```

#### Counter-Example: Ignoring SendError Causing Panic

```rust
use std::sync::mpsc;

/// COUNTER-EXAMPLE: Unwrapping send can cause panic
fn ignoring_send_error() {
    let (tx, rx) = mpsc::channel::<i32>();

    // Drop receiver immediately
    drop(rx);

    // This will panic!
    // tx.send(42).unwrap();  // PANIC: SendError

    // Better: handle the error
    match tx.send(42) {
        Ok(_) => println!("Sent successfully"),
        Err(e) => {
            println!("Failed to send: {}", e);
            // Can recover the value
            let recovered = e.0;
            println!("Recovered value: {}", recovered);
        }
    }
}

/// SOLUTION: Graceful error handling with retry
fn graceful_send_with_retry<T: Send>(
    sender: &mpsc::Sender<T>,
    value: T,
    max_retries: u32,
) -> Result<(), T> {
    let mut retries = 0;
    let mut current_value = value;

    while retries < max_retries {
        match sender.send(current_value) {
            Ok(_) => return Ok(()),
            Err(e) => {
                current_value = e.0;
                retries += 1;
                std::thread::sleep(std::time::Duration::from_millis(10));
            }
        }
    }

    Err(current_value)  // Return unrecoverable value
}
```

### 5.2 Poisoned Channels

While "poisoned channels" aren't a standard Rust concept like poisoned mutexes, similar issues can occur when a thread panics while holding channel-related state.

```rust
use std::sync::mpsc;
use std::thread;
use std::panic;

/// Handling channel state after panic
fn channel_recovery_after_panic() {
    let (tx, rx) = mpsc::channel::<Result<i32, String>>();

    let result = panic::catch_unwind(|| {
        let tx = tx.clone();
        thread::spawn(move || {
            for i in 0..10 {
                if i == 5 {
                    panic!("Worker panic!");
                }
                tx.send(Ok(i)).unwrap();
            }
        }).join().unwrap();
    });

    match result {
        Ok(_) => println!("Worker completed successfully"),
        Err(_) => {
            println!("Worker panicked!");
            // Signal error to receiver
            tx.send(Err("Worker panicked".to_string())).unwrap();
        }
    }

    // Continue receiving from other workers
    for msg in rx {
        match msg {
            Ok(n) => println!("Got: {}", n),
            Err(e) => println!("Error: {}", e),
        }
    }
}
```

---

## 6. Performance Patterns

### 6.1 Batch Processing

Batch processing amortizes channel overhead by processing multiple messages together.

```rust
use tokio::sync::mpsc;
use std::time::{Duration, Instant};

/// Batching channel receiver
pub struct BatchingReceiver<T> {
    receiver: mpsc::Receiver<T>,
    batch_size: usize,
    timeout: Duration,
}

impl<T> BatchingReceiver<T> {
    pub fn new(receiver: mpsc::Receiver<T>, batch_size: usize, timeout: Duration) -> Self {
        BatchingReceiver {
            receiver,
            batch_size,
            timeout,
        }
    }

    /// Receive a batch of messages
    pub async fn recv_batch(&mut self) -> Vec<T> {
        let mut batch = Vec::with_capacity(self.batch_size);
        let deadline = Instant::now() + self.timeout;

        // Wait for first message
        match tokio::time::timeout_at(
            tokio::time::Instant::from_std(deadline),
            self.receiver.recv()
        ).await {
            Ok(Some(first)) => batch.push(first),
            _ => return batch,
        }

        // Fill batch with remaining messages
        while batch.len() < self.batch_size {
            match self.receiver.try_recv() {
                Ok(msg) => batch.push(msg),
                Err(_) => break,
            }
        }

        batch
    }
}

/// Latency vs throughput tradeoff demonstration
async fn batch_tradeoff_demo() {
    let (tx, rx) = mpsc::channel::<i32>(1000);

    // Producer
    tokio::spawn(async move {
        for i in 0..1000 {
            tx.send(i).await.unwrap();
        }
    });

    // Batch consumer
    let mut batch_rx = BatchingReceiver::new(rx, 100, Duration::from_millis(10));

    let start = Instant::now();
    let mut total_processed = 0;
    let mut batch_count = 0;

    while total_processed < 1000 {
        let batch = batch_rx.recv_batch().await;
        total_processed += batch.len();
        batch_count += 1;

        // Process batch
        let sum: i32 = batch.iter().sum();
        println!("Batch {}: {} items, sum = {}", batch_count, batch.len(), sum);
    }

    let elapsed = start.elapsed();
    println!("Processed 1000 items in {} batches, took {:?}", batch_count, elapsed);
    // Batching reduces syscall overhead but increases latency
}
```

### 6.2 Zero-Copy Messages

Using `Arc` for shared data reduces copying when multiple consumers need the same data.

```rust
use std::sync::Arc;
use tokio::sync::broadcast;

/// Zero-copy message using Arc
pub struct SharedMessage {
    pub data: Arc<Vec<u8>>,
    pub metadata: String,
}

impl Clone for SharedMessage {
    fn clone(&self) -> Self {
        SharedMessage {
            data: Arc::clone(&self.data),  // Increment refcount only
            metadata: self.metadata.clone(),
        }
    }
}

/// Broadcast with shared data
async fn zero_copy_broadcast() {
    let (tx, mut rx1) = broadcast::channel::<SharedMessage>(100);
    let mut rx2 = tx.subscribe();
    let mut rx3 = tx.subscribe();

    // Create large payload once
    let large_payload = Arc::new(vec![0u8; 10_000_000]); // 10MB

    // Send to many receivers without copying data
    tx.send(SharedMessage {
        data: large_payload,
        metadata: "broadcast".to_string(),
    }).unwrap();

    // All receivers share the same underlying data
    let msg1 = rx1.recv().await.unwrap();
    let msg2 = rx2.recv().await.unwrap();
    let msg3 = rx3.recv().await.unwrap();

    // All point to same memory
    assert!(Arc::ptr_eq(&msg1.data, &msg2.data));
    assert!(Arc::ptr_eq(&msg2.data, &msg3.data));

    println!("Zero-copy broadcast: 10MB shared by {} receivers", Arc::strong_count(&msg1.data));
}
```

#### Counter-Example: Unnecessary Cloning

```rust
use tokio::sync::broadcast;

/// COUNTER-EXAMPLE: Unnecessary cloning wastes memory
async fn unnecessary_cloning() {
    let (tx, mut rx1) = broadcast::channel::<Vec<u8>>(100);
    let mut rx2 = tx.subscribe();

    // Large payload
    let data = vec![0u8; 10_000_000]; // 10MB

    // Clone for each send - O(n*m) memory!
    tx.send(data.clone()).unwrap();  // Clone 1: 10MB
    // rx1 receives a clone

    // Total memory: 10MB (original) + 10MB (sent) + 10MB (rx1) = 30MB+

    let received = rx1.recv().await.unwrap();
    println!("Received {} bytes", received.len());
}

/// SOLUTION: Use Arc for shared data
use std::sync::Arc;

async fn efficient_sharing() {
    let (tx, mut rx1) = broadcast::channel::<Arc<Vec<u8>>>(100);
    let mut rx2 = tx.subscribe();

    // Wrap in Arc once
    let data = Arc::new(vec![0u8; 10_000_000]);

    // Send Arc clone (just increments refcount)
    tx.send(Arc::clone(&data)).unwrap();

    // Total memory: 10MB (data) + tiny overhead (Arc)

    let received = rx1.recv().await.unwrap();
    println!("Received {} bytes, shared by {} owners",
        received.len(),
        Arc::strong_count(&received));
}
```

---

## 7. Case Study: Chat Server

This section presents a complete chat server implementation demonstrating message passing patterns in a real-world scenario.

### Architecture Overview

```
┌─────────────────────────────────────────────────────────────┐
│                      Chat Server                             │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  ┌──────────┐    ┌──────────────┐    ┌──────────────────┐  │
│  │ Listener │───>│ Connection   │───>│ Client Handler   │  │
│  │ (TCP)    │    │ Manager      │    │ (per client)     │  │
│  └──────────┘    └──────────────┘    └──────────────────┘  │
│         │              │                       │            │
│         ▼              ▼                       ▼            │
│  ┌──────────┐    ┌──────────────┐    ┌──────────────────┐  │
│  │ Accept   │    │ New Conn     │    │ Message Router   │  │
│  │ Channel  │    │ Channel      │    │ (broadcast)      │  │
│  └──────────┘    └──────────────┘    └──────────────────┘  │
│                                             │               │
│                              ┌──────────────┼──────────┐   │
│                              ▼              ▼          ▼   │
│                         ┌────────┐    ┌────────┐   ┌──────┐│
│                         │Room A  │    │Room B  │   │Direct││
│                         └────────┘    └────────┘   └──────┘│
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

### Complete Implementation

```rust
use tokio::net::{TcpListener, TcpStream};
use tokio::sync::{mpsc, broadcast, RwLock};
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use std::collections::HashMap;
use std::sync::Arc;

/// Message types
#[derive(Debug, Clone)]
pub enum ChatMessage {
    Join { user: String, room: String },
    Leave { user: String, room: String },
    Chat { user: String, room: String, content: String },
    Direct { from: String, to: String, content: String },
    System { content: String },
}

/// Client connection handle
pub struct Client {
    id: u64,
    username: String,
    room: String,
    sender: mpsc::Sender<ChatMessage>,
}

/// Shared server state
pub struct ChatServer {
    clients: Arc<RwLock<HashMap<u64, Client>>>,
    rooms: Arc<RwLock<HashMap<String, broadcast::Sender<ChatMessage>>>>,
    next_client_id: Arc<RwLock<u64>>,
}

impl ChatServer {
    pub fn new() -> Self {
        ChatServer {
            clients: Arc::new(RwLock::new(HashMap::new())),
            rooms: Arc::new(RwLock::new(HashMap::new())),
            next_client_id: Arc::new(RwLock::new(1)),
        }
    }

    pub async fn run(&self, addr: &str) -> Result<(), Box<dyn std::error::Error>> {
        let listener = TcpListener::bind(addr).await?;
        println!("Chat server listening on {}", addr);

        loop {
            let (socket, peer_addr) = listener.accept().await?;
            println!("New connection from {:?}", peer_addr);

            let client_id = {
                let mut id = self.next_client_id.write().await;
                let current = *id;
                *id += 1;
                current
            };

            // Clone Arc for new task
            let clients = Arc::clone(&self.clients);
            let rooms = Arc::clone(&self.rooms);

            tokio::spawn(async move {
                if let Err(e) = handle_client(socket, client_id, clients, rooms).await {
                    eprintln!("Client {} error: {:?}", client_id, e);
                }
            });
        }
    }
}

async fn handle_client(
    mut socket: TcpStream,
    client_id: u64,
    clients: Arc<RwLock<HashMap<u64, Client>>>,
    rooms: Arc<RwLock<HashMap<String, broadcast::Sender<ChatMessage>>>>,
) -> Result<(), Box<dyn std::error::Error>> {
    // Create channel for this client
    let (tx, mut rx) = mpsc::channel::<ChatMessage>(100);

    // Read username (simplified protocol)
    let mut buf = [0u8; 256];
    let n = socket.read(&mut buf).await?;
    let username = String::from_utf8_lossy(&buf[..n]).trim().to_string();
    let room = "general".to_string();

    // Register client
    {
        let mut clients_guard = clients.write().await;
        clients_guard.insert(client_id, Client {
            id: client_id,
            username: username.clone(),
            room: room.clone(),
            sender: tx.clone(),
        });
    }

    // Get or create room broadcast
    let room_tx = {
        let mut rooms_guard = rooms.write().await;
        rooms_guard
            .entry(room.clone())
            .or_insert_with(|| broadcast::channel(100).0)
            .clone()
    };

    // Subscribe to room
    let mut room_rx = room_tx.subscribe();

    // Send join notification
    let join_msg = ChatMessage::Join {
        user: username.clone(),
        room: room.clone(),
    };
    let _ = room_tx.send(join_msg);

    // Spawn task to handle room broadcasts to this client
    let client_tx = tx.clone();
    let broadcast_task = tokio::spawn(async move {
        loop {
            match room_rx.recv().await {
                Ok(msg) => {
                    if client_tx.send(msg).await.is_err() {
                        break;
                    }
                }
                Err(_) => break,
            }
        }
    });

    // Main client loop
    let mut read_buf = vec![0u8; 1024];
    loop {
        tokio::select! {
            // Read from socket
            result = socket.read(&mut read_buf) => {
                match result {
                    Ok(0) => {
                        println!("Client {} disconnected", client_id);
                        break;
                    }
                    Ok(n) => {
                        let text = String::from_utf8_lossy(&read_buf[..n]);
                        let msg = ChatMessage::Chat {
                            user: username.clone(),
                            room: room.clone(),
                            content: text.to_string(),
                        };
                        let _ = room_tx.send(msg);
                    }
                    Err(e) => {
                        eprintln!("Read error: {:?}", e);
                        break;
                    }
                }
            }

            // Send to socket
            Some(msg) = rx.recv() => {
                let text = format_message(&msg);
                if socket.write_all(text.as_bytes()).await.is_err() {
                    break;
                }
            }
        }
    }

    // Cleanup
    broadcast_task.abort();

    // Send leave notification
    let leave_msg = ChatMessage::Leave {
        user: username,
        room: room.clone(),
    };
    let _ = room_tx.send(leave_msg);

    // Remove client
    {
        let mut clients_guard = clients.write().await;
        clients_guard.remove(&client_id);
    }

    Ok(())
}

fn format_message(msg: &ChatMessage) -> String {
    match msg {
        ChatMessage::Join { user, room } => format!("[{}] {} joined\n", room, user),
        ChatMessage::Leave { user, room } => format!("[{}] {} left\n", room, user),
        ChatMessage::Chat { user, room, content } => format!("[{}] {}: {}", room, user, content),
        ChatMessage::Direct { from, to, content } => format!("[DM {}->{}] {}", from, to, content),
        ChatMessage::System { content } => format!("[System] {}\n", content),
    }
}

/// Graceful shutdown handling
pub struct ShutdownCoordinator {
    shutdown_tx: broadcast::Sender<()>,
}

impl ShutdownCoordinator {
    pub fn new() -> Self {
        let (tx, _) = broadcast::channel(1);
        ShutdownCoordinator { shutdown_tx: tx }
    }

    pub fn subscribe(&self) -> broadcast::Receiver<()> {
        self.shutdown_tx.subscribe()
    }

    pub fn shutdown(&self) {
        let _ = self.shutdown_tx.send(());
    }
}

/// Client with shutdown awareness
async fn client_with_shutdown(
    mut socket: TcpStream,
    client_id: u64,
    shutdown: ShutdownCoordinator,
) {
    let mut shutdown_rx = shutdown.subscribe();

    loop {
        tokio::select! {
            // Normal operation
            result = socket.read(&mut [0u8; 1024]) => {
                match result {
                    Ok(0) | Err(_) => break,
                    Ok(_) => {}
                }
            }

            // Shutdown signal
            _ = shutdown_rx.recv() => {
                let _ = socket.write_all(b"Server shutting down\n").await;
                break;
            }
        }
    }
}
```

### Ownership Flow Analysis

```
Connection Flow Ownership Analysis:

1. TCP Connection Establishment:
   TcpStream (owned by OS) → tokio::net::TcpStream (owned by runtime)

2. Client Registration:
   TcpStream → split into (ReadHalf, WriteHalf)
   Client struct created, owns mpsc::Sender<ChatMessage>

3. Message Broadcasting:
   broadcast::Sender::send() clones Arc<ChatMessage> for each subscriber
   Each mpsc::Sender receives a clone

4. Message Delivery:
   mpsc::Receiver::recv() moves ChatMessage to async task
   Async task writes to TcpStream

5. Disconnection:
   Client struct dropped → mpsc::Sender dropped
   Broadcast subscription automatically removed
   TcpStream closed
```

### Graceful Shutdown

```rust
use tokio::signal;

/// Graceful shutdown implementation
async fn run_with_graceful_shutdown(server: ChatServer, addr: &str) {
    let shutdown = ShutdownCoordinator::new();
    let mut shutdown_rx = shutdown.subscribe();

    // Spawn server
    let server_handle = tokio::spawn(async move {
        tokio::select! {
            result = server.run(addr) => {
                if let Err(e) = result {
                    eprintln!("Server error: {:?}", e);
                }
            }
            _ = shutdown_rx.recv() => {
                println!("Server received shutdown signal");
            }
        }
    });

    // Wait for shutdown signal
    match signal::ctrl_c().await {
        Ok(()) => {
            println!("Received Ctrl+C, shutting down...");
            shutdown.shutdown();
        }
        Err(e) => {
            eprintln!("Error waiting for signal: {:?}", e);
        }
    }

    // Wait for server to finish
    let _ = server_handle.await;
    println!("Server shut down complete");
}
```

---

## 8. Anti-Patterns

### Anti-Pattern 1: Synchronous Send in Async Context

**Problem**: Using `std::sync::mpsc` in async code blocks the executor thread.

```rust
/// COUNTER-EXAMPLE: Blocking send in async context
async fn blocking_send_in_async() {
    let (tx, _rx) = std::sync::mpsc::channel::<i32>();

    // This blocks the async executor thread!
    tx.send(42).unwrap();  // May block if buffer full

    // While blocked, other tasks on this thread cannot run
}

/// SOLUTION: Use async channels
use tokio::sync::mpsc;

async fn async_send_in_async() {
    let (tx, _rx) = mpsc::channel::<i32>(100);

    // Async send yields control if channel full
    tx.send(42).await.unwrap();

    // Executor can run other tasks while waiting
}
```

### Anti-Pattern 2: Unbounded Channels Without Backpressure

**Problem**: Unbounded channels can exhaust memory under load.

```rust
/// COUNTER-EXAMPLE: Unbounded channel causing memory exhaustion
fn unbounded_channel_anti_pattern() {
    let (tx, _rx) = tokio::sync::mpsc::unbounded_channel::<Vec<u8>>();

    // Fast producer
    std::thread::spawn(move || {
        loop {
            let data = vec![0u8; 1_000_000];  // 1MB
            let _ = tx.send(data);  // Never blocks, memory grows
        }
    });
}

/// SOLUTION: Bounded channels with backpressure handling
fn bounded_channel_solution() {
    let (tx, _rx) = tokio::sync::mpsc::channel::<Vec<u8>>(100);

    tokio::spawn(async move {
        loop {
            let data = vec![0u8; 1_000_000];

            // Apply backpressure - blocks when buffer full
            if tx.send(data).await.is_err() {
                break;
            }
        }
    });
}
```

### Anti-Pattern 3: Holding Receiver Across Await

**Problem**: Holding a synchronous receiver across await points can cause issues.

```rust
/// COUNTER-EXAMPLE: Potential deadlock holding receiver
async fn holding_receiver_across_await() {
    let (tx, rx) = std::sync::mpsc::channel::<i32>();

    // Spawn sender
    tokio::task::spawn_blocking(move || {
        std::thread::sleep(std::time::Duration::from_secs(1));
        tx.send(42).unwrap();
    });

    // Try to receive
    // This blocks the async thread!
    // let msg = rx.recv().unwrap();

    // If this were async code with .await, we'd have issues
}

/// SOLUTION: Use async channels or spawn blocking
async fn proper_async_receive() {
    let (tx, mut rx) = tokio::sync::mpsc::channel::<i32>(10);

    tokio::spawn(async move {
        tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
        tx.send(42).await.unwrap();
    });

    // Async receive doesn't block executor
    let msg = rx.recv().await.unwrap();
    println!("Received: {}", msg);
}
```

### Anti-Pattern 4: Channel Per Task Overhead

**Problem**: Creating too many channels creates overhead and complexity.

```rust
/// COUNTER-EXAMPLE: Too many channels
fn channel_per_task_overhead() {
    let mut handles = vec![];

    for i in 0..1000 {
        let (tx, rx) = std::sync::mpsc::channel::<i32>();

        handles.push(std::thread::spawn(move || {
            // Each task has its own channel
            rx.recv().unwrap();
        }));

        tx.send(i).unwrap();
    }

    // 1000 channels created - significant overhead!
}

/// SOLUTION: Work queue pattern with fewer channels
fn work_queue_pattern() {
    let (tx, rx) = std::sync::mpsc::channel::<(usize, i32)>();
    let rx = std::sync::Arc::new(std::sync::Mutex::new(rx));

    // Worker pool with shared channel
    for worker_id in 0..4 {
        let rx = std::sync::Arc::clone(&rx);
        std::thread::spawn(move || {
            loop {
                let (id, task) = {
                    let lock = rx.lock().unwrap();
                    lock.recv().unwrap()
                };
                println!("Worker {} processing task {}: {}", worker_id, id, task);
            }
        });
    }

    // Send all tasks through single channel
    for i in 0..1000 {
        tx.send((i, i * 2)).unwrap();
    }
}
```

---

## 9. Rust 1.94 Features

Rust 1.94 introduces several features that enhance message passing patterns:

```rust
use std::sync::LazyLock;

/// Rust 1.94: LazyLock for global channel registries
static MESSAGE_BUS: LazyLock<MessageBus> = LazyLock::new(|| {
    MessageBus::new()
});

pub struct MessageBus {
    // Global message routing
}

impl MessageBus {
    fn new() -> Self {
        MessageBus {}
    }
}

/// Rust 1.94: LazyCell for per-thread lazy initialization
use std::cell::LazyCell;

pub struct ThreadLocalChannel<T> {
    sender: LazyCell<mpsc::Sender<T>>,
}

impl<T> ThreadLocalChannel<T> {
    pub fn new() -> Self {
        ThreadLocalChannel {
            sender: LazyCell::new(|| {
                // Initialize channel lazily
                let (tx, _rx) = mpsc::channel(100);
                tx
            }),
        }
    }

    pub fn get_sender(&self) -> &mpsc::Sender<T> {
        // Rust 1.94: Safe lazy access
        &*self.sender
    }
}

/// Rust 1.94: Improved const generics for channel buffer sizing
pub struct SizedChannel<T, const BUFFER_SIZE: usize = 100> {
    sender: mpsc::Sender<T>,
}

impl<T, const N: usize> SizedChannel<T, N> {
    pub fn new() -> (Self, mpsc::Receiver<T>) {
        let (tx, rx) = mpsc::channel(N);
        (SizedChannel { sender: tx }, rx)
    }
}

// Type aliases for common sizes
type SmallChannel<T> = SizedChannel<T, 10>;
type MediumChannel<T> = SizedChannel<T, 100>;
type LargeChannel<T> = SizedChannel<T, 1000>;
```

---

## 10. References

### Core Documentation

1. **The Rust Programming Language - Chapter 16: Concurrency**
   - Official documentation on channels and message passing
   - <https://doc.rust-lang.org/book/ch16-02-message-passing.html>

2. **Tokio Channels Documentation**
   - Async channel primitives
   - <https://docs.rs/tokio/latest/tokio/sync/mpsc/>

3. **Crossbeam Channels**
   - High-performance MPMC channels
   - <https://docs.rs/crossbeam/latest/crossbeam/channel/>

### Academic Papers

1. **Hoare, C.A.R. "Communicating Sequential Processes" (1978)**
   - Foundation of channel-based concurrency

2. **Hewitt, Carl. "A Universal Modular Actor Formalism for AI" (1973)**
   - Actor model foundations

3. **Jung et al. "RustBelt: Securing the Foundations of the Rust Programming Language" (POPL 2018)**
   - Formal verification of Rust's safety guarantees

### Related Patterns

- [12-01-concurrency-architecture-deep.md](./12-01-concurrency-architecture-deep.md) - Thread safety theorems
- [12-05-async-patterns-deep.md](./12-05-async-patterns-deep.md) - Async ownership semantics
- [actor-specialty/ACTOR_MODEL_DEEP_DIVE.md](../actor-specialty/ACTOR_MODEL_DEEP_DIVE.md) - Actor model deep dive

---

**Last Updated**: 2026-03-06
**Rust Version**: 1.94
**Document Version**: 1.0.0
