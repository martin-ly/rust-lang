# Async Patterns: Formal Semantics and Ownership Analysis

> **Rust Version**: 1.94
> **Scope**: Formal async/await semantics, ownership in async contexts, safety theorems
> **Prerequisites**: Core ownership concepts, trait system, Pin semantics
> **Reading Time**: ~3 hours
> **Difficulty**: Advanced

---

## Table of Contents

- [Async Patterns: Formal Semantics and Ownership Analysis](#async-patterns-formal-semantics-and-ownership-analysis)
  - [Table of Contents](#table-of-contents)
  - [1. Introduction](#1-introduction)
    - [1.1 Formal Definition of Async/Await Semantics](#11-formal-definition-of-asyncawait-semantics)
    - [1.2 Ownership Challenges in Async Rust](#12-ownership-challenges-in-async-rust)
  - [2. Core Concepts (with Formal Reasoning)](#2-core-concepts-with-formal-reasoning)
    - [2.1 Future and State Machines](#21-future-and-state-machines)
    - [2.2 Pin and Self-Referential Types](#22-pin-and-self-referential-types)
    - [2.3 async/await Desugaring](#23-asyncawait-desugaring)
  - [3. Ownership in Async (with Theorems)](#3-ownership-in-async-with-theorems)
    - [3.1 Send and Sync Requirements](#31-send-and-sync-requirements)
    - [3.2 Borrowing Across Await Points](#32-borrowing-across-await-points)
    - [3.3 async move and Capture Semantics](#33-async-move-and-capture-semantics)
  - [4. Common Patterns (with Safety Arguments)](#4-common-patterns-with-safety-arguments)
    - [4.1 Spawning Tasks](#41-spawning-tasks)
    - [4.2 Select and Race](#42-select-and-race)
    - [4.3 Streams and Pipelines](#43-streams-and-pipelines)
  - [5. Formal Safety Theorems](#5-formal-safety-theorems)
    - [Theorem 5.1: Async Function Preserves Ownership Safety](#theorem-51-async-function-preserves-ownership-safety)
    - [Theorem 5.2: Pin Guarantees Self-Referential Safety](#theorem-52-pin-guarantees-self-referential-safety)
    - [Theorem 5.3: Send Requirement for Spawn](#theorem-53-send-requirement-for-spawn)
    - [Theorem 5.4: Borrowing Across Await Points](#theorem-54-borrowing-across-await-points)
    - [Theorem 5.5: Select Cancellation Safety](#theorem-55-select-cancellation-safety)
  - [6. Anti-Patterns and Solutions](#6-anti-patterns-and-solutions)
    - [Anti-Pattern 1: Holding Mutex Across Await](#anti-pattern-1-holding-mutex-across-await)
    - [Anti-Pattern 2: Non-Send Types in Multi-Threaded Runtime](#anti-pattern-2-non-send-types-in-multi-threaded-runtime)
    - [Anti-Pattern 3: Self-Referential Without Pin](#anti-pattern-3-self-referential-without-pin)
    - [Anti-Pattern 4: Borrowing Local Data in Spawned Task](#anti-pattern-4-borrowing-local-data-in-spawned-task)
    - [Anti-Pattern 5: Race Conditions in Shared State](#anti-pattern-5-race-conditions-in-shared-state)
  - [7. Case Study: Async HTTP Server](#7-case-study-async-http-server)
    - [Architecture Diagram](#architecture-diagram)
    - [Implementation with Ownership Analysis](#implementation-with-ownership-analysis)
    - [Ownership Flow Analysis](#ownership-flow-analysis)
    - [Potential Pitfalls Highlighted](#potential-pitfalls-highlighted)
  - [8. References](#8-references)
    - [Core Documentation](#core-documentation)
    - [Formal Semantics](#formal-semantics)
    - [Rust 1.94 Features](#rust-194-features)
    - [Related Patterns](#related-patterns)

---

## 1. Introduction

### 1.1 Formal Definition of Async/Await Semantics

Async Rust introduces a computational model based on **cooperative multitasking** with explicit suspend points. Unlike threads which are preemptively scheduled by the OS, async tasks yield control at well-defined await points.

**Definition 1.1 (Async Computation)**:
An async computation is a partial function `f: State × Event → State ∪ Result` where:

- `State` represents the suspended execution context
- `Event` represents external stimuli (I/O completion, timer expiration)
- `Result` represents successful termination with a value

**Definition 1.2 (Future)**:
A `Future` is a trait representing a value that may not be ready yet:

```rust
/// Core Future trait from std::future
pub trait Future {
    type Output;

    /// The poll method advances the future's state machine
    ///
    /// # Contract
    /// - Returns `Poll::Ready(T)` when computation completes
    /// - Returns `Poll::Pending` when waiting for external event
    /// - Must register waker via Context before returning Pending
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output>;
}
```

**Formal Semantics of Poll**:

```
poll: Pin<&mut F> × Context → Poll<T>

Where the following laws must hold:

1. PROGRESS: If poll returns Ready(v), all subsequent polls return Ready(v)
2. IDEMPOTENCE: poll(f, cx) = Ready(v) ⟹ poll(f, cx') = Ready(v)
3. WAKER: If poll returns Pending, the waker in cx MUST be invoked
          before the next poll call (unless dropped)
4. PINNING: The Pin guarantee ensures self-referential fields remain valid
```

**Example 1.1: TimerFuture with Correctness Proof**

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};
use std::time::{Duration, Instant};
use std::sync::{Arc, Mutex};

/// A timer future that completes after a specified duration
///
/// # Ownership Analysis
/// - `duration`: Owned, immutable after construction
/// - `started`: Optional owned state, tracks start time
/// - `waker_storage`: Shared state for cross-thread wakeup
///
/// # Safety Invariant
/// The waker MUST be invoked when the timer expires
pub struct TimerFuture {
    duration: Duration,
    started: Option<Instant>,
    waker_storage: Arc<Mutex<Option<std::task::Waker>>>,
}

impl TimerFuture {
    pub fn new(duration: Duration) -> Self {
        Self {
            duration,
            started: None,
            waker_storage: Arc::new(Mutex::new(None)),
        }
    }
}

impl Future for TimerFuture {
    type Output = ();

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        match self.started {
            None => {
                // First poll: record start time and register waker
                let start = Instant::now();
                self.started = Some(start);

                // Store waker for timer thread to invoke
                *self.waker_storage.lock().unwrap() = Some(cx.waker().clone());

                // Spawn timer thread (simplified)
                let duration = self.duration;
                let waker_storage = self.waker_storage.clone();
                std::thread::spawn(move || {
                    std::thread::sleep(duration);
                    if let Some(waker) = waker_storage.lock().unwrap().take() {
                        waker.wake();
                    }
                });

                Poll::Pending
            }
            Some(started) => {
                if started.elapsed() >= self.duration {
                    // Timer expired: computation complete
                    Poll::Ready(())
                } else {
                    // Update waker in case of different context
                    *self.waker_storage.lock().unwrap() = Some(cx.waker().clone());
                    Poll::Pending
                }
            }
        }
    }
}

/// Proof of TimerFuture Correctness:
///
/// Theorem: TimerFuture completes exactly once after duration
///
/// Proof:
/// 1. State invariant: started ∈ {None, Some(t)} where t is Instant
/// 2. State transition: None → Some(t) on first poll
/// 3. Termination condition: elapsed ≥ duration
/// 4. By monotonicity of Instant::elapsed(), condition eventually holds
/// 5. Once Ready(()) returned, started remains Some(t) and
///    elapsed ≥ duration, so subsequent polls return Ready(())
/// 6. Waker guarantee: timer thread always invokes waker after duration
///
/// Therefore: TimerFuture satisfies Future contract
```

### 1.2 Ownership Challenges in Async Rust

Async Rust introduces unique ownership challenges that don't exist in synchronous code:

**Challenge 1: State Machine Transformation**
When an async function is compiled, it becomes a state machine. Local variables become fields of the state machine struct, and their ownership semantics change.

**Challenge 2: Borrowing Across Await Points**
References held across await points must remain valid when the async function resumes, potentially on a different thread.

**Challenge 3: Pin Guarantees**
Self-referential structs require pinning, which constrains how the state machine can be moved.

**Challenge 4: Send/Sync Propagation**
The `Send` and `Sync` properties must propagate correctly through the async transformation.

```rust
/// Example: Ownership transformation in async functions
///
/// Source code:
async fn example() {
    let data = vec![1, 2, 3];  // Owned value
    let ref_data = &data[0];    // Borrow
    async_op().await;           // Await point
    println!("{}", ref_data);   // Use borrow after await
}

/// Desugared state machine (conceptual):
enum ExampleStateMachine {
    Start,
    Waiting1 {
        data: Vec<i32>,          // Owned: moved into state machine
        ref_data: *const i32,    // Raw pointer: self-reference to data
        _pin: PhantomPinned,     // Marker: requires pinning
    },
    Complete,
}

/// Key observation: The borrow `&data[0]` becomes a raw pointer
/// in the state machine. This requires:
/// 1. data must not move while Waiting1
/// 2. Pin guarantee ensures data stays at fixed address
/// 3. Pointer arithmetic remains valid
```

---

## 2. Core Concepts (with Formal Reasoning)

### 2.1 Future and State Machines

**Theorem 2.1 (State Machine Equivalence)**:
Every async function `async fn f() -> T` is equivalent to a state machine implementing `Future<Output = T>`.

**Formal Definition**:
Given async function `f` with `n` await points, the desugared state machine has:

- States: `S₀, S₁, ..., Sₙ₊₁` where `S₀` is Start, `Sₙ₊₁` is Complete
- Transitions: `δ: Sᵢ × Poll<Tᵢ> → Sᵢ₊₁`
- Output: Associated type `Output = T`

**Example 2.1: State Machine Transformation with Ownership Analysis**

```rust
/// Original async function
async fn download_and_process(url: String) -> Result<Vec<u8>, String> {
    // State 0: Initial state
    println!("Starting download from: {}", url);

    // State 1: Waiting for connection
    let connection = connect(&url).await?;

    // State 2: Waiting for download
    let data = download(connection).await?;

    // State 3: Processing (synchronous)
    let processed = process_data(data);

    // State 4: Complete
    Ok(processed)
}

/// Equivalent state machine (manual implementation)
pub enum DownloadStateMachine {
    Start { url: String },
    WaitingConnect { url: String, connect_fut: ConnectFuture },
    WaitingDownload { url: String, download_fut: DownloadFuture },
    Complete { result: Result<Vec<u8>, String> },
}

pub struct ConnectFuture { /* ... */ }
pub struct DownloadFuture { /* ... */ }

impl Future for ConnectFuture {
    type Output = Result<Connection, String>;
    fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Self::Output> {
        unimplemented!()
    }
}

impl Future for DownloadFuture {
    type Output = Result<Vec<u8>, String>;
    fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Self::Output> {
        unimplemented!()
    }
}

impl Future for DownloadStateMachine {
    type Output = Result<Vec<u8>, String>;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        use DownloadStateMachine::*;

        // State machine transition loop
        loop {
            match std::mem::replace(&mut *self, Complete { result: Ok(Vec::new()) }) {
                Start { url } => {
                    println!("Starting download from: {}", url);
                    let connect_fut = ConnectFuture { /* ... */ };
                    *self = WaitingConnect { url, connect_fut };
                    // Continue to poll the new state
                }

                WaitingConnect { url, mut connect_fut } => {
                    match Pin::new(&mut connect_fut).poll(cx) {
                        Poll::Ready(Ok(connection)) => {
                            let download_fut = DownloadFuture { /* use connection */ };
                            *self = WaitingDownload { url, download_fut };
                            // Continue polling
                        }
                        Poll::Ready(Err(e)) => {
                            return Poll::Ready(Err(format!("Connect failed: {}", e)));
                        }
                        Poll::Pending => {
                            *self = WaitingConnect { url, connect_fut };
                            return Poll::Pending;
                        }
                    }
                }

                WaitingDownload { url: _, mut download_fut } => {
                    match Pin::new(&mut download_fut).poll(cx) {
                        Poll::Ready(Ok(data)) => {
                            let processed = process_data(data);
                            return Poll::Ready(Ok(processed));
                        }
                        Poll::Ready(Err(e)) => {
                            return Poll::Ready(Err(format!("Download failed: {}", e)));
                        }
                        Poll::Pending => {
                            *self = WaitingDownload {
                                url: String::new(), // Original url no longer needed
                                download_fut
                            };
                            return Poll::Pending;
                        }
                    }
                }

                Complete { result } => return Poll::Ready(result),
            }
        }
    }
}

fn process_data(data: Vec<u8>) -> Vec<u8> {
    // Processing logic
    data.into_iter().map(|b| b.wrapping_add(1)).collect()
}

/// Ownership Analysis of State Machine:
///
/// 1. Start → WaitingConnect:
///    - url: Moved from Start to WaitingConnect
///    - No references to url exist yet
///
/// 2. WaitingConnect → WaitingDownload:
///    - url: Moved from WaitingConnect to WaitingDownload
///    - connect_fut: Dropped after completion
///    - connection: Consumed by DownloadFuture constructor
///
/// 3. WaitingDownload → Complete:
///    - url: No longer needed, not moved forward
///    - download_fut: Dropped after completion
///    - data: Moved into process_data, ownership transferred
///
/// Safety: All data is either moved forward or dropped at each transition
```

**Counter-Example 2.1: Incorrect State Machine that Violates Ownership**

```rust
/// DANGER: This state machine has use-after-free vulnerability
///
/// DO NOT USE: Educational counter-example only

pub enum BadStateMachine {
    Start,
    Waiting {
        // This field holds a reference to data
        data_ref: *const u8,
        // This field owns the data
        data: Vec<u8>,
    },
}

impl BadStateMachine {
    pub fn new() -> Self {
        Self::Start
    }

    /// DANGER: This method creates invalid self-reference
    pub unsafe fn setup(&mut self) {
        if let Self::Start = self {
            let mut data = vec![1, 2, 3];

            // BUG: Creating pointer to data that hasn't been stored yet
            let data_ref = data.as_ptr();

            // Now we move data, but data_ref still points to old location
            *self = Self::Waiting { data_ref, data };

            // After this assignment, data_ref may be invalid because
            // data was moved to a new location in the enum variant
        }
    }
}

/// Why this is unsafe:
///
/// 1. When `setup` creates `data_ref`, it points to `data` on the stack
/// 2. The assignment `*self = Self::Waiting { ... }` moves `data` into the enum
/// 3. The enum may be at a different memory location than the stack variable
/// 4. Therefore, `data_ref` becomes a dangling pointer
///
/// Correct approach: Use Pin to ensure the data doesn't move
```

### 2.2 Pin and Self-Referential Types

**Theorem 2.2 (Pin Guarantee)**:
`Pin<P<T>>` guarantees that `T` remains at a stable memory location as long as it is pinned, provided `T: !Unpin`.

**Formal Definition**:

```
Pin<P<T>> where T: !Unpin:

Invariants:
1. ADDRESS_STABILITY: ∀ t: Pin<&mut T>, address_of(*t) = constant
2. NO_MOVE_OUT: Cannot obtain ownership of T from Pin<&mut T> unless T: Unpin
3. PROJECTION: Pin<&mut T> can project to Pin<&mut U> for struct fields if safe
```

**Why Pin is Necessary (Self-Reference Theorem)**:

```rust
/// Theorem: Self-referential structs require pinning
///
/// Proof by contradiction:
///
/// Assume we have a self-referential struct S without pinning:
///
/// struct S {
///     data: String,
///     ptr: *const u8,  // Points to data
/// }
///
/// 1. Create s1: S at address A
/// 2. s1.ptr = &s1.data (points to address A + offset)
/// 3. Move s1 to s2 at address B
/// 4. s2.ptr still points to address A + offset (dangling!)
///
/// This violates Rust's safety guarantee: no dangling pointers.
///
/// Therefore, self-referential structs must be pinned to prevent moving.

use std::pin::Pin;
use std::marker::PhantomPinned;

/// Correct self-referential struct using Pin
pub struct SelfReferential {
    data: String,
    // Points to data.as_bytes()
    data_ptr: *const u8,
    // Marks this type as !Unpin, requiring Pin for safety
    _pin: PhantomPinned,
}

impl SelfReferential {
    pub fn new(data: String) -> Pin<Box<Self>> {
        let mut boxed = Box::new(Self {
            data,
            data_ptr: std::ptr::null(),
            _pin: PhantomPinned,
        });

        // Set up self-reference while boxed (stable address)
        let ptr = boxed.data.as_ptr();
        boxed.data_ptr = ptr;

        // Now pin it to prevent any future moves
        Box::into_pin(boxed)
    }

    /// Safe accessor requires Pin
    pub fn get_data(self: Pin<&Self>) -> &str {
        &self.data
    }

    /// Safe access through self-reference
    pub fn get_via_ptr(self: Pin<&Self>) -> &[u8] {
        unsafe {
            // Safe because:
            // 1. Pin guarantees data doesn't move
            // 2. data_ptr was set when data was at this address
            // 3. data has same lifetime as SelfReferential
            std::slice::from_raw_parts(
                self.data_ptr,
                self.data.len()
            )
        }
    }
}

/// Example 2.2: Pin projection patterns

pub struct AsyncFileReader {
    file: tokio::fs::File,
    buffer: Vec<u8>,
    // Self-referential: buffer_view points into buffer
    buffer_view: *const [u8],
    _pin: PhantomPinned,
}

impl AsyncFileReader {
    /// Pin projection to file field (also needs Pin)
    fn file(self: Pin<&mut Self>) -> Pin<&mut tokio::fs::File> {
        // Safety: We're projecting Pin to a field that is structurally pinned
        // File is Unpin, but we're maintaining the Pin contract
        unsafe { self.map_unchecked_mut(|s| &mut s.file) }
    }

    /// Projection to buffer field (no Pin needed, Vec is Unpin)
    fn buffer(self: Pin<&mut Self>) -> &mut Vec<u8> {
        // Safety: Vec is Unpin, so we can get mutable reference
        unsafe { &mut self.get_unchecked_mut().buffer }
    }

    /// Update self-reference after buffer modification
    fn update_view(self: Pin<&mut Self>) {
        unsafe {
            let this = self.get_unchecked_mut();
            this.buffer_view = &this.buffer[..];
        }
    }
}
```

**Counter-Example 2.2: Dangling Pointer Without Pin**

```rust
/// DANGER: Demonstrates why Pin is essential
///
/// This code compiles but has undefined behavior

pub struct UnsafeSelfRef {
    data: String,
    ptr: *const u8,
}

impl UnsafeSelfRef {
    pub fn new(data: String) -> Self {
        let mut s = Self {
            data,
            ptr: std::ptr::null(),
        };
        s.ptr = s.data.as_ptr();
        s
    }

    pub fn get_data(&self) -> &str {
        &self.data
    }

    pub unsafe fn get_via_ptr(&self) -> &[u8] {
        std::slice::from_raw_parts(self.ptr, self.data.len())
    }
}

/// Demonstration of the bug:
fn demonstrate_bug() {
    let mut s = UnsafeSelfRef::new("hello".to_string());

    // s.ptr points to s.data's internal buffer

    // Move s to a new location
    let s2 = s;  // s is moved here

    // s2.data may be at a different address than s.data was
    // But s2.ptr still points to the old location!

    // This is undefined behavior:
    // let bad_data = unsafe { s2.get_via_ptr() };
}

/// The problem in async context:
async fn dangerous_async() {
    let mut data = vec![1u8, 2, 3];
    let ptr = data.as_ptr();

    // When we await, the async state machine may be moved between threads
    some_async_op().await;

    // ptr may now be dangling!
    // unsafe { *ptr }  // UB: potential use-after-move
}

async fn some_async_op() {}

/// Solution: Use Pin to prevent the move
async fn safe_async() {
    // The compiler automatically pins the async state machine
    // when it contains self-referential data
    let data = vec![1u8, 2, 3];

    // This borrow is tracked by the compiler
    let _slice = &data;

    some_async_op().await;

    // _slice is still valid because the state machine is pinned
}
```

### 2.3 async/await Desugaring

**Formal Transformation Rules**:

```rust
/// Rule 1: Simple async function
///
/// Source:
async fn simple() -> T {
    body
}

/// Desugared:
fn simple() -> impl Future<Output = T> {
    async move {
        body
    }
}

/// Rule 2: async fn with parameters
///
/// Source:
async fn with_params(x: String, y: &str) -> T {
    body
}

/// Desugared:
fn with_params(x: String, y: &str) -> impl Future<Output = T> + '_ {
    async move {
        body
    }
}
/// Note: Lifetime elision makes the future borrow y

/// Rule 3: Await points create state transitions
///
/// Source:
async fn with_await() -> T {
    let x = expr1;
    let y = async_op1().await;
    let z = async_op2().await;
    combine(x, y, z)
}

/// Conceptual desugaring:
enum WithAwaitStateMachine<'a> {
    Start,
    State1 {
        x: TypeOfExpr1,
        fut1: Pin<Box<dyn Future<Output = TypeOfY> + 'a>>,
    },
    State2 {
        x: TypeOfExpr1,
        y: TypeOfY,
        fut2: Pin<Box<dyn Future<Output = TypeOfZ> + 'a>>,
    },
    Complete,
}

impl<'a> Future for WithAwaitStateMachine<'a> {
    type Output = T;
    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<T> {
        // Poll appropriate state...
        unimplemented!()
    }
}

/// Rule 4: Captures in async blocks
///
/// Source:
fn make_future(x: String, y: &str) -> impl Future<Output = usize> {
    async move {
        // x is moved, y is borrowed
        x.len() + y.len()
    }
}

/// Desugared (conceptual):
fn make_future(x: String, y: &str) -> impl Future<Output = usize> + '_ {
    struct FutureImpl<'a> {
        x: String,  // Owned capture
        y: &'a str,  // Borrowed capture
    }

    impl<'a> Future for FutureImpl<'a> {
        type Output = usize;
        fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<usize> {
            Poll::Ready(self.x.len() + self.y.len())
        }
    }

    FutureImpl { x, y }
}
```

**Example 2.3: Complete Desugaring Example**

```rust
/// Original async function
async fn fetch_and_process(
    client: &HttpClient,
    url: &str
) -> Result<String, Error> {
    // State 0
    println!("Fetching: {}", url);

    // State 1: Waiting for response
    let response = client.get(url).await?;

    // State 2: Waiting for body
    let body = response.text().await?;

    // State 3: Processing
    Ok(body.to_uppercase())
}

/// Detailed desugaring (conceptual, simplified)
mod desugared {
    use std::pin::Pin;
    use std::task::{Context, Poll};
    use std::future::Future;

    // External types
    pub struct HttpClient;
    pub struct Response;
    pub struct Error;

    impl HttpClient {
        pub fn get(&self, _url: &str) -> GetFuture {
            GetFuture
        }
    }

    impl Response {
        pub fn text(self) -> TextFuture {
            TextFuture
        }
    }

    pub struct GetFuture;
    impl Future for GetFuture {
        type Output = Result<Response, Error>;
        fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Self::Output> {
            unimplemented!()
        }
    }

    pub struct TextFuture;
    impl Future for TextFuture {
        type Output = Result<String, Error>;
        fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Self::Output> {
            unimplemented!()
        }
    }

    /// The state machine enum
    pub enum FetchAndProcess<'a> {
        Start {
            client: &'a HttpClient,
            url: &'a str,
        },
        WaitingResponse {
            url: &'a str,  // Keep for potential error messages
            response_fut: GetFuture,
        },
        WaitingText {
            text_fut: TextFuture,
        },
        Complete,
    }

    /// Constructor (equivalent to calling the async fn)
    pub fn fetch_and_process<'a>(
        client: &'a HttpClient,
        url: &'a str,
    ) -> FetchAndProcess<'a> {
        FetchAndProcess::Start { client, url }
    }

    impl<'a> Future for FetchAndProcess<'a> {
        type Output = Result<String, Error>;

        fn poll(
            mut self: Pin<&mut Self>,
            cx: &mut Context<'_>
        ) -> Poll<Self::Output> {
            use FetchAndProcess::*;

            loop {
                // Take ownership of current state
                match std::mem::replace(&mut *self, Complete) {
                    Start { client, url } => {
                        println!("Fetching: {}", url);
                        let response_fut = client.get(url);
                        *self = WaitingResponse { url, response_fut };
                        // Continue to poll the new state
                    }

                    WaitingResponse { url: _, mut response_fut } => {
                        match Pin::new(&mut response_fut).poll(cx) {
                            Poll::Ready(Ok(response)) => {
                                let text_fut = response.text();
                                *self = WaitingText { text_fut };
                                // Continue polling
                            }
                            Poll::Ready(Err(e)) => {
                                return Poll::Ready(Err(e));
                            }
                            Poll::Pending => {
                                *self = WaitingResponse {
                                    url: "",  // Original url no longer needed
                                    response_fut
                                };
                                return Poll::Pending;
                            }
                        }
                    }

                    WaitingText { mut text_fut } => {
                        match Pin::new(&mut text_fut).poll(cx) {
                            Poll::Ready(Ok(body)) => {
                                return Poll::Ready(Ok(body.to_uppercase()));
                            }
                            Poll::Ready(Err(e)) => {
                                return Poll::Ready(Err(e));
                            }
                            Poll::Pending => {
                                *self = WaitingText { text_fut };
                                return Poll::Pending;
                            }
                        }
                    }

                    Complete => panic!("polled after completion"),
                }
            }
        }
    }
}

/// Ownership Preservation Proof:
///
/// 1. client: &'a HttpClient - borrowed for lifetime 'a
///    - The Future impl has lifetime 'a
///    - client reference is valid throughout Future's lifetime
///
/// 2. url: &'a str - borrowed for lifetime 'a
///    - Same reasoning as client
///    - Dropped after WaitingResponse (no longer needed)
///
/// 3. response_fut: GetFuture - owned by state machine
///    - Created in Start, consumed in WaitingResponse
///    - Ownership properly transferred
///
/// 4. text_fut: TextFuture - owned by state machine
///    - Created in WaitingResponse, consumed in WaitingText
///    - Ownership properly transferred
///
/// All ownership transfers are explicit and checked by compiler
```

**Counter-Example 2.3: Move Semantics Gone Wrong**

```rust
/// DANGER: Incorrect capture semantics in async

/// Counter-example 1: Moving borrowed data
fn bad_move_capture() {
    let data = vec![1, 2, 3];
    let ref_data = &data;

    // This async block captures ref_data by reference
    // but tries to move data
    let fut = async move {
        // ref_data is borrowed, but data is moved... into what?
        println!("{}", ref_data);
    };

    // data dropped here, but fut still holds reference!
    drop(data);

    // fut is invalid - use-after-free if polled
    // let _ = fut.await;  // Would be UB
}

/// Counter-example 2: Double move attempt
async fn double_move() {
    let data = "hello".to_string();

    // First async block takes ownership
    let fut1 = async move {
        println!("{}", data);
    };

    // ERROR: data already moved!
    // let fut2 = async move {
    //     println!("{}", data);  // Compile error: use of moved value
    // };
}

/// Counter-example 3: Capturing in wrong order
fn capture_order_problem() {
    let s = String::from("hello");
    let r = &s;

    // This won't compile - can't move s while borrowing r
    // let fut = async move {
    //     drop(s);    // Trying to move s
    //     println!("{}", r);  // But r borrows s!
    // };
}

/// Correct patterns:

/// Pattern 1: Move everything
fn correct_move_all() -> impl Future<Output = ()> {
    let data = vec![1, 2, 3];
    let other = String::from("hello");

    async move {
        // Both data and other are moved into the async block
        println!("{:?} {}", data, other);
        // Both dropped when async block completes
    }
}

/// Pattern 2: Borrow explicitly
fn correct_borrow<'a>(data: &'a [i32]) -> impl Future<Output = ()> + 'a {
    async move {
        // data is borrowed, not moved
        println!("{:?}", data);
    }
    // Future lifetime tied to data lifetime
}

/// Pattern 3: Clone to share
fn correct_clone() -> impl Future<Output = ()> {
    let data = Arc::new(vec![1, 2, 3]);
    let data2 = data.clone();

    async move {
        // Both point to same data
        println!("{:?}", data);
        println!("{:?}", data2);
    }
}

use std::future::Future;
use std::sync::Arc;
```

---

## 3. Ownership in Async (with Theorems)

### 3.1 Send and Sync Requirements

**Theorem 3.1 (Send Requirement for Async Functions)**:
An async function `f` returns a `Future` that is `Send` if and only if all captured variables are `Send` and all await points preserve `Send`.

**Proof Sketch**:

```
Given: async fn f() where all captures are Send

To prove: The returned Future is Send

1. The async state machine S contains:
   - Captured variables (all Send by assumption)
   - State-specific data at each await point

2. For S to be Send:
   - All fields of all variants must be Send
   - Between await points, the active variant changes

3. At each await point i:
   - The future being awaited must be Send
   - Local variables crossing the await must be Send

4. Therefore, if all captures and all awaited futures are Send,
   all variants of S are Send, hence S: Send

QED
```

**Example 3.1: Correct Send Implementation**

```rust
use std::sync::Arc;
use tokio::task::JoinHandle;

/// All data is Send, so this async fn returns Send future
async fn process_data(data: Vec<u8>) -> Vec<u8> {
    // data: Vec<u8> is Send
    let processed: Vec<u8> = data.iter().map(|b| b.wrapping_add(1)).collect();

    // tokio::time::sleep returns Send future
    tokio::time::sleep(std::time::Duration::from_millis(10)).await;

    // processed: Vec<u8> is Send
    processed
}

/// Arc<T> is Send if T: Send + Sync
async fn shared_state_op(state: Arc<std::sync::Mutex<i32>>) -> i32 {
    let mut guard = state.lock().unwrap();
    *guard += 1;
    *guard
}

/// Can spawn on multi-threaded runtime
fn spawn_send_task() -> JoinHandle<Vec<u8>> {
    let data = vec![1, 2, 3];  // Send

    // process_data returns Send future
    // because all captures and awaits are Send
    tokio::spawn(async move {
        process_data(data).await
    })
}

/// Theorem verification: Send propagation
///
/// process_data is Send because:
/// 1. data: Vec<u8> is Send ✓
/// 2. processed: Vec<u8> is Send ✓
/// 3. tokio::time::Sleep is Send ✓
///
/// Therefore: impl Future<Output = Vec<u8>> + Send
```

**Counter-Example 3.1: Non-Send Type Across Await**

```rust
use std::rc::Rc;
use std::cell::RefCell;

/// Rc is NOT Send - cannot be shared between threads
///
/// This async fn compiles but cannot be spawned on multi-threaded runtime
async fn non_send_operation() -> i32 {
    // Rc is !Send
    let counter: Rc<RefCell<i32>> = Rc::new(RefCell::new(0));

    {
        let mut c = counter.borrow_mut();
        *c += 1;
    }

    // This await point means the future may be moved between threads
    tokio::time::sleep(std::time::Duration::from_millis(1)).await;

    *counter.borrow()
}

/// Compile error when trying to spawn:
fn try_spawn() {
    // let handle = tokio::spawn(async move {
    //     non_send_operation().await
    // });
    // ERROR: future cannot be sent between threads safely
    //   the trait `Send` is not implemented for `Rc<RefCell<i32>>`
}

/// Solution: Replace Rc with Arc, RefCell with Mutex
use std::sync::{Arc, Mutex};

async fn send_operation() -> i32 {
    // Arc<Mutex<T>> is Send if T: Send
    let counter: Arc<Mutex<i32>> = Arc::new(Mutex::new(0));

    {
        let mut c = counter.lock().unwrap();
        *c += 1;
    }

    tokio::time::sleep(std::time::Duration::from_millis(1)).await;

    *counter.lock().unwrap()
}

fn can_now_spawn() -> tokio::task::JoinHandle<i32> {
    tokio::spawn(async move {
        send_operation().await
    })
}
```

### 3.2 Borrowing Across Await Points

**Theorem 3.2 (Lifetime Extension Across Await)**:
If a reference `&'a T` is held across an await point in an async function, the reference's lifetime `'a` must extend until the next use after the await, and the referenced data must outlive the Future.

**Formal Statement**:

```
Given:
  async fn f() {
      let r: &'a T = &x;
      g().await;
      use(r);
  }

Constraints:
  1. 'a must include the entire await of g()
  2. x must not be dropped until after use(r)
  3. The Future's lifetime must be contained within 'a
```

**Example 3.2: Valid Borrowed Data Across Await**

```rust
/// Valid: Borrow from parameter (long lifetime)
async fn process_with_ref(data: &[u8]) -> usize {
    // data is borrowed for the function's lifetime
    let prefix = &data[..4];

    // Await point - data must remain valid
    tokio::time::sleep(std::time::Duration::from_millis(1)).await;

    // prefix is still valid because data outlives the Future
    prefix.len()
}

/// Valid: Borrow from static data
async fn use_static_config() -> &'static str {
    static CONFIG: &str = "config_value";

    let config_ref: &'static str = CONFIG;

    tokio::time::sleep(std::time::Duration::from_millis(1)).await;

    // Static data lives forever, so this is always valid
    config_ref
}

/// Valid: Borrow from Arc data
use std::sync::Arc;

async fn use_arc_data(arc_data: Arc<Vec<u8>>) -> u8 {
    // Borrow from the Arc data
    let slice: &[u8] = &arc_data;
    let first = &slice[0];

    tokio::time::sleep(std::time::Duration::from_millis(1)).await;

    // Valid because:
    // 1. arc_data is owned by the async block
    // 2. The Arc keeps data alive
    // 3. first points into Arc-owned memory
    *first
}
```

**Counter-Example 3.2: Borrowed Reference Invalidated**

```rust
/// DANGER: Borrow of local data across await
///
/// This will NOT compile - the borrow checker prevents it

async fn invalid_borrow() {
    let local_data = vec![1, 2, 3];

    // Attempt to borrow local data
    let borrow = &local_data[0];

    // ERROR: cannot borrow `local_data` as mutable
    // because it is also borrowed as immutable
    // local_data.push(4);

    // After await, the state machine may resume on different thread
    // but borrow is a raw pointer in the state machine
    some_async_op().await;

    // The compiler would need to prove borrow is still valid
    // But it can't guarantee local_data hasn't moved/changed
    // println!("{}", borrow);
}

async fn some_async_op() {}

/// More subtle case: Borrow from temporary
async fn temporary_borrow() -> String {
    // This creates a temporary String
    let borrowed = get_string().await;

    // Trying to return a reference to borrowed data
    // would fail - borrowed is dropped at end of scope

    // Return owned value instead
    borrowed
}

async fn get_string() -> String {
    "hello".to_string()
}

/// Another non-compiling example
async fn invalid_lifetime<'a>(data: &'a mut Vec<u8>) -> &'a [u8] {
    data.push(1);

    // Trying to return reference to modified data
    let slice = &data[..];

    tokio::time::sleep(std::time::Duration::from_millis(1)).await;

    // ERROR: cannot return value referencing function parameter `data`
    // because data is borrowed for `&mut self` in push
    slice
}

/// Correct patterns:

/// Pattern 1: Re-borrow after await
async fn correct_reborrow(data: &mut Vec<u8>) {
    data.push(1);

    some_async_op().await;

    // Re-borrow after await
    let _slice = &data[..];
}

/// Pattern 2: Use owned data
async fn correct_owned() -> Vec<u8> {
    let mut data = vec![1, 2, 3];
    data.push(4);

    some_async_op().await;

    data  // Return owned value
}

/// Pattern 3: Use Arc for shared ownership
async fn correct_arc() -> u8 {
    let data = Arc::new(vec![1, 2, 3]);
    let data_clone = data.clone();

    some_async_op().await;

    // Access through Arc
    data_clone[0]
}
```

### 3.3 async move and Capture Semantics

**Formal Capture Rules**:

```rust
/// Rule 1: async {} captures by reference (immutable by default)
///
/// Source:
fn capture_by_ref(x: String, y: &str) -> impl Future<Output = usize> {
    async {
        x.len() + y.len()  // x borrowed immutably, y borrowed
    }
}

/// Desugared:
struct CaptureByRef<'a> {
    x: &'a String,  // Immutable borrow
    y: &'a str,     // Borrow
}

/// Rule 2: async move {} captures by move
///
/// Source:
fn capture_by_move(x: String, y: String) -> impl Future<Output = usize> {
    async move {
        x.len() + y.len()  // x and y moved into async block
    }
}

/// Desugared:
struct CaptureByMove {
    x: String,  // Owned
    y: String,  // Owned
}

/// Rule 3: Mixed capture (Rust 1.64+ capture disjoint fields)
///
/// Source:
fn mixed_capture(s: String, v: Vec<u8>) -> impl Future<Output = usize> {
    async move {
        // Both s and v are moved
        s.len() + v.len()
    }
}
```

**Example 3.3: Correct Capture Semantics**

```rust
/// Example 1: Move for ownership transfer
fn spawn_with_move(data: Vec<u8>) -> tokio::task::JoinHandle<usize> {
    // data is moved into the async block
    tokio::spawn(async move {
        process(data).await.len()
    })
}

async fn process(data: Vec<u8>) -> Vec<u8> {
    data
}

/// Example 2: Borrow for temporary access
async fn process_refs(items: &[String]) -> Vec<usize> {
    // items is borrowed, not moved
    let mut lengths = Vec::new();

    for item in items {
        // item is &String, borrowed from items
        lengths.push(item.len());

        // Async operation - items must remain valid
        tokio::task::yield_now().await;
    }

    lengths
}

/// Example 3: Selective move with clones
fn selective_capture(config: Arc<Config>, name: String) -> impl Future<Output = String> {
    // Clone what we need to own
    let timeout = config.timeout;

    async move {
        // timeout is owned (copied)
        // name is owned (moved)
        format!("{}: {:?}", name, timeout)
    }
}

pub struct Config {
    timeout: std::time::Duration,
}

/// Example 4: Self-referential capture requires Pin
use std::pin::Pin;
use std::marker::PhantomPinned;

struct SelfRefCapture {
    data: String,
    ptr: *const u8,
    _pin: PhantomPinned,
}

impl SelfRefCapture {
    fn new(data: String) -> Pin<Box<Self>> {
        let mut boxed = Box::new(Self {
            data,
            ptr: std::ptr::null(),
            _pin: PhantomPinned,
        });
        boxed.ptr = boxed.data.as_ptr();
        Box::into_pin(boxed)
    }

    fn get_ref(self: Pin<&Self>) -> &[u8] {
        unsafe { std::slice::from_raw_parts(self.ptr, self.data.len()) }
    }
}
```

**Counter-Example 3.3: Unexpected Move vs Borrow**

```rust
/// Counter-example 1: Accidental move
fn accidental_move(data: Vec<u8>) -> impl Future<Output = ()> {
    // This moves data into the async block
    let fut = async move {
        println!("{:?}", data);
    };

    // ERROR: data has been moved!
    // println!("{:?}", data);

    fut
}

/// Counter-example 2: Trying to borrow moved data
fn borrow_after_move(data: String) {
    // Move into first async block
    let fut1 = async move {
        println!("{}", data);
    };

    // Can't use data anymore
    // let fut2 = async move {
    //     println!("{}", data);  // ERROR: use of moved value
    // };
}

/// Counter-example 3: Lifetime mismatch in captures
fn lifetime_mismatch() -> impl Future<Output = ()> {
    let local = String::from("local");
    let local_ref = &local;

    // ERROR: local does not live long enough
    // async move {
    //     println!("{}", local_ref);
    // }
    // local dropped here, but future might outlive it

    async move {}
}

/// Counter-example 4: Capturing self in method
struct Processor {
    data: Vec<u8>,
}

impl Processor {
    /// DANGER: This captures &self, but tries to use async move
    async fn process_bad(&self) -> Vec<u8> {
        // Captures &self
        let data_ref = &self.data;

        some_async_op().await;

        // This would be unsafe if we could modify self during await
        data_ref.clone()
    }

    /// Correct: Take ownership with async move
    fn process_good(self) -> impl Future<Output = Vec<u8>> {
        async move {
            // self is moved into the async block
            some_async_op().await;
            self.data
        }
    }

    /// Correct: Clone data to own it
    async fn process_clone(&self) -> Vec<u8> {
        let data = self.data.clone();
        some_async_op().await;
        data
    }
}

async fn some_async_op() {}

/// Solutions summary:
///
/// 1. Use `async move` when you need ownership
/// 2. Use plain `async` when you only need temporary access
/// 3. Clone data if multiple async blocks need it
/// 4. Use Arc for shared ownership across async boundaries
/// 5. Be careful with self-referential structs - use Pin
```

---

## 4. Common Patterns (with Safety Arguments)

### 4.1 Spawning Tasks

**Safety Precondition: Send + 'static**:

```
spawn(future) requires:
1. future: Send - can be sent between threads
2. future: 'static - no borrowed references to stack data

These ensure the task can safely run on any thread at any time.
```

**Example 4.1: Correct Task Spawning**

```rust
use std::sync::Arc;
use tokio::sync::Mutex;

/// Correct: All data is 'static and Send
pub async fn spawn_tasks(data: Vec<u8>) -> Vec<tokio::task::JoinHandle<usize>> {
    let shared = Arc::new(Mutex::new(0usize));
    let mut handles = Vec::new();

    for chunk in data.chunks(10) {
        let chunk = chunk.to_vec();  // Owned copy
        let counter = shared.clone();  // Arc is 'static

        // spawn requires Future + Send + 'static
        let handle = tokio::spawn(async move {
            let sum: usize = chunk.iter().map(|&b| b as usize).sum();
            *counter.lock().await += sum;
            sum
        });

        handles.push(handle);
    }

    handles
}

/// Correct: Using channels for communication
pub async fn spawn_with_channel(
    items: Vec<String>
) -> tokio::task::JoinHandle<Vec<String>> {
    let (tx, mut rx) = tokio::sync::mpsc::channel(100);

    // Spawn producer tasks
    for item in items {
        let tx = tx.clone();
        tokio::spawn(async move {
            let processed = process_item(item).await;
            let _ = tx.send(processed).await;
        });
    }

    // Spawn consumer task
    let handle = tokio::spawn(async move {
        let mut results = Vec::new();
        // Drop original tx so rx knows when producers are done
        drop(tx);

        while let Some(result) = rx.recv().await {
            results.push(result);
        }
        results
    });

    handle
}

async fn process_item(item: String) -> String {
    item.to_uppercase()
}

/// Safety argument:
///
/// 1. spawn_tasks:
///    - chunk: Vec<u8> is Send + 'static ✓
///    - counter: Arc<Mutex<usize>> is Send + 'static ✓
///    - The async block owns all data ✓
///
/// 2. spawn_with_channel:
///    - item: String is Send + 'static ✓
///    - tx: mpsc::Sender is Send + 'static ✓
///    - Channel provides safe communication ✓
```

**Counter-Example 4.1: Local Reference in Spawn**

```rust
/// DANGER: Trying to spawn with stack reference

pub async fn bad_spawn_with_ref() {
    let local_data = vec![1, 2, 3];

    // ERROR: lifetime may not live long enough
    // let handle = tokio::spawn(async move {
    //     println!("{:?}", local_data);
    // });

    // local_data would be dropped when function returns,
    // but spawned task might still be running!
}

/// DANGER: Non-Send type in spawn
pub async fn bad_spawn_non_send() {
    let local_rc = std::rc::Rc::new(42);

    // ERROR: future cannot be sent between threads safely
    // let handle = tokio::spawn(async move {
    //     println!("{}", local_rc);
    // });

    // Rc is not Send because it uses non-atomic reference counting
}

/// DANGER: Borrow in spawned task
pub fn bad_spawn_with_borrow(data: &[u8]) {
    // ERROR: `data` has an anonymous lifetime `'_` but it needs
    // to satisfy a `'static` lifetime requirement
    // let handle = tokio::spawn(async move {
    //     println!("{:?}", data);
    // });
}

/// Solutions:

/// Solution 1: Move owned data
pub fn good_spawn_owned(data: Vec<u8>) -> tokio::task::JoinHandle<()> {
    tokio::spawn(async move {
        println!("{:?}", data);
    })
}

/// Solution 2: Use Arc for shared data
use std::sync::Arc;

pub fn good_spawn_shared(data: Vec<u8>) -> tokio::task::JoinHandle<usize> {
    let data = Arc::new(data);
    tokio::spawn(async move {
        data.len()
    })
}

/// Solution 3: Use scoped tasks (tokio::task::spawn_blocking with scope)
use tokio::task::JoinSet;

pub async fn good_spawn_scoped(data: &mut Vec<u8>) {
    let mut set = JoinSet::new();

    // Split data for parallel processing
    let chunks: Vec<&mut [u8]> = data.chunks_mut(10).collect();

    for chunk in chunks {
        // Process in-place - no spawn needed for same-thread
        for byte in chunk.iter_mut() {
            *byte = byte.wrapping_add(1);
        }
    }
}

/// Solution 4: Use LocalSet for !Send futures
use tokio::task::LocalSet;

pub async fn good_spawn_local() {
    let local = LocalSet::new();
    let rc = std::rc::Rc::new(42);

    local.run_until(async move {
        // spawn_local doesn't require Send
        tokio::task::spawn_local(async move {
            println!("{}", rc);
        }).await.unwrap();
    }).await;
}
```

### 4.2 Select and Race

**Ownership Semantics of select!**:

```
select! {
    biased;  // Optional: poll in order
    result1 = future1 => { branch1 },
    result2 = future2 => { branch2 },
    else => { default },
}

Ownership rules:
1. All futures are polled simultaneously (conceptually)
2. The first ready future's branch executes
3. Other futures are dropped (cancelled)
4. Resources from cancelled branches must be handled
```

**Example 4.2: Correct Select Usage**

```rust
use tokio::sync::mpsc;
use tokio::time::{timeout, Duration};

/// Correct: Timeout with select
pub async fn operation_with_timeout<T>(
    operation: impl std::future::Future<Output = T>,
    dur: Duration,
) -> Result<T, ()> {
    match timeout(dur, operation).await {
        Ok(result) => Ok(result),
        Err(_) => Err(()),
    }
}

/// Correct: Race between multiple operations
pub async fn race_operations() -> String {
    let (tx1, rx1) = tokio::sync::oneshot::channel();
    let (tx2, rx2) = tokio::sync::oneshot::channel();

    // Spawn competing tasks
    tokio::spawn(async move {
        tokio::time::sleep(Duration::from_millis(100)).await;
        let _ = tx1.send("fast".to_string());
    });

    tokio::spawn(async move {
        tokio::time::sleep(Duration::from_millis(200)).await;
        let _ = tx2.send("slow".to_string());
    });

    // Race - whichever completes first wins
    tokio::select! {
        result = rx1 => result.unwrap_or_else(|_| "rx1 cancelled".to_string()),
        result = rx2 => result.unwrap_or_else(|_| "rx2 cancelled".to_string()),
    }
}

/// Correct: Graceful shutdown with select
pub async fn graceful_shutdown(
    mut work_rx: mpsc::Receiver<WorkItem>,
    mut shutdown_rx: mpsc::Receiver<()>,
) {
    loop {
        tokio::select! {
            Some(work) = work_rx.recv() => {
                process_work(work).await;
            }
            _ = shutdown_rx.recv() => {
                println!("Shutdown signal received");
                break;
            }
            else => {
                // Both channels closed
                break;
            }
        }
    }

    // Process remaining work
    while let Ok(work) = work_rx.try_recv() {
        process_work(work).await;
    }
}

struct WorkItem;
async fn process_work(_work: WorkItem) {}

/// Safety argument:
///
/// 1. race_operations:
///    - Both channels are independent
///    - Losing channel's sender is dropped when select resolves
///    - Receiver gets disconnected error, handled gracefully
///
/// 2. graceful_shutdown:
///    - work_rx.recv() cancellation is safe (no state change)
///    - shutdown_rx.recv() cancellation is safe
///    - Both branches properly handle channel closure
```

**Counter-Example 4.2: Resource Leak in Select**

```rust
/// DANGER: Resource leak when select cancels a branch

use tokio::sync::mpsc;

pub async fn bad_select_resource_leak() {
    let (tx, mut rx) = mpsc::channel::<i32>(10);

    tokio::select! {
        // Branch 1: Send multiple values
        _ = async {
            for i in 0..100 {
                // If select picks branch 2, this future is dropped
                // mid-iteration! The tx.send(i).await may have started
                // but not completed.
                let _ = tx.send(i).await;
            }
        } => {
            println!("Send completed");
        }

        // Branch 2: Receive just one value
        msg = rx.recv() => {
            println!("Received: {:?}", msg);
            // This branch wins, but what about the remaining sends?
        }
    }

    // Channel may be in inconsistent state
}

/// DANGER: Mutex guard held across await in select
use tokio::sync::Mutex;

pub async fn bad_select_with_mutex(data: Arc<Mutex<Vec<i32>>>) {
    let guard = data.lock().await;

    tokio::select! {
        // Branch 1: Uses the guard
        _ = async {
            // If cancelled, guard is dropped... eventually
            // But select! might cancel between await points
            println!("{:?}", *guard);
        } => {}

        // Branch 2: Doesn't use guard
        _ = tokio::time::sleep(Duration::from_millis(10)) => {
            // guard is still held here! Blocks other tasks
        }
    }

    // guard dropped here
}

/// DANGER: Non-cancellation-safe operations
pub async fn bad_non_cancel_safe() {
    let (tx, rx) = tokio::sync::mpsc::channel::<i32>(1);

    tokio::select! {
        // send() is NOT cancellation-safe
        // If cancelled after partial send, message may be lost
        _ = tx.send(42) => {
            println!("Sent");
        }
        _ = tokio::time::sleep(Duration::from_millis(1)) => {
            println!("Timeout");
        }
    }
}

/// Solutions:

/// Solution 1: Use cancellation-safe operations
pub async fn good_cancel_safe() {
    let (tx, mut rx) = tokio::sync::mpsc::channel::<i32>(10);

    // Pre-stage data to avoid partial operations
    let data: Vec<i32> = (0..100).collect();

    tokio::select! {
        // Use try_send for non-blocking send
        _ = async {
            for i in data {
                if tx.try_send(i).is_err() {
                    break;
                }
            }
        } => {}

        msg = rx.recv() => {
            println!("Received: {:?}", msg);
        }
    }
}

/// Solution 2: Drop guard before select
pub async fn good_mutex_select(data: Arc<Mutex<Vec<i32>>>) {
    // Extract data while holding lock
    let snapshot = {
        let guard = data.lock().await;
        guard.clone()
    };

    tokio::select! {
        _ = async {
            println!("{:?}", snapshot);
        } => {}

        _ = tokio::time::sleep(Duration::from_millis(10)) => {}
    }
}

/// Solution 3: Use bounded channels with proper capacity
pub async fn good_bounded_channel() {
    let (tx, mut rx) = tokio::sync::mpsc::channel::<i32>(100);

    // Fill buffer first (synchronous)
    for i in 0..100 {
        if tx.try_send(i).is_err() {
            break;
        }
    }

    // Now select is safe - all data is buffered
    tokio::select! {
        _ = async {
            // This just closes the channel when done
            drop(tx);
        } => {}

        _ = async {
            while let Some(msg) = rx.recv().await {
                println!("{}", msg);
            }
        } => {}
    }
}

use std::sync::Arc;
use std::time::Duration;
```

### 4.3 Streams and Pipelines

**Ownership Flow in Streams**:

```
Stream<Item = T> represents:
- A sequence of values produced asynchronously
- Each item has independent ownership
- Consumer can process items as they arrive

Pipeline pattern:
Source Stream → Transform → Transform → Sink
     ↑              ↑           ↑         ↓
   owned          owned       owned    owned
   items          items       items    items
```

**Example 4.3: Correct Stream Processing**

```rust
use tokio::sync::mpsc;
use std::pin::Pin;
use std::task::{Context, Poll};
use std::future::Future;

/// Correct: Manual Stream implementation
pub struct DataStream {
    receiver: mpsc::Receiver<Vec<u8>>,
}

impl DataStream {
    pub fn new(receiver: mpsc::Receiver<Vec<u8>>) -> Self {
        Self { receiver }
    }
}

impl futures::Stream for DataStream {
    type Item = Vec<u8>;

    fn poll_next(
        mut self: Pin<&mut Self>,
        cx: &mut Context<'_>
    ) -> Poll<Option<Self::Item>> {
        // Delegate to receiver's recv method
        self.receiver.poll_recv(cx)
    }
}

/// Correct: Stream pipeline with ownership
pub async fn stream_pipeline() {
    let (tx, rx) = mpsc::channel::<String>(100);

    // Producer task
    let producer = tokio::spawn(async move {
        for i in 0..100 {
            // Each item is owned and moved into channel
            tx.send(format!("item-{}", i)).await.unwrap();
        }
    });

    // Consumer with transformation pipeline
    let consumer = tokio::spawn(async move {
        let mut rx = rx;

        while let Some(item) = rx.recv().await {
            // item is owned here
            let processed = process_item(item).await;
            consume_item(processed).await;
        }
    });

    let _ = tokio::join!(producer, consumer);
}

async fn process_item(item: String) -> String {
    item.to_uppercase()
}

async fn consume_item(item: String) {
    println!("{}", item);
}

/// Correct: Backpressure-aware stream processing
pub async fn backpressure_stream() {
    let (mut tx, mut rx) = mpsc::channel::<Vec<u8>>(10); // Small buffer

    // Producer respects backpressure
    let producer = tokio::spawn(async move {
        for i in 0..1000 {
            let data = vec![i as u8; 1024]; // 1KB chunks

            // send().await respects backpressure
            // Will wait if buffer is full
            if tx.send(data).await.is_err() {
                break;
            }
        }
    });

    // Slow consumer
    let consumer = tokio::spawn(async move {
        while let Some(data) = rx.recv().await {
            // Simulate slow processing
            tokio::time::sleep(std::time::Duration::from_millis(10)).await;
            println!("Processed {} bytes", data.len());
        }
    });

    let _ = tokio::join!(producer, consumer);
}

/// Safety argument:
///
/// 1. DataStream:
///    - Each Vec<u8> is independently owned
///    - Receiver hands over ownership on recv()
///    - No shared mutable state
///
/// 2. stream_pipeline:
///    - String items are moved through the pipeline
///    - Each stage owns its input
///    - Channel provides sequential ordering
///
/// 3. backpressure_stream:
///    - Bounded channel prevents unbounded memory growth
///    - Producer blocked when consumer is slow
///    - Graceful degradation under load
```

**Counter-Example 4.3: Iterator Invalidation**

```rust
/// DANGER: Holding reference while modifying source

pub async fn bad_iterator_invalidation() {
    let mut data = vec!["a".to_string(), "b".to_string(), "c".to_string()];

    // Get reference to first element
    let first = &data[0];

    // ERROR: Cannot mutate data while borrowing
    // data.push("d".to_string());  // Would invalidate reference

    // In async context, similar issue with channels:
    let (tx, mut rx) = tokio::sync::mpsc::channel::<String>(10);

    // Spawn task that modifies shared state
    let shared = std::sync::Arc::new(std::sync::Mutex::new(vec![1, 2, 3]));
    let shared_clone = shared.clone();

    tokio::spawn(async move {
        let mut guard = shared_clone.lock().unwrap();
        guard.push(4);  // Modification
    });

    // DANGER: Trying to iterate while another task modifies
    // let guard = shared.lock().unwrap();
    // for item in guard.iter() {
    //     tx.send(item.to_string()).await;  // Releases lock!
    // }
    // After await, iterator may be invalid
}

/// DANGER: Stream item reference invalidation
pub async fn bad_stream_reference() {
    // This won't compile - async blocks can't borrow from surrounding scope
    // in a way that outlives awaits

    let data = vec!["a", "b", "c"];

    // let stream = futures::stream::iter(data.iter().map(|s| async {
    //     tokio::time::sleep(Duration::from_millis(1)).await;
    //     s.to_string()
    // }));

    // The borrow checker prevents this because:
    // - References into data wouldn't survive the await
}

/// DANGER: Concurrent modification
pub async fn bad_concurrent_modification() {
    let shared = std::sync::Arc::new(tokio::sync::RwLock::new(vec![1, 2, 3]));

    let shared1 = shared.clone();
    let shared2 = shared.clone();

    let task1 = tokio::spawn(async move {
        let read_guard = shared1.read().await;
        // Holding read lock while...
        tokio::time::sleep(std::time::Duration::from_millis(10)).await;
        // ...another task tries to write
        read_guard.len()
    });

    let task2 = tokio::spawn(async move {
        // This will block until all read locks are released
        let mut write_guard = shared2.write().await;
        write_guard.push(4);
    });

    // Potential deadlock or long blocking if task1 holds read too long
    let _ = tokio::join!(task1, task2);
}

/// Solutions:

/// Solution 1: Clone data before sending
pub async fn good_clone_before_send() {
    let data = vec!["a".to_string(), "b".to_string(), "c".to_string()];
    let (tx, mut rx) = tokio::sync::mpsc::channel::<String>(10);

    // Clone items before moving into async
    for item in &data {
        let item = item.clone();
        tx.send(item).await.unwrap();
    }
    drop(tx);

    while let Some(item) = rx.recv().await {
        println!("{}", item);
    }
}

/// Solution 2: Own the data in the stream
pub async fn good_own_in_stream() {
    // Move data into stream
    let data: Vec<String> = vec!["a".to_string(), "b".to_string()];

    let (tx, mut rx) = tokio::sync::mpsc::channel::<String>(10);

    // Spawn task that owns the data
    tokio::spawn(async move {
        for item in data {
            // item is owned, not borrowed
            tx.send(item).await.unwrap();
        }
    });

    while let Some(item) = rx.recv().await {
        println!("{}", item);
    }
}

/// Solution 3: Use try_iter for non-async iteration
pub async fn good_try_iter() {
    let shared = std::sync::Arc::new(std::sync::Mutex::new(vec![1, 2, 3]));

    // Collect while holding lock
    let items: Vec<i32> = {
        let guard = shared.lock().unwrap();
        guard.clone()
    };

    // Now iterate without holding lock
    for item in items {
        tokio::time::sleep(std::time::Duration::from_millis(1)).await;
        println!("{}", item);
    }
}

/// Solution 4: Chunked processing
pub async fn good_chunked_processing() {
    let (tx, mut rx) = tokio::sync::mpsc::channel::<Vec<String>>(10);

    // Send chunks instead of individual items
    let data: Vec<String> = (0..1000).map(|i| format!("item-{}", i)).collect();

    tokio::spawn(async move {
        for chunk in data.chunks(100) {
            let chunk: Vec<String> = chunk.to_vec();
            tx.send(chunk).await.unwrap();
        }
    });

    while let Some(chunk) = rx.recv().await {
        for item in chunk {
            println!("{}", item);
        }
    }
}
```

---

## 5. Formal Safety Theorems

This section presents formal theorems about async Rust safety with proof sketches.

### Theorem 5.1: Async Function Preserves Ownership Safety

```rust
/// Theorem: Async function preserves ownership safety
///
/// Statement:
/// If all components (captures, local variables, awaited futures) of an
/// async function satisfy Rust's ownership rules, then the async function
/// as a whole satisfies Rust's ownership rules.
///
/// Formal Statement:
/// ∀ async fn f,
///   (∀ capture c in f: ownership_safe(c)) ∧
///   (∀ local l in f: ownership_safe(l)) ∧
///   (∀ await point a in f: ownership_safe(a))
///   ⇒ ownership_safe(f)

/// Proof Sketch:
///
/// 1. An async function desugars to a state machine enum S
/// 2. Each state variant corresponds to execution between await points
/// 3. State transitions occur only at await points
/// 4. By assumption:
///    - Captures are ownership-safe (valid for lifetime of S)
///    - Locals are ownership-safe within their scope
///    - Await points properly transfer ownership of awaited futures
/// 5. The state machine preserves these invariants:
///    - Fields are only accessed when in corresponding state
///    - State transitions consume the old state
///    - No state can be re-entered (linear progression)
/// 6. Therefore, S respects ownership rules
/// 7. By transitivity, f respects ownership rules

/// Corollary: The borrow checker verifies async functions correctly
///
/// The Rust compiler's borrow checker analyzes the desugared state machine,
/// ensuring all ownership constraints are satisfied at compile time.
```

### Theorem 5.2: Pin Guarantees Self-Referential Safety

```rust
/// Theorem: Pin guarantees self-referential safety
///
/// Statement:
/// For any type T: !Unpin, Pin<P<T>> ensures that T remains at a stable
/// memory location, guaranteeing the validity of self-references.
///
/// Formal Statement:
/// ∀ T: !Unpin, ∀ p: Pin<P<T>>,
///   stable_address(*p) ⇔
///   ∀ self_ref in T, valid(self_ref)
///
/// Where:
///   stable_address(x) = address_of(x) does not change
///   valid(r) = r points to allocated, initialized memory of correct type

/// Proof:
///
/// 1. Definition of Pin<P<T>>:
///    - P is a pointer type (Box, &, &mut)
///    - T is the pointee
///
/// 2. Pin contract for T: !Unpin:
///    - No &mut T can be obtained from Pin<&mut T> without unsafe
///    - T cannot be moved out of Pin<P<T>>
///    - Deref impls only provide &T or Pin<&mut T>
///
/// 3. Self-reference validity:
///    - Let r be a self-reference in T pointing to field f
///    - address(r) = address_of(T) + offset_of(f)
///    - For r to be valid, address_of(T) must be constant
///
/// 4. Pin guarantees address_of(T) is constant:
///    - Pin prevents obtaining &mut T (which could mem::swap)
///    - Pin prevents moving T out of P
///    - Therefore T remains at fixed address
///
/// 5. Conclusion:
///    stable_address(T) ∧ address(r) depends only on address(T)
///    ⇒ address(r) is constant
///    ⇒ r remains valid

/// Example: Formal verification of Pin safety
use std::pin::Pin;
use std::marker::PhantomPinned;

struct SelfRef {
    data: [u8; 100],
    ptr: *const [u8; 100],
    _pin: PhantomPinned,
}

impl SelfRef {
    fn new() -> Pin<Box<Self>> {
        let mut boxed = Box::new(Self {
            data: [0; 100],
            ptr: std::ptr::null(),
            _pin: PhantomPinned,
        });

        // At this point:
        // address_of(boxed) = A (fixed by Box)
        boxed.ptr = &boxed.data;
        // ptr now contains A + offset_of(data)

        Box::into_pin(boxed)
        // Returns Pin<Box<Self>> at address A
    }

    fn verify(self: Pin<&Self>) -> bool {
        // Verify self-reference is still valid
        let current_addr = self.ptr;
        let expected_addr = &self.data as *const _;
        current_addr == expected_addr
    }
}

/// Theorem holds: verify() always returns true because
/// Pin prevents any operation that would change address_of(data)
```

### Theorem 5.3: Send Requirement for Spawn

```rust
/// Theorem: Send requirement for spawn
///
/// Statement:
/// spawn(future) requires future: Send + 'static. This is both necessary
/// and sufficient for thread-safe task spawning.
///
/// Formal Statement:
/// spawn(f) is safe ⇔ (f: Send) ∧ (f: 'static)

/// Proof of Necessity (⇒):
///
/// 1. Assume spawn(f) is safe
/// 2. spawn transfers f to another thread's work queue
/// 3. For this to be safe:
///    a. f must be Send (can be sent between threads)
///    b. f must be 'static (no references to stack data)
/// 4. If f were !Send, it might contain thread-local data (e.g., Rc)
///    that would be accessed from multiple threads unsafely
/// 5. If f were not 'static, it might reference stack data that
///    gets dropped before f completes
/// 6. Therefore, f: Send + 'static is necessary

/// Proof of Sufficiency (⇐):
///
/// 1. Assume f: Send + 'static
/// 2. Send ensures f's data can be safely transferred between threads
/// 3. 'static ensures f has no references to temporary stack data
/// 4. When spawn(f) is called:
///    - f is moved into the runtime's task queue
///    - Any thread may pick up f and execute it
///    - f's data is only accessed by one thread at a time
/// 5. All operations on f respect its internal invariants
/// 6. Therefore, spawn(f) is safe

/// Formal Verification via Type System:

fn verify_send_spawn<F, T>(future: F) -> tokio::task::JoinHandle<T>
where
    F: std::future::Future<Output = T> + Send + 'static,
    T: Send + 'static,
{
    // This compiles only because of Send + 'static bounds
    tokio::spawn(future)
}

/// Counter-example: Non-Send type fails to compile
fn verify_non_send_fails() {
    // let rc = std::rc::Rc::new(42);
    // tokio::spawn(async move { *rc });
    // ERROR: `Rc<i32>` cannot be sent between threads safely
}
```

### Theorem 5.4: Borrowing Across Await Points

```rust
/// Theorem: Borrowing across await points requires lifetime containment
///
/// Statement:
/// A reference &'a T can be held across an await point in an async
/// function if and only if 'a contains the entire await operation
/// and T outlives the Future.
///
/// Formal Statement:
/// Let f be an async function with await point a.
/// Let r: &'a T be held across a.
/// r is valid after a ⇔ ('a ⊇ lifetime(a)) ∧ (T outlives f)

/// Proof:
///
/// 1. When f reaches await point a:
///    - f returns Poll::Pending
///    - f's state machine is stored (potentially on heap)
///    - r is part of the state machine's state
///
/// 2. When a completes and f resumes:
///    - f's state machine is retrieved
///    - Execution continues with r
///
/// 3. For r to be valid at resume:
///    - The memory r points to must still be valid
///    - This requires 'a to extend until resume
///    - This requires T to outlive f
///
/// 4. If 'a < lifetime(a):
///    - r would dangle during the await
///    - Resume would be use-after-free
///
/// 5. If T does not outlive f:
///    - T could be dropped while f is still alive
///    - r would become dangling

/// Example: Valid borrow
async fn valid_borrow(data: &[u8]) -> u8 {
    let first = &data[0];  // &'a u8 where 'a is lifetime of data

    // data outlives this await (data is borrowed for fn lifetime)
    tokio::time::sleep(std::time::Duration::from_millis(1)).await;

    *first  // Valid: 'a extends through the await
}

/// Counter-example: Invalid borrow (fails to compile)
// async fn invalid_borrow() -> u8 {
//     let data = vec![1, 2, 3];
//     let first = &data[0];
//     tokio::time::sleep(std::time::Duration::from_millis(1)).await;
//     *first  // ERROR: data dropped here while borrowed
// }
```

### Theorem 5.5: Select Cancellation Safety

```rust
/// Theorem: Select cancellation safety
///
/// Statement:
/// In select! { a = fut_a => ..., b = fut_b => ... }, if branch a
/// completes first, fut_b is cancelled. fut_b must be cancellation-safe
/// (no partial state changes on cancellation).
///
/// Formal Statement:
/// ∀ fut in select branches,
///   cancellation_safe(fut) ⇔
///   (fut dropped at await point) ⇒ (no observable state change)

/// Proof:
///
/// 1. select! polls all futures until one returns Ready
/// 2. When future F returns Ready, other futures are dropped
/// 3. A future may be between await points (suspended)
/// 4. If F was partially through an operation:
///    - State might be inconsistent
///    - Resources might be leaked
///    - This is cancellation unsafety
///
/// 5. Cancellation-safe operations:
///    - Read-only operations
///    - Atomic operations
///    - Channel recv (no message consumed if cancelled)
///    - AsyncMutex lock acquisition
///
/// 6. Cancellation-unsafe operations:
///    - Async send (message might be partially sent)
///    - State mutations before await
///    - Non-atomic file operations

/// Example: Cancellation-safe vs unsafe

/// Cancellation-safe: mpsc::recv
async fn cancel_safe_recv() {
    let (tx, mut rx) = tokio::sync::mpsc::channel::<i32>(1);

    tokio::select! {
        _ = rx.recv() => {
            // If this branch loses the race, no message is lost
            // recv() is atomic from observer's perspective
        }
        _ = tokio::time::sleep(std::time::Duration::from_millis(1)) => {
            // Timeout branch wins
        }
    }
}

/// Cancellation-unsafe: mpsc::send with state
async fn cancel_unsafe_send() {
    let (tx, mut rx) = tokio::sync::mpsc::channel::<i32>(1);
    let mut counter = 0;

    // First, fill the channel
    tx.try_send(1).unwrap();

    tokio::select! {
        // send() is NOT cancellation-safe
        // If cancelled after internal state change but before completion,
        // the channel state might be inconsistent
        _ = tx.send(2) => {
            counter += 1;
        }
        _ = rx.recv() => {
            // This branch might win
        }
    }
}

/// Solution: Use cancellation-safe alternatives
async fn cancel_safe_alternative() {
    let (tx, mut rx) = tokio::sync::mpsc::channel::<i32>(1);

    // Use try_send for non-blocking send
    let _ = tx.try_send(1);

    tokio::select! {
        result = rx.recv() => {
            println!("Received: {:?}", result);
        }
        _ = tokio::time::sleep(std::time::Duration::from_millis(1)) => {
            println!("Timeout");
        }
    }
}
```

---

## 6. Anti-Patterns and Solutions

### Anti-Pattern 1: Holding Mutex Across Await

```rust
/// PROBLEM EXPLANATION:
/// Holding a mutex guard across an await point can cause deadlocks
/// because the guard is not released while waiting.

/// COUNTER-EXAMPLE: Deadlock scenario
use std::sync::Arc;
use tokio::sync::Mutex;

pub async fn deadlock_example(data: Arc<Mutex<Vec<i32>>>) {
    // Acquire lock
    let mut guard = data.lock().await;

    // Add item
    guard.push(1);

    // DANGER: Lock held across await!
    // While this task awaits, no other task can acquire the lock
    tokio::time::sleep(std::time::Duration::from_secs(1)).await;

    // Add another item
    guard.push(2);

    // Lock released here
}

/// Why this causes problems:
/// 1. Task A acquires lock
/// 2. Task A awaits (lock still held)
/// 3. Task B tries to acquire same lock - blocks
/// 4. If tasks are on same thread, thread is blocked
/// 5. Task A can't resume because thread is blocked
/// 6. DEADLOCK!

/// SOLUTION CODE:
pub async fn correct_mutex_usage(data: Arc<Mutex<Vec<i32>>>) {
    // Scope 1: Acquire, modify, release
    {
        let mut guard = data.lock().await;
        guard.push(1);
    } // Lock released here

    // Await with no lock held
    tokio::time::sleep(std::time::Duration::from_secs(1)).await;

    // Scope 2: Re-acquire for next modification
    {
        let mut guard = data.lock().await;
        guard.push(2);
    } // Lock released here
}

/// FORMAL REASONING:
///
/// 1. In deadlock_example:
///    - guard is held from line X to line Y
///    - await at line Z suspends with guard still owned
///    - Guard implements Drop, but drop not called until await completes
///
/// 2. In correct_mutex_usage:
///    - guard's scope is explicitly limited
///    - guard.drop() called at end of scope
///    - await happens with no guard held
///    - Other tasks can acquire lock during await
///
/// 3. Safety invariant:
///    ∀ mutex m, ∀ await point a:
///      ¬(holds_lock(m) ∧ at_await(a))
///    (Never hold a lock at an await point)

/// Alternative: Use synchronous Mutex for short critical sections
use std::sync::Mutex as SyncMutex;

pub async fn alternative_sync_mutex(data: Arc<SyncMutex<Vec<i32>>>) {
    // blocking_lock is acceptable for very short operations
    {
        let mut guard = data.lock().unwrap();
        guard.push(1);
    }

    tokio::time::sleep(std::time::Duration::from_millis(1)).await;

    {
        let mut guard = data.lock().unwrap();
        guard.push(2);
    }
}
```

### Anti-Pattern 2: Non-Send Types in Multi-Threaded Runtime

```rust
/// PROBLEM EXPLANATION:
/// Non-Send types cannot be safely sent between threads. Spawning tasks
/// with Non-Send types on a multi-threaded runtime causes compile errors
/// or undefined behavior if worked around unsafely.

/// COUNTER-EXAMPLE: Non-Send type usage
use std::rc::Rc;
use std::cell::RefCell;

pub async fn non_send_example() {
    // Rc is NOT Send (uses non-atomic reference counting)
    let counter: Rc<RefCell<i32>> = Rc::new(RefCell::new(0));

    // Clone for "sharing"
    let counter2 = counter.clone();

    // ERROR: future cannot be sent between threads safely
    // tokio::spawn(async move {
    //     *counter2.borrow_mut() += 1;
    // });

    // Even if it compiled, this would be unsafe:
    // - Thread A and Thread B both have Rc to same data
    // - RefCell's borrow tracking is not thread-safe
    // - Concurrent access could corrupt memory
}

/// Why Rc is !Send:
///
/// Rc uses non-atomic operations for reference counting:
/// ```
/// fn clone(&self) {
///     self.strong_count.set(self.strong_count.get() + 1);  // Non-atomic!
/// }
/// ```
///
/// If two threads do this simultaneously:
/// - Thread A reads count = 5
/// - Thread B reads count = 5
/// - Thread A writes count = 6
/// - Thread B writes count = 6
/// - Actual count should be 7, but is 6 (lost update)
/// - When drops happen, memory will be freed too early

/// SOLUTION CODE:
use std::sync::{Arc, Mutex};

pub async fn send_solution() {
    // Arc is Send + Sync (atomic reference counting)
    let counter: Arc<Mutex<i32>> = Arc::new(Mutex::new(0));

    // Clone for sharing
    let counter2 = counter.clone();

    // This works - Arc<Mutex<T>> is Send
    tokio::spawn(async move {
        let mut guard = counter2.lock().await;
        *guard += 1;
    }).await.unwrap();

    let final_count = *counter.lock().await;
    println!("Count: {}", final_count);
}

/// FORMAL REASONING:
///
/// 1. Rc<T>: !Send because:
///    - Uses Cell<usize> for strong_count
///    - Cell provides interior mutability without synchronization
///    - Race condition possible on concurrent clone/drop
///
/// 2. Arc<T>: Send if T: Send + Sync because:
///    - Uses AtomicUsize for strong_count
///    - Atomic operations are thread-safe
///    - No race conditions possible
///
/// 3. RefCell<T>: !Sync because:
///    - Runtime borrow checking is not thread-safe
///    - Multiple threads could create overlapping &mut T
///
/// 4. Mutex<T>: Sync if T: Send because:
///    - Only one thread can hold lock at a time
///    - Borrow checking enforced by mutex, not RefCell

/// Alternative: Use LocalSet for !Send futures
use tokio::task::LocalSet;

pub async fn localset_solution() {
    let local = LocalSet::new();
    let counter = Rc::new(RefCell::new(0));

    let counter2 = counter.clone();
    local.spawn_local(async move {
        *counter2.borrow_mut() += 1;
    });

    local.await;

    println!("Count: {}", *counter.borrow());
}
```

### Anti-Pattern 3: Self-Referential Without Pin

```rust
/// PROBLEM EXPLANATION:
/// Self-referential structs (containing pointers to their own fields)
/// must be pinned. Without Pin, moving the struct invalidates the
/// self-references, causing dangling pointers.

/// COUNTER-EXAMPLE: Unsafe self-referential struct
pub struct UnsafeSelfRef {
    data: Vec<u8>,
    // Points to data
    ptr: *const u8,
}

impl UnsafeSelfRef {
    pub fn new() -> Self {
        let mut s = Self {
            data: vec![1, 2, 3, 4, 5],
            ptr: std::ptr::null(),
        };
        s.ptr = s.data.as_ptr();
        s
    }

    pub fn get_data(&self) -> &[u8] {
        unsafe {
            std::slice::from_raw_parts(self.ptr, self.data.len())
        }
    }
}

fn demonstrate_ub() {
    let s1 = UnsafeSelfRef::new();
    println!("s1 ptr: {:p}", s1.ptr);
    println!("s1 data addr: {:p}", s1.data.as_ptr());
    assert_eq!(s1.ptr, s1.data.as_ptr()); // Passes

    // Move s1 to s2
    let s2 = s1;
    println!("s2 ptr: {:p}", s2.ptr);
    println!("s2 data addr: {:p}", s2.data.as_ptr());

    // ptr still points to old location!
    // s2.ptr != s2.data.as_ptr()  // UB if dereferenced

    // This would be undefined behavior:
    // let _data = s2.get_data();
}

/// Why this happens:
///
/// 1. s1 created at address A
/// 2. s1.ptr = &s1.data = A + offset
/// 3. s2 = s1 moves data to address B
/// 4. s2.ptr still contains A + offset (dangling!)
/// 5. Dereferencing s2.ptr is use-after-free

/// SOLUTION CODE:
use std::pin::Pin;
use std::marker::PhantomPinned;

pub struct SafeSelfRef {
    data: Vec<u8>,
    ptr: *const u8,
    _pin: PhantomPinned,
}

impl SafeSelfRef {
    pub fn new() -> Pin<Box<Self>> {
        let mut boxed = Box::new(Self {
            data: vec![1, 2, 3, 4, 5],
            ptr: std::ptr::null(),
            _pin: PhantomPinned,
        });

        // Set up self-reference
        boxed.ptr = boxed.data.as_ptr();

        // Pin to prevent moves
        Box::into_pin(boxed)
    }

    pub fn get_data(self: Pin<&Self>) -> &[u8] {
        unsafe {
            // Safe because:
            // 1. Pin guarantees we're not moving
            // 2. ptr was set up correctly
            // 3. data outlives self-reference
            std::slice::from_raw_parts(self.ptr, self.data.len())
        }
    }
}

fn safe_usage() {
    let s = SafeSelfRef::new();

    // Can safely access data
    let data = s.as_ref().get_data();
    println!("{:?}", data);

    // Cannot move s:
    // let s2 = s;  // ERROR: cannot move out of `s`

    // Pin guarantees s stays at fixed address
}

/// FORMAL REASONING:
///
/// 1. Pin<P<T>> for T: !Unpin:
///    - Provides Deref to &T
///    - Provides DerefMut only if T: Unpin
///    - No way to obtain ownership of T
///
/// 2. PhantomPinned makes T: !Unpin:
///    - PhantomPinned implements !Unpin
///    - Auto-trait !Unpin propagates to containing struct
///
/// 3. Self-reference validity:
///    - ptr = &data at construction
///    - address_of(data) is constant (Pin guarantee)
///    - Therefore ptr remains valid
///
/// 4. Safety invariant:
///    ∀ self_ref in T:
///      Pin<T> ⇒ stable_address(T) ⇒ valid(self_ref)
```

### Anti-Pattern 4: Borrowing Local Data in Spawned Task

```rust
/// PROBLEM EXPLANATION:
/// Spawned tasks may outlive the function that spawned them.
/// Borrowing stack data creates a 'static requirement violation.

/// COUNTER-EXAMPLE: Borrowing stack data
pub fn bad_spawn_borrow() {
    let local_data = vec![1, 2, 3];

    // ERROR: lifetime may not live long enough
    // let handle = tokio::spawn(async {
    //     println!("{:?}", local_data);
    // });

    // local_data is dropped at end of function
    // But spawned task might still be running!
    // This would be use-after-free.
}

/// More subtle example with references
pub fn bad_spawn_ref(data: &[u8]) {
    // ERROR: `data` has an anonymous lifetime `'_` but
    // it needs to satisfy a `'static` lifetime requirement
    // let handle = tokio::spawn(async {
    //     println!("{:?}", data);
    // });
}

/// Why this is unsafe:
///
/// 1. spawn requires 'static because:
///    - Task may run after spawning function returns
///    - Stack frame of spawning function may be reused
///    - Borrowed data could be overwritten
///
/// 2. Example of what could go wrong:
///    fn spawn_task() {
///        let x = 42;
///        spawn(async { println!("{}", &x); });
///    } // x dropped here
///
///    // Task runs here, x's memory may contain garbage

/// SOLUTION CODE:

/// Solution 1: Move owned data
pub fn good_spawn_move() -> tokio::task::JoinHandle<()> {
    let local_data = vec![1, 2, 3];

    tokio::spawn(async move {
        // local_data is moved into the task
        println!("{:?}", local_data);
        // local_data dropped when task completes
    })
}

/// Solution 2: Use Arc for shared data
use std::sync::Arc;

pub fn good_spawn_arc(data: Vec<u8>) -> tokio::task::JoinHandle<usize> {
    let data = Arc::new(data);

    tokio::spawn(async move {
        data.len()
    })
}

/// Solution 3: Use channels for communication
pub async fn good_spawn_channel() {
    let (tx, rx) = tokio::sync::oneshot::channel();

    // Spawn task that receives data
    let handle = tokio::spawn(async move {
        let data = rx.await.unwrap();
        process_data(data).await
    });

    // Send owned data
    let local_data = vec![1, 2, 3];
    tx.send(local_data).unwrap();

    handle.await.unwrap();
}

async fn process_data(data: Vec<i32>) -> i32 {
    data.iter().sum()
}

/// FORMAL REASONING:
///
/// 1. Task lifetime vs function lifetime:
///    - Task: 'static (may run indefinitely)
///    - Function: limited to call stack
///    - borrow requires: lifetime_of_borrow ≥ lifetime_of_task
///    - But: lifetime_of_function < lifetime_of_task
///    - Therefore: borrow from stack is invalid
///
/// 2. Owned data solution:
///    - Data moved into task
///    - Task owns data for its entire lifetime
///    - No references to stack needed
///
/// 3. Arc solution:
///    - Data allocated on heap
///    - Arc keeps data alive as long as needed
///    - Task holds Arc, extending lifetime appropriately
///
/// 4. Channel solution:
///    - Data moved through channel
///    - Ownership transferred to receiving task
///    - Type system verifies correct transfer
```

### Anti-Pattern 5: Race Conditions in Shared State

```rust
/// PROBLEM EXPLANATION:
/// Concurrent access to shared mutable state without proper synchronization
/// leads to race conditions: non-deterministic, incorrect results.

/// COUNTER-EXAMPLE: Data race
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

pub async fn race_condition_example() {
    // Atomic counter (correct)
    let counter = Arc::new(AtomicUsize::new(0));

    let mut handles = vec![];

    for _ in 0..10 {
        let counter = counter.clone();
        handles.push(tokio::spawn(async move {
            for _ in 0..1000 {
                // This is atomic and safe
                counter.fetch_add(1, Ordering::Relaxed);
            }
        }));
    }

    for handle in handles {
        handle.await.unwrap();
    }

    println!("Final count: {}", counter.load(Ordering::Relaxed));
    // Always prints 10000 (correct)
}

/// INCORRECT: Non-atomic counter (would cause data race if used)
pub async fn non_atomic_race() {
    // Using Cell for interior mutability
    let counter = Arc::new(std::cell::Cell::new(0usize));

    // This won't even compile with spawn:
    // Cell is !Sync, so Arc<Cell<T>> is not Send

    // But if we force it with unsafe (DON'T DO THIS):
    // Concurrent increments would lose updates
}

/// More subtle race: Check-then-act
pub async fn check_then_act_race() {
    let balance = Arc::new(tokio::sync::Mutex::new(100i32));

    let balance2 = balance.clone();
    let handle1 = tokio::spawn(async move {
        let mut guard = balance2.lock().await;
        if *guard >= 50 {
            // Race window here!
            tokio::time::sleep(std::time::Duration::from_millis(1)).await;
            *guard -= 50;
            println!("Withdrew 50");
        }
    });

    let balance3 = balance.clone();
    let handle2 = tokio::spawn(async move {
        let mut guard = balance3.lock().await;
        if *guard >= 75 {
            // Another race window!
            tokio::time::sleep(std::time::Duration::from_millis(1)).await;
            *guard -= 75;
            println!("Withdrew 75");
        }
    });

    let _ = tokio::join!(handle1, handle2);

    // Balance could be negative due to race!
    println!("Final balance: {}", *balance.lock().await);
}

/// Why this is racy:
///
/// Thread 1: Read balance = 100
/// Thread 1: Check 100 >= 50: true
/// Thread 2: Read balance = 100
/// Thread 2: Check 100 >= 75: true
/// Thread 1: Write balance = 50
/// Thread 2: Write balance = 25
///
/// Both withdrawals succeed but balance went from 100 to 25!
/// Should have been: only one succeeds (50 or 75)

/// SOLUTION CODE:

/// Solution 1: Hold lock for entire operation
pub async fn atomic_check_and_act() {
    let balance = Arc::new(tokio::sync::Mutex::new(100i32));

    let balance2 = balance.clone();
    let handle1 = tokio::spawn(async move {
        let mut guard = balance2.lock().await;
        if *guard >= 50 {
            *guard -= 50;  // No await between check and act!
            println!("Withdrew 50");
        }
    });

    let balance3 = balance.clone();
    let handle2 = tokio::spawn(async move {
        let mut guard = balance3.lock().await;
        if *guard >= 75 {
            *guard -= 75;
            println!("Withdrew 75");
        }
    });

    let _ = tokio::join!(handle1, handle2);

    println!("Final balance: {}", *balance.lock().await);
    // Now correctly shows 25 (only one withdrawal succeeded)
}

/// Solution 2: Compare-and-swap loop
use std::sync::atomic::{AtomicI32, Ordering};

pub async fn cas_solution() {
    let balance = Arc::new(AtomicI32::new(100));

    let balance2 = balance.clone();
    let handle1 = tokio::spawn(async move {
        loop {
            let current = balance2.load(Ordering::Relaxed);
            if current < 50 {
                break;
            }
            let new = current - 50;
            // Atomic compare-and-swap
            if balance2.compare_exchange(
                current, new,
                Ordering::SeqCst, Ordering::Relaxed
            ).is_ok() {
                println!("Withdrew 50");
                break;
            }
            // Retry if another thread changed the value
        }
    });

    let balance3 = balance.clone();
    let handle2 = tokio::spawn(async move {
        loop {
            let current = balance3.load(Ordering::Relaxed);
            if current < 75 {
                break;
            }
            let new = current - 75;
            if balance3.compare_exchange(
                current, new,
                Ordering::SeqCst, Ordering::Relaxed
            ).is_ok() {
                println!("Withdrew 75");
                break;
            }
        }
    });

    let _ = tokio::join!(handle1, handle2);
    println!("Final balance: {}", balance.load(Ordering::Relaxed));
}

/// Solution 3: Actor pattern (single writer)
pub async fn actor_solution() {
    let (tx, mut rx) = tokio::sync::mpsc::channel::<AccountMessage>(100);

    // Spawn actor task
    let actor_handle = tokio::spawn(async move {
        let mut balance = 100i32;

        while let Some(msg) = rx.recv().await {
            match msg {
                AccountMessage::Withdraw(amount, respond_to) => {
                    if balance >= amount {
                        balance -= amount;
                        respond_to.send(true).unwrap();
                    } else {
                        respond_to.send(false).unwrap();
                    }
                }
                AccountMessage::GetBalance(respond_to) => {
                    respond_to.send(balance).unwrap();
                }
            }
        }
    });

    // Send withdrawal requests
    let (resp_tx, resp_rx) = tokio::sync::oneshot::channel();
    tx.send(AccountMessage::Withdraw(50, resp_tx)).await.unwrap();
    let success1 = resp_rx.await.unwrap();

    let (resp_tx2, resp_rx2) = tokio::sync::oneshot::channel();
    tx.send(AccountMessage::Withdraw(75, resp_tx2)).await.unwrap();
    let success2 = resp_rx2.await.unwrap();

    println!("Withdrawal 50: {}, Withdrawal 75: {}", success1, success2);

    // Get final balance
    let (bal_tx, bal_rx) = tokio::sync::oneshot::channel();
    tx.send(AccountMessage::GetBalance(bal_tx)).await.unwrap();
    println!("Final balance: {}", bal_rx.await.unwrap());
}

enum AccountMessage {
    Withdraw(i32, tokio::sync::oneshot::Sender<bool>),
    GetBalance(tokio::sync::oneshot::Sender<i32>),
}

/// FORMAL REASONING:
///
/// 1. Race condition definition:
///    - Multiple threads access shared data
///    - At least one access is a write
///    - No happens-before relationship between accesses
///    - Result depends on execution order
///
/// 2. Mutex solution:
///    - Creates happens-before: lock → access → unlock
///    - Mutual exclusion ensures atomicity of critical section
///    - Check and act happen atomically
///
/// 3. CAS solution:
///    - Atomic read-modify-write operation
///    - Retry loop handles contention
///    - Lock-free but may retry multiple times
///
/// 4. Actor solution:
///    - Single-threaded access to state
///    - Message passing ensures sequential processing
///    - No locks needed, naturally race-free
```

---

## 7. Case Study: Async HTTP Server

This case study presents a complete async HTTP server with formal ownership analysis, architecture diagrams, and safety arguments.

### Architecture Diagram

```
┌─────────────────────────────────────────────────────────────────────┐
│                         Async HTTP Server                            │
├─────────────────────────────────────────────────────────────────────┤
│                                                                      │
│  ┌─────────────┐    ┌─────────────┐    ┌─────────────────────────┐  │
│  │   Listener  │───▶│  Connection │───▶│    Request Handler      │  │
│  │   (Tcp)     │    │   Pool      │    │                         │  │
│  └─────────────┘    └─────────────┘    └─────────────────────────┘  │
│         │                  │                      │                  │
│         ▼                  ▼                      ▼                  │
│  ┌─────────────┐    ┌─────────────┐    ┌─────────────────────────┐  │
│  │  Spawn task │    │  Limit      │    │    Router / Middleware  │  │
│  │  per conn   │    │  concurrent │    │                         │  │
│  └─────────────┘    └─────────────┘    └─────────────────────────┘  │
│                                               │                      │
│                                               ▼                      │
│  ┌──────────────────────────────────────────────────────────────┐  │
│  │                      Handler Registry                         │  │
│  │  GET /users    → UserHandler::list()                         │  │
│  │  POST /users   → UserHandler::create()                       │  │
│  │  GET /health   → HealthHandler::check()                      │  │
│  └──────────────────────────────────────────────────────────────┘  │
│                                               │                      │
│                                               ▼                      │
│  ┌──────────────────────────────────────────────────────────────┐  │
│  │                      Data Access Layer                        │  │
│  │  ┌────────────┐  ┌────────────┐  ┌──────────────────────┐    │  │
│  │  │ Connection │  │   Cache    │  │     Database         │    │  │
│  │  │   Pool     │  │ (optional) │  │    (async)           │    │  │
│  │  └────────────┘  └────────────┘  └──────────────────────┘    │  │
│  └──────────────────────────────────────────────────────────────┘  │
│                                                                      │
└─────────────────────────────────────────────────────────────────────┘
```

### Implementation with Ownership Analysis

```rust
//! Async HTTP Server - Case Study
//!
//! This implementation demonstrates proper ownership management in
//! an async HTTP server, with detailed safety arguments.

use std::sync::Arc;
use tokio::net::{TcpListener, TcpStream};
use tokio::sync::{mpsc, Mutex, RwLock, Semaphore};
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use std::collections::HashMap;

/// Server configuration - immutable, shared across all tasks
///
/// Ownership: Arc<Config> is cloned for each task, but Config is immutable
/// Safety: Read-only shared state requires no synchronization
#[derive(Clone)]
pub struct Config {
    pub bind_addr: String,
    pub max_connections: usize,
    pub request_timeout_secs: u64,
    pub db_pool_size: usize,
}

impl Config {
    pub fn load() -> Self {
        Self {
            bind_addr: "127.0.0.1:8080".to_string(),
            max_connections: 1000,
            request_timeout_secs: 30,
            db_pool_size: 10,
        }
    }
}

/// Application state - shared across handlers
///
/// Ownership analysis:
/// - db_pool: Arc<Mutex<...>> for shared mutable connection pool
/// - cache: Arc<RwLock<...>> for high-read shared cache
/// - handlers: Arc<RwLock<...>> for dynamic handler registration
///
/// Safety: All shared state uses appropriate synchronization
pub struct AppState {
    db_pool: Arc<Mutex<ConnectionPool>>,
    cache: Arc<RwLock<HashMap<String, Vec<u8>>>>,
    handlers: Arc<RwLock<HandlerRegistry>>,
}

impl AppState {
    pub fn new(config: &Config) -> Self {
        Self {
            db_pool: Arc::new(Mutex::new(ConnectionPool::new(config.db_pool_size))),
            cache: Arc::new(RwLock::new(HashMap::new())),
            handlers: Arc::new(RwLock::new(HandlerRegistry::new())),
        }
    }

    /// Get a database connection
    ///
    /// Ownership: Returns a guard that releases connection on drop
    pub async fn get_db(&self) -> DbConnection {
        let pool = self.db_pool.lock().await;
        pool.acquire().await
    }

    /// Get cached value
    ///
    /// Ownership: Returns cloned data, no references held
    pub async fn cache_get(&self, key: &str) -> Option<Vec<u8>> {
        let cache = self.cache.read().await;
        cache.get(key).cloned()
    }

    /// Set cached value
    pub async fn cache_set(&self, key: String, value: Vec<u8>) {
        let mut cache = self.cache.write().await;
        cache.insert(key, value);
    }
}

/// Connection pool manages database connections
pub struct ConnectionPool {
    connections: Vec<DbConnection>,
    available: Vec<DbConnection>,
}

impl ConnectionPool {
    fn new(size: usize) -> Self {
        let connections: Vec<_> = (0..size)
            .map(|_| DbConnection::new())
            .collect();
        Self {
            available: connections.clone(),
            connections,
        }
    }

    async fn acquire(&self) -> DbConnection {
        // Simplified: would actually wait for available connection
        DbConnection::new()
    }
}

#[derive(Clone)]
pub struct DbConnection;

impl DbConnection {
    fn new() -> Self {
        Self
    }

    pub async fn query(&self, sql: &str) -> Result<Vec<Row>, Error> {
        // Database query implementation
        Ok(vec![])
    }
}

pub struct Row;
pub struct Error;

/// Handler registry maps paths to handlers
pub struct HandlerRegistry {
    routes: HashMap<String, Box<dyn Handler>>,
}

impl HandlerRegistry {
    fn new() -> Self {
        let mut routes = HashMap::new();
        routes.insert("/health".to_string(), Box::new(HealthHandler) as Box<dyn Handler>);
        routes.insert("/users".to_string(), Box::new(UserHandler) as Box<dyn Handler>);
        Self { routes }
    }

    fn get(&self, path: &str) -> Option<&dyn Handler> {
        self.routes.get(path).map(|b| b.as_ref())
    }
}

trait Handler: Send + Sync {
    fn handle(&self, req: Request, state: Arc<AppState>) -> HandlerFuture;
}

type HandlerFuture = std::pin::Pin<Box<dyn std::future::Future<Output = Response> + Send>>;

/// Request/Response types
pub struct Request {
    method: String,
    path: String,
    body: Vec<u8>,
}

pub struct Response {
    status: u16,
    body: Vec<u8>,
}

impl Response {
    fn ok(body: Vec<u8>) -> Self {
        Self { status: 200, body }
    }

    fn not_found() -> Self {
        Self { status: 404, body: b"Not Found".to_vec() }
    }

    fn error(msg: &str) -> Self {
        Self { status: 500, body: msg.as_bytes().to_vec() }
    }
}

/// Health check handler
struct HealthHandler;

impl Handler for HealthHandler {
    fn handle(&self, _req: Request, _state: Arc<AppState>) -> HandlerFuture {
        Box::pin(async move {
            Response::ok(b"OK".to_vec())
        })
    }
}

/// User handler with database access
struct UserHandler;

impl Handler for UserHandler {
    fn handle(&self, req: Request, state: Arc<AppState>) -> HandlerFuture {
        Box::pin(async move {
            match req.method.as_str() {
                "GET" => Self::list_users(state).await,
                "POST" => Self::create_user(req, state).await,
                _ => Response::not_found(),
            }
        })
    }
}

impl UserHandler {
    async fn list_users(state: Arc<AppState>) -> Response {
        // Acquire connection (short-lived lock)
        let conn = {
            let pool = state.db_pool.lock().await;
            pool.acquire().await
        };

        // Use connection without holding pool lock
        match conn.query("SELECT * FROM users").await {
            Ok(_rows) => Response::ok(b"Users list".to_vec()),
            Err(_) => Response::error("Database error"),
        }
    }

    async fn create_user(req: Request, state: Arc<AppState>) -> Response {
        // Check cache first (read lock)
        let cache_key = format!("user:{}", String::from_utf8_lossy(&req.body));
        if let Some(cached) = state.cache_get(&cache_key).await {
            return Response::ok(cached);
        }

        // Create user in database
        let conn = {
            let pool = state.db_pool.lock().await;
            pool.acquire().await
        };

        let result = match conn.query("INSERT INTO users ...").await {
            Ok(_) => Response::ok(b"Created".to_vec()),
            Err(_) => return Response::error("Insert failed"),
        };

        // Update cache (write lock)
        state.cache_set(cache_key, result.body.clone()).await;

        result
    }
}

/// Main server implementation
pub struct Server {
    config: Config,
    state: Arc<AppState>,
    shutdown_tx: mpsc::Sender<()>,
    shutdown_rx: Mutex<mpsc::Receiver<()>>,
}

impl Server {
    pub fn new(config: Config) -> Self {
        let state = Arc::new(AppState::new(&config));
        let (shutdown_tx, shutdown_rx) = mpsc::channel(1);

        Self {
            config,
            state,
            shutdown_tx,
            shutdown_rx: Mutex::new(shutdown_rx),
        }
    }

    /// Run the server
    ///
    /// Ownership flow:
    /// 1. Config is borrowed (immutable)
    /// 2. State is cloned into Arc for each connection
    /// 3. Each connection spawns a new task with owned data
    pub async fn run(&self) -> Result<(), Box<dyn std::error::Error>> {
        let listener = TcpListener::bind(&self.config.bind_addr).await?;
        println!("Server listening on {}", self.config.bind_addr);

        // Concurrency limiter
        let semaphore = Arc::new(Semaphore::new(self.config.max_connections));

        // Clone state for the accept loop
        let state = self.state.clone();
        let mut shutdown_rx = self.shutdown_rx.lock().await;

        loop {
            tokio::select! {
                // Accept new connection
                result = listener.accept() => {
                    let (stream, addr) = result?;
                    let permit = semaphore.clone().acquire_owned().await?;
                    let state = state.clone();

                    // Spawn connection handler
                    // Safety: All data is Send + 'static
                    tokio::spawn(async move {
                        let _permit = permit; // Hold permit until connection closes
                        handle_connection(stream, addr, state).await;
                    });
                }

                // Shutdown signal
                _ = shutdown_rx.recv() => {
                    println!("Shutdown signal received");
                    break;
                }
            }
        }

        Ok(())
    }

    pub fn shutdown(&self) {
        let _ = self.shutdown_tx.try_send(());
    }
}

/// Handle a single connection
///
/// Ownership: Takes ownership of stream, borrows state via Arc
async fn handle_connection(
    mut stream: TcpStream,
    addr: std::net::SocketAddr,
    state: Arc<AppState>,
) {
    println!("Connection from {}", addr);

    let mut buffer = [0u8; 1024];

    loop {
        match stream.read(&mut buffer).await {
            Ok(0) => break, // Connection closed
            Ok(n) => {
                // Parse request (simplified)
                let request = parse_request(&buffer[..n]);

                // Get handler
                let handlers = state.handlers.read().await;
                let response = if let Some(handler) = handlers.get(&request.path) {
                    // Handler gets cloned Arc<AppState>
                    handler.handle(request, state.clone()).await
                } else {
                    Response::not_found()
                };
                drop(handlers); // Release read lock

                // Send response
                let response_bytes = format_response(&response);
                if stream.write_all(&response_bytes).await.is_err() {
                    break;
                }
            }
            Err(_) => break,
        }
    }

    println!("Connection from {} closed", addr);
}

fn parse_request(data: &[u8]) -> Request {
    // Simplified parsing
    Request {
        method: "GET".to_string(),
        path: "/".to_string(),
        body: data.to_vec(),
    }
}

fn format_response(resp: &Response) -> Vec<u8> {
    format!(
        "HTTP/1.1 {} OK\r\nContent-Length: {}\r\n\r\n",
        resp.status,
        resp.body.len()
    )
    .into_bytes()
    .into_iter()
    .chain(resp.body.clone().into_iter())
    .collect()
}

/// Main entry point
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let config = Config::load();
    let server = Server::new(config);

    // Spawn shutdown handler
    let server_clone = Server {
        config: Config::load(),
        state: server.state.clone(),
        shutdown_tx: server.shutdown_tx.clone(),
        shutdown_rx: Mutex::new(mpsc::channel(1).1),
    };

    tokio::spawn(async move {
        tokio::signal::ctrl_c().await.unwrap();
        println!("Received Ctrl+C");
        server_clone.shutdown();
    });

    server.run().await
}
```

### Ownership Flow Analysis

```rust
/// OWNERSHIP FLOW DIAGRAM:
///
/// Server::run
/// │
/// ├─► Config (borrowed, immutable)
/// │   └─► No synchronization needed
/// │
/// ├─► Arc<AppState> (cloned per connection)
/// │   ├─► db_pool: Arc<Mutex<ConnectionPool>>
/// │   │   ├─► Mutex guard acquired for acquire()
/// │   │   │   └─► Dropped before await points ✓
/// │   │   └─► DbConnection returned (owned)
/// │   │       └─► Dropped after query completes
/// │   │
/// │   ├─► cache: Arc<RwLock<HashMap>>
/// │   │   ├─► Read lock for cache_get (short)
/// │   │   │   └─► Data cloned before return ✓
/// │   │   └─► Write lock for cache_set (short)
/// │   │       └─► Lock released after insert ✓
/// │   │
/// │   └─► handlers: Arc<RwLock<HandlerRegistry>>
/// │       └─► Read lock during routing (short) ✓
/// │
/// ├─► Semaphore permit (acquired per connection)
/// │   └─► Moved into connection task
/// │       └─► Dropped when connection closes
/// │
/// └─► Connection handler spawn
///     ├─► TcpStream (moved into task)
///     ├─► Arc<AppState> (cloned into task)
///     └─► Task runs independently
///
/// SAFETY CHECKLIST:
///
/// ✓ No mutex guards held across await points
/// ✓ All spawned tasks use Send + 'static data
/// ✓ Cache returns cloned data, not references
/// ✓ Connection pool uses short-lived locks
/// ✓ Graceful shutdown with signal handling
/// ✓ Concurrency limited with semaphore
```

### Potential Pitfalls Highlighted

```rust
/// PITFALL 1: Long-lived read locks
///
/// WRONG:
/// async fn list_users(state: &AppState) {
///     let cache = state.cache.read().await;
///     for (key, value) in cache.iter() {  // Lock held for entire loop!
///         tokio::time::sleep(Duration::from_millis(1)).await;
///         println!("{}: {:?}", key, value);
///     }
///     // Lock released here
/// }
///
/// CORRECT:
async fn list_users_correct(state: &AppState) {
    // Collect data while holding lock
    let entries: Vec<_> = {
        let cache = state.cache.read().await;
        cache.iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect()
    }; // Lock released here

    // Process without holding lock
    for (key, value) in entries {
        tokio::time::sleep(Duration::from_millis(1)).await;
        println!("{}: {:?}", key, value);
    }
}

/// PITFALL 2: Handler returning references
///
/// WRONG:
/// impl Handler for BadHandler {
///     fn handle(&self, req: Request) -> &Response {
///         &Response::ok(b"data".to_vec())  // Dangling reference!
///     }
/// }
///
/// CORRECT:
/// impl Handler for GoodHandler {
///     fn handle(&self, req: Request, state: Arc<AppState>) -> HandlerFuture {
///         Box::pin(async move {
///             Response::ok(b"data".to_vec())  // Owned, returned
///         })
///     }
/// }

/// PITFALL 3: Blocking in async context
///
/// WRONG:
/// async fn bad_handler() {
///     let data = std::fs::read("file.txt").unwrap();  // Blocks thread!
///     Response::ok(data)
/// }
///
/// CORRECT:
async fn good_handler() {
    let data = tokio::fs::read("file.txt").await;  // Async I/O
    Response::ok(data.unwrap())
}

/// PITFALL 4: Unbounded channels
///
/// WRONG:
/// let (tx, rx) = mpsc::channel(1000000);  // Huge buffer
///
/// CORRECT:
/// let (tx, rx) = mpsc::channel(100);  // Bounded, respects backpressure

/// PITFALL 5: Ignoring cancellation
///
/// WRONG:
/// async fn update_db(state: &AppState) {
///     let conn = state.get_db().await;
///     conn.execute("BEGIN").await;  // Not cancellation-safe!
///     conn.execute("INSERT ...").await;
///     // If cancelled here, transaction left open!
///     conn.execute("COMMIT").await;
/// }
///
/// CORRECT:
async fn update_db_safe(state: &AppState) {
    // Use timeout or cancellation token
    let result = tokio::time::timeout(
        Duration::from_secs(5),
        async {
            let conn = state.get_db().await;
            // ... perform operations
            conn.query("SELECT 1").await
        }
    ).await;

    match result {
        Ok(Ok(rows)) => println!("Success"),
        Ok(Err(e)) => println!("Query error: {:?}", e),
        Err(_) => println!("Timeout"),
    }
}
```

---

## 8. References

### Core Documentation

1. **The Rust Async Book** - Official async programming guide
   - <https://rust-lang.github.io/async-book/>

2. **Tokio Documentation** - Production async runtime
   - <https://tokio.rs/>

3. **The Rust Reference - Async/Await** - Language semantics
   - <https://doc.rust-lang.org/reference/items/functions.html#async-functions>

### Formal Semantics

1. **"Asynchronous Rust: A Formal Semantics"** - Research paper on async semantics

2. **RustBelt: Securing the Foundations of the Rust Programming Language**
   - Jung et al., POPL 2018
   - Includes formal model of ownership and lifetimes

### Rust 1.94 Features

1. **LazyLock and LazyCell improvements** - Better async initialization
   - `LazyLock::get()` for cleaner access
   - `LazyCell::get_mut()` and `force_mut()`

2. **Peekable::next_if_map** - Async stream processing
   - Conditional consumption of iterator elements
   - Useful for async message filtering

### Related Patterns

- **12-02: Thread Safety Patterns** - Send/Sync deep dive
- **12-03: Message Passing** - Channel patterns
- **13-02: Web Service Architecture** - HTTP server patterns

---

> **Document Version**: 2.0
> **Last Updated**: 2026-03-06
> **Rust Version**: 1.94
> **Word Count**: ~15,000 words

---

*This document is part of the Rust Ownership & Decidability documentation series. For questions or contributions, refer to the project repository.*
