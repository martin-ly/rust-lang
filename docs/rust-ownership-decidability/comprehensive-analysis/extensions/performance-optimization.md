# Rust性能优化深度指南

> **零成本抽象背后的性能技术**

---

## 1. 编译器优化

### 1.1 LTO与优化级别

```toml
# Cargo.toml 优化配置
[profile.release]
opt-level = 3           # 最高优化级别
lto = "fat"             # 全程序链接时优化
codegen-units = 1       # 单一代码生成单元（更好优化）
panic = "abort"         # 无展开代码
strip = true            # 去除符号

[profile.release.build-override]
opt-level = 3           # 构建脚本也优化
```

### 1.2 内联控制

```rust
// 强制内联
#[inline(always)]
fn hot_path(x: i32) -> i32 {
    x * 2 + 1
}

// 建议内联（编译器决定）
#[inline]
fn suggestion(x: i32) -> i32 {
    x * 2
}

// 禁止内联
#[inline(never)]
fn no_inline(x: i32) -> i32 {
    expensive_operation(x)
}

// 冷路径标记
#[cold]
fn error_handler() {
    // 编译器将优化为远离热代码
}
```

### 1.3 分支预测提示

```rust
// 标准库中的likely/unlikely
#[cfg(feature = "nightly")]
use std::intrinsics::{likely, unlikely};

// 稳定版替代方案
#[inline(always)]
pub fn likely(b: bool) -> bool {
    #[cfg(feature = "nightly")]
    unsafe { std::intrinsics::likely(b) }
    #[cfg(not(feature = "nightly"))]
    b
}

pub fn optimized_search(arr: &[i32], target: i32) -> Option<usize> {
    for (i, &x) in arr.iter().enumerate() {
        if likely(x != target) {
            continue;
        }
        return Some(i);
    }
    None
}
```

---

## 2. 内存优化

### 2.1 内存布局优化

```rust
// 糟糕的内存布局（填充浪费）
struct BadLayout {
    a: u8,      // 1 byte + 7 padding
    b: u64,     // 8 bytes
    c: u8,      // 1 byte + 7 padding
    d: u64,     // 8 bytes
}               // 总: 32 bytes

// 优化后的布局
struct GoodLayout {
    b: u64,     // 8 bytes
    d: u64,     // 8 bytes
    a: u8,      // 1 byte
    c: u8,      // 1 byte
    _padding: [u8; 6],  // 6 bytes
}               // 总: 24 bytes

// 使用cargo-show-asm检查布局
// cargo install cargo-show-asm
```

### 2.2  arena分配器

```rust
use bumpalo::Bump;

// Arena分配模式
fn process_items_arena(items: &[Item]) -> Vec<Processed> {
    let arena = Bump::new();
    let mut results = Vec::new();

    for item in items {
        // 快速分配，无全局锁
        let processed = arena.alloc(Processed::new(item));
        results.push(processed);
    }

    // arena在函数结束时一次性释放
    results
}

// 自定义arena
pub struct Arena<T> {
    chunks: Vec<Vec<T>>,
    current: Vec<T>,
}

impl<T> Arena<T> {
    pub fn alloc(&mut self, value: T) -> &mut T {
        if self.current.capacity() == self.current.len() {
            let new_chunk = std::mem::replace(
                &mut self.current,
                Vec::with_capacity(self.current.capacity() * 2)
            );
            self.chunks.push(new_chunk);
        }
        self.current.push(value);
        self.current.last_mut().unwrap()
    }
}
```

### 2.3 零拷贝技术

```rust
// 使用Cow避免不必要克隆
use std::borrow::Cow;

pub fn process_data(input: &str) -> Cow<str> {
    if input.contains("special") {
        // 需要修改，克隆
        Cow::Owned(input.replace("special", "normal"))
    } else {
        // 无需修改，借用
        Cow::Borrowed(input)
    }
}

// 切片复用
pub fn parse_headers(data: &[u8]) -> Vec<&[u8]> {
    data.split(|&b| b == b'\n')
        .map(|line| line.trim_ascii())
        .filter(|line| !line.is_empty())
        .collect()
}
```

---

## 3. 并发性能

### 3.1 无锁数据结构

```rust
use crossbeam::queue::ArrayQueue;
use crossbeam::epoch::{self, Atomic, Owned};
use std::sync::atomic::Ordering;

// 无锁队列
pub struct LockFreeQueue<T> {
    queue: ArrayQueue<T>,
}

impl<T> LockFreeQueue<T> {
    pub fn push(&self, item: T) -> Result<(), T> {
        self.queue.push(item)
    }

    pub fn pop(&self) -> Option<T> {
        self.queue.pop()
    }
}

// 无锁栈 (Treiber Stack)
pub struct TreiberStack<T> {
    head: Atomic<Node<T>>,
}

struct Node<T> {
    data: T,
    next: Atomic<Node<T>>,
}

impl<T> TreiberStack<T> {
    pub fn push(&self, data: T) {
        let new = Owned::new(Node {
            data,
            next: Atomic::null(),
        });

        let guard = epoch::pin();

        loop {
            let head = self.head.load(Ordering::Relaxed, &guard);
            new.next.store(head, Ordering::Relaxed);

            match self.head.compare_and_set(head, new, Ordering::Release, &guard) {
                Ok(_) => break,
                Err(e) => new = e.new,
            }
        }
    }
}
```

### 3.2 线程局部存储

```rust
use std::cell::RefCell;
use std::collections::HashMap;

// 线程局部缓存
thread_local! {
    static BUFFER: RefCell<Vec<u8>> = RefCell::new(Vec::with_capacity(4096));
    static CACHE: RefCell<HashMap<u64, String>> = RefCell::new(HashMap::new());
}

pub fn with_buffer<F, R>(f: F) -> R
where
    F: FnOnce(&mut Vec<u8>) -> R,
{
    BUFFER.with(|buf| {
        let mut buf = buf.borrow_mut();
        buf.clear();
        f(&mut buf)
    })
}

// 使用示例
pub fn format_message(msg: &str) -> String {
    with_buffer(|buf| {
        buf.extend_from_slice(b"[LOG] ");
        buf.extend_from_slice(msg.as_bytes());
        String::from_utf8_lossy(buf).to_string()
    })
}
```

### 3.3 SIMD优化

```rust
// 使用packed_simd或std::simd (nightly)
#[cfg(feature = "simd")]
use std::simd::*;

// 向量加法SIMD
pub fn vector_add_simd(a: &[f32], b: &[f32], c: &mut [f32]) {
    assert_eq!(a.len(), b.len());
    assert_eq!(a.len(), c.len());

    let chunks = a.len() / 4;

    for i in 0..chunks {
        let va = f32x4::from_slice(&a[i * 4..]);
        let vb = f32x4::from_slice(&b[i * 4..]);
        let vc = va + vb;
        vc.copy_to_slice(&mut c[i * 4..]);
    }

    // 处理剩余元素
    for i in chunks * 4..a.len() {
        c[i] = a[i] + b[i];
    }
}

// 使用auto_vectorization提示
#[repr(align(32))]
struct AlignedBuffer([f32; 256]);
```

---

## 4. 异步性能

### 4.1 减少分配

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

// 栈分配的Future
pub struct StackFuture<F> {
    inner: F,
}

impl<F: Future> Future for StackFuture<F> {
    type Output = F::Output;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        // Safety: pin projection
        let inner = unsafe { self.map_unchecked_mut(|s| &mut s.inner) };
        inner.poll(cx)
    }
}

// 批量处理减少上下文切换
pub async fn process_batch(items: Vec<Item>) -> Vec<Result> {
    let mut results = Vec::with_capacity(items.len());

    // 使用 FuturesUnordered 并发处理但限制并发度
    use futures::stream::{FuturesUnordered, StreamExt};

    let mut stream = items
        .into_iter()
        .map(process_item)
        .collect::<FuturesUnordered<_>>();

    while let Some(result) = stream.next().await {
        results.push(result);
    }

    results
}
```

### 4.2 优化Waker使用

```rust
use std::task::Waker;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};

// 高效Waker实现
pub struct OptimizedWaker {
    waker: Waker,
    has_woken: AtomicBool,
}

impl OptimizedWaker {
    pub fn new(waker: Waker) -> Self {
        Self {
            waker,
            has_woken: AtomicBool::new(false),
        }
    }

    pub fn wake(&self) {
        // 只唤醒一次，避免重复唤醒开销
        if !self.has_woken.swap(true, Ordering::AcqRel) {
            self.waker.wake_by_ref();
        }
    }

    pub fn reset(&self) {
        self.has_woken.store(false, Ordering::Release);
    }
}
```

---

## 5. I/O优化

### 5.1 缓冲策略

```rust
use std::io::{self, BufRead, Write};

// 自定义缓冲区大小
pub fn copy_with_buffer<R, W>(mut reader: R, mut writer: W) -> io::Result<u64>
where
    R: BufRead,
    W: Write,
{
    // 64KB缓冲区（通常是最佳平衡点）
    let mut buffer = vec![0; 64 * 1024];
    let mut total = 0u64;

    loop {
        let n = reader.read(&mut buffer)?;
        if n == 0 {
            break;
        }
        writer.write_all(&buffer[..n])?;
        total += n as u64;
    }

    writer.flush()?;
    Ok(total)
}

// 预读优化
pub struct PrefetchReader<R> {
    inner: R,
    buffer: Vec<u8>,
    prefetch_size: usize,
}

impl<R: io::Read> PrefetchReader<R> {
    pub fn new(inner: R) -> Self {
        Self {
            inner,
            buffer: Vec::with_capacity(256 * 1024),
            prefetch_size: 64 * 1024,
        }
    }

    pub fn prefetch(&mut self) -> io::Result<()> {
        let start = self.buffer.len();
        self.buffer.resize(start + self.prefetch_size, 0);

        match self.inner.read(&mut self.buffer[start..])? {
            0 => {
                self.buffer.truncate(start);
                Ok(())
            }
            n => {
                self.buffer.truncate(start + n);
                Ok(())
            }
        }
    }
}
```

### 5.2 io_uring (Linux)

```rust
#[cfg(target_os = "linux")]
use io_uring::{IoUring, opcode, types};

// io_uring批量操作
pub struct UringDriver {
    ring: IoUring,
}

impl UringDriver {
    pub fn new(entries: u32) -> io::Result<Self> {
        Ok(Self {
            ring: IoUring::new(entries)?,
        })
    }

    pub fn read_vectored(
        &mut self,
        fd: RawFd,
        bufs: &mut [IoSliceMut<'_>],
        offset: u64,
    ) -> io::Result<usize> {
        let user_data = 0x42;

        let read_op = opcode::Readv::new(
            types::Fd(fd),
            bufs.as_mut_ptr() as *mut _,
            bufs.len() as u32,
        )
        .offset(offset)
        .build()
        .user_data(user_data);

        unsafe {
            self.ring.submission()
                .push(&read_op)
                .map_err(|e| io::Error::new(io::ErrorKind::Other, e))?;
        }

        self.ring.submit_and_wait(1)?;

        let cqe = self.ring.completion().next().unwrap();
        if cqe.result() >= 0 {
            Ok(cqe.result() as usize)
        } else {
            Err(io::Error::from_raw_os_error(-cqe.result()))
        }
    }
}
```

---

## 6. 算法优化

### 6.1 缓存友好算法

```rust
// 矩阵乘法 - 缓存不友好版本
fn matmul_slow(a: &[f32], b: &[f32], c: &mut [f32], n: usize) {
    for i in 0..n {
        for j in 0..n {
            let mut sum = 0.0;
            for k in 0..n {
                sum += a[i * n + k] * b[k * n + j];  // b列访问不连续
            }
            c[i * n + j] = sum;
        }
    }
}

// 矩阵乘法 - 缓存友好版本 (分块)
const BLOCK_SIZE: usize = 64;

fn matmul_fast(a: &[f32], b: &[f32], c: &mut [f32], n: usize) {
    for i0 in (0..n).step_by(BLOCK_SIZE) {
        for j0 in (0..n).step_by(BLOCK_SIZE) {
            for k0 in (0..n).step_by(BLOCK_SIZE) {
                // 处理BLOCK_SIZE x BLOCK_SIZE块
                for i in i0..(i0 + BLOCK_SIZE).min(n) {
                    for j in j0..(j0 + BLOCK_SIZE).min(n) {
                        let mut sum = c[i * n + j];
                        for k in k0..(k0 + BLOCK_SIZE).min(n) {
                            sum += a[i * n + k] * b[k * n + j];
                        }
                        c[i * n + j] = sum;
                    }
                }
            }
        }
    }
}
```

### 6.2 哈希表优化

```rust
use std::collections::HashMap;
use std::hash::BuildHasherDefault;
use twox_hash::XxHash64;

// 使用更快的哈希函数（非抗碰撞）
pub type FastHashMap<K, V> = HashMap<K, V, BuildHasherDefault<XxHash64>>;

// 预分配容量
pub fn with_capacity<K, V>(cap: usize) -> FastHashMap<K, V> {
    FastHashMap::with_capacity_and_hasher(cap, BuildHasherDefault::default())
}

// 使用FxHash (最快，整数键最佳)
use rustc_hash::FxHashMap;

pub fn count_frequencies(items: &[u64]) -> FxHashMap<u64, usize> {
    let mut counts = FxHashMap::default();
    counts.reserve(items.len() / 2);  // 预分配

    for &item in items {
        *counts.entry(item).or_insert(0) += 1;
    }

    counts
}
```

---

## 7. 测量与分析

### 7.1 Criterion基准测试

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn fibonacci(n: u64) -> u64 {
    match n {
        0 => 1,
        1 => 1,
        n => fibonacci(n - 1) + fibonacci(n - 2),
    }
}

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("fib 20", |b| {
        b.iter(|| fibonacci(black_box(20)))
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
```

### 7.2 性能分析工具

```bash
# Flamegraph生成
cargo install flamegraph
cargo flamegraph --bin myapp

# Cachegrind分析
cargo install valgrind
cargo valgrind --tool=cachegrind --bin myapp

# perf分析
perf record --call-graph dwarf ./target/release/myapp
perf report

# heaptrack分析内存
heaptrack ./target/release/myapp
heaptrack_gui heaptrack.myapp.xxx.gz
```

### 7.3 运行时性能监控

```rust
use std::time::Instant;

// 简单计时器
pub struct Timer {
    name: &'static str,
    start: Instant,
}

impl Timer {
    pub fn new(name: &'static str) -> Self {
        Self {
            name,
            start: Instant::now(),
        }
    }
}

impl Drop for Timer {
    fn drop(&mut self) {
        let elapsed = self.start.elapsed();
        eprintln!("{}: {:?}", self.name, elapsed);
    }
}

// 使用
fn process() {
    let _t = Timer::new("process");
    // ... 处理逻辑
}
```

---

**维护者**: Rust Performance Team
**更新日期**: 2026-03-05
