# 常见问题解答 (FAQ)

## 进程管理

### Q: 如何创建子进程？

A: 使用 `std::process::Command` 来创建子进程：

```rust
use std::process::Command;

let output = Command::new("ls")
    .arg("-la")
    .output()?;
```

### Q: 如何等待子进程完成？

A: 使用 `wait()` 或 `wait_with_output()` 方法：

```rust
let mut child = Command::new("sleep").arg("5").spawn()?;
let status = child.wait()?;
```

### Q: 如何向子进程发送信号？

A: 使用 `kill()` 方法发送信号：

```rust
let mut child = Command::new("long_running_process").spawn()?;
child.kill()?; // 发送 SIGTERM
```

### Q: 如何处理子进程的标准输入输出？

A: 使用 `stdin()`, `stdout()`, `stderr()` 方法：

```rust
use std::process::{Command, Stdio};
use std::io::Write;

let mut child = Command::new("grep")
    .arg("pattern")
    .stdin(Stdio::piped())
    .stdout(Stdio::piped())
    .spawn()?;

child.stdin.as_mut().unwrap().write_all(b"data")?;
let output = child.wait_with_output()?;
```

### Q: 如何设置子进程的环境变量？

A: 使用 `env()` 或 `envs()` 方法：

```rust
use std::collections::HashMap;

let mut env_vars = HashMap::new();
env_vars.insert("RUST_LOG", "debug");
env_vars.insert("DATABASE_URL", "postgres://localhost/db");

let child = Command::new("my_app")
    .envs(env_vars.iter())
    .spawn()?;
```

### Q: 如何设置子进程的工作目录？

A: 使用 `current_dir()` 方法：

```rust
let child = Command::new("git")
    .arg("status")
    .current_dir("/path/to/repo")
    .spawn()?;
```

### Q: 如何处理僵尸进程？

A: 确保正确等待子进程完成：

```rust
let mut child = Command::new("process").spawn()?;
let _status = child.wait()?; // 等待子进程完成，避免僵尸进程
```

## 进程间通信

### Q: 管道和套接字有什么区别？

A:

- **管道**: 单向通信，适用于父子进程，性能高
- **套接字**: 双向通信，适用于无关进程，支持网络通信

### Q: 如何实现双向通信？

A: 使用两个管道或套接字：

```rust
use std::process::{Command, Stdio};
use std::io::Write;

let mut child = Command::new("process")
    .stdin(Stdio::piped())
    .stdout(Stdio::piped())
    .spawn()?;

// 写入到子进程
child.stdin.as_mut().unwrap().write_all(b"data")?;

// 从子进程读取
let output = child.wait_with_output()?;
```

### Q: 共享内存和消息传递哪个更好？

A: 取决于使用场景：

- **共享内存**: 适合大数据传输，性能高，但需要同步
- **消息传递**: 适合小数据，简单易用，类型安全

### Q: 如何处理 IPC 错误？

A: 使用适当的错误处理策略：

```rust
use std::sync::mpsc;

fn ipc_operation() -> Result<String, Box<dyn std::error::Error>> {
    let (tx, rx) = mpsc::channel();
    
    match rx.recv_timeout(std::time::Duration::from_secs(5)) {
        Ok(result) => Ok(result),
        Err(mpsc::RecvTimeoutError::Timeout) => {
            Err("IPC timeout".into())
        }
        Err(mpsc::RecvTimeoutError::Disconnected) => {
            Err("IPC disconnected".into())
        }
    }
}
```

### Q: 如何实现命名管道？

A: 在 Unix 系统上使用 `mkfifo`：

```rust
use std::fs::File;
use std::io::{Read, Write};

#[cfg(unix)]
fn named_pipe_example() -> std::io::Result<()> {
    let pipe_path = "/tmp/my_pipe";
    
    // 创建命名管道
    unsafe {
        use std::os::unix::fs::FileTypeExt;
        std::os::unix::fs::mkfifo(pipe_path, 0o666)?;
    }
    
    // 写入数据
    let mut file = File::create(pipe_path)?;
    file.write_all(b"Hello from writer!")?;
    
    Ok(())
}
```

### Q: 如何实现进程间共享内存？

A: 使用内存映射文件：

```rust
use memmap2::MmapMut;
use std::fs::OpenOptions;

fn shared_memory_example() -> std::io::Result<()> {
    let file = OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .open("shared_data.bin")?;
    
    file.set_len(1024)?;
    let mut mmap = unsafe { MmapMut::map_mut(&file)? };
    
    // 写入数据
    mmap[0..8].copy_from_slice(&42u64.to_le_bytes());
    mmap.flush()?;
    
    Ok(())
}
```

## 同步机制

### Q: Mutex 和 RwLock 如何选择？

A: 根据访问模式选择：

- **Mutex**: 适用于独占访问，简单高效
- **RwLock**: 适用于读多写少的场景，允许多个读取者

```rust
use std::sync::{Mutex, RwLock};

// 独占访问
let data = Mutex::new(vec![1, 2, 3]);
let mut guard = data.lock().unwrap();
guard.push(4);

// 读写分离
let data = RwLock::new(vec![1, 2, 3]);
{
    let reader = data.read().unwrap(); // 多个读取者
    println!("{:?}", *reader);
}
{
    let mut writer = data.write().unwrap(); // 单个写入者
    writer.push(4);
}
```

### Q: 如何避免死锁？

A: 使用一致的锁顺序和超时机制：

```rust
use std::sync::{Mutex, MutexGuard};
use std::time::Duration;

fn avoid_deadlock() {
    let mutex1 = Mutex::new(1);
    let mutex2 = Mutex::new(2);
    
    // 一致的锁顺序
    let guard1 = mutex1.lock().unwrap();
    let guard2 = mutex2.lock().unwrap();
    
    // 或者使用 try_lock 避免阻塞
    if let Ok(guard1) = mutex1.try_lock() {
        if let Ok(guard2) = mutex2.try_lock() {
            // 成功获取两个锁
        }
    }
}
```

### Q: 原子操作和锁有什么区别？

A: 原子操作更轻量，适用于简单操作：

```rust
use std::sync::atomic::{AtomicUsize, Ordering};

let counter = AtomicUsize::new(0);

// 原子操作 - 无锁，性能高
counter.fetch_add(1, Ordering::SeqCst);

// 锁 - 适用于复杂操作
let mutex_counter = Mutex::new(0);
let mut guard = mutex_counter.lock().unwrap();
*guard += 1;
```

### Q: 如何实现条件变量？

A: 使用 `Condvar` 进行线程协调：

```rust
use std::sync::{Arc, Mutex, Condvar};
use std::thread;

fn condition_variable_example() {
    let pair = Arc::new((Mutex::new(false), Condvar::new()));
    let pair2 = pair.clone();
    
    // 等待线程
    let waiter = thread::spawn(move || {
        let (lock, cvar) = &*pair2;
        let mut started = lock.lock().unwrap();
        while !*started {
            started = cvar.wait(started).unwrap();
        }
        println!("Condition met!");
    });
    
    // 通知线程
    thread::sleep(Duration::from_millis(100));
    let (lock, cvar) = &*pair;
    let mut started = lock.lock().unwrap();
    *started = true;
    cvar.notify_one();
    
    waiter.join().unwrap();
}
```

### Q: 如何实现无锁数据结构？

A: 使用原子操作和 CAS（Compare-And-Swap）：

```rust
use std::sync::atomic::{AtomicPtr, Ordering};
use std::ptr;

struct LockFreeStack<T> {
    head: AtomicPtr<Node<T>>,
}

struct Node<T> {
    data: T,
    next: AtomicPtr<Node<T>>,
}

impl<T> LockFreeStack<T> {
    fn new() -> Self {
        LockFreeStack {
            head: AtomicPtr::new(ptr::null_mut()),
        }
    }
    
    fn push(&self, data: T) {
        let new_node = Box::into_raw(Box::new(Node {
            data,
            next: AtomicPtr::new(ptr::null_mut()),
        }));
        
        loop {
            let head = self.head.load(Ordering::Acquire);
            unsafe {
                (*new_node).next.store(head, Ordering::Release);
            }
            
            if self.head.compare_exchange_weak(
                head,
                new_node,
                Ordering::Release,
                Ordering::Relaxed,
            ).is_ok() {
                break;
            }
        }
    }
}
```

## 性能优化

### Q: 如何优化进程创建的性能？

A: 使用进程池和预创建：

```rust
use std::sync::mpsc;
use std::thread;

struct ProcessPool {
    workers: Vec<thread::JoinHandle<()>>,
    sender: mpsc::Sender<ProcessTask>,
}

impl ProcessPool {
    fn new(size: usize) -> Self {
        let (sender, receiver) = mpsc::channel();
        let receiver = Arc::new(Mutex::new(receiver));
        
        let mut workers = Vec::new();
        for _ in 0..size {
            let receiver = receiver.clone();
            workers.push(thread::spawn(move || {
                while let Ok(task) = receiver.lock().unwrap().recv() {
                    // 处理任务
                }
            }));
        }
        
        ProcessPool { workers, sender }
    }
}
```

### Q: 如何优化 IPC 性能？

A: 使用零拷贝和批量传输：

```rust
use std::sync::Arc;

struct ZeroCopyBuffer {
    data: Arc<[u8]>,
    ref_count: Arc<AtomicUsize>,
}

impl ZeroCopyBuffer {
    fn new(data: Vec<u8>) -> Self {
        ZeroCopyBuffer {
            data: Arc::from(data),
            ref_count: Arc::new(AtomicUsize::new(1)),
        }
    }
    
    fn clone(&self) -> Self {
        self.ref_count.fetch_add(1, Ordering::SeqCst);
        ZeroCopyBuffer {
            data: self.data.clone(),
            ref_count: self.ref_count.clone(),
        }
    }
}
```

### Q: 如何监控进程性能？

A: 使用性能指标和监控工具：

```rust
use std::time::{Duration, Instant};

struct PerformanceMonitor {
    start_time: Instant,
    request_count: AtomicUsize,
    total_response_time: AtomicU64,
}

impl PerformanceMonitor {
    fn new() -> Self {
        PerformanceMonitor {
            start_time: Instant::now(),
            request_count: AtomicUsize::new(0),
            total_response_time: AtomicU64::new(0),
        }
    }
    
    fn record_request(&self, response_time: Duration) {
        self.request_count.fetch_add(1, Ordering::Relaxed);
        self.total_response_time.fetch_add(
            response_time.as_millis() as u64,
            Ordering::Relaxed
        );
    }
    
    fn get_stats(&self) -> PerformanceStats {
        let count = self.request_count.load(Ordering::Relaxed);
        let total_time = self.total_response_time.load(Ordering::Relaxed);
        
        PerformanceStats {
            request_count: count,
            average_response_time: if count > 0 {
                Duration::from_millis(total_time / count as u64)
            } else {
                Duration::from_millis(0)
            },
            uptime: self.start_time.elapsed(),
        }
    }
}
```

## 错误处理

### Q: 如何处理进程启动失败？

A: 使用适当的错误处理和重试机制：

```rust
use std::process::Command;
use std::time::Duration;

fn start_process_with_retry(command: &str, max_retries: u32) -> Result<(), Box<dyn std::error::Error>> {
    for attempt in 1..=max_retries {
        match Command::new(command).spawn() {
            Ok(_) => return Ok(()),
            Err(e) => {
                eprintln!("Attempt {} failed: {}", attempt, e);
                if attempt < max_retries {
                    std::thread::sleep(Duration::from_secs(1));
                }
            }
        }
    }
    Err("Failed to start process after all retries".into())
}
```

### Q: 如何处理 IPC 超时？

A: 使用超时机制和错误恢复：

```rust
use std::sync::mpsc;
use std::time::Duration;

fn ipc_with_timeout<T>(receiver: &mpsc::Receiver<T>, timeout: Duration) -> Result<T, String> {
    match receiver.recv_timeout(timeout) {
        Ok(value) => Ok(value),
        Err(mpsc::RecvTimeoutError::Timeout) => {
            Err("IPC timeout".to_string())
        }
        Err(mpsc::RecvTimeoutError::Disconnected) => {
            Err("IPC disconnected".to_string())
        }
    }
}
```

### Q: 如何处理资源泄漏？

A: 使用 RAII 模式和自动清理：

```rust
use std::sync::{Arc, Mutex};
use std::sync::atomic::{AtomicUsize, Ordering};

struct ResourceManager {
    resources: Arc<Mutex<Vec<Resource>>>,
    ref_count: Arc<AtomicUsize>,
}

impl ResourceManager {
    fn new() -> Self {
        ResourceManager {
            resources: Arc::new(Mutex::new(Vec::new())),
            ref_count: Arc::new(AtomicUsize::new(1)),
        }
    }
    
    fn clone(&self) -> Self {
        self.ref_count.fetch_add(1, Ordering::SeqCst);
        ResourceManager {
            resources: self.resources.clone(),
            ref_count: self.ref_count.clone(),
        }
    }
}

impl Drop for ResourceManager {
    fn drop(&mut self) {
        if self.ref_count.fetch_sub(1, Ordering::SeqCst) == 1 {
            // 最后一个引用，清理资源
            if let Ok(mut resources) = self.resources.lock() {
                resources.clear();
            }
        }
    }
}
```

## 跨平台兼容性

### Q: 如何处理不同平台的差异？

A: 使用条件编译和平台抽象：

```rust
#[cfg(target_os = "windows")]
fn get_process_info(pid: u32) -> Result<ProcessInfo, Box<dyn std::error::Error>> {
    // Windows 特定的实现
    Ok(ProcessInfo::new())
}

#[cfg(not(target_os = "windows"))]
fn get_process_info(pid: u32) -> Result<ProcessInfo, Box<dyn std::error::Error>> {
    // Unix 特定的实现
    Ok(ProcessInfo::new())
}

trait PlatformProcessManager {
    fn create_process(&self, command: &str) -> Result<Child, Box<dyn std::error::Error>>;
    fn kill_process(&self, pid: u32) -> Result<(), Box<dyn std::error::Error>>;
}
```

### Q: 如何处理信号？

A: 使用跨平台的信号处理：

```rust
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

fn signal_handling() -> Result<(), Box<dyn std::error::Error>> {
    let running = Arc::new(AtomicBool::new(true));
    let running_clone = running.clone();
    
    ctrlc::set_handler(move || {
        running_clone.store(false, Ordering::SeqCst);
    })?;
    
    while running.load(Ordering::SeqCst) {
        // 主程序逻辑
        std::thread::sleep(Duration::from_millis(100));
    }
    
    Ok(())
}
```

## 调试和诊断

### Q: 如何调试进程间通信问题？

A: 使用日志和调试工具：

```rust
use std::sync::atomic::{AtomicUsize, Ordering};

struct IPCDebugger {
    message_count: AtomicUsize,
    error_count: AtomicUsize,
}

impl IPCDebugger {
    fn new() -> Self {
        IPCDebugger {
            message_count: AtomicUsize::new(0),
            error_count: AtomicUsize::new(0),
        }
    }
    
    fn log_message(&self, message: &str) {
        let count = self.message_count.fetch_add(1, Ordering::Relaxed);
        println!("IPC Message #{}: {}", count + 1, message);
    }
    
    fn log_error(&self, error: &str) {
        let count = self.error_count.fetch_add(1, Ordering::Relaxed);
        eprintln!("IPC Error #{}: {}", count + 1, error);
    }
}
```

### Q: 如何诊断性能问题？

A: 使用性能分析工具和指标：

```rust
use std::time::{Duration, Instant};

struct PerformanceProfiler {
    measurements: Vec<Duration>,
}

impl PerformanceProfiler {
    fn new() -> Self {
        PerformanceProfiler {
            measurements: Vec::new(),
        }
    }
    
    fn measure<F, R>(&mut self, f: F) -> R
    where
        F: FnOnce() -> R,
    {
        let start = Instant::now();
        let result = f();
        let duration = start.elapsed();
        self.measurements.push(duration);
        result
    }
    
    fn get_statistics(&self) -> PerformanceStatistics {
        if self.measurements.is_empty() {
            return PerformanceStatistics::default();
        }
        
        let total: Duration = self.measurements.iter().sum();
        let count = self.measurements.len();
        let average = total / count as u32;
        
        let min = self.measurements.iter().min().unwrap();
        let max = self.measurements.iter().max().unwrap();
        
        PerformanceStatistics {
            count,
            total,
            average,
            min: *min,
            max: *max,
        }
    }
}
```

---

*本 FAQ 涵盖了进程、通信与同步机制模块中最常见的问题和解决方案，为开发者提供实用的参考指南。*
