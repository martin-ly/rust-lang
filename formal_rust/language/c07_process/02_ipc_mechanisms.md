# 进程间通信机制

## 概述

进程间通信（IPC）是分布式系统和并发编程的核心技术。Rust 通过类型安全的抽象提供了多种 IPC 机制，包括管道、共享内存、消息队列和套接字通信。本章深入探讨这些机制的设计原理、实现方式以及最佳实践。

## 管道通信

### 匿名管道

匿名管道是最基本的 IPC 机制，适用于父子进程间的单向通信。

```rust
use std::process::{Command, Stdio};
use std::io::{self, Write, Read};

fn anonymous_pipe_example() -> io::Result<()> {
    // 创建子进程，设置管道
    let mut child = Command::new("grep")
        .arg("pattern")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()?;
    
    // 获取子进程的 stdin
    let mut stdin = child.stdin.take().unwrap();
    
    // 向子进程写入数据
    stdin.write_all(b"line1\nline2\npattern\nline3\n")?;
    drop(stdin); // 关闭 stdin，发送 EOF
    
    // 读取子进程的输出
    let output = child.wait_with_output()?;
    println!("Output: {}", String::from_utf8_lossy(&output.stdout));
    
    Ok(())
}
```

### 命名管道（FIFO）

命名管道允许无关进程间的通信。

```rust
use std::fs::File;
use std::io::{self, Read, Write};
use std::os::unix::fs::FileTypeExt;

fn named_pipe_example() -> io::Result<()> {
    let pipe_path = "/tmp/my_pipe";
    
    // 创建命名管道
    unsafe {
        use std::os::unix::fs::FileTypeExt;
        std::os::unix::fs::mkfifo(pipe_path, 0o666).unwrap();
    }
    
    // 写入进程
    let write_handle = std::thread::spawn(move || {
        let mut file = File::create(pipe_path).unwrap();
        file.write_all(b"Hello from writer!\n").unwrap();
    });
    
    // 读取进程
    let read_handle = std::thread::spawn(move || {
        let mut file = File::open(pipe_path).unwrap();
        let mut buffer = [0; 1024];
        let n = file.read(&mut buffer).unwrap();
        println!("Read: {}", String::from_utf8_lossy(&buffer[..n]));
    });
    
    write_handle.join().unwrap();
    read_handle.join().unwrap();
    
    // 清理
    std::fs::remove_file(pipe_path).unwrap();
    Ok(())
}
```

### 双向管道通信

```rust
use std::process::{Command, Stdio};
use std::io::{self, Write, Read, BufRead, BufReader};

fn bidirectional_pipe() -> io::Result<()> {
    let mut child = Command::new("python3")
        .arg("-c")
        .arg("import sys; print('Ready'); sys.stdout.flush(); 
              for line in sys.stdin: print(f'Echo: {line.strip()}'); sys.stdout.flush()")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()?;
    
    let mut stdin = child.stdin.take().unwrap();
    let stdout = child.stdout.take().unwrap();
    let mut reader = BufReader::new(stdout);
    
    // 读取初始响应
    let mut line = String::new();
    reader.read_line(&mut line)?;
    println!("Child says: {}", line.trim());
    
    // 发送消息并读取响应
    let messages = vec!["Hello", "World", "Rust", "IPC"];
    for msg in messages {
        writeln!(stdin, "{}", msg)?;
        stdin.flush()?;
        
        line.clear();
        reader.read_line(&mut line)?;
        println!("Response: {}", line.trim());
    }
    
    drop(stdin);
    child.wait()?;
    Ok(())
}
```

## 共享内存

### 基础共享内存

```rust
use std::sync::{Arc, Mutex};
use std::thread;

struct SharedMemory<T> {
    data: Arc<Mutex<T>>,
}

impl<T> SharedMemory<T> {
    fn new(data: T) -> Self {
        SharedMemory {
            data: Arc::new(Mutex::new(data)),
        }
    }
    
    fn read(&self) -> T 
    where 
        T: Clone,
    {
        self.data.lock().unwrap().clone()
    }
    
    fn write(&self, value: T) {
        *self.data.lock().unwrap() = value;
    }
}

fn shared_memory_example() {
    let shared = SharedMemory::new(0);
    let shared_clone = shared.clone();
    
    // 写入线程
    let writer = thread::spawn(move || {
        for i in 1..=10 {
            shared.write(i);
            thread::sleep(std::time::Duration::from_millis(100));
        }
    });
    
    // 读取线程
    let reader = thread::spawn(move || {
        for _ in 0..10 {
            let value = shared_clone.read();
            println!("Read: {}", value);
            thread::sleep(std::time::Duration::from_millis(50));
        }
    });
    
    writer.join().unwrap();
    reader.join().unwrap();
}
```

### 内存映射文件

```rust
use memmap2::{Mmap, MmapMut};
use std::fs::OpenOptions;

fn memory_mapped_file() -> io::Result<()> {
    let file = OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .open("shared_data.bin")?;
    
    // 设置文件大小
    file.set_len(1024)?;
    
    // 创建内存映射
    let mut mmap = unsafe { MmapMut::map_mut(&file)? };
    
    // 写入数据
    mmap[0..8].copy_from_slice(&42u64.to_le_bytes());
    mmap.flush()?;
    
    // 在另一个进程中读取
    let child = Command::new("cat")
        .arg("shared_data.bin")
        .output()?;
    
    println!("Child output: {:?}", child.stdout);
    Ok(())
}
```

## 消息队列

### 自定义消息队列

```rust
use std::collections::VecDeque;
use std::sync::{Arc, Mutex, Condvar};
use std::thread;

struct MessageQueue<T> {
    queue: Arc<Mutex<VecDeque<T>>>,
    not_empty: Arc<Condvar>,
}

impl<T> MessageQueue<T> {
    fn new() -> Self {
        MessageQueue {
            queue: Arc::new(Mutex::new(VecDeque::new())),
            not_empty: Arc::new(Condvar::new()),
        }
    }
    
    fn send(&self, message: T) {
        let mut queue = self.queue.lock().unwrap();
        queue.push_back(message);
        self.not_empty.notify_one();
    }
    
    fn receive(&self) -> Option<T> {
        let mut queue = self.queue.lock().unwrap();
        while queue.is_empty() {
            queue = self.not_empty.wait(queue).unwrap();
        }
        queue.pop_front()
    }
}

fn message_queue_example() {
    let mq = Arc::new(MessageQueue::new());
    let mq_clone = mq.clone();
    
    // 发送者
    let sender = thread::spawn(move || {
        for i in 0..10 {
            mq.send(format!("Message {}", i));
            thread::sleep(std::time::Duration::from_millis(100));
        }
    });
    
    // 接收者
    let receiver = thread::spawn(move || {
        for _ in 0..10 {
            if let Some(msg) = mq_clone.receive() {
                println!("Received: {}", msg);
            }
        }
    });
    
    sender.join().unwrap();
    receiver.join().unwrap();
}
```

### 系统消息队列

```rust
use std::sync::mpsc;

fn system_message_queue() {
    let (tx, rx) = mpsc::channel();
    let tx_clone = tx.clone();
    
    // 多个发送者
    let sender1 = thread::spawn(move || {
        for i in 0..5 {
            tx.send(format!("Sender1: {}", i)).unwrap();
            thread::sleep(std::time::Duration::from_millis(100));
        }
    });
    
    let sender2 = thread::spawn(move || {
        for i in 0..5 {
            tx_clone.send(format!("Sender2: {}", i)).unwrap();
            thread::sleep(std::time::Duration::from_millis(150));
        }
    });
    
    // 接收者
    let receiver = thread::spawn(move || {
        for msg in rx {
            println!("{}", msg);
        }
    });
    
    sender1.join().unwrap();
    sender2.join().unwrap();
    drop(tx); // 关闭发送端
    receiver.join().unwrap();
}
```

## 套接字通信

### Unix 域套接字

```rust
use std::os::unix::net::{UnixStream, UnixListener};
use std::io::{self, Read, Write};

fn unix_socket_example() -> io::Result<()> {
    let socket_path = "/tmp/rust_ipc.sock";
    
    // 清理旧套接字
    let _ = std::fs::remove_file(socket_path);
    
    // 服务器
    let server = thread::spawn(move || {
        let listener = UnixListener::bind(socket_path)?;
        println!("Server listening on {}", socket_path);
        
        for stream in listener.incoming() {
            let mut stream = stream?;
            let mut buffer = [0; 1024];
            let n = stream.read(&mut buffer)?;
            let message = String::from_utf8_lossy(&buffer[..n]);
            println!("Server received: {}", message);
            
            let response = format!("Echo: {}", message);
            stream.write_all(response.as_bytes())?;
        }
        Ok::<(), io::Error>(())
    });
    
    // 客户端
    thread::sleep(std::time::Duration::from_millis(100));
    let client = thread::spawn(move || {
        let mut stream = UnixStream::connect(socket_path)?;
        let message = "Hello from client!";
        stream.write_all(message.as_bytes())?;
        
        let mut buffer = [0; 1024];
        let n = stream.read(&mut buffer)?;
        let response = String::from_utf8_lossy(&buffer[..n]);
        println!("Client received: {}", response);
        
        Ok::<(), io::Error>(())
    });
    
    client.join().unwrap()?;
    server.join().unwrap()?;
    
    // 清理
    std::fs::remove_file(socket_path)?;
    Ok(())
}
```

### TCP 套接字

```rust
use std::net::{TcpListener, TcpStream};
use std::io::{self, Read, Write};

fn tcp_socket_example() -> io::Result<()> {
    let server = thread::spawn(|| {
        let listener = TcpListener::bind("127.0.0.1:8080")?;
        println!("TCP Server listening on 127.0.0.1:8080");
        
        for stream in listener.incoming() {
            let mut stream = stream?;
            let mut buffer = [0; 1024];
            let n = stream.read(&mut buffer)?;
            let message = String::from_utf8_lossy(&buffer[..n]);
            println!("Server received: {}", message);
            
            let response = format!("TCP Echo: {}", message);
            stream.write_all(response.as_bytes())?;
        }
        Ok::<(), io::Error>(())
    });
    
    thread::sleep(std::time::Duration::from_millis(100));
    
    let client = thread::spawn(|| {
        let mut stream = TcpStream::connect("127.0.0.1:8080")?;
        let message = "Hello TCP!";
        stream.write_all(message.as_bytes())?;
        
        let mut buffer = [0; 1024];
        let n = stream.read(&mut buffer)?;
        let response = String::from_utf8_lossy(&buffer[..n]);
        println!("Client received: {}", response);
        
        Ok::<(), io::Error>(())
    });
    
    client.join().unwrap()?;
    server.join().unwrap()?;
    Ok(())
}
```

## 高级 IPC 模式

### 发布-订阅模式

```rust
use std::collections::HashMap;
use std::sync::{Arc, RwLock};

struct PubSub<T> {
    subscribers: Arc<RwLock<HashMap<String, Vec<Box<dyn Fn(T) + Send + Sync>>>>>,
}

impl<T: Clone + Send + Sync + 'static> PubSub<T> {
    fn new() -> Self {
        PubSub {
            subscribers: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    fn subscribe<F>(&self, topic: String, callback: F)
    where
        F: Fn(T) + Send + Sync + 'static,
    {
        let mut subs = self.subscribers.write().unwrap();
        subs.entry(topic).or_insert_with(Vec::new).push(Box::new(callback));
    }
    
    fn publish(&self, topic: &str, message: T) {
        if let Some(callbacks) = self.subscribers.read().unwrap().get(topic) {
            for callback in callbacks {
                callback(message.clone());
            }
        }
    }
}

fn pubsub_example() {
    let pubsub = Arc::new(PubSub::new());
    let pubsub_clone = pubsub.clone();
    
    // 订阅者
    pubsub.subscribe("news".to_string(), move |msg: String| {
        println!("News subscriber received: {}", msg);
    });
    
    pubsub.subscribe("weather".to_string(), move |msg: String| {
        println!("Weather subscriber received: {}", msg);
    });
    
    // 发布者
    let publisher = thread::spawn(move || {
        pubsub_clone.publish("news", "Breaking news!".to_string());
        thread::sleep(std::time::Duration::from_millis(100));
        pubsub_clone.publish("weather", "Sunny today!".to_string());
    });
    
    publisher.join().unwrap();
}
```

### 请求-响应模式

```rust
use std::sync::mpsc;

struct RequestResponse {
    request_tx: mpsc::Sender<String>,
    response_rx: mpsc::Receiver<String>,
}

impl RequestResponse {
    fn new() -> (Self, RequestHandler) {
        let (request_tx, request_rx) = mpsc::channel();
        let (response_tx, response_rx) = mpsc::channel();
        
        let client = RequestResponse {
            request_tx,
            response_rx,
        };
        
        let handler = RequestHandler {
            request_rx,
            response_tx,
        };
        
        (client, handler)
    }
    
    fn request(&self, message: String) -> io::Result<String> {
        self.request_tx.send(message)?;
        Ok(self.response_rx.recv()?)
    }
}

struct RequestHandler {
    request_rx: mpsc::Receiver<String>,
    response_tx: mpsc::Sender<String>,
}

impl RequestHandler {
    fn run(mut self) {
        while let Ok(request) = self.request_rx.recv() {
            let response = format!("Processed: {}", request);
            let _ = self.response_tx.send(response);
        }
    }
}

fn request_response_example() {
    let (client, handler) = RequestResponse::new();
    
    // 启动处理器
    let handler_thread = thread::spawn(move || {
        handler.run();
    });
    
    // 发送请求
    let client_thread = thread::spawn(move || {
        for i in 0..5 {
            let response = client.request(format!("Request {}", i)).unwrap();
            println!("Response: {}", response);
        }
    });
    
    client_thread.join().unwrap();
    handler_thread.join().unwrap();
}
```

## 性能优化与最佳实践

### 零拷贝 IPC

```rust
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

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
    
    fn as_slice(&self) -> &[u8] {
        &self.data
    }
}

impl Drop for ZeroCopyBuffer {
    fn drop(&mut self) {
        if self.ref_count.fetch_sub(1, Ordering::SeqCst) == 1 {
            // 最后一个引用被释放，可以安全清理
        }
    }
}
```

### 批量传输

```rust
use std::sync::mpsc;

struct BatchProcessor<T> {
    batch_size: usize,
    timeout: std::time::Duration,
}

impl<T> BatchProcessor<T> {
    fn new(batch_size: usize, timeout: std::time::Duration) -> Self {
        BatchProcessor { batch_size, timeout }
    }
    
    fn process_batch<I>(&self, items: I) -> Vec<T>
    where
        I: Iterator<Item = T>,
    {
        let mut batch = Vec::new();
        let mut items = items.peekable();
        
        while let Some(item) = items.next() {
            batch.push(item);
            
            if batch.len() >= self.batch_size || items.peek().is_none() {
                // 处理批次
                break;
            }
        }
        
        batch
    }
}
```

## 总结

Rust 的 IPC 机制通过类型安全的抽象提供了强大的进程间通信能力。从简单的管道到复杂的发布-订阅模式，Rust 确保了通信的安全性和效率。

### 关键要点

1. **类型安全** - 所有 IPC 机制都通过类型系统保证安全性
2. **零成本抽象** - 高性能的 IPC 实现
3. **错误处理** - 全面的错误处理机制
4. **跨平台兼容** - 统一的 API 适配不同平台

### 下一步

在下一章中，我们将探讨同步与并发控制机制，包括信号量、互斥锁、条件变量和原子操作。
