# Rust 生产案例研究

本文档通过五个真实的生产级案例，展示 Rust 语言特性如何在实际项目中协同工作。每个案例都包含完整的设计思路、实现细节和经验总结，适合中级到高级 Rust 学习者参考。

---

## 案例 1: 实现一个线程池 (like Rayon)

### 背景

在高性能计算场景中，需要利用多核 CPU 并行处理任务。Rayon 是 Rust 生态中著名的并行计算库，其核心是一个高效的工作窃取(work-stealing)线程池。

### 问题分析

- 如何高效分配任务到多个工作线程？
- 如何避免线程间的锁竞争？
- 如何实现任务窃取以平衡负载？
- 如何处理任务结果的返回？

### 架构设计

```
┌─────────────────────────────────────────────────────────────┐
│                      ThreadPool                              │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐         │
│  │  Worker 1   │  │  Worker 2   │  │  Worker N   │         │
│  │ ┌─────────┐ │  │ ┌─────────┐ │  │ ┌─────────┐ │         │
│  │ │ Task Q  │ │  │ │ Task Q  │ │  │ │ Task Q  │ │         │
│  │ │  [A,B]  │ │  │ │  [C]    │ │  │ │  [D]    │ │         │
│  │ └────┬────┘ │  │ └────┬────┘ │  │ └────┬────┘ │         │
│  │      │      │  │      │      │  │      │      │         │
│  │  Stealer◄──────►Stealer◄──────►Stealer   │      │         │
│  └─────────────┘  └─────────────┘  └─────────────┘         │
│         ▲                                                  │
│         │ Spawn                                            │
│    ┌────┴────┐                                             │
│    │  Sender │◄─── User                                    │
│    └─────────┘                                             │
└─────────────────────────────────────────────────────────────┘
```

### 核心实现

```rust
use std::sync::{mpsc, Arc, Mutex};
use std::thread;

// 任务类型: 一个可以发送一次的闭包
pub struct Job {
    // Box<dyn FnOnce() + Send + 'static> 允许存储任何可以安全发送到其他线程的闭包
    f: Box<dyn FnOnce() + Send + 'static>,
}

// 工作线程的消息类型
enum WorkerMessage {
    NewJob(Job),
    Terminate,
}

// 工作线程结构
pub struct Worker {
    id: usize,
    thread: Option<thread::JoinHandle<()>>,
}

impl Worker {
    fn new(id: usize, receiver: Arc<Mutex<mpsc::Receiver<WorkerMessage>>>) -> Worker {
        let thread = thread::spawn(move || {
            loop {
                // 获取锁并接收消息
                let message = receiver.lock().unwrap().recv();

                match message {
                    Ok(WorkerMessage::NewJob(job)) => {
                        println!("Worker {} got a job; executing.", id);
                        (job.f)(); // 执行任务
                    }
                    Ok(WorkerMessage::Terminate) => {
                        println!("Worker {} was told to terminate.", id);
                        break;
                    }
                    Err(_) => break,
                }
            }
        });

        Worker {
            id,
            thread: Some(thread),
        }
    }
}

// 线程池
pub struct ThreadPool {
    workers: Vec<Worker>,
    sender: Option<mpsc::Sender<WorkerMessage>>,
}

impl ThreadPool {
    pub fn new(size: usize) -> ThreadPool {
        assert!(size > 0);

        // 创建通道用于任务分发
        let (sender, receiver) = mpsc::channel();
        let receiver = Arc::new(Mutex::new(receiver));

        // 创建工作线程
        let mut workers = Vec::with_capacity(size);
        for id in 0..size {
            workers.push(Worker::new(id, Arc::clone(&receiver)));
        }

        ThreadPool {
            workers,
            sender: Some(sender),
        }
    }

    pub fn execute<F>(&self, f: F)
    where
        F: FnOnce() + Send + 'static,
    {
        let job = Job { f: Box::new(f) };
        // 发送任务到工作队列
        self.sender
            .as_ref()
            .unwrap()
            .send(WorkerMessage::NewJob(job))
            .unwrap();
    }
}

impl Drop for ThreadPool {
    fn drop(&mut self) {
        // 发送终止信号给所有工作线程
        for _ in &self.workers {
            self.sender.as_ref().unwrap().send(WorkerMessage::Terminate).ok();
        }

        // 等待所有线程结束
        for worker in &mut self.workers {
            if let Some(thread) = worker.thread.take() {
                thread.join().unwrap();
            }
        }
    }
}
```

### 关键要点

1. **类型擦除**: 使用 `Box<dyn FnOnce() + Send + 'static>` 存储不同类型的闭包
2. **RAII 模式**: 通过 `Drop` 实现优雅关闭，避免资源泄漏
3. **线程安全**: `Arc<Mutex<T>>` 实现多线程共享状态的安全访问
4. **解耦设计**: 将任务提交与执行分离，提高系统的可扩展性

---

## 案例 2: 实现异步 HTTP 客户端

### 背景

现代应用需要高效地并发处理大量网络请求。使用 async/await 可以编写看起来像同步代码、但能高效利用系统资源的异步程序。

### 问题分析

- 如何管理大量并发连接而不阻塞线程？
- 如何实现请求的超时和取消？
- 如何处理连接池和复用？
- 如何优雅地处理错误和重试？

### 架构设计

```
┌────────────────────────────────────────────────────────────┐
│                    AsyncHttpClient                          │
│                                                             │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────┐│
│  │ Request     │  │ Connection  │  │ Retry Logic         ││
│  │ Builder     │  │ Pool        │  │ (Exponential Backoff)││
│  └──────┬──────┘  └──────┬──────┘  └──────────┬──────────┘│
│         │                │                     │           │
│         ▼                ▼                     ▼           │
│  ┌─────────────────────────────────────────────────────┐  │
│  │                    Runtime                           │  │
│  │  ┌─────────┐  ┌─────────┐  ┌─────────┐             │  │
│  │  │ Task 1  │  │ Task 2  │  │ Task N  │ ...         │  │
│  │  │ (HTTP)  │  │ (HTTP)  │  │ (HTTP)  │             │  │
│  │  └────┬────┘  └────┬────┘  └────┬────┘             │  │
│  │       └────────────┴────────────┘                   │  │
│  │                   Reactor                           │  │
│  └─────────────────────────────────────────────────────┘  │
└────────────────────────────────────────────────────────────┘
```

### 核心实现

```rust
use std::time::Duration;
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};
use tokio::time::{timeout, Instant, Sleep};
use tokio::net::TcpStream;

// HTTP 请求结构
pub struct Request {
    method: String,
    url: String,
    headers: Vec<(String, String)>,
    body: Option<Vec<u8>>,
}

pub struct RequestBuilder {
    request: Request,
}

impl RequestBuilder {
    pub fn new(method: &str, url: &str) -> Self {
        RequestBuilder {
            request: Request {
                method: method.to_string(),
                url: url.to_string(),
                headers: Vec::new(),
                body: None,
            },
        }
    }

    pub fn header(mut self, key: &str, value: &str) -> Self {
        self.request.headers.push((key.to_string(), value.to_string()));
        self
    }

    pub fn body(mut self, body: Vec<u8>) -> Self {
        self.request.body = Some(body);
        self
    }

    pub fn build(self) -> Request {
        self.request
    }
}

// HTTP 响应结构
pub struct Response {
    pub status: u16,
    pub headers: Vec<(String, String)>,
    pub body: Vec<u8>,
}

// 带重试策略的请求
pub struct RetryConfig {
    pub max_retries: u32,
    pub initial_delay: Duration,
    pub max_delay: Duration,
}

impl Default for RetryConfig {
    fn default() -> Self {
        RetryConfig {
            max_retries: 3,
            initial_delay: Duration::from_millis(100),
            max_delay: Duration::from_secs(10),
        }
    }
}

// 异步 HTTP 客户端
pub struct AsyncHttpClient {
    retry_config: RetryConfig,
    timeout: Duration,
}

impl AsyncHttpClient {
    pub fn new() -> Self {
        AsyncHttpClient {
            retry_config: RetryConfig::default(),
            timeout: Duration::from_secs(30),
        }
    }

    pub fn with_timeout(mut self, timeout: Duration) -> Self {
        self.timeout = timeout;
        self
    }

    pub async fn request(&self, req: Request) -> Result<Response, HttpError> {
        // 带重试的执行
        let mut last_error = None;
        let mut delay = self.retry_config.initial_delay;

        for attempt in 0..=self.retry_config.max_retries {
            match self.execute_request(&req).await {
                Ok(response) => return Ok(response),
                Err(e) if attempt < self.retry_config.max_retries => {
                    // 指数退避
                    tokio::time::sleep(delay).await;
                    delay = std::cmp::min(delay * 2, self.retry_config.max_delay);
                    last_error = Some(e);
                }
                Err(e) => return Err(e),
            }
        }

        Err(last_error.unwrap_or(HttpError::Unknown))
    }

    async fn execute_request(&self, req: &Request) -> Result<Response, HttpError> {
        // 使用 timeout 包装异步操作
        match timeout(self.timeout, self.do_request(req)).await {
            Ok(result) => result,
            Err(_) => Err(HttpError::Timeout),
        }
    }

    async fn do_request(&self, _req: &Request) -> Result<Response, HttpError> {
        // 实际的 HTTP 请求实现...
        // 这里简化处理，实际会使用 hyper 或 reqwest
        Ok(Response {
            status: 200,
            headers: vec![],
            body: vec![],
        })
    }
}

#[derive(Debug)]
pub enum HttpError {
    Timeout,
    ConnectionFailed,
    InvalidUrl,
    Unknown,
}

// 使用示例
async fn fetch_user_data(client: &AsyncHttpClient, user_id: u64) -> Result<String, HttpError> {
    let request = RequestBuilder::new("GET", &format!("https://api.example.com/users/{}", user_id))
        .header("Accept", "application/json")
        .header("Authorization", "Bearer token123")
        .build();

    let response = client.request(request).await?;

    if response.status == 200 {
        Ok(String::from_utf8_lossy(&response.body).to_string())
    } else {
        Err(HttpError::Unknown)
    }
}
```

### 关键要点

1. **Builder 模式**: `RequestBuilder` 提供流畅的 API 用于构造请求
2. **错误处理**: 使用 `?` 运算符和自定义错误类型实现清晰的错误传播
3. **超时控制**: `tokio::time::timeout` 防止请求无限挂起
4. **指数退避**: 智能重试策略避免服务器过载
5. **零成本抽象**: async/await 编译为高效的状态机，无运行时开销

---

## 案例 3: 实现内存安全的 LRU Cache

### 背景

缓存是提升系统性能的关键组件。LRU (Least Recently Used) 缓存需要在 O(1) 时间内完成读写操作，同时保证内存安全。

### 问题分析

- 如何在 O(1) 时间内完成读写和淘汰？
- 如何处理 key 和 value 的所有权关系？
- 如何避免内存泄漏和 use-after-free？
- 如何实现线程安全？

### 架构设计

```
┌──────────────────────────────────────────────────────────────┐
│                      LRUCache<K, V>                           │
│                                                                │
│  ┌─────────────────────────────────────────────────────────┐ │
│  │                   HashMap<K, NodePtr>                    │ │
│  │  ┌─────┐  ┌─────┐  ┌─────┐  ┌─────┐  ┌─────┐          │ │
│  │  │ Key1│  │ Key2│  │ Key3│  │ ... │  │ KeyN│          │ │
│  │  └──┬──┘  └──┬──┘  └──┬──┘  └─────┘  └──┬──┘          │ │
│  │     │        │        │                   │            │ │
│  │     ▼        ▼        ▼                   ▼            │ │
│  │  ┌─────┐  ┌─────┐  ┌─────┐            ┌─────┐         │ │
│  │  │Ptr 1│  │Ptr 2│  │Ptr 3│            │Ptr N│         │ │
│  │  └──┬──┘  └──┬──┘  └──┬──┘            └──┬──┘         │ │
│  └─────┼────────┼────────┼───────────────────┼───────────┘ │
│        │        │        │                   │              │
│        ▼        ▼        ▼                   ▼              │
│  ┌──────────────────────────────────────────────────────┐  │
│  │                   Doubly Linked List                  │  │
│  │                                                       │  │
│  │   ┌─────────┐    ┌─────────┐    ┌─────────┐         │  │
│  │   │  Node1  │◄──►│  Node2  │◄──►│  Node3  │◄──►...   │  │
│  │   │ (Most   │    │         │    │ (Least  │         │  │
│  │   │ Recent) │    │         │    │ Recent) │         │  │
│  │   └─────────┘    └─────────┘    └─────────┘         │  │
│  │                                                       │  │
│  └──────────────────────────────────────────────────────┘  │
└──────────────────────────────────────────────────────────────┘
```

### 核心实现

```rust
use std::collections::HashMap;
use std::hash::Hash;
use std::ptr::NonNull;

// 链表节点
struct Node<K, V> {
    key: K,
    value: V,
    prev: Option<NonNull<Node<K, V>>>,
    next: Option<NonNull<Node<K, V>>>,
}

pub struct LRUCache<K, V> {
    capacity: usize,
    map: HashMap<K, NonNull<Node<K, V>>>,
    // 哨兵节点: head.next 是最新使用的, tail.prev 是最久未使用的
    head: Box<Node<K, V>>,
    tail: Box<Node<K, V>>,
}

impl<K, V> LRUCache<K, V>
where
    K: Eq + Hash + Clone,
{
    pub fn new(capacity: usize) -> Self {
        let mut head = Box::new(Node {
            key: unsafe { std::mem::zeroed() },
            value: unsafe { std::mem::zeroed() },
            prev: None,
            next: None,
        });
        let mut tail = Box::new(Node {
            key: unsafe { std::mem::zeroed() },
            value: unsafe { std::mem::zeroed() },
            prev: None,
            next: None,
        });

        // 连接哨兵节点
        head.next = Some(NonNull::from(&mut *tail));
        tail.prev = Some(NonNull::from(&mut *head));

        LRUCache {
            capacity,
            map: HashMap::with_capacity(capacity),
            head,
            tail,
        }
    }

    pub fn get(&mut self, key: &K) -> Option<&V> {
        if let Some(&node_ptr) = self.map.get(key) {
            // 移动到链表头部(最近使用)
            unsafe {
                self.move_to_head(node_ptr);
                Some(&(*node_ptr.as_ptr()).value)
            }
        } else {
            None
        }
    }

    pub fn put(&mut self, key: K, value: V) {
        if let Some(&node_ptr) = self.map.get(&key) {
            // 更新已存在的节点
            unsafe {
                (*node_ptr.as_ptr()).value = value;
                self.move_to_head(node_ptr);
            }
        } else {
            // 创建新节点
            let new_node = Box::new(Node {
                key: key.clone(),
                value,
                prev: None,
                next: None,
            });
            let node_ptr = NonNull::from(Box::leak(new_node));

            self.map.insert(key, node_ptr);
            unsafe {
                self.add_to_head(node_ptr);
            }

            // 如果超过容量，淘汰最久未使用的
            if self.map.len() > self.capacity {
                unsafe {
                    self.remove_tail();
                }
            }
        }
    }

    unsafe fn move_to_head(&mut self, node: NonNull<Node<K, V>>) {
        self.remove_node(node);
        self.add_to_head(node);
    }

    unsafe fn remove_node(&mut self, node: NonNull<Node<K, V>>) {
        let node = node.as_ptr();
        if let Some(prev) = (*node).prev {
            (*prev.as_ptr()).next = (*node).next;
        }
        if let Some(next) = (*node).next {
            (*next.as_ptr()).prev = (*node).prev;
        }
    }

    unsafe fn add_to_head(&mut self, node: NonNull<Node<K, V>>) {
        let node = node.as_ptr();
        (*node).prev = Some(NonNull::from(&mut *self.head));
        (*node).next = self.head.next;

        if let Some(next) = self.head.next {
            (*next.as_ptr()).prev = Some(NonNull::from(&mut *node));
        }
        self.head.next = Some(NonNull::from(&mut *node));
    }

    unsafe fn remove_tail(&mut self) {
        if let Some(tail_prev) = self.tail.prev {
            if tail_prev.as_ptr() != &mut *self.head {
                let key = (*tail_prev.as_ptr()).key.clone();
                self.remove_node(tail_prev);
                self.map.remove(&key);
                // 释放内存
                let _ = Box::from_raw(tail_prev.as_ptr());
            }
        }
    }
}

// 确保 Drop 时释放所有节点
impl<K, V> Drop for LRUCache<K, V> {
    fn drop(&mut self) {
        unsafe {
            let mut current = self.head.next;
            while let Some(node) = current {
                if node.as_ptr() == &mut *self.tail {
                    break;
                }
                current = (*node.as_ptr()).next;
                let _ = Box::from_raw(node.as_ptr());
            }
        }
    }
}

// 线程安全的包装器
use std::sync::{Arc, RwLock};

pub struct ThreadSafeLRUCache<K, V> {
    inner: Arc<RwLock<LRUCache<K, V>>>,
}

impl<K, V> ThreadSafeLRUCache<K, V>
where
    K: Eq + Hash + Clone + Send + Sync + 'static,
    V: Send + Sync + 'static,
{
    pub fn new(capacity: usize) -> Self {
        ThreadSafeLRUCache {
            inner: Arc::new(RwLock::new(LRUCache::new(capacity))),
        }
    }

    pub fn get(&self, key: &K) -> Option<V>
    where
        V: Clone,
    {
        self.inner.read().unwrap().get(key).cloned()
    }

    pub fn put(&self, key: K, value: V) {
        self.inner.write().unwrap().put(key, value);
    }
}

impl<K, V> Clone for ThreadSafeLRUCache<K, V> {
    fn clone(&self) -> Self {
        ThreadSafeLRUCache {
            inner: Arc::clone(&self.inner),
        }
    }
}
```

### 关键要点

1. **Unsafe Rust 的审慎使用**: 使用 `NonNull` 实现 O(1) 链表操作，但通过封装确保外部 API 安全
2. **内存管理**: 使用 `Box::leak` 和 `Box::from_raw` 精细控制内存生命周期
3. **RAII 模式**: `Drop` 实现确保所有节点正确释放，避免内存泄漏
4. **线程安全**: 通过 `Arc<RwLock<T>>` 包装提供线程安全接口
5. **零拷贝优化**: 通过引用返回避免不必要的克隆

---

## 案例 4: 跨平台文件系统抽象

### 背景

需要编写能在 Windows、macOS 和 Linux 上运行的文件系统工具，处理不同平台的路径表示、权限模型和文件系统特性差异。

### 问题分析

- 如何处理不同平台的路径分隔符和格式？
- 如何统一不同平台的权限模型？
- 如何处理符号链接和硬链接？
- 如何实现高性能的文件遍历？

### 架构设计

```
┌────────────────────────────────────────────────────────────────┐
│                   CrossPlatformFs                              │
│                                                                 │
│  ┌───────────────┐  ┌───────────────┐  ┌───────────────────┐  │
│  │  PathUtils    │  │  Permissions  │  │  File Operations  │  │
│  │               │  │               │  │                   │  │
│  │ - join()      │  │ - set_mode()  │  │ - copy()          │  │
│  │ - normalize() │  │ - get_mode()  │  │ - move()          │  │
│  │ - absolute()  │  │ - is_readable │  │ - remove()        │  │
│  └───────┬───────┘  └───────┬───────┘  └─────────┬─────────┘  │
│          │                  │                    │             │
│          └──────────────────┼────────────────────┘             │
│                             ▼                                  │
│  ┌────────────────────────────────────────────────────────┐   │
│  │                    Platform Abstraction                 │   │
│  │                                                         │   │
│  │  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐  │   │
│  │  │   Windows    │  │    Unix      │  │    macOS     │  │   │
│  │  │              │  │              │  │              │  │   │
│  │  │ - UNC paths  │  │ - symlinks   │  │ - resource   │  │   │
│  │  │ - ACL        │  │ - umask      │  │   forks      │  │   │
│  │  │ - drive      │  │ - xattrs     │  │ - extended   │  │   │
│  │  │   letters    │  │              │  │   attrs      │  │   │
│  │  └──────────────┘  └──────────────┘  └──────────────┘  │   │
│  └────────────────────────────────────────────────────────┘   │
└────────────────────────────────────────────────────────────────┘
```

### 核心实现

```rust
use std::path::{Path, PathBuf, Component};
use std::io;
use std::fs;

// 跨平台路径处理
pub struct CrossPlatformPath {
    inner: PathBuf,
}

impl CrossPlatformPath {
    pub fn new<P: AsRef<Path>>(path: P) -> Self {
        CrossPlatformPath {
            inner: path.as_ref().to_path_buf(),
        }
    }

    // 规范化路径: 统一分隔符, 解析 . 和 ..
    pub fn normalize(&self) -> PathBuf {
        let mut components = Vec::new();

        for component in self.inner.components() {
            match component {
                Component::Prefix(_) | Component::RootDir => {
                    components.push(component.as_os_str().to_owned());
                }
                Component::CurDir => {
                    // 跳过 .
                }
                Component::ParentDir => {
                    // 处理 ..
                    if let Some(last) = components.last() {
                        if last != ".." && !last.to_string_lossy().ends_with(":") {
                            components.pop();
                        } else {
                            components.push(component.as_os_str().to_owned());
                        }
                    }
                }
                Component::Normal(name) => {
                    components.push(name.to_owned());
                }
            }
        }

        if components.is_empty() {
            return PathBuf::from(".");
        }

        let mut result = PathBuf::new();
        for (i, comp) in components.iter().enumerate() {
            if i > 0 {
                result.push(comp);
            } else {
                result = PathBuf::from(comp);
            }
        }
        result
    }

    // 获取相对于 base 的路径
    pub fn relative_to(&self, base: &Path) -> Option<PathBuf> {
        let normalized_self = self.normalize();
        let normalized_base = CrossPlatformPath::new(base).normalize();

        let self_components: Vec<_> = normalized_self.components().collect();
        let base_components: Vec<_> = normalized_base.components().collect();

        let mut common_prefix = 0;
        for (a, b) in self_components.iter().zip(base_components.iter()) {
            if a == b {
                common_prefix += 1;
            } else {
                break;
            }
        }

        let mut result = PathBuf::new();
        for _ in common_prefix..base_components.len() {
            result.push("..");
        }
        for comp in &self_components[common_prefix..] {
            result.push(comp.as_os_str());
        }

        Some(result)
    }
}

// 跨平台文件系统操作
pub struct CrossPlatformFs;

impl CrossPlatformFs {
    // 安全的递归删除(先处理内容再删除目录)
    pub fn remove_dir_all_safe(path: &Path) -> io::Result<()> {
        fn remove_dir_all_recursive(path: &Path) -> io::Result<()> {
            // 先处理目录内容
            for entry in fs::read_dir(path)? {
                let entry = entry?;
                let path = entry.path();

                if path.is_dir() {
                    remove_dir_all_recursive(&path)?;
                } else {
                    fs::remove_file(&path)?;
                }
            }
            // 最后删除空目录
            fs::remove_dir(path)
        }

        if path.is_dir() {
            remove_dir_all_recursive(path)
        } else {
            fs::remove_file(path)
        }
    }

    // 原子写入: 写入临时文件后重命名
    pub fn write_atomic<P: AsRef<Path>>(path: P, contents: &[u8]) -> io::Result<()> {
        let path = path.as_ref();
        let temp_path = path.with_extension("tmp");

        // 写入临时文件
        fs::write(&temp_path, contents)?;

        // 原子重命名
        fs::rename(&temp_path, path)?;

        Ok(())
    }

    // 获取文件信息
    pub fn metadata(path: &Path) -> io::Result<FileMetadata> {
        let metadata = fs::metadata(path)?;

        #[cfg(unix)]
        {
            use std::os::unix::fs::MetadataExt;
            Ok(FileMetadata {
                size: metadata.len(),
                is_file: metadata.is_file(),
                is_dir: metadata.is_dir(),
                is_symlink: metadata.file_type().is_symlink(),
                permissions: Some(metadata.mode()),
                modified: metadata.modified().ok(),
                accessed: metadata.accessed().ok(),
            })
        }

        #[cfg(windows)]
        {
            use std::os::windows::fs::MetadataExt;
            Ok(FileMetadata {
                size: metadata.len(),
                is_file: metadata.is_file(),
                is_dir: metadata.is_dir(),
                is_symlink: metadata.file_type().is_symlink(),
                permissions: None, // Windows 使用 ACL
                modified: metadata.modified().ok(),
                accessed: metadata.accessed().ok(),
            })
        }
    }

    // 并行文件遍历
    pub fn walk_dir_parallel<F>(
        root: &Path,
        mut callback: F,
    ) -> io::Result<()>
    where
        F: FnMut(&Path) + Send + Clone,
    {
        use rayon::prelude::*;

        fn walk_recursive<F: FnMut(&Path) + Clone>(
            path: &Path,
            callback: &mut F,
        ) -> io::Result<()> {
            callback(path);

            if path.is_dir() {
                let entries: Vec<_> = fs::read_dir(path)?.collect::<Result<_, _>>()?;

                // 对子目录进行并行处理
                entries.par_iter().for_each_with(callback.clone(), |cb, entry| {
                    let _ = walk_recursive(&entry.path(), cb);
                });
            }
            Ok(())
        }

        walk_recursive(root, &mut callback)
    }
}

// 文件元数据结构
#[derive(Debug)]
pub struct FileMetadata {
    pub size: u64,
    pub is_file: bool,
    pub is_dir: bool,
    pub is_symlink: bool,
    pub permissions: Option<u32>, // Unix 权限模式
    pub modified: Option<std::time::SystemTime>,
    pub accessed: Option<std::time::SystemTime>,
}

// 平台特定的权限处理
pub struct PermissionManager;

impl PermissionManager {
    #[cfg(unix)]
    pub fn set_executable(path: &Path, executable: bool) -> io::Result<()> {
        use std::os::unix::fs::PermissionsExt;

        let mut permissions = fs::metadata(path)?.permissions();
        let mode = permissions.mode();

        if executable {
            permissions.set_mode(mode | 0o111); // 添加执行权限
        } else {
            permissions.set_mode(mode & !0o111); // 移除执行权限
        }

        fs::set_permissions(path, permissions)
    }

    #[cfg(windows)]
    pub fn set_executable(_path: &Path, _executable: bool) -> io::Result<()> {
        // Windows 通过文件扩展名决定可执行性
        Ok(())
    }
}
```

### 关键要点

1. **路径抽象**: 使用 `std::path::PathBuf` 和 `Component` 处理跨平台路径差异
2. **条件编译**: `#[cfg]` 属性处理平台特定代码
3. **原子操作**: `write_atomic` 确保数据完整性
4. **并行处理**: 使用 Rayon 实现高效的并行目录遍历
5. **安全删除**: 递归删除时先处理内容再删除目录，避免意外数据丢失

---

## 案例 5: 高性能日志库设计

### 背景

在高并发系统中，日志记录不能成为性能瓶颈。需要设计一个零分配、异步、可扩展的日志系统。

### 问题分析

- 如何避免日志记录阻塞业务代码？
- 如何减少内存分配和复制？
- 如何支持结构化日志和多种输出目标？
- 如何实现日志级别和热更新？

### 架构设计

```
┌─────────────────────────────────────────────────────────────────┐
│                     Log Architecture                             │
│                                                                   │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │                      User Code                            │  │
│  │                                                           │  │
│  │  info!("User {} logged in from {}", user_id, ip);         │  │
│  └──────────────────────────┬───────────────────────────────┘  │
│                             │                                     │
│                             ▼                                     │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │                    LogRecord (Zero-Copy)                  │  │
│  │                                                           │  │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────────┐  │  │
│  │  │ level: Info │  │ timestamp   │  │ message: &str    │  │  │
│  │  │ target:     │  │ thread_id   │  │ (borrowed from  │  │  │
│  │  │   "auth"    │  │ file/line   │  │  format_args!)  │  │  │
│  │  └─────────────┘  └─────────────┘  └─────────────────┘  │  │
│  └──────────────────────────┬───────────────────────────────┘  │
│                             │                                     │
│                             ▼                                     │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │                  Async Channel (crossbeam)                │  │
│  │                                                           │  │
│  │   生产者 ──► │ LogRecord │ LogRecord │ ... │ ◄── 消费者  │  │
│  │   (多线程)    └─────────┴─────────┴─────┘    (单线程)    │  │
│  │                                                           │  │
│  └──────────────────────────┬───────────────────────────────┘  │
│                             │                                     │
│              ┌──────────────┼──────────────┐                     │
│              ▼              ▼              ▼                     │
│  ┌────────────────┐ ┌─────────────┐ ┌─────────────────────┐    │
│  │ Console Output │ │ File Writer │ │ Structured (JSON)   │    │
│  │                │ │ (rotated)   │ │ (to ELK/CloudWatch) │    │
│  └────────────────┘ └─────────────┘ └─────────────────────┘    │
└─────────────────────────────────────────────────────────────────┘
```

### 核心实现

```rust
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::time::SystemTime;
use crossbeam::channel::{bounded, Sender, Receiver};

// 日志级别
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Level {
    Trace = 0,
    Debug = 1,
    Info = 2,
    Warn = 3,
    Error = 4,
}

impl Level {
    fn as_str(&self) -> &'static str {
        match self {
            Level::Trace => "TRACE",
            Level::Debug => "DEBUG",
            Level::Info => "INFO",
            Level::Warn => "WARN",
            Level::Error => "ERROR",
        }
    }
}

// 全局日志级别(原子操作, 可热更新)
static GLOBAL_LEVEL: AtomicUsize = AtomicUsize::new(Level::Info as usize);

pub fn set_max_level(level: Level) {
    GLOBAL_LEVEL.store(level as usize, Ordering::Relaxed);
}

fn max_level() -> Level {
    match GLOBAL_LEVEL.load(Ordering::Relaxed) {
        0 => Level::Trace,
        1 => Level::Debug,
        2 => Level::Info,
        3 => Level::Warn,
        _ => Level::Error,
    }
}

// 日志记录结构(尽量减少分配)
pub struct LogRecord {
    pub level: Level,
    pub target: &'static str,
    pub file: &'static str,
    pub line: u32,
    pub time: SystemTime,
    pub thread_id: std::thread::ThreadId,
    // 使用闭包延迟格式化, 避免不必要的字符串分配
    pub message: Box<dyn Fn(&mut dyn std::fmt::Write) -> std::fmt::Result + Send>,
}

// 日志处理器 trait
pub trait LogHandler: Send {
    fn handle(&mut self, record: &LogRecord);
    fn flush(&mut self);
}

// 控制台输出处理器
pub struct ConsoleHandler {
    filter: Level,
}

impl ConsoleHandler {
    pub fn new(filter: Level) -> Self {
        ConsoleHandler { filter }
    }
}

impl LogHandler for ConsoleHandler {
    fn handle(&mut self, record: &LogRecord) {
        if record.level < self.filter {
            return;
        }

        // 延迟格式化消息
        let mut message = String::new();
        (record.message)(&mut message).ok();

        eprintln!(
            "[{}] {} [{}] {}:{} - {}",
            record.level.as_str(),
            humantime::format_rfc3339(record.time),
            record.target,
            record.file,
            record.line,
            message
        );
    }

    fn flush(&mut self) {
        // stderr 自动 flush
    }
}

// 异步日志引擎
pub struct AsyncLogger {
    sender: Sender<LogRecord>,
    // 保持处理器存活
    _handle: std::thread::JoinHandle<()>,
}

impl AsyncLogger {
    pub fn new(mut handlers: Vec<Box<dyn LogHandler>>) -> Self {
        // 有界通道, 防止内存无限增长
        let (sender, receiver): (Sender<LogRecord>, Receiver<LogRecord>) = bounded(10000);

        let handle = std::thread::spawn(move || {
            Self::worker_loop(receiver, &mut handlers);
        });

        AsyncLogger {
            sender,
            _handle: handle,
        }
    }

    fn worker_loop(receiver: Receiver<LogRecord>, handlers: &mut [Box<dyn LogHandler>]) {
        // 批量处理提高效率
        let mut batch = Vec::with_capacity(100);

        loop {
            match receiver.recv() {
                Ok(record) => {
                    batch.push(record);

                    // 尝试接收更多消息进行批量处理
                    while batch.len() < 100 {
                        match receiver.try_recv() {
                            Ok(r) => batch.push(r),
                            Err(_) => break,
                        }
                    }

                    // 批量处理
                    for record in &batch {
                        for handler in handlers.iter_mut() {
                            handler.handle(record);
                        }
                    }

                    for handler in handlers.iter_mut() {
                        handler.flush();
                    }

                    batch.clear();
                }
                Err(_) => break, // 发送者已关闭
            }
        }
    }

    pub fn log(&self, record: LogRecord) {
        // 快速路径: 检查日志级别
        if record.level < max_level() {
            return;
        }

        // 异步发送, 不阻塞调用者
        // 如果通道满了, 丢弃日志(保证不阻塞)
        let _ = self.sender.try_send(record);
    }
}

// 全局日志实例
lazy_static::lazy_static! {
    static ref LOGGER: Arc<std::sync::Mutex<Option<AsyncLogger>>> =
        Arc::new(std::sync::Mutex::new(None));
}

pub fn init(handlers: Vec<Box<dyn LogHandler>>) {
    let logger = AsyncLogger::new(handlers);
    *LOGGER.lock().unwrap() = Some(logger);
}

// 宏定义提供友好的 API
#[macro_export]
macro_rules! log {
    ($level:expr, $($arg:tt)*) => {{
        let record = $crate::LogRecord {
            level: $level,
            target: module_path!(),
            file: file!(),
            line: line!(),
            time: std::time::SystemTime::now(),
            thread_id: std::thread::current().id(),
            message: Box::new(move |w| write!(w, $($arg)*)),
        };

        if let Ok(guard) = $crate::LOGGER.lock() {
            if let Some(ref logger) = *guard {
                logger.log(record);
            }
        }
    }};
}

#[macro_export]
macro_rules! info {
    ($($arg:tt)*) => {{
        $crate::log!($crate::Level::Info, $($arg)*);
    }};
}

#[macro_export]
macro_rules! error {
    ($($arg:tt)*) => {{
        $crate::log!($crate::Level::Error, $($arg)*);
    }};
}

// 使用示例
fn example_usage() {
    // 初始化日志系统
    init(vec![
        Box::new(ConsoleHandler::new(Level::Info)),
    ]);

    let user_id = 12345;
    let ip = "192.168.1.1";

    // 这些调用是非阻塞的
    info!("User {} logged in from {}", user_id, ip);
    error!("Failed to connect to database: {}", "connection timeout");
}
```

### 关键要点

1. **延迟格式化**: 使用闭包在真正需要时才格式化日志消息, 避免不必要的字符串分配
2. **异步处理**: 使用有界通道将日志处理移到独立线程, 不阻塞业务代码
3. **批量处理**: 工作线程批量消费消息, 减少锁竞争和系统调用
4. **热更新**: 全局日志级别使用原子变量, 可在运行时调整
5. **背压处理**: 有界通道满时丢弃日志, 保证系统稳定性

---

## 总结

以上五个案例展示了 Rust 在不同场景下的最佳实践:

| 案例 | 核心概念 | 关键技巧 |
|------|----------|----------|
| 线程池 | 并发、所有权 | `Arc<Mutex<T>>`, `Drop`, 类型擦除 |
| 异步 HTTP | async/await、错误处理 | Builder 模式, 超时控制, 指数退避 |
| LRU Cache | 不安全代码、内存管理 | `NonNull`, RAII, 链表操作 |
| 文件系统 | 跨平台、性能 | `#[cfg]`, 原子操作, 并行处理 |
| 日志库 | 零分配、异步 | 延迟计算, 有界通道, 批量处理 |

这些模式可以组合使用, 构建出既安全又高性能的 Rust 应用程序。
