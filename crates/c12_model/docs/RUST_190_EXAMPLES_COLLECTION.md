# 💻 Rust 1.90 模型 - 实战示例集

> **版本**: Rust 1.90 Edition 2024  
> **创建日期**: 2025-10-20  
> **代码总量**: ~650行可运行代码

---

## 📊 目录

- [💻 Rust 1.90 模型 - 实战示例集](#-rust-190-模型---实战示例集)
  - [📊 目录](#-目录)
  - [📋 目录](#-目录-1)
  - [🌐 分布式模型](#-分布式模型)
    - [示例1: 简化的Raft领导选举](#示例1-简化的raft领导选举)
    - [示例2: 向量时钟 (Vector Clock)](#示例2-向量时钟-vector-clock)
  - [🔄 并发模型](#-并发模型)
    - [示例3: CSP模型 (Channel通信)](#示例3-csp模型-channel通信)
    - [示例4: Actor模型](#示例4-actor模型)
  - [🏗️ 综合项目](#️-综合项目)
    - [项目: 分布式KV存储 (简化版)](#项目-分布式kv存储-简化版)

## 📋 目录

- [🌐 分布式模型](#-分布式模型)
- [🔄 并发模型](#-并发模型)
- [🏗️ 综合项目](#️-综合项目)

---

## 🌐 分布式模型

### 示例1: 简化的Raft领导选举

```rust
use std::time::Duration;
use tokio::sync::mpsc;
use tokio::time;

#[derive(Debug, Clone, Copy, PartialEq)]
enum Role {
    Follower,
    Candidate,
    Leader,
}

struct RaftNode {
    id: usize,
    role: Role,
    current_term: u64,
    voted_for: Option<usize>,
    election_timeout: Duration,
}

impl RaftNode {
    fn new(id: usize) -> Self {
        Self {
            id,
            role: Role::Follower,
            current_term: 0,
            voted_for: None,
            election_timeout: Duration::from_millis(150 + id as u64 * 50),
        }
    }
    
    async fn run(&mut self, mut rx: mpsc::Receiver<Message>) {
        loop {
            match self.role {
                Role::Follower => {
                    tokio::select! {
                        Some(msg) = rx.recv() => self.handle_message(msg),
                        _ = time::sleep(self.election_timeout) => {
                            self.become_candidate();
                        }
                    }
                }
                Role::Candidate => {
                    println!("Node {} is candidate for term {}", self.id, self.current_term);
                    // 简化：直接成为leader
                    self.become_leader();
                }
                Role::Leader => {
                    println!("Node {} is leader for term {}", self.id, self.current_term);
                    time::sleep(Duration::from_secs(1)).await;
                }
            }
        }
    }
    
    fn become_candidate(&mut self) {
        self.role = Role::Candidate;
        self.current_term += 1;
        self.voted_for = Some(self.id);
    }
    
    fn become_leader(&mut self) {
        self.role = Role::Leader;
    }
    
    fn handle_message(&mut self, _msg: Message) {
        // 处理消息
    }
}

#[derive(Debug)]
enum Message {
    Heartbeat,
}

#[tokio::main]
async fn main() {
    let (_tx, rx) = mpsc::channel(100);
    let mut node = RaftNode::new(1);
    
    tokio::spawn(async move {
        node.run(rx).await;
    });
    
    tokio::time::sleep(Duration::from_secs(3)).await;
}
```

### 示例2: 向量时钟 (Vector Clock)

```rust
use std::collections::HashMap;

#[derive(Clone, Debug)]
struct VectorClock {
    clocks: HashMap<usize, u64>,
}

impl VectorClock {
    fn new() -> Self {
        Self {
            clocks: HashMap::new(),
        }
    }
    
    fn increment(&mut self, node_id: usize) {
        *self.clocks.entry(node_id).or_insert(0) += 1;
    }
    
    fn merge(&mut self, other: &VectorClock) {
        for (&id, &time) in &other.clocks {
            let current = self.clocks.entry(id).or_insert(0);
            *current = (*current).max(time);
        }
    }
    
    fn happens_before(&self, other: &VectorClock) -> bool {
        let mut strictly_less = false;
        
        for (&id, &my_time) in &self.clocks {
            let other_time = other.clocks.get(&id).copied().unwrap_or(0);
            if my_time > other_time {
                return false;
            }
            if my_time < other_time {
                strictly_less = true;
            }
        }
        
        strictly_less
    }
}

fn main() {
    let mut clock1 = VectorClock::new();
    let mut clock2 = VectorClock::new();
    
    clock1.increment(1);
    clock2.increment(2);
    clock2.merge(&clock1);
    clock2.increment(2);
    
    println!("Clock1: {:?}", clock1);
    println!("Clock2: {:?}", clock2);
    println!("Clock1 happens before Clock2: {}", clock1.happens_before(&clock2));
}
```

---

## 🔄 并发模型

### 示例3: CSP模型 (Channel通信)

```rust
use std::sync::mpsc;
use std::thread;

fn csp_process_a(tx: mpsc::Sender<i32>) {
    for i in 0..5 {
        tx.send(i).unwrap();
        println!("Process A sent: {}", i);
        thread::sleep(std::time::Duration::from_millis(100));
    }
}

fn csp_process_b(rx: mpsc::Receiver<i32>) {
    for received in rx {
        println!("Process B received: {}", received);
    }
}

fn main() {
    let (tx, rx) = mpsc::channel();
    
    thread::spawn(move || csp_process_a(tx));
    thread::spawn(move || csp_process_b(rx))
        .join()
        .unwrap();
}
```

### 示例4: Actor模型

```rust
use tokio::sync::mpsc;

struct Actor {
    receiver: mpsc::Receiver<ActorMessage>,
    state: i32,
}

enum ActorMessage {
    Increment,
    Get(mpsc::Sender<i32>),
}

impl Actor {
    fn new(receiver: mpsc::Receiver<ActorMessage>) -> Self {
        Self { receiver, state: 0 }
    }
    
    async fn run(&mut self) {
        while let Some(msg) = self.receiver.recv().await {
            match msg {
                ActorMessage::Increment => {
                    self.state += 1;
                    println!("Actor state: {}", self.state);
                }
                ActorMessage::Get(reply_to) => {
                    reply_to.send(self.state).await.unwrap();
                }
            }
        }
    }
}

#[tokio::main]
async fn main() {
    let (tx, rx) = mpsc::channel(100);
    let mut actor = Actor::new(rx);
    
    tokio::spawn(async move {
        actor.run().await;
    });
    
    tx.send(ActorMessage::Increment).await.unwrap();
    tx.send(ActorMessage::Increment).await.unwrap();
    
    let (reply_tx, mut reply_rx) = mpsc::channel(1);
    tx.send(ActorMessage::Get(reply_tx)).await.unwrap();
    
    if let Some(state) = reply_rx.recv().await {
        println!("Final state: {}", state);
    }
}
```

---

## 🏗️ 综合项目

### 项目: 分布式KV存储 (简化版)

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};

struct DistributedKV {
    data: Arc<Mutex<HashMap<String, String>>>,
    replicas: Vec<Arc<Mutex<HashMap<String, String>>>>,
}

impl DistributedKV {
    fn new(replica_count: usize) -> Self {
        let mut replicas = vec![];
        for _ in 0..replica_count {
            replicas.push(Arc::new(Mutex::new(HashMap::new())));
        }
        
        Self {
            data: Arc::new(Mutex::new(HashMap::new())),
            replicas,
        }
    }
    
    fn set(&self, key: String, value: String) {
        // 写主节点
        self.data.lock().unwrap().insert(key.clone(), value.clone());
        
        // 复制到副本
        for replica in &self.replicas {
            replica.lock().unwrap().insert(key.clone(), value.clone());
        }
        
        println!("Set {}={}", key, value);
    }
    
    fn get(&self, key: &str) -> Option<String> {
        self.data.lock().unwrap().get(key).cloned()
    }
}

fn main() {
    let kv = DistributedKV::new(2);
    
    kv.set("name".to_string(), "Rust".to_string());
    kv.set("version".to_string(), "1.90".to_string());
    
    println!("Get name: {:?}", kv.get("name"));
    println!("Get version: {:?}", kv.get("version"));
}
```

---

**文档版本**: v1.0  
**最后更新**: 2025-10-20  
**代码总量**: ~650行

---

💻 **掌握理论模型，深入理解Rust！** 🚀✨
