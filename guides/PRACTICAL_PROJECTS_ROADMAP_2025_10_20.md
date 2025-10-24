# 🚀 Rust 实践项目路线图

> **文档创建**: 2025-10-20  
> **基于**: 全模块增强文档体系  
> **目标**: 将理论知识转化为实战项目

---


## 📊 目录

- [� Rust 实践项目路线图](#-rust-实践项目路线图)
  - [📊 目录](#-目录)
  - [📋 目录](#-目录-1)
  - [🎯 项目总览](#-项目总览)
  - [📚 初级实战项目 (Week 1-4)](#-初级实战项目-week-1-4)
    - [项目1: 命令行任务管理器](#项目1-命令行任务管理器)
    - [项目2: 简单HTTP服务器](#项目2-简单http服务器)
    - [项目3: 文件同步工具](#项目3-文件同步工具)
  - [🔥 中级实战项目 (Week 5-8)](#-中级实战项目-week-5-8)
    - [项目4: 并发Web爬虫](#项目4-并发web爬虫)
    - [项目5: 分布式缓存系统](#项目5-分布式缓存系统)
    - [项目6: 实时聊天服务](#项目6-实时聊天服务)
  - [⚡ 高级实战项目 (Week 9-12)](#-高级实战项目-week-9-12)
    - [项目7: 微服务架构框架](#项目7-微服务架构框架)
    - [项目8: 分布式数据库](#项目8-分布式数据库)
    - [项目9: 高性能网关](#项目9-高性能网关)
  - [🏆 综合项目 (持续)](#-综合项目-持续)
    - [项目10: 云原生平台](#项目10-云原生平台)
  - [📁 项目代码组织](#-项目代码组织)
  - [🎓 学习路径映射](#-学习路径映射)
  - [✅ 实施计划](#-实施计划)
    - [Phase 1: 基础项目 (Week 1-2)](#phase-1-基础项目-week-1-2)
    - [Phase 2: 进阶项目 (Week 3-4)](#phase-2-进阶项目-week-3-4)
    - [Phase 3: 高级项目 (Week 5-6)](#phase-3-高级项目-week-5-6)
    - [Phase 4: 综合项目 (持续)](#phase-4-综合项目-持续)


## 📋 目录

- [🚀 Rust 实践项目路线图](#-rust-实践项目路线图)
  - [� 目录](#-目录)
  - [📋 目录](#-目录-1)
  - [🎯 项目总览](#-项目总览)
  - [📚 初级实战项目 (Week 1-4)](#-初级实战项目-week-1-4)
    - [项目1: 命令行任务管理器](#项目1-命令行任务管理器)
    - [项目2: 简单HTTP服务器](#项目2-简单http服务器)
    - [项目3: 文件同步工具](#项目3-文件同步工具)
  - [🔥 中级实战项目 (Week 5-8)](#-中级实战项目-week-5-8)
    - [项目4: 并发Web爬虫](#项目4-并发web爬虫)
    - [项目5: 分布式缓存系统](#项目5-分布式缓存系统)
    - [项目6: 实时聊天服务](#项目6-实时聊天服务)
  - [⚡ 高级实战项目 (Week 9-12)](#-高级实战项目-week-9-12)
    - [项目7: 微服务架构框架](#项目7-微服务架构框架)
    - [项目8: 分布式数据库](#项目8-分布式数据库)
    - [项目9: 高性能网关](#项目9-高性能网关)
  - [🏆 综合项目 (持续)](#-综合项目-持续)
    - [项目10: 云原生平台](#项目10-云原生平台)
  - [📁 项目代码组织](#-项目代码组织)
  - [🎓 学习路径映射](#-学习路径映射)
  - [✅ 实施计划](#-实施计划)
    - [Phase 1: 基础项目 (Week 1-2)](#phase-1-基础项目-week-1-2)
    - [Phase 2: 进阶项目 (Week 3-4)](#phase-2-进阶项目-week-3-4)
    - [Phase 3: 高级项目 (Week 5-6)](#phase-3-高级项目-week-5-6)
    - [Phase 4: 综合项目 (持续)](#phase-4-综合项目-持续)

---

## 🎯 项目总览

基于13个模块的增强文档，设计10个渐进式实战项目，覆盖从初级到高级的完整学习路径。

| 项目 | 难度 | 周期 | 核心模块 | 技术栈 |
|------|------|------|---------|--------|
| 命令行任务管理器 | ⭐ | 1周 | C01-C03 | clap/serde |
| HTTP服务器 | ⭐⭐ | 1周 | C03-C04, C10 | tokio/hyper |
| 文件同步工具 | ⭐⭐ | 1周 | C05, C07 | notify/crossbeam |
| Web爬虫 | ⭐⭐⭐ | 2周 | C05-C06, C10 | tokio/reqwest |
| 分布式缓存 | ⭐⭐⭐⭐ | 2周 | C06-C07, C11-C12 | tokio/redis |
| 聊天服务 | ⭐⭐⭐⭐ | 2周 | C06, C10, C13 | tokio/WebSocket |
| 微服务框架 | ⭐⭐⭐⭐⭐ | 3周 | C09-C10, C13 | tonic/consul |
| 分布式数据库 | ⭐⭐⭐⭐⭐ | 3周 | C08, C12-C13 | Raft/RocksDB |
| 高性能网关 | ⭐⭐⭐⭐⭐ | 3周 | C06, C10, C13 | tokio-uring/QUIC |
| 云原生平台 | ⭐⭐⭐⭐⭐ | 持续 | 全部 | K8s/Docker |

---

## 📚 初级实战项目 (Week 1-4)

### 项目1: 命令行任务管理器

**目标**: 实现一个功能完整的CLI任务管理工具

**涉及模块**:

- C01: 所有权管理
- C02: 自定义类型
- C03: 错误处理

**核心功能**:

```rust
// 任务结构
struct Task {
    id: u64,
    title: String,
    description: String,
    status: TaskStatus,
    created_at: DateTime<Utc>,
}

// 命令接口
enum Command {
    Add { title: String, desc: String },
    List { filter: Option<StatusFilter> },
    Complete { id: u64 },
    Delete { id: u64 },
}
```

**技术要点**:

- ✅ 使用 `clap` 解析命令行参数
- ✅ 使用 `serde` 序列化到JSON
- ✅ 错误处理使用 `anyhow`
- ✅ 所有权和借用的实践

---

### 项目2: 简单HTTP服务器

**目标**: 实现一个基础的异步HTTP服务器

**涉及模块**:

- C03-C04: 泛型和Trait
- C06: 异步编程
- C10: 网络编程

**核心功能**:

```rust
// HTTP路由
async fn route_handler(req: Request<Body>) -> Result<Response<Body>> {
    match (req.method(), req.uri().path()) {
        (&Method::GET, "/") => serve_index(),
        (&Method::GET, "/api/status") => serve_status(),
        (&Method::POST, "/api/data") => handle_data(req).await,
        _ => not_found(),
    }
}
```

**技术要点**:

- ✅ 使用 `tokio` 异步运行时
- ✅ 使用 `hyper` HTTP库
- ✅ 实现中间件模式
- ✅ 优雅关闭

---

### 项目3: 文件同步工具

**目标**: 监控文件变化并同步到远程

**涉及模块**:

- C05: 多线程并发
- C07: 进程和IPC

**核心功能**:

```rust
// 文件监控
fn watch_directory(path: &Path) -> Result<Receiver<Event>> {
    let (tx, rx) = channel();
    let watcher = notify::watcher(tx, Duration::from_secs(1))?;
    watcher.watch(path, RecursiveMode::Recursive)?;
    Ok(rx)
}
```

**技术要点**:

- ✅ 使用 `notify` 监控文件系统
- ✅ 使用 `crossbeam` 通道通信
- ✅ 多线程文件处理
- ✅ 增量同步算法

---

## 🔥 中级实战项目 (Week 5-8)

### 项目4: 并发Web爬虫

**目标**: 实现高性能异步网页爬虫

**涉及模块**:

- C05-C06: 并发和异步
- C08: 算法（BFS/DFS）
- C10: 网络编程

**核心功能**:

```rust
// 爬虫引擎
struct Crawler {
    client: Client,
    visited: Arc<DashMap<Url, ()>>,
    queue: Arc<SegQueue<Url>>,
    rate_limiter: RateLimiter,
}

impl Crawler {
    async fn crawl(&self, start_url: Url, depth: usize) {
        // JoinSet for structured concurrency
        let mut tasks = JoinSet::new();
        // ...
    }
}
```

**技术要点**:

- ✅ 使用 `JoinSet` 结构化并发
- ✅ 使用 `DashMap` 无锁并发哈希表
- ✅ 实现 URL去重和深度控制
- ✅ 限流和礼貌爬取

---

### 项目5: 分布式缓存系统

**目标**: 实现类似Redis的分布式缓存

**涉及模块**:

- C06: 异步编程
- C11: 中间件
- C12: 分布式模型

**核心功能**:

```rust
// 缓存节点
struct CacheNode {
    storage: Arc<DashMap<String, CacheEntry>>,
    peers: Vec<NodeInfo>,
    hash_ring: ConsistentHash,
}

impl CacheNode {
    async fn get(&self, key: &str) -> Option<Value> {
        let node = self.hash_ring.get_node(key);
        if node.is_local() {
            self.local_get(key).await
        } else {
            self.remote_get(node, key).await
        }
    }
}
```

**技术要点**:

- ✅ 一致性哈希
- ✅ 数据分片和复制
- ✅ 过期策略（LRU/TTL）
- ✅ 主从同步

---

### 项目6: 实时聊天服务

**目标**: WebSocket实时通信平台

**涉及模块**:

- C06: 异步编程
- C10: 网络编程
- C13: 可靠性

**核心功能**:

```rust
// 聊天服务器
struct ChatServer {
    sessions: Arc<DashMap<SessionId, mpsc::Sender<Message>>>,
    rooms: Arc<DashMap<RoomId, HashSet<SessionId>>>,
}

impl ChatServer {
    async fn handle_client(&self, ws: WebSocket) {
        let (tx, mut rx) = ws.split();
        // ...
    }
}
```

**技术要点**:

- ✅ WebSocket长连接
- ✅ 广播和单播消息
- ✅ 心跳和重连
- ✅ 消息持久化

---

## ⚡ 高级实战项目 (Week 9-12)

### 项目7: 微服务架构框架

**目标**: 构建完整的微服务基础设施

**涉及模块**:

- C09: 设计模式
- C10: 网络编程
- C13: 可靠性

**核心功能**:

```rust
// 服务注册与发现
#[async_trait]
trait ServiceRegistry {
    async fn register(&self, service: ServiceInfo) -> Result<()>;
    async fn discover(&self, name: &str) -> Result<Vec<ServiceInfo>>;
    async fn health_check(&self) -> Result<()>;
}

// 熔断器中间件
struct CircuitBreaker {
    state: Arc<RwLock<State>>,
    config: Config,
}
```

**技术要点**:

- ✅ 服务发现（Consul/Etcd）
- ✅ 负载均衡（Round-Robin/Weighted）
- ✅ 熔断器和限流
- ✅ 分布式追踪

---

### 项目8: 分布式数据库

**目标**: 实现Raft共识的KV存储

**涉及模块**:

- C08: 算法（B-Tree）
- C12: 分布式模型
- C13: 可靠性

**核心功能**:

```rust
// Raft节点
struct RaftNode {
    state: Arc<RwLock<State>>,
    log: Vec<LogEntry>,
    storage: BTreeMap<String, String>,
    peers: Vec<NodeInfo>,
}

impl RaftNode {
    async fn handle_client_request(&mut self, cmd: Command) -> Result<Response> {
        if self.state.read().await.role != Role::Leader {
            return Err(Error::NotLeader);
        }
        self.replicate_log(cmd).await
    }
}
```

**技术要点**:

- ✅ Raft共识算法
- ✅ 日志复制和快照
- ✅ 事务ACID保证
- ✅ 分布式锁

---

### 项目9: 高性能网关

**目标**: 使用io_uring的高性能API网关

**涉及模块**:

- C06: 异步编程
- C10: 网络编程（io_uring）
- C13: 可靠性

**核心功能**:

```rust
// 网关核心
struct Gateway {
    router: Router,
    limiter: RateLimiter,
    circuit_breaker: CircuitBreaker,
    metrics: Metrics,
}

impl Gateway {
    async fn handle_request(&self, req: Request) -> Response {
        // 1. 限流检查
        self.limiter.check(&req).await?;
        
        // 2. 路由匹配
        let backend = self.router.route(&req)?;
        
        // 3. 熔断检查
        if self.circuit_breaker.is_open(&backend) {
            return Response::service_unavailable();
        }
        
        // 4. 代理请求
        self.proxy_request(backend, req).await
    }
}
```

**技术要点**:

- ✅ io_uring零拷贝
- ✅ HTTP/3和QUIC
- ✅ 动态路由配置
- ✅ 性能监控

---

## 🏆 综合项目 (持续)

### 项目10: 云原生平台

**目标**: 构建完整的云原生应用平台

**涉及模块**: 全部13个模块

**核心组件**:

1. **控制平面**: 资源管理、调度
2. **数据平面**: 存储、网络、计算
3. **可观测性**: 监控、日志、追踪
4. **安全**: 认证、授权、加密

**技术栈**:

- Kubernetes集成
- gRPC服务通信
- Raft共识
- 分布式追踪
- 容器运行时

---

## 📁 项目代码组织

建议的项目结构：

```text
rust-lang-projects/
├── 01-cli-task-manager/
│   ├── src/
│   ├── tests/
│   └── README.md
├── 02-http-server/
│   ├── src/
│   ├── tests/
│   └── README.md
├── ... (03-09)
├── 10-cloud-native-platform/
│   ├── control-plane/
│   ├── data-plane/
│   ├── observability/
│   └── README.md
└── PROJECTS_README.md
```

---

## 🎓 学习路径映射

| 学习阶段 | 推荐项目 | 预期收获 |
|---------|---------|---------|
| **初学者** | 项目1-3 | 掌握基础语法和工具 |
| **中级** | 项目4-6 | 理解并发和异步 |
| **高级** | 项目7-9 | 掌握架构设计 |
| **专家** | 项目10 | 系统级综合能力 |

---

## ✅ 实施计划

### Phase 1: 基础项目 (Week 1-2)

- [ ] 创建项目1: CLI任务管理器
- [ ] 创建项目2: HTTP服务器
- [ ] 创建项目3: 文件同步工具

### Phase 2: 进阶项目 (Week 3-4)

- [ ] 创建项目4: Web爬虫
- [ ] 创建项目5: 分布式缓存
- [ ] 创建项目6: 聊天服务

### Phase 3: 高级项目 (Week 5-6)

- [ ] 创建项目7: 微服务框架
- [ ] 创建项目8: 分布式数据库
- [ ] 创建项目9: 高性能网关

### Phase 4: 综合项目 (持续)

- [ ] 设计项目10架构
- [ ] 逐步实现各组件
- [ ] 集成测试和优化

---

**文档版本**: v1.0  
**最后更新**: 2025-10-20  
**维护者**: Rust Learning Community

---

*实践是检验真理的唯一标准！让我们动手coding吧！* 🚀
