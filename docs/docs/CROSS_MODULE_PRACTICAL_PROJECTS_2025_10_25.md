# 🚀 Rust 学习系统 - 跨模块综合实战项目指南

> **创建日期**: 2025-10-25  
> **文档版本**: v1.0  
> **项目数量**: 10 个渐进式项目

---

## 📋 文档简介

本文档提供**10个精心设计的跨模块综合实战项目**,每个项目都整合多个模块的知识点,帮助学习者:

- 🎯 **综合运用知识** - 将分散的知识点串联起来
- 💻 **构建实际应用** - 开发有实用价值的项目
- 🔄 **循序渐进学习** - 从简单到复杂逐步提升
- 🏆 **积累项目经验** - 打造个人技术作品集

---

## 🎯 项目难度分级

| 等级 | 难度 | 适合人群 | 预计时间 | 模块数量 |
|------|------|---------|---------|---------|
| **⭐** | 入门 | 完成 C01-C03 | 3-5 天 | 2-3 个 |
| **⭐⭐** | 初级 | 完成 C01-C04 | 5-7 天 | 3-4 个 |
| **⭐⭐⭐** | 中级 | 完成 C01-C06 | 7-14 天 | 4-5 个 |
| **⭐⭐⭐⭐** | 高级 | 完成 C01-C08 | 14-21 天 | 5-7 个 |
| **⭐⭐⭐⭐⭐** | 专家 | 完成所有模块 | 21-30 天 | 7+ 个 |

---

## 📚 项目总览

| # | 项目名称 | 难度 | 涉及模块 | 核心技术 | 应用场景 |
|---|---------|------|---------|---------|---------|
| 1 | [CLI 文件处理工具](#项目1-cli-文件处理工具-) | ⭐ | C01-C03 | 文件I/O、错误处理 | 命令行工具 |
| 2 | [并发下载器](#项目2-并发下载器-) | ⭐⭐ | C01-C05, C10 | 多线程、网络 | 下载工具 |
| 3 | [异步聊天服务器](#项目3-异步聊天服务器-) | ⭐⭐⭐ | C05-C06, C10 | 异步I/O、TCP | 即时通讯 |
| 4 | [Web API 服务](#项目4-web-api-服务-) | ⭐⭐⭐ | C02-C06, C10-C11 | Web框架、数据库 | Web后端 |
| 5 | [分布式任务队列](#项目5-分布式任务队列-) | ⭐⭐⭐⭐ | C05-C06, C10-C13 | 分布式、消息队列 | 后台任务 |
| 6 | [高性能代理服务器](#项目6-高性能代理服务器-) | ⭐⭐⭐⭐ | C05-C06, C10, C13 | 异步、负载均衡 | 网络代理 |
| 7 | [实时数据处理引擎](#项目7-实时数据处理引擎-) | ⭐⭐⭐⭐ | C05-C08, C13 | 流处理、算法 | 数据分析 |
| 8 | [微服务框架](#项目8-微服务框架-) | ⭐⭐⭐⭐⭐ | C06, C09-C13 | 微服务、架构 | 企业应用 |
| 9 | [区块链节点](#项目9-区块链节点-) | ⭐⭐⭐⭐⭐ | C05-C08, C10, C13 | 密码学、P2P | 区块链 |
| 10 | [操作系统内核模块](#项目10-操作系统内核模块-) | ⭐⭐⭐⭐⭐ | C01-C07, C13 | 系统编程、硬件 | 嵌入式/OS |

---

## 🎓 项目详细说明

---

### 项目1: CLI 文件处理工具 ⭐

#### 项目概述

**目标**: 开发一个命令行工具,用于处理文本文件(搜索、替换、统计等)

**难度**: 入门 (⭐)  
**时间**: 3-5 天  
**适合**: 刚学完 C01-C03 的初学者

#### 涉及模块与知识点

| 模块 | 核心知识点 | 应用场景 |
|------|-----------|---------|
| **C01** | 所有权、借用 | 字符串处理、文件句柄管理 |
| **C02** | 结构体、枚举 | 配置结构、错误类型 |
| **C03** | 错误处理、模式匹配 | Result/Option、命令解析 |

#### 功能需求

**基础功能** (必做):

1. 文件搜索 - 在文件中搜索关键词
2. 内容替换 - 批量替换文件内容
3. 统计分析 - 行数、字数、字符数统计
4. 文件对比 - 比较两个文件的差异

**进阶功能** (选做):
5. 正则表达式支持
6. 递归目录搜索
7. 彩色输出
8. 配置文件支持

#### 技术要点

```rust
// 1. 所有权与借用 (C01)
fn read_file(path: &Path) -> Result<String, io::Error> {
    fs::read_to_string(path)  // 所有权转移到返回值
}

// 2. 结构体设计 (C02)
struct SearchConfig {
    pattern: String,
    file_path: PathBuf,
    case_sensitive: bool,
}

// 3. 错误处理 (C03)
fn search(config: &SearchConfig) -> Result<Vec<String>, Box<dyn Error>> {
    let contents = read_file(&config.file_path)?;  // ? 操作符
    let results = find_matches(&contents, &config.pattern);
    Ok(results)
}

// 4. 迭代器与闭包 (C03)
fn find_matches<'a>(contents: &'a str, pattern: &str) -> Vec<&'a str> {
    contents
        .lines()
        .filter(|line| line.contains(pattern))
        .collect()
}
```

#### 项目结构

```text
cli-file-tool/
├── Cargo.toml
├── src/
│   ├── main.rs         # 入口,命令行解析
│   ├── lib.rs          # 库代码
│   ├── search.rs       # 搜索功能
│   ├── replace.rs      # 替换功能
│   ├── stats.rs        # 统计功能
│   ├── config.rs       # 配置管理
│   └── error.rs        # 错误类型定义
├── tests/
│   └── integration_tests.rs
└── README.md
```

#### 学习目标

- ✅ 熟练掌握所有权和借用
- ✅ 能够设计清晰的结构体
- ✅ 正确使用 Result 和 Option
- ✅ 熟悉文件 I/O 操作
- ✅ 能写单元测试和集成测试

#### 扩展方向

1. 添加 GUI (使用 egui)
2. 支持更多文件格式 (CSV, JSON)
3. 性能优化 (内存映射文件)
4. 发布到 crates.io

#### 参考资源

- 项目示例: [ripgrep](https://github.com/BurntSushi/ripgrep)
- CLI 库: [clap](https://crates.io/crates/clap)
- 相关文档: C01-C03 的 Tier 2 实践指南

---

### 项目2: 并发下载器 ⭐⭐

#### 项目概述

**目标**: 开发一个支持多线程并发下载的工具,可以同时下载多个文件并显示进度

**难度**: 初级 (⭐⭐)  
**时间**: 5-7 天  
**适合**: 学完 C01-C05 和 C10 基础的学习者

#### 涉及模块与知识点

| 模块 | 核心知识点 | 应用场景 |
|------|-----------|---------|
| **C01** | 所有权、Arc | 多线程共享数据 |
| **C02** | Trait、Send/Sync | 并发安全类型 |
| **C04** | 泛型 | 通用下载器接口 |
| **C05** | 多线程、Mutex | 并发下载、进度同步 |
| **C10** | HTTP 客户端 | 网络请求 |

#### 功能需求

**基础功能**:

1. 单文件下载
2. 多文件并发下载
3. 下载进度显示
4. 断点续传
5. 失败重试

**进阶功能**:
6. 分块并发下载(单文件多线程)
7. 下载速度限制
8. 代理支持
9. 下载队列管理

#### 技术要点

```rust
use std::sync::{Arc, Mutex};
use std::thread;
use reqwest;

// 1. 共享状态设计 (C05)
struct DownloadProgress {
    total_bytes: u64,
    downloaded_bytes: Arc<Mutex<u64>>,
}

// 2. 泛型下载器接口 (C04)
trait Downloader {
    fn download(&self, url: &str) -> Result<(), DownloadError>;
    fn progress(&self) -> f64;
}

// 3. 多线程下载 (C05)
struct ConcurrentDownloader {
    num_threads: usize,
    progress: Arc<Mutex<HashMap<String, DownloadProgress>>>,
}

impl ConcurrentDownloader {
    fn download_batch(&self, urls: Vec<String>) -> Result<(), Box<dyn Error>> {
        let (tx, rx) = mpsc::channel();
        let progress = Arc::clone(&self.progress);
        
        // 启动工作线程
        for _ in 0..self.num_threads {
            let rx = rx.clone();
            let progress = Arc::clone(&progress);
            
            thread::spawn(move || {
                while let Ok(url) = rx.recv() {
                    let result = download_file(&url, &progress);
                    // 处理结果...
                }
            });
        }
        
        // 分发任务
        for url in urls {
            tx.send(url)?;
        }
        
        Ok(())
    }
}

// 4. HTTP 下载 (C10)
fn download_file(url: &str, progress: &Arc<Mutex<u64>>) -> Result<(), Box<dyn Error>> {
    let response = reqwest::blocking::get(url)?;
    let total_size = response.content_length().unwrap_or(0);
    
    // 读取并更新进度
    // ...
    
    Ok(())
}
```

#### 项目结构

```text
concurrent-downloader/
├── Cargo.toml
├── src/
│   ├── main.rs           # CLI 入口
│   ├── lib.rs
│   ├── downloader/
│   │   ├── mod.rs        # 下载器trait
│   │   ├── concurrent.rs # 并发下载实现
│   │   └── resumable.rs  # 断点续传
│   ├── progress/
│   │   ├── mod.rs        # 进度追踪
│   │   └── display.rs    # 进度显示
│   ├── queue.rs          # 下载队列
│   └── config.rs         # 配置
├── tests/
└── README.md
```

#### 学习目标

- ✅ 掌握 Arc/Mutex 并发模式
- ✅ 理解 Send/Sync trait
- ✅ 能使用 channel 进行线程通信
- ✅ 熟悉 HTTP 客户端库使用
- ✅ 能处理并发错误和重试

#### 扩展方向

1. 添加 TUI (使用 tui-rs)
2. 支持 BitTorrent 协议
3. 云存储集成 (S3, OSS)
4. 下载历史和统计

---

### 项目3: 异步聊天服务器 ⭐⭐⭐

#### 项目概述

**目标**: 使用异步 I/O 开发一个支持多客户端的实时聊天服务器

**难度**: 中级 (⭐⭐⭐)  
**时间**: 7-14 天  
**适合**: 学完 C06 异步编程的学习者

#### 涉及模块与知识点

| 模块 | 核心知识点 | 应用场景 |
|------|-----------|---------|
| **C05** | Arc、Mutex | 共享客户端状态 |
| **C06** | async/await、tokio | 异步服务器 |
| **C09** | 发布-订阅模式 | 消息广播 |
| **C10** | TCP、WebSocket | 网络通信 |
| **C11** | tokio、serde | 运行时、序列化 |

#### 功能需求

**基础功能**:

1. TCP 连接管理
2. 消息广播
3. 用户昵称
4. 多房间支持
5. 在线用户列表

**进阶功能**:
6. WebSocket 支持
7. 私聊功能
8. 消息历史
9. 用户认证
10. 文件传输

#### 技术要点

```rust
use tokio::net::{TcpListener, TcpStream};
use tokio::sync::{broadcast, mpsc};
use std::sync::Arc;

// 1. 服务器状态 (C05 + C06)
struct ChatServer {
    clients: Arc<Mutex<HashMap<String, ClientInfo>>>,
    broadcast_tx: broadcast::Sender<Message>,
}

// 2. 客户端信息
struct ClientInfo {
    id: String,
    nickname: String,
    room: String,
    tx: mpsc::Sender<Message>,
}

// 3. 异步服务器主循环 (C06)
async fn run_server(addr: &str) -> Result<(), Box<dyn Error>> {
    let listener = TcpListener::bind(addr).await?;
    let (broadcast_tx, _) = broadcast::channel(100);
    let server = Arc::new(ChatServer::new(broadcast_tx));
    
    loop {
        let (socket, addr) = listener.accept().await?;
        let server = Arc::clone(&server);
        
        // 为每个连接启动一个任务
        tokio::spawn(async move {
            handle_client(socket, addr, server).await
        });
    }
}

// 4. 客户端处理 (C06 + C10)
async fn handle_client(
    socket: TcpStream,
    addr: SocketAddr,
    server: Arc<ChatServer>,
) -> Result<(), Box<dyn Error>> {
    let (reader, writer) = socket.into_split();
    let mut reader = BufReader::new(reader);
    let mut writer = BufWriter::new(writer);
    
    // 订阅广播频道
    let mut broadcast_rx = server.broadcast_tx.subscribe();
    
    // 同时处理读取和广播消息
    tokio::select! {
        // 读取客户端消息
        result = read_messages(&mut reader, &server) => {
            // 处理...
        }
        // 接收广播消息
        result = write_broadcasts(&mut writer, &mut broadcast_rx) => {
            // 处理...
        }
    }
    
    Ok(())
}

// 5. 消息广播 (C09 发布-订阅)
async fn broadcast_message(server: &ChatServer, msg: Message) {
    let _ = server.broadcast_tx.send(msg);
}
```

#### 项目结构

```text
async-chat-server/
├── Cargo.toml
├── src/
│   ├── main.rs           # 服务器入口
│   ├── server.rs         # 服务器逻辑
│   ├── client.rs         # 客户端处理
│   ├── message.rs        # 消息定义
│   ├── room.rs           # 房间管理
│   ├── protocol/         # 协议定义
│   │   ├── tcp.rs
│   │   └── websocket.rs
│   └── storage/          # 消息存储
│       └── history.rs
├── client-cli/           # 命令行客户端
│   └── main.rs
├── tests/
└── README.md
```

#### 学习目标

- ✅ 深入理解 async/await
- ✅ 掌握 tokio 运行时使用
- ✅ 熟悉异步 TCP 编程
- ✅ 理解 broadcast channel
- ✅ 能处理异步并发问题

#### 扩展方向

1. Web 客户端 (React + WebSocket)
2. 消息加密
3. Redis 集群支持 (多服务器)
4. 语音/视频通话 (WebRTC)

---

### 项目4: Web API 服务 ⭐⭐⭐

#### 项目概述

**目标**: 开发一个完整的 RESTful API 服务,包含数据库、认证、中间件等

**难度**: 中级 (⭐⭐⭐)  
**时间**: 7-14 天  
**适合**: 想做 Web 后端开发的学习者

#### 涉及模块与知识点

| 模块 | 核心知识点 | 应用场景 |
|------|-----------|---------|
| **C02** | Trait、泛型 | Repository 模式 |
| **C04** | 泛型、关联类型 | 通用 CRUD |
| **C06** | async/await | 异步处理 |
| **C09** | 设计模式 | MVC、依赖注入 |
| **C10** | HTTP | RESTful API |
| **C11** | Web框架、数据库 | axum、sqlx |
| **C13** | 日志、监控 | tracing、metrics |

#### 功能需求

**基础功能**:

1. RESTful CRUD API
2. 数据库集成 (PostgreSQL)
3. 用户认证 (JWT)
4. 请求验证
5. 错误处理

**进阶功能**:
6. 分页和过滤
7. 文件上传
8. 缓存 (Redis)
9. 限流
10. API 文档 (OpenAPI)

#### 技术要点

```rust
use axum::{Router, extract::{State, Path, Query}, Json};
use sqlx::PgPool;
use serde::{Deserialize, Serialize};

// 1. 应用状态 (C09 依赖注入)
#[derive(Clone)]
struct AppState {
    db: PgPool,
    redis: RedisPool,
    config: Arc<Config>,
}

// 2. Repository 模式 (C02 + C04)
#[async_trait]
trait Repository<T> {
    async fn find_by_id(&self, id: i64) -> Result<T, Error>;
    async fn find_all(&self) -> Result<Vec<T>, Error>;
    async fn create(&self, entity: &T) -> Result<T, Error>;
    async fn update(&self, entity: &T) -> Result<T, Error>;
    async fn delete(&self, id: i64) -> Result<(), Error>;
}

// 3. 用户仓库实现
struct UserRepository {
    pool: PgPool,
}

#[async_trait]
impl Repository<User> for UserRepository {
    async fn find_by_id(&self, id: i64) -> Result<User, Error> {
        let user = sqlx::query_as!(
            User,
            "SELECT * FROM users WHERE id = $1",
            id
        )
        .fetch_one(&self.pool)
        .await?;
        
        Ok(user)
    }
    
    // 其他方法...
}

// 4. API 处理器 (C06 + C10)
async fn get_user(
    State(state): State<AppState>,
    Path(id): Path<i64>,
) -> Result<Json<User>, ApiError> {
    let repo = UserRepository::new(state.db);
    let user = repo.find_by_id(id).await?;
    Ok(Json(user))
}

async fn create_user(
    State(state): State<AppState>,
    Json(input): Json<CreateUserInput>,
) -> Result<Json<User>, ApiError> {
    // 验证输入
    input.validate()?;
    
    // 创建用户
    let repo = UserRepository::new(state.db);
    let user = repo.create(&input.into()).await?;
    
    Ok(Json(user))
}

// 5. 中间件 (C09)
async fn auth_middleware(
    headers: HeaderMap,
    mut request: Request<Body>,
    next: Next,
) -> Result<Response, StatusCode> {
    // JWT 验证
    let token = extract_token(&headers)?;
    let claims = verify_token(&token)?;
    
    // 注入用户信息
    request.extensions_mut().insert(claims);
    
    Ok(next.run(request).await)
}

// 6. 路由配置 (C10)
fn app_routes(state: AppState) -> Router {
    Router::new()
        .route("/users", get(list_users).post(create_user))
        .route("/users/:id", get(get_user).put(update_user).delete(delete_user))
        .route("/auth/login", post(login))
        .route("/auth/register", post(register))
        .layer(middleware::from_fn(auth_middleware))
        .layer(middleware::from_fn(logging_middleware))
        .layer(middleware::from_fn(cors_middleware))
        .with_state(state)
}
```

#### 项目结构

```text
web-api-service/
├── Cargo.toml
├── migrations/           # 数据库迁移
│   └── 001_init.sql
├── src/
│   ├── main.rs
│   ├── config.rs         # 配置管理
│   ├── models/           # 数据模型
│   │   ├── user.rs
│   │   └── post.rs
│   ├── repositories/     # 数据访问层
│   │   ├── mod.rs
│   │   ├── user_repo.rs
│   │   └── post_repo.rs
│   ├── services/         # 业务逻辑层
│   │   ├── mod.rs
│   │   ├── user_service.rs
│   │   └── auth_service.rs
│   ├── handlers/         # HTTP 处理器
│   │   ├── mod.rs
│   │   ├── user_handler.rs
│   │   └── auth_handler.rs
│   ├── middleware/       # 中间件
│   │   ├── mod.rs
│   │   ├── auth.rs
│   │   └── logging.rs
│   ├── error.rs          # 错误处理
│   └── utils/
│       └── validation.rs
├── tests/
│   ├── integration/
│   └── unit/
└── README.md
```

#### 学习目标

- ✅ 掌握 Web 框架使用
- ✅ 熟悉异步数据库操作
- ✅ 理解 Repository 模式
- ✅ 能实现 JWT 认证
- ✅ 掌握中间件机制

#### 扩展方向

1. GraphQL API
2. gRPC 服务
3. 实时通知 (WebSocket)
4. 微服务拆分

---

### 项目5: 分布式任务队列 ⭐⭐⭐⭐

#### 项目概述

**目标**: 开发一个分布式后台任务队列系统,支持任务调度、失败重试、监控

**难度**: 高级 (⭐⭐⭐⭐)  
**时间**: 14-21 天  
**适合**: 有一定项目经验的学习者

#### 涉及模块与知识点

| 模块 | 核心知识点 | 应用场景 |
|------|-----------|---------|
| **C05** | 线程池 | 工作线程 |
| **C06** | async/await | 异步任务 |
| **C08** | 优先队列、堆 | 任务调度 |
| **C09** | 生产者-消费者 | 任务分发 |
| **C10** | RPC | 节点通信 |
| **C11** | Redis、PostgreSQL | 任务存储 |
| **C12** | 一致性哈希 | 负载均衡 |
| **C13** | 容错、监控 | 可靠性 |

#### 功能需求

**基础功能**:

1. 任务提交和执行
2. 优先级队列
3. 失败重试
4. 任务状态追踪
5. 工作线程池

**进阶功能**:
6. 分布式调度
7. 死信队列
8. 任务依赖 (DAG)
9. 定时任务 (Cron)
10. 实时监控

#### 技术架构

```text
┌─────────────────────────────────────────────┐
│           任务队列架构                       │
├─────────────────────────────────────────────┤
│                                             │
│  客户端层 (任务提交)                         │
│  ├─ API 接口                                │
│  ├─ SDK                                     │
│  └─ CLI 工具                                │
│              ↓                              │
│  调度层 (任务调度)                           │
│  ├─ 任务路由 (一致性哈希)                    │
│  ├─ 优先级调度                               │
│  ├─ 定时触发 (Cron)                         │
│  └─ 依赖解析 (DAG)                          │
│              ↓                              │
│  执行层 (任务执行)                           │
│  ├─ Worker 节点集群                         │
│  ├─ 线程池 / 异步任务                       │
│  ├─ 任务隔离 (沙箱)                         │
│  └─ 超时控制                                 │
│              ↓                              │
│  存储层 (状态持久化)                         │
│  ├─ Redis (队列、缓存)                      │
│  ├─ PostgreSQL (任务元数据)                 │
│  └─ 对象存储 (任务结果)                      │
│              ↓                              │
│  监控层 (可观测性)                           │
│  ├─ Metrics (Prometheus)                   │
│  ├─ Logging (tracing)                      │
│  ├─ Tracing (分布式追踪)                    │
│  └─ Dashboard (Grafana)                    │
│                                             │
└─────────────────────────────────────────────┘
```

#### 技术要点

```rust
// 1. 任务定义 (C02)
#[async_trait]
trait Task: Send + Sync {
    async fn execute(&self, ctx: &TaskContext) -> Result<TaskResult, TaskError>;
    fn max_retries(&self) -> u32 { 3 }
    fn timeout(&self) -> Duration { Duration::from_secs(300) }
}

// 2. 任务队列 (C08 + C11)
struct TaskQueue {
    priority_queue: Arc<Mutex<BinaryHeap<PrioritizedTask>>>,
    redis: RedisPool,
    db: PgPool,
}

impl TaskQueue {
    async fn enqueue(&self, task: Task, priority: Priority) -> Result<TaskId> {
        // 持久化到数据库
        let task_id = self.db.insert_task(&task).await?;
        
        // 加入 Redis 队列
        self.redis.lpush("queue:pending", task_id).await?;
        
        // 加入内存优先队列
        let mut queue = self.priority_queue.lock().await;
        queue.push(PrioritizedTask { task_id, priority });
        
        Ok(task_id)
    }
    
    async fn dequeue(&self) -> Option<Task> {
        // 从优先队列取出
        let mut queue = self.priority_queue.lock().await;
        let prioritized = queue.pop()?;
        
        // 从数据库加载完整任务
        self.db.load_task(prioritized.task_id).await.ok()
    }
}

// 3. Worker 线程池 (C05)
struct WorkerPool {
    num_workers: usize,
    queue: Arc<TaskQueue>,
    shutdown: Arc<AtomicBool>,
}

impl WorkerPool {
    fn start(&self) {
        for id in 0..self.num_workers {
            let queue = Arc::clone(&self.queue);
            let shutdown = Arc::clone(&self.shutdown);
            
            thread::spawn(move || {
                let rt = tokio::runtime::Runtime::new().unwrap();
                rt.block_on(async {
                    while !shutdown.load(Ordering::Relaxed) {
                        if let Some(task) = queue.dequeue().await {
                            execute_task(task, id).await;
                        } else {
                            tokio::time::sleep(Duration::from_millis(100)).await;
                        }
                    }
                });
            });
        }
    }
}

// 4. 任务执行与重试 (C06 + C13)
async fn execute_task(task: Box<dyn Task>, worker_id: usize) {
    let ctx = TaskContext::new(worker_id);
    let max_retries = task.max_retries();
    let timeout = task.timeout();
    
    for attempt in 1..=max_retries {
        match tokio::time::timeout(timeout, task.execute(&ctx)).await {
            Ok(Ok(result)) => {
                // 任务成功
                store_result(&result).await;
                return;
            }
            Ok(Err(e)) if e.is_retriable() => {
                // 可重试错误
                warn!("Task failed (attempt {}/{}): {}", attempt, max_retries, e);
                backoff(attempt).await;
                continue;
            }
            Ok(Err(e)) => {
                // 不可重试错误
                error!("Task failed permanently: {}", e);
                move_to_dead_letter(&task).await;
                return;
            }
            Err(_) => {
                // 超时
                warn!("Task timeout (attempt {}/{})", attempt, max_retries);
                backoff(attempt).await;
                continue;
            }
        }
    }
    
    // 超过最大重试次数
    move_to_dead_letter(&task).await;
}

// 5. 分布式调度 (C12)
struct DistributedScheduler {
    nodes: Arc<RwLock<Vec<Node>>>,
    hash_ring: Arc<RwLock<ConsistentHash>>,
}

impl DistributedScheduler {
    fn route_task(&self, task_id: &TaskId) -> Node {
        let ring = self.hash_ring.read().unwrap();
        ring.get_node(task_id.hash())
    }
    
    async fn rebalance(&self) {
        // 节点变化时重新平衡任务
        let mut ring = self.hash_ring.write().unwrap();
        let nodes = self.nodes.read().unwrap();
        ring.rebuild(&nodes);
    }
}
```

#### 项目结构

```text
distributed-task-queue/
├── Cargo.toml
├── src/
│   ├── bin/
│   │   ├── server.rs     # 调度器服务
│   │   ├── worker.rs     # Worker 服务
│   │   └── cli.rs        # 管理 CLI
│   ├── lib.rs
│   ├── core/
│   │   ├── task.rs       # 任务trait定义
│   │   ├── queue.rs      # 队列实现
│   │   └── executor.rs   # 执行器
│   ├── scheduler/
│   │   ├── mod.rs
│   │   ├── priority.rs   # 优先级调度
│   │   ├── cron.rs       # 定时任务
│   │   └── dag.rs        # 依赖解析
│   ├── distributed/
│   │   ├── mod.rs
│   │   ├── hash_ring.rs  # 一致性哈希
│   │   ├── coordinator.rs # 节点协调
│   │   └── discovery.rs  # 服务发现
│   ├── storage/
│   │   ├── redis.rs
│   │   ├── postgres.rs
│   │   └── s3.rs
│   ├── monitoring/
│   │   ├── metrics.rs
│   │   ├── logging.rs
│   │   └── tracing.rs
│   └── error.rs
├── examples/
│   ├── simple_task.rs
│   └── dag_workflow.rs
├── tests/
└── README.md
```

#### 学习目标

- ✅ 掌握分布式系统设计
- ✅ 理解任务调度算法
- ✅ 熟悉消息队列使用
- ✅ 能实现容错机制
- ✅ 掌握分布式追踪

#### 扩展方向

1. 工作流引擎 (如 Airflow)
2. 多租户支持
3. 任务编排 DSL
4. AI 模型推理支持

---

### 项目6: 高性能代理服务器 ⭐⭐⭐⭐

#### 项目概述

**目标**: 开发一个高性能的反向代理/负载均衡器,支持 HTTP/HTTPS/WebSocket

**难度**: 高级 (⭐⭐⭐⭐)  
**时间**: 14-21 天  
**适合**: 关注性能优化的学习者

#### 涉及模块与知识点

| 模块 | 核心知识点 | 应用场景 |
|------|-----------|---------|
| **C05** | 多线程 | 并发连接 |
| **C06** | async/await、io_uring | 高性能 I/O |
| **C08** | 算法优化 | 路由匹配 |
| **C09** | 代理模式 | 请求转发 |
| **C10** | HTTP/TLS | 协议处理 |
| **C13** | 监控、限流 | 可靠性 |

#### 功能需求

**基础功能**:

1. HTTP/HTTPS 代理
2. 负载均衡 (轮询、最少连接)
3. 健康检查
4. 连接池
5. 请求/响应日志

**进阶功能**:
6. WebSocket 代理
7. gRPC 支持
8. 限流和熔断
9. 缓存
10. SSL 卸载
11. 流量镜像

#### 技术要点

```rust
use tokio::net::{TcpListener, TcpStream};
use hyper::{Client, Server, Request, Response, Body};

// 1. 代理配置 (C09)
struct ProxyConfig {
    upstreams: Vec<Upstream>,
    load_balancer: Box<dyn LoadBalancer>,
    health_checker: HealthChecker,
    rate_limiter: RateLimiter,
}

// 2. 负载均衡策略 (C08)
trait LoadBalancer: Send + Sync {
    fn select(&self, upstreams: &[Upstream]) -> Option<&Upstream>;
}

struct RoundRobinBalancer {
    counter: AtomicUsize,
}

impl LoadBalancer for RoundRobinBalancer {
    fn select(&self, upstreams: &[Upstream]) -> Option<&Upstream> {
        if upstreams.is_empty() {
            return None;
        }
        let idx = self.counter.fetch_add(1, Ordering::Relaxed) % upstreams.len();
        Some(&upstreams[idx])
    }
}

struct LeastConnectionBalancer {
    connections: Arc<RwLock<HashMap<String, usize>>>,
}

impl LoadBalancer for LeastConnectionBalancer {
    fn select(&self, upstreams: &[Upstream]) -> Option<&Upstream> {
        let connections = self.connections.read().unwrap();
        upstreams
            .iter()
            .min_by_key(|u| connections.get(&u.addr).unwrap_or(&0))
    }
}

// 3. 代理处理 (C06 + C10)
async fn proxy_handler(
    req: Request<Body>,
    config: Arc<ProxyConfig>,
) -> Result<Response<Body>, hyper::Error> {
    // 选择上游服务器
    let upstream = config.load_balancer.select(&config.upstreams)
        .ok_or_else(|| "No available upstream")?;
    
    // 限流检查
    if !config.rate_limiter.allow().await {
        return Response::builder()
            .status(429)
            .body(Body::from("Too Many Requests"))
            .unwrap();
    }
    
    // 健康检查
    if !config.health_checker.is_healthy(upstream).await {
        // 尝试下一个
        return Err(...);
    }
    
    // 转发请求
    let client = Client::new();
    let uri = transform_uri(req.uri(), upstream);
    let mut proxy_req = Request::builder()
        .method(req.method())
        .uri(uri)
        .body(req.into_body())
        .unwrap();
    
    // 添加代理头
    proxy_req.headers_mut().insert("X-Forwarded-For", ...);
    
    // 发送请求
    let response = client.request(proxy_req).await?;
    
    Ok(response)
}

// 4. 健康检查 (C13)
struct HealthChecker {
    upstreams: Arc<RwLock<HashMap<String, HealthStatus>>>,
}

impl HealthChecker {
    async fn check_loop(&self, upstream: Upstream) {
        loop {
            let健康 = self.check(&upstream).await;
            
            let mut状态 = self.upstreams.write().unwrap();
            状态.insert(upstream.addr.clone(), 健康);
            
            tokio::time::sleep(Duration::from_secs(10)).await;
        }
    }
    
    async fn check(&self, upstream: &Upstream) -> HealthStatus {
        // HTTP 健康检查
        match reqwest::get(&upstream.health_url).await {
            Ok(resp) if resp.status().is_success() => HealthStatus::Healthy,
            _ => HealthStatus::Unhealthy,
        }
    }
}

// 5. 限流 (C13)
struct RateLimiter {
    permits: Arc<Semaphore>,
    refill_rate: usize,
}

impl RateLimiter {
    async fn allow(&self) -> bool {
        self.permits.try_acquire().is_ok()
    }
    
    async fn refill_loop(&self) {
        loop {
            tokio::time::sleep(Duration::from_secs(1)).await;
            self.permits.add_permits(self.refill_rate);
        }
    }
}

// 6. 连接池 (C05)
struct ConnectionPool {
    connections: Arc<Mutex<HashMap<String, Vec<TcpStream>>>>,
    max_size: usize,
}

impl ConnectionPool {
    async fn get(&self, addr: &str) -> Option<TcpStream> {
        let mut conns = self.connections.lock().await;
        conns.get_mut(addr)?.pop()
    }
    
    async fn put(&self, addr: String, conn: TcpStream) {
        let mut conns = self.connections.lock().await;
        let pool = conns.entry(addr).or_insert_with(Vec::new);
        if pool.len() < self.max_size {
            pool.push(conn);
        }
    }
}
```

#### 学习目标

- ✅ 掌握高性能 I/O 技术
- ✅ 理解负载均衡算法
- ✅ 熟悉 HTTP 代理实现
- ✅ 能实现限流和熔断
- ✅ 掌握连接池管理

#### 扩展方向

1. 配置热重载
2. 动态上游发现
3. WAF (Web 应用防火墙)
4. A/B 测试支持

---

### 项目7: 实时数据处理引擎 ⭐⭐⭐⭐

#### 项目概述

**目标**: 开发一个实时流数据处理引擎,类似 Apache Flink/Spark Streaming

**难度**: 高级 (⭐⭐⭐⭐)  
**时间**: 14-21 天  
**适合**: 关注大数据和算法的学习者

#### 涉及模块与知识点

| 模块 | 核心知识点 | 应用场景 |
|------|-----------|---------|
| **C05** | 并发数据结构 | 流处理管道 |
| **C06** | async stream | 异步数据流 |
| **C08** | 算法、数据结构 | 窗口、聚合 |
| **C09** | Pipeline 模式 | 数据处理链 |
| **C10** | 网络 I/O | 数据源/接收器 |
| **C13** | 容错 | Exactly-once 语义 |

#### 功能需求

**基础功能**:

1. 数据源抽象 (Kafka, File, TCP)
2. 数据转换 (map, filter, flatMap)
3. 窗口聚合 (滚动、滑动、会话)
4. 状态管理
5. 数据接收器 (Database, File, Kafka)

**进阶功能**:
6. 精确一次语义 (Exactly-once)
7. 事件时间处理
8. 水印 (Watermark)
9. Join 操作
10. CEP (复杂事件处理)

#### 技术要点

```rust
// 1. 数据流抽象 (C06 + C08)
trait DataStream<T>: Send {
    fn map<U, F>(self, f: F) -> Box<dyn DataStream<U>>
    where
        F: Fn(T) -> U + Send + 'static,
        U: Send + 'static;
    
    fn filter<F>(self, f: F) -> Box<dyn DataStream<T>>
    where
        F: Fn(&T) -> bool + Send + 'static;
    
    fn window(self, window: WindowSpec) -> Box<dyn WindowedStream<T>>;
}

// 2. 窗口处理 (C08)
enum WindowSpec {
    Tumbling(Duration),         // 滚动窗口
    Sliding(Duration, Duration), // 滑动窗口
    Session(Duration),           // 会话窗口
}

struct TumblingWindow<T> {
    size: Duration,
    buffer: Arc<Mutex<HashMap<WindowKey, Vec<T>>>>,
}

impl<T: Send + 'static> TumblingWindow<T> {
    async fn process(&self, event: Event<T>) {
        let window_key = self.assign_window(&event);
        
        let mut buffer = self.buffer.lock().await;
        buffer.entry(window_key)
            .or_insert_with(Vec::new)
            .push(event.data);
        
        // 检查窗口是否关闭
        if self.should_trigger(window_key) {
            let data = buffer.remove(&window_key).unwrap();
            self.emit_window(window_key, data).await;
        }
    }
}

// 3. 状态管理 (C05)
trait StateBackend: Send + Sync {
    fn get(&self, key: &[u8]) -> Option<Vec<u8>>;
    fn put(&self, key: &[u8], value: &[u8]);
    fn checkpoint(&self) -> CheckpointId;
    fn restore(&self, checkpoint: CheckpointId);
}

struct RocksDBBackend {
    db: Arc<rocksdb::DB>,
}

// 4. 精确一次语义 (C13)
struct CheckpointCoordinator {
    epoch: AtomicU64,
    barriers: Arc<Mutex<HashMap<u64, Vec<BarrierResponse>>>>,
}

impl CheckpointCoordinator {
    async fn trigger_checkpoint(&self) -> CheckpointId {
        let epoch = self.epoch.fetch_add(1, Ordering::SeqCst);
        
        // 向所有 operator 发送 barrier
        self.broadcast_barrier(epoch).await;
        
        // 等待所有 operator 响应
        self.wait_for_barriers(epoch).await;
        
        // 通知完成
        CheckpointId::new(epoch)
    }
}

// 5. 处理管道 (C09 Pipeline)
struct ProcessingPipeline<T> {
    stages: Vec<Box<dyn ProcessStage<T>>>,
}

impl<T: Send + 'static> ProcessingPipeline<T> {
    async fn process(&self, mut data: T) -> Result<T, Error> {
        for stage in &self.stages {
            data = stage.process(data).await?;
        }
        Ok(data)
    }
}

// 6. 事件时间与水印 (C08)
struct WatermarkGenerator {
    max_out_of_orderness: Duration,
    last_event_time: Arc<Mutex<Option<Instant>>>,
}

impl WatermarkGenerator {
    fn generate(&self, event_time: Instant) -> Option<Watermark> {
        let mut last = self.last_event_time.lock().unwrap();
        
        if let Some(prev_time) = *last {
            if event_time > prev_time {
                *last = Some(event_time);
                return Some(Watermark {
                    timestamp: event_time - self.max_out_of_orderness,
                });
            }
        } else {
            *last = Some(event_time);
        }
        
        None
    }
}

// 7. Join 操作 (C08)
struct JoinOperator<L, R> {
    left_buffer: Arc<Mutex<HashMap<Key, Vec<L>>>>,
    right_buffer: Arc<Mutex<HashMap<Key, Vec<R>>>>,
    window: Duration,
}

impl<L, R> JoinOperator<L, R> {
    async fn join_left(&self, key: Key, left: L) -> Vec<(L, R)> {
        let mut results = Vec::new();
        
        // 与右侧缓存的元素进行 join
        let right_buf = self.right_buffer.lock().await;
        if let Some(rights) = right_buf.get(&key) {
            for right in rights {
                results.push((left.clone(), right.clone()));
            }
        }
        
        // 缓存左侧元素
        let mut left_buf = self.left_buffer.lock().await;
        left_buf.entry(key).or_insert_with(Vec::new).push(left);
        
        results
    }
}
```

#### 项目结构

```text
realtime-stream-engine/
├── Cargo.toml
├── src/
│   ├── lib.rs
│   ├── core/
│   │   ├── stream.rs        # 数据流抽象
│   │   ├── operator.rs      # 算子
│   │   └── event.rs         # 事件定义
│   ├── window/
│   │   ├── mod.rs
│   │   ├── tumbling.rs
│   │   ├── sliding.rs
│   │   └── session.rs
│   ├── state/
│   │   ├── mod.rs
│   │   ├── backend.rs       # 状态后端
│   │   └── checkpoint.rs    # 检查点
│   ├── time/
│   │   ├── watermark.rs
│   │   └── event_time.rs
│   ├── connector/
│   │   ├── kafka.rs
│   │   ├── file.rs
│   │   └── tcp.rs
│   └── examples/
│       ├── word_count.rs
│       ├── tumbling_window.rs
│       └── join_example.rs
├── benches/
└── README.md
```

#### 学习目标

- ✅ 理解流处理架构
- ✅ 掌握窗口算法
- ✅ 熟悉状态管理
- ✅ 理解精确一次语义
- ✅ 掌握事件时间处理

---

### 项目8: 微服务框架 ⭐⭐⭐⭐⭐

#### 项目概述

**目标**: 开发一个完整的微服务框架,提供服务发现、配置管理、链路追踪等

**难度**: 专家 (⭐⭐⭐⭐⭐)  
**时间**: 21-30 天  
**适合**: 有丰富经验,想深入微服务架构的学习者

#### 涉及模块

C06 (异步), C09 (设计模式), C10 (网络), C11 (库生态), C12 (架构), C13 (可靠性)

#### 功能需求

**核心功能**:

1. 服务注册与发现
2. RPC 框架 (gRPC/Thrift)
3. 负载均衡
4. 熔断器
5. 配置中心
6. 分布式追踪
7. 监控与告警
8. 日志聚合

**进阶功能**:
9. 服务网格 (Sidecar)
10. 灰度发布
11. API 网关
12. 分布式事务

#### 学习目标

- 掌握微服务架构设计
- 理解分布式系统模式
- 熟悉云原生技术栈

---

### 项目9: 区块链节点 ⭐⭐⭐⭐⭐

#### 项目概述

**目标**: 实现一个简化的区块链节点,支持 P2P 网络、共识算法、智能合约

**难度**: 专家 (⭐⭐⭐⭐⭐)  
**时间**: 21-30 天  
**适合**: 对区块链和密码学感兴趣的学习者

#### 涉及模块

C05 (并发), C06 (异步), C07 (进程), C08 (算法), C10 (网络), C13 (可靠性)

#### 功能需求

**核心功能**:

1. 区块结构
2. P2P 网络
3. 共识算法 (PoW/PoS)
4. 交易池
5. Merkle 树
6. UTXO/Account 模型
7. 钱包管理
8. 简单智能合约

#### 学习目标

- 理解区块链原理
- 掌握密码学应用
- 熟悉 P2P 网络编程

---

### 项目10: 操作系统内核模块 ⭐⭐⭐⭐⭐

#### 项目概述

**目标**: 使用 Rust 编写操作系统内核模块或嵌入式系统

**难度**: 专家 (⭐⭐⭐⭐⭐)  
**时间**: 21-30 天  
**适合**: 对系统编程和硬件有深入兴趣的学习者

#### 涉及模块

C01 (所有权), C02 (类型), C05 (并发), C07 (进程), C08 (算法), C13 (可靠性)

#### 功能需求

**核心功能**:

1. 启动加载
2. 内存管理
3. 进程调度
4. 文件系统
5. 设备驱动
6. 系统调用
7. 中断处理

#### 学习目标

- 深入理解操作系统
- 掌握 unsafe Rust
- 熟悉硬件交互

---

## 📊 项目选择建议

### 按学习阶段选择

| 阶段 | 推荐项目 | 理由 |
|------|---------|------|
| **入门** (C01-C03) | 项目1 | 巩固基础,建立信心 |
| **初级** (C01-C04) | 项目2 | 引入并发概念 |
| **中级** (C01-C06) | 项目3, 4 | 掌握异步和 Web |
| **高级** (C01-C10) | 项目5, 6, 7 | 综合运用,深入优化 |
| **专家** (全部) | 项目8, 9, 10 | 挑战复杂系统 |

### 按兴趣方向选择

| 兴趣方向 | 推荐项目 |
|---------|---------|
| **Web 后端** | 项目4 → 项目3 → 项目8 |
| **系统编程** | 项目2 → 项目6 → 项目10 |
| **大数据** | 项目7 → 项目5 |
| **区块链** | 项目9 |
| **性能优化** | 项目6 → 项目7 |

---

## 🎯 项目实施建议

### 开发流程

1. **需求分析** (1天)
   - 明确项目目标
   - 列出功能清单
   - 设计系统架构

2. **技术选型** (1天)
   - 选择依赖库
   - 确定技术栈
   - 搭建项目骨架

3. **迭代开发** (主要时间)
   - MVP 优先
   - 增量添加功能
   - 持续测试

4. **优化完善** (2-3天)
   - 性能优化
   - 错误处理完善
   - 文档编写

5. **部署上线** (1-2天)
   - CI/CD 配置
   - 容器化
   - 监控配置

### 学习建议

1. **不要追求完美** - 先做出来,再优化
2. **多写测试** - 测试是最好的文档
3. **参考优秀项目** - 学习开源项目的代码
4. **记录遇到的问题** - 建立自己的知识库
5. **分享你的项目** - 获得反馈,持续改进

---

## 📚 相关资源

- 📖 [跨模块学习路线图](./CROSS_MODULE_LEARNING_ROADMAP_2025_10_25.md)
- 🧠 [统一知识图谱](./UNIFIED_KNOWLEDGE_GRAPH_2025_10_25.md)
- 📚 [主文档索引](./MASTER_DOCUMENTATION_INDEX.md)

---

**文档版本**: v1.0  
**创建日期**: 2025-10-25  
**维护状态**: 活跃维护  
**反馈渠道**: GitHub Issues

**祝项目开发顺利! 🚀**
