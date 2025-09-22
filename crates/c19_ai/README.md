# C19 AI - 人工智能与机器学习库 (2025 Edition)

[![Rust](https://img.shields.io/badge/rust-1.89+-orange.svg)](https://www.rust-lang.org/)
[![License](https://img.shields.io/badge/license-MIT-blue.svg)](LICENSE)
[![Version](https://img.shields.io/badge/version-0.3.0-green.svg)](Cargo.toml)

一个基于 Rust 1.89 的现代化 AI 和机器学习库，集成了最新的开源 AI 框架和工具。支持 2025 年最新的 AI 技术栈，包括 Candle、Burn、Tch、DFDx 等深度学习框架。

## 🚀 主要特性

- 🤖 **机器学习**: 支持监督学习、无监督学习和强化学习
- 🧠 **深度学习**: 集成 Candle 0.10、Burn 0.15、Tch 0.16、DFDx 0.15 等现代深度学习框架
- 🗣️ **自然语言处理**: 支持 BERT、GPT、LLaMA 等预训练模型
- 👁️ **计算机视觉**: OpenCV 集成和图像处理功能
- 📊 **数据处理**: 高性能的 DataFrame 和数据处理管道
- 🔍 **向量搜索**: 支持向量数据库和语义搜索
- 🚀 **高性能**: 利用 Rust 的零成本抽象和内存安全
- 🌐 **多模态AI**: 支持文本、图像、音频等多模态处理
- 🔗 **联邦学习**: 支持分布式和隐私保护的机器学习
- ⚡ **边缘AI**: 支持移动端和边缘设备部署
- 🧮 **量子机器学习**: 探索量子计算在机器学习中的应用
- 🌐 **Web管理界面**: 现代化的Web管理界面，支持模型管理、用户管理、配置管理等

## 📦 核心模块

### 缓存系统

- **内存缓存**: 高性能内存缓存实现
- **LRU缓存**: 最近最少使用缓存策略
- **TTL缓存**: 带生存时间的缓存
- **缓存管理**: 统一的缓存管理接口

### 推理引擎

- **模型推理**: 统一的模型推理接口
- **推理队列**: 异步推理任务队列
- **结果缓存**: 推理结果缓存机制
- **性能监控**: 推理性能指标收集

### 存储管理

- **多后端支持**: 本地存储、S3、GCS、Azure
- **文件元数据**: 完整的文件元数据管理
- **复制机制**: 数据复制和备份
- **统一接口**: 统一的存储访问接口

### WebSocket通信

- **实时通信**: 支持实时双向通信
- **消息处理**: 灵活的消息处理机制
- **房间管理**: 多房间支持
- **连接管理**: 连接状态监控

### 消息系统

- **消息队列**: 高性能消息队列
- **生产者/消费者**: 异步消息处理
- **消息代理**: 消息路由和分发
- **事件处理**: 事件驱动架构

### API服务器

- **REST API**: 完整的REST API支持
- **中间件**: 认证、日志、限流、CORS等
- **路由处理**: 灵活的路由配置
- **错误处理**: 统一的错误处理机制

### 数据库集成

- **ORM系统**: 对象关系映射
- **实体管理**: 数据库实体定义
- **事务处理**: 完整的事务管理
- **多数据库支持**: PostgreSQL、MySQL、SQLite、Redis、MongoDB

### 认证授权

- **用户管理**: 完整的用户管理系统
- **角色权限**: 基于角色的访问控制(RBAC)
- **JWT认证**: JSON Web Token认证
- **会话管理**: 用户会话管理
- **密码安全**: Argon2密码哈希
- **安全特性**: 登录锁定、2FA支持

### 监控日志

- **指标收集**: Counter、Histogram、Gauge、Timer
- **日志记录**: Error、Warn、Info、Debug、Trace
- **仪表板**: 监控仪表板系统
- **性能分析**: 性能指标分析

### Web管理界面

- **仪表板**: 系统概览和关键指标展示
- **模型管理**: 模型创建、编辑、部署和监控
- **用户管理**: 用户账户、角色和权限管理
- **配置管理**: 系统配置的查看、编辑和管理
- **实时更新**: 支持实时数据更新和通知
- **响应式设计**: 支持移动端和桌面端访问

### 数据处理

- **DataFrame**: 高性能数据处理
- **预处理**: 缺失值、标准化、归一化、缩放、异常值处理
- **特征工程**: 数学、统计、时间、文本特征
- **处理管道**: 数据处理管道

### 模型管理

- **模型注册**: 模型注册和版本管理
- **模型存储**: 模型文件存储
- **模型部署**: 模型部署和监控
- **版本控制**: 模型版本控制

### 训练系统

- **训练管道**: 完整的训练管道
- **任务管理**: 训练任务管理
- **调度器**: 任务调度系统
- **指标收集**: 训练指标收集
- **检查点**: 训练检查点机制

### 向量搜索

- **嵌入生成**: 文本和图像嵌入
- **相似性搜索**: 向量相似性搜索
- **向量数据库**: 向量存储和检索
- **语义搜索**: 语义相似性搜索

### 大语言模型

- **聊天接口**: 对话式AI接口
- **文本补全**: 文本生成和补全
- **嵌入服务**: 文本嵌入生成
- **模型管理**: LLM模型管理
- **多提供商**: 支持多个LLM提供商

### 配置管理

- **多源配置**: 环境变量、文件、数据库、命令行
- **配置验证**: 配置值验证和类型检查
- **热重载**: 配置热重载支持
- **默认值**: 智能默认值管理

## 🛠️ 安装和使用

### 添加依赖

在 `Cargo.toml` 中添加：

```toml
[dependencies]
c19_ai = "0.3.0"
```

### 基本使用

#### 启动Web管理界面

```rust
use c19_ai::web_ui::{create_web_ui_routes, WebUIState};
use axum::Router;
use std::net::SocketAddr;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建Web UI状态
    let state = WebUIState {
        api_base_url: "http://localhost:3000/api".to_string(),
        version: env!("CARGO_PKG_VERSION").to_string(),
        build_time: chrono::Utc::now().to_rfc3339(),
    };

    // 创建Web UI路由
    let app = create_web_ui_routes(state);

    // 启动服务器
    let addr = SocketAddr::from(([0, 0, 0, 0], 8080));
    println!("Web UI服务器启动在 http://{}", addr);
    
    axum::serve(
        tokio::net::TcpListener::bind(addr).await?,
        app
    ).await?;

    Ok(())
}
```

#### 基本AI功能使用

```rust
use c19_ai::prelude::*;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建 AI 引擎
    let mut ai_engine = AIEngine::new();
    
    // 加载预训练模型
    ai_engine.load_model("bert-base-chinese").await?;
    
    // 进行推理
    let result = ai_engine.predict("你好，世界！").await?;
    println!("预测结果: {:?}", result);
    
    Ok(())
}
```

### 配置管理示例

```rust
use c19_ai::config::{ConfigManager, ConfigSource};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建配置管理器
    let config_manager = ConfigManager::new()
        .add_source(ConfigSource::File("config.json".to_string()));

    // 加载配置
    config_manager.load_all().await?;

    // 获取配置值
    let server_host: String = config_manager
        .get_or_default("server.host", "0.0.0.0".to_string())
        .await?;
    let server_port: i64 = config_manager
        .get_or_default("server.port", 8080)
        .await?;

    println!("服务器: {}:{}", server_host, server_port);
    Ok(())
}
```

### API服务器示例

```rust
use c19_ai::config::{ConfigManager, ConfigSource};
use axum::{extract::State, response::Json, routing::get, Router};

#[derive(Clone)]
struct AppState {
    config_manager: Arc<ConfigManager>,
}

async fn health_check() -> Json<serde_json::Value> {
    Json(serde_json::json!({
        "status": "healthy",
        "version": "0.3.0"
    }))
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建配置管理器
    let config_manager = ConfigManager::new()
        .add_source(ConfigSource::File("config.json".to_string()));
    config_manager.load_all().await?;

    // 创建应用状态
    let state = AppState {
        config_manager: Arc::new(config_manager),
    };

    // 创建路由
    let app = Router::new()
        .route("/health", get(health_check))
        .with_state(state);

    // 启动服务器
    let listener = tokio::net::TcpListener::bind("0.0.0.0:8080").await?;
    axum::serve(listener, app).await?;

    Ok(())
}
```

## 📁 项目结构

```text
c19_ai/
├── src/
│   ├── lib.rs                 # 主库文件
│   ├── config/                # 配置管理
│   │   ├── mod.rs
│   │   ├── manager.rs         # 配置管理器
│   │   ├── schema.rs          # 配置模式
│   │   └── validation.rs      # 配置验证
│   ├── cache/                 # 缓存系统
│   │   ├── mod.rs
│   │   ├── manager.rs         # 缓存管理器
│   │   ├── memory.rs          # 内存缓存
│   │   ├── lru.rs             # LRU缓存
│   │   └── ttl.rs             # TTL缓存
│   ├── inference/             # 推理引擎
│   │   ├── mod.rs
│   │   ├── engine.rs          # 推理引擎
│   │   ├── queue.rs           # 推理队列
│   │   └── cache.rs           # 推理缓存
│   ├── storage/               # 存储管理
│   │   ├── mod.rs
│   │   ├── manager.rs         # 存储管理器
│   │   ├── local.rs           # 本地存储
│   │   ├── s3.rs              # S3存储
│   │   ├── gcs.rs             # GCS存储
│   │   └── azure.rs           # Azure存储
│   ├── websocket/             # WebSocket通信
│   │   ├── mod.rs
│   │   ├── manager.rs         # WebSocket管理器
│   │   ├── handler.rs         # 消息处理器
│   │   ├── client.rs          # WebSocket客户端
│   │   ├── server.rs          # WebSocket服务器
│   │   ├── room.rs            # 房间管理
│   │   └── message.rs         # 消息定义
│   ├── messaging/             # 消息系统
│   │   ├── mod.rs
│   │   ├── manager.rs         # 消息管理器
│   │   ├── producer.rs        # 消息生产者
│   │   ├── consumer.rs        # 消息消费者
│   │   └── broker.rs          # 消息代理
│   ├── database/              # 数据库集成
│   │   ├── mod.rs
│   │   ├── connection.rs      # 数据库连接
│   │   ├── transaction.rs     # 事务管理
│   │   ├── orm.rs             # ORM系统
│   │   ├── entities.rs        # 数据库实体
│   │   └── models.rs          # 数据模型
│   ├── auth/                  # 认证授权
│   │   ├── mod.rs
│   │   ├── manager.rs         # 认证管理器
│   │   ├── user.rs            # 用户管理
│   │   ├── role.rs            # 角色管理
│   │   ├── permission.rs      # 权限管理
│   │   ├── jwt.rs             # JWT认证
│   │   ├── session.rs         # 会话管理
│   │   └── oauth.rs           # OAuth认证
│   ├── monitoring/            # 监控日志
│   │   ├── mod.rs
│   │   ├── metrics.rs         # 指标收集
│   │   ├── logging.rs         # 日志记录
│   │   └── dashboard.rs       # 监控仪表板
│   ├── web_ui/               # Web管理界面
│   │   ├── mod.rs            # Web UI模块
│   │   ├── dashboard.rs      # 仪表板页面
│   │   ├── model_manager.rs  # 模型管理页面
│   │   ├── user_manager.rs   # 用户管理页面
│   │   └── config_manager.rs # 配置管理页面
│   ├── data_processing/       # 数据处理
│   │   ├── mod.rs
│   │   ├── dataframe.rs       # DataFrame实现
│   │   ├── preprocessing.rs   # 数据预处理
│   │   ├── feature_engineering.rs # 特征工程
│   │   └── pipeline.rs        # 处理管道
│   ├── model_management/      # 模型管理
│   │   ├── mod.rs
│   │   ├── registry.rs        # 模型注册
│   │   ├── storage.rs         # 模型存储
│   │   ├── deployment.rs      # 模型部署
│   │   └── monitoring.rs      # 模型监控
│   ├── training/              # 训练系统
│   │   ├── mod.rs
│   │   ├── pipeline.rs        # 训练管道
│   │   ├── job.rs             # 训练任务
│   │   ├── scheduler.rs       # 任务调度
│   │   └── metrics.rs         # 训练指标
│   ├── vector_search/         # 向量搜索
│   │   ├── mod.rs
│   │   ├── embeddings.rs      # 嵌入生成
│   │   ├── similarity.rs      # 相似性搜索
│   │   └── database.rs        # 向量数据库
│   ├── llm/                   # 大语言模型
│   │   ├── mod.rs
│   │   ├── chat.rs            # 聊天接口
│   │   ├── completions.rs     # 文本补全
│   │   ├── embeddings.rs      # 嵌入服务
│   │   ├── models.rs          # 模型管理
│   │   └── providers.rs       # 提供商接口
│   └── validation/            # 数据验证
│       ├── mod.rs
│       ├── schema.rs          # 验证模式
│       └── validator.rs       # 验证器
├── examples/                  # 示例代码
│   ├── config_example.rs      # 配置管理示例
│   ├── api_server.rs          # API服务器示例
│   └── config.json            # 配置文件示例
├── scripts/                   # 脚本文件
│   └── init.sql               # 数据库初始化脚本
├── tests/                     # 测试文件
│   ├── integration_tests.rs   # 集成测试
│   └── performance_tests.rs   # 性能测试
├── Cargo.toml                 # 项目配置
└── README.md                  # 项目文档
```

## 🔧 配置

### 环境变量

```bash
# 服务器配置
C19_AI_SERVER_HOST=0.0.0.0
C19_AI_SERVER_PORT=8080
C19_AI_SERVER_WORKERS=4

# 数据库配置
C19_AI_DATABASE_HOST=localhost
C19_AI_DATABASE_PORT=5432
C19_AI_DATABASE_NAME=c19_ai
C19_AI_DATABASE_USERNAME=postgres
C19_AI_DATABASE_PASSWORD=your_password

# 缓存配置
C19_AI_CACHE_DEFAULT_TTL=3600
C19_AI_CACHE_MAX_SIZE=1000

# 存储配置
C19_AI_STORAGE_DEFAULT_BACKEND=local
C19_AI_STORAGE_LOCAL_BASE_PATH=/tmp/c19_ai

# 认证配置
C19_AI_AUTH_JWT_SECRET=your-secret-key
C19_AI_AUTH_JWT_EXPIRY=86400

# 日志配置
C19_AI_LOGGING_LEVEL=info
C19_AI_LOGGING_FORMAT=json
```

### 配置文件

创建 `config.json` 文件：

```json
{
  "server": {
    "host": "0.0.0.0",
    "port": 8080,
    "workers": 4
  },
  "database": {
    "host": "localhost",
    "port": 5432,
    "name": "c19_ai",
    "username": "postgres",
    "password": "your_password"
  },
  "cache": {
    "default_ttl": 3600,
    "max_size": 1000
  },
  "storage": {
    "default_backend": "local",
    "local": {
      "base_path": "/tmp/c19_ai"
    }
  },
  "auth": {
    "jwt_secret": "your-secret-key",
    "jwt_expiry": 86400
  },
  "logging": {
    "level": "info",
    "format": "json"
  }
}
```

## 🗄️ 数据库

### 初始化数据库

```bash
# 创建数据库
createdb c19_ai

# 运行初始化脚本
psql -d c19_ai -f scripts/init.sql
```

### 数据库表结构

- **users**: 用户表
- **roles**: 角色表
- **user_roles**: 用户角色关联表
- **user_sessions**: 用户会话表
- **api_keys**: API密钥表
- **models**: 模型表
- **training_jobs**: 训练任务表
- **inference_jobs**: 推理任务表
- **datasets**: 数据集表
- **performance_metrics**: 性能指标表
- **audit_logs**: 审计日志表
- **system_config**: 系统配置表
- **cache_statistics**: 缓存统计表
- **storage_backends**: 存储后端表
- **file_metadata**: 文件元数据表

## 🧪 测试

### 运行测试

```bash
# 运行所有测试
cargo test

# 运行集成测试
cargo test --test integration_tests

# 运行性能测试
cargo test --test performance_tests

# 运行特定测试
cargo test test_ai_engine_initialization
```

### 运行示例

```bash
# 运行配置管理示例
cargo run --example config_example

# 运行API服务器示例
cargo run --example api_server
```

## 📊 性能特性

- **零成本抽象**: 利用Rust的零成本抽象特性
- **内存安全**: 编译时内存安全保证
- **并发安全**: 内置并发安全机制
- **高性能**: 优化的数据结构和算法
- **异步支持**: 全面的异步编程支持
- **缓存优化**: 多级缓存策略
- **连接池**: 数据库连接池管理
- **批处理**: 批量操作支持

## 🔒 安全特性

- **密码安全**: Argon2密码哈希
- **JWT认证**: 安全的JWT令牌认证
- **会话管理**: 安全的会话管理
- **权限控制**: 基于角色的访问控制
- **输入验证**: 全面的输入验证
- **SQL注入防护**: 参数化查询
- **XSS防护**: 输出编码和验证
- **CSRF防护**: CSRF令牌验证
- **速率限制**: API速率限制
- **审计日志**: 完整的操作审计

## 🌐 API接口

### 健康检查

```http
GET /health
```

### 配置管理1

```http
GET /config/{key}
POST /config
GET /configs
```

### 用户管理

```http
POST /auth/login
POST /auth/logout
POST /auth/register
GET /users
POST /users
PUT /users/{id}
DELETE /users/{id}
```

### 模型管理1

```http
GET /models
POST /models
GET /models/{id}
PUT /models/{id}
DELETE /models/{id}
POST /models/{id}/deploy
```

### 推理服务

```http
POST /inference
GET /inference/{id}
GET /inference/queue
```

### 训练服务

```http
POST /training
GET /training/{id}
GET /training/queue
```

## 🤝 贡献

欢迎贡献代码！请遵循以下步骤：

1. Fork 项目
2. 创建特性分支 (`git checkout -b feature/AmazingFeature`)
3. 提交更改 (`git commit -m 'Add some AmazingFeature'`)
4. 推送到分支 (`git push origin feature/AmazingFeature`)
5. 打开 Pull Request

## 📄 许可证

本项目采用 MIT 许可证 - 查看 [LICENSE](LICENSE) 文件了解详情。

## 🙏 致谢

感谢以下开源项目的贡献：

- [Rust](https://www.rust-lang.org/) - 系统编程语言
- [Tokio](https://tokio.rs/) - 异步运行时
- [Axum](https://github.com/tokio-rs/axum) - Web框架
- [Serde](https://serde.rs/) - 序列化框架
- [SQLx](https://github.com/launchbadge/sqlx) - 异步SQL工具包
- [Candle](https://github.com/huggingface/candle) - 深度学习框架
- [Burn](https://github.com/burn-rs/burn) - 深度学习框架

## 📞 联系方式

- 项目主页: [GitHub Repository](https://github.com/your-username/c19_ai)
- 问题报告: [Issues](https://github.com/your-username/c19_ai/issues)
- 讨论区: [Discussions](https://github.com/your-username/c19_ai/discussions)

---

**C19 AI** - 让AI开发更简单、更安全、更高效！ 🚀
