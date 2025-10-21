# 学习路径

## 📋 目录

- [概述](#概述)
- [初学者路径](#初学者路径)
- [进阶路径](#进阶路径)
- [专家路径](#专家路径)
- [场景化学习](#场景化学习)

---

## 概述

本文档提供系统化的学习路径，帮助您逐步掌握 Rust 开源库生态。

---

## 初学者路径

### 第1阶段：基础工具 (1-2周)

#### 1. 序列化与配置

- **学习内容**: `serde`, `serde_json`, `toml`
- **实践项目**: 配置文件解析器
- **文档位置**: `01_infrastructure/serialization/`

#### 2. 错误处理

- **学习内容**: `anyhow`, `thiserror`
- **实践项目**: 错误处理工具库
- **文档位置**: `cross_cutting/error_handling/`

#### 3. 日志系统

- **学习内容**: `log`, `env_logger`
- **实践项目**: 带日志的命令行工具
- **文档位置**: `03_application_dev/logging/`

### 第2阶段：CLI 开发 (2-3周)

#### 1. 命令行解析

- **学习内容**: `clap`
- **实践项目**: 文件管理工具
- **文档位置**: `03_application_dev/cli_tools/`

#### 2. 文件操作

- **学习内容**: `walkdir`, `fs`
- **实践项目**: 代码统计工具
- **文档位置**: `02_system_programming/io/`

#### 3. 正则表达式

- **学习内容**: `regex`
- **实践项目**: 文本搜索工具
- **文档位置**: `01_infrastructure/text_processing/`

---

## 进阶路径

### 第3阶段：异步编程 (3-4周)

#### 1. Tokio 基础

- **学习内容**: `tokio`, `futures`
- **实践项目**: 异步文件处理器
- **文档位置**: `02_system_programming/async_runtime/`

#### 2. HTTP 客户端

- **学习内容**: `reqwest`
- **实践项目**: API 客户端库
- **文档位置**: `03_application_dev/http_clients/`

#### 3. 并发编程

- **学习内容**: `crossbeam`, `rayon`
- **实践项目**: 并发数据处理
- **文档位置**: `02_system_programming/concurrency/`

### 第4阶段：Web 开发 (4-6周)

#### 1. Web 框架

- **学习内容**: `axum`, `actix-web`
- **实践项目**: REST API 服务
- **文档位置**: `03_application_dev/web_frameworks/`

#### 2. 数据库

- **学习内容**: `sqlx`, `diesel`
- **实践项目**: CRUD 应用
- **文档位置**: `03_application_dev/databases/`

#### 3. 中间件

- **学习内容**: `tower`, `tower-http`
- **实践项目**: 认证中间件
- **文档位置**: `03_application_dev/middleware/`

---

## 专家路径

### 第5阶段：高级主题 (6-8周)

#### 1. 分布式系统

- **学习内容**: `rdkafka`, `lapin`
- **实践项目**: 消息队列系统
- **文档位置**: `03_application_dev/message_queues/`

#### 2. 微服务

- **学习内容**: `tonic`, gRPC
- **实践项目**: 微服务架构
- **文档位置**: `03_application_dev/grpc/`

#### 3. 性能优化

- **学习内容**: `criterion`, profiling tools
- **实践项目**: 性能基准测试
- **文档位置**: `05_toolchain/profiling/`

### 第6阶段：领域专精 (持续)

#### Web3 / 区块链

- **路径**: `04_domain_specific/blockchain/`
- **项目**: 智能合约交互工具

#### 游戏开发

- **路径**: `04_domain_specific/game/`
- **项目**: 2D 游戏原型

#### 机器学习

- **路径**: `04_domain_specific/ml/`
- **项目**: 数据分析管道

---

## 场景化学习

### 场景1：构建 RESTful API

**学习顺序**:

1. `axum` (Web 框架)
2. `sqlx` (数据库)
3. `serde` (序列化)
4. `tower-http` (中间件)
5. `jsonwebtoken` (认证)

**项目示例**: 博客 API 系统

**预计时间**: 4-6周

---

### 场景2：开发 CLI 工具

**学习顺序**:

1. `clap` (参数解析)
2. `anyhow` (错误处理)
3. `tokio` (异步运行时)
4. `indicatif` (进度条)
5. `reqwest` (HTTP 请求)

**项目示例**: 文件下载管理器

**预计时间**: 2-3周

---

### 场景3：数据处理管道

**学习顺序**:

1. `polars` (数据处理)
2. `serde` (序列化)
3. `rayon` (并行计算)
4. `plotters` (可视化)
5. `sqlx` (数据存储)

**项目示例**: 日志分析系统

**预计时间**: 3-4周

---

## 学习建议

### 1. 动手实践

每个库都应该：

- ✅ 阅读官方文档
- ✅ 运行示例代码
- ✅ 完成小项目
- ✅ 阅读源码（可选）

### 2. 循序渐进

- 不要跳过基础
- 每个阶段完成后再进入下一个
- 遇到问题及时查文档

### 3. 项目驱动

- 以实际项目为导向
- 边学边做，学以致用
- 构建个人作品集

### 4. 社区参与

- 加入 Rust 社区
- 阅读开源项目代码
- 参与贡献

---

## 学习资源

- 📖 [Rust Book](https://doc.rust-lang.org/book/)
- 📚 [Rust by Example](https://doc.rust-lang.org/rust-by-example/)
- 🎓 [Rustlings](https://github.com/rust-lang/rustlings)
- 💬 [Rust 官方论坛](https://users.rust-lang.org/)
- 💭 [Rust Reddit](https://www.reddit.com/r/rust/)

---

## 进度追踪

使用这个检查清单追踪学习进度：

### 初学者

- [ ] 序列化 (serde)
- [ ] 错误处理 (anyhow/thiserror)
- [ ] CLI 工具 (clap)
- [ ] 日志 (log/tracing)

### 进阶

- [ ] 异步编程 (tokio)
- [ ] Web 框架 (axum)
- [ ] 数据库 (sqlx)
- [ ] HTTP 客户端 (reqwest)

### 专家

- [ ] 消息队列 (rdkafka/lapin)
- [ ] gRPC (tonic)
- [ ] 性能优化 (criterion)
- [ ] 领域专精 (选择一个方向)
