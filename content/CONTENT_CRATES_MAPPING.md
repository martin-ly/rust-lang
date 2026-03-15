# Content 与 Crates 映射指南

> 连接前沿内容与核心学习模块

---

## 🗺️ 映射关系概览

```text
content/                    crates/
─────────                   ───────
emerging/        ────────▶  C04, C11
ecosystem/       ────────▶  C05, C06, C10
production/      ────────▶  C07, C12
academic/        ────────▶  C01, C04
scenarios/       ────────▶  C09, C10
representations/ ────────▶  (知识表示)
```

---

## 📂 详细映射

### content/emerging/ → C04 + C11

| Content 文档 | 关联 Crate | 说明 |
|--------------|------------|------|
| `rust_195_roadmap.md` | C04 泛型 | 新泛型特性预览 |
| `generic_const_items.md` | C04 泛型 | 泛型常量项目 |
| `async_closures.md` | C06 异步 | 异步闭包 |
| `coroutines.md` | C03 控制流 | 协程底层 |

**学习路径**:

1. 完成 C04 基础泛型
2. 学习 C11 宏系统
3. 阅读 content/emerging/
4. 尝试 nightly 特性

---

### content/ecosystem/ → C05 + C06 + C10

| Content 文档 | 关联 Crate | 说明 |
|--------------|------------|------|
| `web_frameworks/axum_deep_dive.md` | C10 网络 | Web 框架深入 |
| `databases/sqlx_guide.md` | C06 异步 | 数据库异步访问 |
| `async_runtimes/tokio_deep_dive.md` | C06 异步 | Tokio 深入 |
| `serialization/serde_guide.md` | C02 类型系统 | 序列化 |

**学习路径**:

1. 完成 C05 并发基础
2. 学习 C06 异步编程
3. 掌握 C10 网络基础
4. 阅读 content/ecosystem/
5. 构建实际项目

---

### content/production/ → C07 + C12

| Content 文档 | 关联 Crate | 说明 |
|--------------|------------|------|
| `kubernetes_deployment_guide.md` | C12 WASM | 容器化部署 |
| `monitoring_setup.md` | C06 异步 | 监控和日志 |
| `ci_cd_pipeline.md` | C07 进程 | 持续集成 |

**学习路径**:

1. 完成 C07 进程管理
2. 学习 C12 WASM 基础
3. 阅读 content/production/
4. 实践部署流程

---

### content/academic/ → C01 + C04

| Content 文档 | 关联 Crate | 说明 |
|--------------|------------|------|
| `rustbelt_formal_verification.md` | C01 所有权 | 形式化验证 |
| `tree_borrows_pldi_2025.md` | C01 所有权 | 借用检查器理论 |
| `coq_formalization_guide.md` | C04 泛型 | 类型理论 |

**学习路径**:

1. 深入理解 C01 所有权
2. 学习 C04 泛型理论
3. 阅读 content/academic/
4. 研究论文和形式化方法

---

### content/scenarios/ → C09 + C10

| Content 文档 | 关联 Crate | 说明 |
|--------------|------------|------|
| `web_application.md` | C10 网络 | Web 应用架构 |
| `distributed_system.md` | C06 异步 | 分布式系统 |
| `embedded_system.md` | C07 进程 | 嵌入式系统 |

**学习路径**:

1. 掌握 C09 设计模式
2. 学习 C10 网络编程
3. 阅读 content/scenarios/
4. 设计系统架构

---

## 🔗 实战项目映射

### 项目 1: Web 应用

**涉及内容**:

- crates: C04 + C06 + C09 + C10
- content: ecosystem/web_frameworks + scenarios/web_application

**实现步骤**:

1. C04 泛型 - 设计类型安全的 API
2. C06 异步 - 处理并发请求
3. C09 设计模式 - 使用 MVC/分层架构
4. C10 网络 - HTTP 服务
5. content - 部署到生产环境

### 项目 2: 分布式任务队列

**涉及内容**:

- crates: C05 + C06 + C07
- content: ecosystem/async_runtimes + production/monitoring

**实现步骤**:

1. C05 并发 - 线程池和任务调度
2. C06 异步 - 异步任务处理
3. C07 进程 - 进程间通信
4. content - 监控和日志

### 项目 3: WebAssembly 应用

**涉及内容**:

- crates: C04 + C12
- content: production/kubernetes_deployment

**实现步骤**:

1. C04 泛型 - 设计通用接口
2. C12 WASM - 浏览器端实现
3. content - 容器化部署

---

## 📚 推荐阅读顺序

### 基础阶段 (Week 1-3)

1. crates/C01 - 所有权
2. crates/C02 - 类型系统
3. crates/C03 - 控制流

### 进阶阶段 (Week 4-7)

1. crates/C04 - 泛型
2. crates/C05 - 并发
3. crates/C06 - 异步

### 实战阶段 (Week 8-12)

1. content/ecosystem/ - 生态库
2. crates/C09 - 设计模式
3. crates/C10 - 网络编程

### 生产阶段 (Week 13+)

1. content/production/ - 生产实践
2. crates/C07 - 进程管理
3. crates/C12 - WASM

### 深入研究 (持续)

1. content/academic/ - 学术前沿
2. content/emerging/ - 新特性

---

## 🎯 学习检查点

### 检查点 1: 基础掌握

- [ ] 能解释所有权、借用、生命周期
- [ ] 能使用基本类型和泛型
- [ ] 能编写控制流和模式匹配

### 检查点 2: 进阶技能

- [ ] 能实现 Trait 和泛型结构
- [ ] 能编写多线程程序
- [ ] 能使用 async/await

### 检查点 3: 实战能力

- [ ] 能使用生态库
- [ ] 能设计系统架构
- [ ] 能编写网络应用

### 检查点 4: 生产就绪

- [ ] 能部署到生产环境
- [ ] 能监控和调试
- [ ] 能优化性能

---

## 🔍 快速查找

### 按主题查找

| 主题 | Crates | Content |
|------|--------|---------|
| Web 开发 | C10, C12 | ecosystem/web_frameworks |
| 系统编程 | C05, C07 | production/ |
| 异步编程 | C06 | ecosystem/async_runtimes |
| 形式化方法 | C01, C04 | academic/ |
| 架构设计 | C09 | scenarios/ |

### 按难度查找

| 难度 | Crates | Content |
|------|--------|---------|
| 初级 | C01-C03 | - |
| 中级 | C04-C06 | ecosystem/ |
| 高级 | C07-C12 | production/ |
| 专家 | - | academic/, emerging/ |

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-03-15
**状态**: ✅ 100% 完成
