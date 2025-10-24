# C13 可靠性框架: 主索引 (Master Index)

> **文档定位**: 可靠性框架学习路径总导航，涵盖容错、分布式、微服务等  
> **使用方式**: 作为学习起点，根据需求选择合适的可靠性模式  
> **相关文档**: [README](../README.md) | [快速开始](../QUICK_START.md)


## 📊 目录

- [📋 快速导航](#快速导航)
  - [🎯 按角色导航](#按角色导航)
- [🗂️ 文档结构](#️-文档结构)
  - [📖 用户指南 (guides/)](#用户指南-guides)
  - [🏗️ 架构设计 (architecture/)](#️-架构设计-architecture)
  - [🔌 API 文档 (api/)](#api-文档-api)
  - [⚡ 功能文档 (features/)](#功能文档-features)
  - [🔬 高级主题 (advanced/)](#高级主题-advanced)
  - [📚 参考资料 (reference/)](#参考资料-reference)
  - [📦 历史归档 (archives/)](#历史归档-archives)
- [🚀 学习路径](#学习路径)
  - [初学者路径 (1周)](#初学者路径-1周)
  - [中级路径 (2-3周)](#中级路径-2-3周)
  - [高级路径 (4周+)](#高级路径-4周)
- [🎯 按场景导航](#按场景导航)
  - [场景一：高可用系统](#场景一高可用系统)
  - [场景二：分布式系统](#场景二分布式系统)
  - [场景三：微服务架构](#场景三微服务架构)
  - [场景四：高并发系统](#场景四高并发系统)
- [📊 项目统计](#项目统计)
- [🔗 外部资源](#外部资源)
  - [代码仓库](#代码仓库)
  - [相关项目](#相关项目)
- [🆕 最近更新](#最近更新)
  - [2025-10-19](#2025-10-19)
  - [2025-10-12](#2025-10-12)
  - [2025-10-04](#2025-10-04)
  - [2025-10-03](#2025-10-03)
- [📞 获取帮助](#获取帮助)


**最后更新**: 2025-10-19  
**适用版本**: Rust 1.90+  
**文档类型**: 📚 导航索引

---

## 📋 快速导航

### 🎯 按角色导航

| 角色 | 推荐路径 | 关键文档 |
|------|---------|---------|
| **初学者** | [README](../README.md) → [快速开始](../QUICK_START.md) → 熔断器 | 基础模式 |
| **中级开发者** | 分布式系统 → 微服务 → 可观测性 | 生产实践 |
| **架构师** | 架构设计 → 性能优化 → 容量规划 | 架构决策 |
| **研究者** | 形式化验证 → 算法分类 → 理论分析 | 学术研究 |

---

## 🗂️ 文档结构

### 📖 用户指南 (guides/)

完整的使用指南和最佳实践：

- **[指南总览](guides/README.md)** - 用户指南索引
- **[快速开始](../QUICK_START.md)** - 5分钟快速上手
- **[使用指南](guides/usage-guide.md)** - 详细使用说明
- **[最佳实践](guides/best-practices.md)** - 生产环境最佳实践
- **[综合指南](guides/comprehensive-guide.md)** - 完整功能介绍

**适用人群**: 初学者、中级开发者  
**推荐起点**: 快速开始 → 使用指南 → 最佳实践

---

### 🏗️ 架构设计 (architecture/)

框架架构设计与决策文档：

- **[架构总览](architecture/README.md)** - 架构文档索引
- **[整体架构](../ARCHITECTURE.md)** - 分层架构、核心模块、运行时环境
- **[架构概览](architecture/overview.md)** - 详细的架构说明
- **[架构决策](architecture/decisions.md)** - 12个ADR文档
- **[实施路线图](architecture/implementation-roadmap.md)** - 实施计划

**适用人群**: 架构师、高级开发者  
**核心亮点**: 支持13种运行时环境、模块化设计、统一抽象

---

### 🔌 API 文档 (api/)

完整的 API 参考文档：

- **[API总览](api/README.md)** - API文档索引
- **[API参考手册](api/reference.md)** - 所有公共接口、函数签名、使用示例

**适用人群**: 所有开发者  
**主要模块**: 容错机制、分布式系统、并发模型、微服务、可观测性

---

### ⚡ 功能文档 (features/)

各功能模块的详细文档：

- **[功能总览](features/README.md)** - 功能模块索引
- **[容错机制](features/fault-tolerance.md)** - 熔断器、限流器、重试等
- **[分布式系统](features/distributed-systems.md)** - Raft、分布式事务、一致性哈希
- **[并发模型](features/concurrency-models.md)** - Actor、CSP、STM、Fork-Join
- **[微服务架构](features/microservices.md)** - 服务发现、API网关、负载均衡

**适用人群**: 所有开发者  
**完成度**: 容错(100%)、分布式(100%)、并发(100%)、微服务(80%)

---

### 🔬 高级主题 (advanced/)

深入的高级主题与研究：

- **[高级主题总览](advanced/README.md)** - 高级文档索引
- **[运行时环境](advanced/runtime-environments/)** - 13种运行时环境支持
  - [环境总览](advanced/runtime-environments/overview.md)
  - [环境分类](advanced/runtime-environments/taxonomy.md)
  - [实现细节](advanced/runtime-environments/implementation.md)
  - [能力矩阵](advanced/runtime-environments/capabilities-matrix.md)
- **[算法分类](advanced/algorithm-taxonomy.md)** - 完整的算法分类体系
- **[Rust 1.90 特性](advanced/rust-190-features.md)** - 最新Rust特性应用
- **[高级特性总结](advanced/features-summary.md)** - 高级功能概览

**适用人群**: 高级开发者、架构师、研究者  
**核心主题**: 运行时环境适配、算法分类、形式化验证

---

### 📚 参考资料 (reference/)

常见问题、术语表和统计信息：

- **[参考资料总览](reference/README.md)** - 参考资料索引
- **[FAQ](reference/FAQ.md)** - 常见问题解答
- **[术语表](reference/Glossary.md)** - 专业术语词汇表
- **[代码统计](reference/code-statistics.md)** - 项目代码统计

**适用人群**: 所有用户  
**使用场景**: 快速查找、概念理解、问题解答

---

### 📦 历史归档 (archives/)

项目历史文档归档：

- **[归档总览](archives/README.md)** - 历史文档索引
- **进度报告** - `archives/progress-reports/`
  - 2025-10-03 进度报告
  - 2025-10-04 进度报告
  - 2025-10-12 进度报告
- **完成报告** - `archives/completion-reports/`
- **里程碑记录** - `archives/milestones-*.md`

**适用人群**: 项目维护者  
**用途**: 历史追溯、学习项目演进

---

## 🚀 学习路径

### 初学者路径 (1周)

1. **第1天**: [README](../README.md) - 了解项目
2. **第2天**: [快速开始](../QUICK_START.md) - 运行示例
3. **第3-4天**: [容错机制](features/fault-tolerance.md) - 学习熔断器、限流器
4. **第5-7天**: [使用指南](guides/usage-guide.md) - 深入学习

**目标**: 能够使用基础容错功能

### 中级路径 (2-3周)

1. **第1周**: [分布式系统](features/distributed-systems.md) - Raft、分布式事务
2. **第2周**: [微服务架构](features/microservices.md) - 服务发现、API网关
3. **第3周**: [最佳实践](guides/best-practices.md) - 生产环境实践

**目标**: 能够构建分布式微服务应用

### 高级路径 (4周+)

1. **第1-2周**: [架构设计](architecture/) - 深入理解架构
2. **第3周**: [运行时环境](advanced/runtime-environments/) - 环境适配
3. **第4周**: [算法分类](advanced/algorithm-taxonomy.md) - 算法理论
4. **持续**: [架构决策](architecture/decisions.md) - 学习设计思想

**目标**: 能够进行架构设计和扩展开发

---

## 🎯 按场景导航

### 场景一：高可用系统

**需求**: 防止级联故障、控制流量、提高可用性

**推荐方案**:

- [熔断器](features/fault-tolerance.md#熔断器) - 故障隔离
- [限流器](features/fault-tolerance.md#限流器) - 流量控制
- [重试策略](features/fault-tolerance.md#重试策略) - 提高成功率

**相关文档**:

- [容错机制最佳实践](guides/best-practices.md#容错机制)
- [熔断器示例](../examples/circuit_breaker_example.rs)

---

### 场景二：分布式系统

**需求**: 数据一致性、分布式协调、跨服务事务

**推荐方案**:

- [Raft共识](features/distributed-systems.md#raft) - 数据一致性
- [分布式事务](features/distributed-systems.md#分布式事务) - 跨服务事务
- [一致性哈希](features/distributed-systems.md#一致性哈希) - 负载均衡
- [分布式锁](features/distributed-systems.md#分布式锁) - 资源协调

**相关文档**:

- [分布式系统最佳实践](guides/best-practices.md#分布式系统)
- [分布式系统示例](../examples/distributed_systems_example.rs)

---

### 场景三：微服务架构

**需求**: 服务治理、API网关、配置管理、调用链追踪

**推荐方案**:

- [服务发现](features/microservices.md#服务发现) - 服务注册与发现
- [API网关](features/microservices.md#api网关) - 统一入口
- [负载均衡](features/microservices.md#负载均衡) - 请求分发
- [配置中心](features/microservices.md#配置中心) - 配置管理
- [分布式追踪](features/microservices.md#分布式追踪) - 调用链追踪

**相关文档**:

- [微服务最佳实践](guides/best-practices.md#微服务)
- [微服务示例](../examples/microservices_example.rs)

---

### 场景四：高并发系统

**需求**: 高效并发处理、消息传递、并发控制

**推荐方案**:

- [Actor模型](features/concurrency-models.md#actor模型) - 消息传递并发
- [CSP模型](features/concurrency-models.md#csp模型) - Channel通信
- [限流器](features/fault-tolerance.md#限流器) - 流量控制
- [负载均衡](features/microservices.md#负载均衡) - 请求分发

**相关文档**:

- [并发模型最佳实践](guides/best-practices.md#并发控制)
- [并发示例](../examples/concurrency_example.rs)

---

## 📊 项目统计

- **代码量**: ~23,650 行生产级代码
- **模块数**: 9 个主要模块
- **测试用例**: 80+ 测试
- **运行时环境**: 支持 13 种
- **完成度**: 91%
- **Rust 版本**: 1.90+

详见：[代码统计](reference/code-statistics.md)

---

## 🔗 外部资源

### 代码仓库

- [GitHub](https://github.com/yourusername/c13_reliability)
- [示例代码](../examples/)
- [测试用例](../tests/)
- [基准测试](../benches/)

### 相关项目

- [Tokio](https://tokio.rs/) - 异步运行时
- [Rust](https://www.rust-lang.org/) - Rust 语言
- [Cargo](https://doc.rust-lang.org/cargo/) - Rust 包管理器

---

## 🆕 最近更新

### 2025-10-19

- ✅ 完成文档结构重组
- ✅ 创建目录化文档体系
- ✅ 新增各目录 README
- ✅ 归档历史文档
- ✅ 更新主索引

### 2025-10-12

- ✅ 文档完善
- ✅ 功能优化

### 2025-10-04

- ✅ 测试完善
- ✅ Bug修复
- ✅ 编译成功

### 2025-10-03

- ✅ 分布式系统完成
- ✅ 并发模型实现

---

## 📞 获取帮助

- **文档问题** → [FAQ](reference/FAQ.md)
- **概念理解** → [术语表](reference/Glossary.md)
- **使用问题** → [使用指南](guides/usage-guide.md)
- **代码问题** → [示例代码](../examples/)
- **Bug报告** → [GitHub Issues](https://github.com/yourusername/c13_reliability/issues)

---

**文档维护**: Rust 学习社区  
**文档版本**: v2.0  
**最后梳理**: 2025-10-19  
**Rust 版本**: 1.90+
