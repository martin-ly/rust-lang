# 📚 Rust学习项目文档索引


## 📊 目录

- [📚 Rust学习项目文档索引](#-rust学习项目文档索引)
  - [📊 目录](#-目录)
  - [📋 文档概述](#-文档概述)
  - [🎯 文档分类](#-文档分类)
    - [核心项目文档](#核心项目文档)
    - [学习资源文档](#学习资源文档)
    - [测试和质量文档](#测试和质量文档)
    - [项目管理和工具文档](#项目管理和工具文档)
    - [社区和资源文档](#社区和资源文档)
  - [📖 核心模块文档](#-核心模块文档)
    - [所有权和借用系统](#所有权和借用系统)
    - [类型系统](#类型系统)
    - [控制流和函数](#控制流和函数)
    - [泛型编程](#泛型编程)
    - [线程和并发](#线程和并发)
    - [异步编程](#异步编程)
    - [进程管理](#进程管理)
    - [算法和数据结构](#算法和数据结构)
    - [设计模式](#设计模式)
    - [网络编程](#网络编程)
    - [中间件](#中间件)
    - [数据模型](#数据模型)
    - [可靠性](#可靠性)
  - [🧪 测试文档](#-测试文档)
    - [测试框架](#测试框架)
    - [性能测试](#性能测试)
    - [文档测试](#文档测试)
    - [公共测试工具](#公共测试工具)
    - [基准测试](#基准测试)
  - [⚙️ 配置文件](#️-配置文件)
    - [Cargo配置](#cargo配置)
    - [CI/CD配置](#cicd配置)
  - [📊 项目管理文档](#-项目管理文档)
    - [项目治理](#项目治理)
    - [进度跟踪](#进度跟踪)
  - [🔧 工具和脚本](#-工具和脚本)
    - [质量检查脚本](#质量检查脚本)
  - [📈 报告和总结](#-报告和总结)
    - [项目报告](#项目报告)
    - [清理报告](#清理报告)
  - [🎓 学习路径](#-学习路径)
    - [初学者路径](#初学者路径)
    - [进阶路径](#进阶路径)
    - [高级路径](#高级路径)
  - [🔍 快速导航](#-快速导航)
    - [按主题查找](#按主题查找)
    - [按功能查找](#按功能查找)
    - [按模块查找](#按模块查找)
  - [📞 获取帮助](#-获取帮助)
    - [技术支持](#技术支持)
    - [学习支持](#学习支持)


**创建时间**: 2025年9月25日 14:25
**版本**: v1.0
**适用对象**: Rust学习者

---

## 📋 文档概述

本文档提供了Rust学习项目的完整文档索引，帮助学习者快速找到所需的学习资源、技术文档和实践指南。

---

## 🎯 文档分类

### 核心项目文档

- **[README.md](README.md)** - 项目主页和入门指南
- **[PROJECT_SCOPE.md](PROJECT_SCOPE.md)** - 项目范围和目标
- **[PROJECT_INDEX.md](PROJECT_INDEX.md)** - 项目导航索引
- **[TECHNICAL_STANDARDS.md](TECHNICAL_STANDARDS.md)** - 技术标准规范

### 学习资源文档

- **[LEARNING_GUIDE.md](LEARNING_GUIDE.md)** - 系统性学习指南（299行）
- **[RUST_BEST_PRACTICES.md](RUST_BEST_PRACTICES.md)** - 最佳实践指南（587行）
- **[PRACTICAL_EXAMPLES.md](PRACTICAL_EXAMPLES.md)** - 实用代码示例
- **[ADVANCED_RUST_GUIDE.md](ADVANCED_RUST_GUIDE.md)** - 高级学习指南（835行）

### 测试和质量文档

- **[TESTING_FRAMEWORK.md](TESTING_FRAMEWORK.md)** - 测试框架指南（651行）
- **[COMPREHENSIVE_TEST_SUITE.md](COMPREHENSIVE_TEST_SUITE.md)** - 综合测试套件
- **[PERFORMANCE_MONITORING_SYSTEM.md](PERFORMANCE_MONITORING_SYSTEM.md)** - 性能监控体系

### 项目管理和工具文档

- **[PROJECT_STRUCTURE_OPTIMIZATION.md](PROJECT_STRUCTURE_OPTIMIZATION.md)** - 结构优化指南（393行）
- **[EXAMPLE_PROJECTS.md](EXAMPLE_PROJECTS.md)** - 示例项目指南（333行）
- **[CI_CD_SETUP.md](CI_CD_SETUP.md)** - CI/CD设置指南（593行）

### 社区和资源文档

- **[COMMUNITY_TOOLS_AND_RESOURCES.md](COMMUNITY_TOOLS_AND_RESOURCES.md)** - 社区工具资源（331行）
- **[COMMUNITY_RESOURCES.md](COMMUNITY_RESOURCES.md)** - 社区资源

---

## 📖 核心模块文档

### 所有权和借用系统

- **[crates/c01_ownership_borrow_scope/README.md](crates/c01_ownership_borrow_scope/README.md)** - 所有权系统学习模块
- **理论基础**: 线性类型理论、生命周期理论、借用检查器理论
- **实践应用**: 所有权转移、借用模式、生命周期注解

### 类型系统

- **[crates/c02_type_system/README.md](crates/c02_type_system/README.md)** - 类型系统学习模块
- **核心特性**: 结构体、枚举、trait、泛型
- **高级特性**: GATs、Const Generics、类型别名

### 控制流和函数

- **[crates/c03_control_fn/README.md](crates/c03_control_fn/README.md)** - 控制流学习模块
- **基础控制流**: if/else、match、循环
- **函数编程**: 函数定义、闭包、迭代器

### 泛型编程

- **[crates/c04_generic/README.md](crates/c04_generic/README.md)** - 泛型编程学习模块
- **泛型基础**: 泛型函数、泛型结构体、泛型枚举
- **高级泛型**: trait bounds、关联类型、生命周期参数

### 线程和并发

- **[crates/c05_threads/README.md](crates/c05_threads/README.md)** - 线程编程学习模块
- **线程基础**: 线程创建、线程同步、线程安全
- **并发原语**: Mutex、RwLock、Channel

### 异步编程

- **[crates/c06_async/README.md](crates/c06_async/README.md)** - 异步编程学习模块
- **异步基础**: Future、async/await、Stream
- **异步运行时**: Tokio、异步任务、异步I/O

### 进程管理

- **[crates/c07_process/README.md](crates/c07_process/README.md)** - 进程管理学习模块
- **进程操作**: 进程创建、进程通信、信号处理
- **系统调用**: 文件系统、网络、系统信息

### 算法和数据结构

- **[crates/c08_algorithms/README.md](crates/c08_algorithms/README.md)** - 算法学习模块
- **基础算法**: 排序、搜索、图算法
- **数据结构**: 向量、哈希表、树结构

### 设计模式

- **[crates/c09_design_pattern/README.md](crates/c09_design_pattern/README.md)** - 设计模式学习模块
- **创建型模式**: 单例、工厂、建造者
- **结构型模式**: 适配器、装饰器、外观
- **行为型模式**: 观察者、策略、命令

### 网络编程

- **[crates/c10_networks/README.md](crates/c10_networks/README.md)** - 网络编程学习模块
- **网络基础**: TCP/UDP、HTTP、WebSocket
- **网络框架**: Axum、Actix-web、Tonic

### 中间件

- **[crates/c11_libraries/README.md](crates/c11_libraries/README.md)** - 中间件学习模块
- **Web中间件**: 认证、日志、缓存
- **系统中间件**: 消息队列、缓存系统

### 数据模型

- **[crates/c12_model/README.md](crates/c12_model/README.md)** - 数据模型学习模块
- **数据建模**: 实体关系、数据验证、序列化
- **数据库**: SQL、NoSQL、ORM

### 可靠性

- **[crates/c13_reliability/README.md](crates/c13_reliability/README.md)** - 可靠性学习模块
- **错误处理**: Result、Option、错误传播
- **测试策略**: 单元测试、集成测试、模糊测试

---

## 🧪 测试文档

### 测试框架

- **[tests/integration/](tests/integration/)** - 集成测试目录
  - `ownership_tests.rs` - 所有权系统集成测试
  - `type_system_tests.rs` - 类型系统集成测试
  - `control_flow_tests.rs` - 控制流集成测试
  - `generic_tests.rs` - 泛型集成测试
  - `async_tests.rs` - 异步编程集成测试
  - `cross_module_tests.rs` - 跨模块集成测试

### 性能测试

- **[tests/performance/](tests/performance/)** - 性能测试目录
  - `benchmarks.rs` - 性能基准测试
  - `memory_tests.rs` - 内存使用测试
  - `concurrency_tests.rs` - 并发性能测试

### 文档测试

- **[tests/documentation/](tests/documentation/)** - 文档测试目录
  - `examples_tests.rs` - 示例代码测试
  - `tutorial_tests.rs` - 教程代码测试

### 公共测试工具

- **[tests/common/](tests/common/)** - 公共测试工具目录
  - `mod.rs` - 测试工具模块
  - `fixtures.rs` - 测试夹具
  - `helpers.rs` - 测试辅助函数

### 基准测试

- **[benches/](benches/)** - 基准测试目录
  - `performance_benchmarks.rs` - 性能基准测试

---

## ⚙️ 配置文件

### Cargo配置

- **[Cargo.toml](Cargo.toml)** - 项目配置文件
- **[.cargo/config.toml](.cargo/config.toml)** - Cargo构建配置
- **[tarpaulin.toml](tarpaulin.toml)** - 代码覆盖率配置

### CI/CD配置

- **[.github/workflows/](.github/workflows/)** - GitHub Actions工作流
  - `ci.yml` - 持续集成工作流
  - `test.yml` - 测试工作流
  - `performance.yml` - 性能监控工作流

---

## 📊 项目管理文档

### 项目治理

- **[project-management/governance/PROJECT_GOVERNANCE.md](project-management/governance/PROJECT_GOVERNANCE.md)** - 项目治理框架
- **[project-management/quality/QUALITY_ASSURANCE_FRAMEWORK.md](project-management/quality/QUALITY_ASSURANCE_FRAMEWORK.md)** - 质量保证框架
- **[project-management/community/COMMUNITY_GUIDELINES.md](project-management/community/COMMUNITY_GUIDELINES.md)** - 社区参与指南

### 进度跟踪

- **[project-management/progress/](project-management/progress/)** - 进度跟踪目录
  - `weekly-report-2025-09-25.md` - 周进度报告
  - `progress-update-2025-09-25-13-16.md` - 进度更新

---

## 🔧 工具和脚本

### 质量检查脚本

- **[scripts/quality-check.sh](scripts/quality-check.sh)** - 代码质量检查脚本
- **[scripts/false-claims-cleanup.sh](scripts/false-claims-cleanup.sh)** - 虚假声明清理脚本
- **[scripts/cleanup-formal-rust.sh](scripts/cleanup-formal-rust.sh)** - formal_rust清理脚本

---

## 📈 报告和总结

### 项目报告

- **[COMPREHENSIVE_PROJECT_SUMMARY_2025_09_25.md](COMPREHENSIVE_PROJECT_SUMMARY_2025_09_25.md)** - 项目综合总结
- **[FINAL_ADVANCEMENT_SUMMARY_2025_09_25.md](FINAL_ADVANCEMENT_SUMMARY_2025_09_25.md)** - 推进总结报告
- **[ULTIMATE_COMPREHENSIVE_SUMMARY_2025_09_25.md](ULTIMATE_COMPREHENSIVE_SUMMARY_2025_09_25.md)** - 终极总结报告

### 清理报告

- **[PROJECT_CLEANUP_SUMMARY_2025_09_25.md](PROJECT_CLEANUP_SUMMARY_2025_09_25.md)** - 项目清理总结
- **[backup-20250925-130618/cleanup-report.md](backup-20250925-130618/cleanup-report.md)** - 清理报告

---

## 🎓 学习路径

### 初学者路径

1. **基础语法** → `crates/c03_control_fn/`
2. **所有权系统** → `crates/c01_ownership_borrow_scope/`
3. **类型系统** → `crates/c02_type_system/`
4. **泛型编程** → `crates/c04_generic/`

### 进阶路径

1. **线程编程** → `crates/c05_threads/`
2. **异步编程** → `crates/c06_async/`
3. **进程管理** → `crates/c07_process/`
4. **算法数据结构** → `crates/c08_algorithms/`

### 高级路径

1. **设计模式** → `crates/c09_design_pattern/`
2. **网络编程** → `crates/c10_networks/`
3. **中间件开发** → `crates/c11_libraries/`
4. **数据建模** → `crates/c12_model/`
5. **可靠性工程** → `crates/c13_reliability/`

---

## 🔍 快速导航

### 按主题查找

- **学习指南**: [LEARNING_GUIDE.md](LEARNING_GUIDE.md)
- **最佳实践**: [RUST_BEST_PRACTICES.md](RUST_BEST_PRACTICES.md)
- **代码示例**: [PRACTICAL_EXAMPLES.md](PRACTICAL_EXAMPLES.md)
- **高级特性**: [ADVANCED_RUST_GUIDE.md](ADVANCED_RUST_GUIDE.md)
- **测试框架**: [TESTING_FRAMEWORK.md](TESTING_FRAMEWORK.md)
- **性能监控**: [PERFORMANCE_MONITORING_SYSTEM.md](PERFORMANCE_MONITORING_SYSTEM.md)

### 按功能查找

- **项目入门**: [README.md](README.md) → [PROJECT_SCOPE.md](PROJECT_SCOPE.md)
- **技术标准**: [TECHNICAL_STANDARDS.md](TECHNICAL_STANDARDS.md)
- **社区资源**: [COMMUNITY_RESOURCES.md](COMMUNITY_RESOURCES.md)
- **CI/CD**: [CI_CD_SETUP.md](CI_CD_SETUP.md)
- **示例项目**: [EXAMPLE_PROJECTS.md](EXAMPLE_PROJECTS.md)

### 按模块查找

- **c01**: [crates/c01_ownership_borrow_scope/README.md](crates/c01_ownership_borrow_scope/README.md)
- **c02**: [crates/c02_type_system/README.md](crates/c02_type_system/README.md)
- **c03**: [crates/c03_control_fn/README.md](crates/c03_control_fn/README.md)
- **c04**: [crates/c04_generic/README.md](crates/c04_generic/README.md)
- **c05**: [crates/c05_threads/README.md](crates/c05_threads/README.md)
- **c06**: [crates/c06_async/README.md](crates/c06_async/README.md)
- **c07**: [crates/c07_process/README.md](crates/c07_process/README.md)
- **c08**: [crates/c08_algorithms/README.md](crates/c08_algorithms/README.md)
- **c09**: [crates/c09_design_pattern/README.md](crates/c09_design_pattern/README.md)
- **c10**: [crates/c10_networks/README.md](crates/c10_networks/README.md)
- **c11**: [crates/c11_libraries/README.md](crates/c11_libraries/README.md)
- **c12**: [crates/c12_model/README.md](crates/c12_model/README.md)
- **c13**: [crates/c13_reliability/README.md](crates/c13_reliability/README.md)

---

## 📞 获取帮助

### 技术支持

- **GitHub Issues**: 报告问题和功能请求
- **社区讨论**: 参与技术讨论
- **代码审查**: 请求代码审查和建议

### 学习支持

- **学习指南**: 遵循系统性学习路径
- **实践项目**: 完成示例项目练习
- **社区交流**: 参与社区学习和讨论

---

**文档索引状态**: ✅ 已完成
**最后更新**: 2025年9月25日 14:25
**适用版本**: Rust 1.70+

---

*本文档索引提供了完整的文档导航，帮助学习者快速找到所需的学习资源。如有任何问题或建议，欢迎反馈。*
