# 开发与贡献指南

> **参与项目开发**，了解开发流程、代码规范和贡献方式

**最后更新**: 2025-10-19  
**适用版本**: Rust 1.90+

---

## 📋 目录

- [开发与贡献指南](#开发与贡献指南)
  - [📋 目录](#-目录)
  - [📋 概述](#-概述)
  - [📚 文档列表](#-文档列表)
    - [1. 贡献指南](#1-贡献指南)
  - [🚀 快速开始](#-快速开始)
    - [环境准备](#环境准备)
    - [获取代码](#获取代码)
    - [本地开发](#本地开发)
  - [📖 开发流程](#-开发流程)
    - [1. Fork 和克隆](#1-fork-和克隆)
    - [2. 创建分支](#2-创建分支)
    - [3. 开发和测试](#3-开发和测试)
    - [4. 提交变更](#4-提交变更)
    - [5. 创建 Pull Request](#5-创建-pull-request)
  - [📝 代码规范](#-代码规范)
    - [Rust 风格](#rust-风格)
    - [命名约定](#命名约定)
    - [文档要求](#文档要求)
    - [测试要求](#测试要求)
  - [🏗️ 架构与模块](#️-架构与模块)
    - [项目结构](#项目结构)
    - [模块职责](#模块职责)
    - [依赖管理](#依赖管理)
  - [✅ 质量保证](#-质量保证)
    - [代码检查](#代码检查)
    - [测试覆盖](#测试覆盖)
    - [性能基准](#性能基准)
  - [📋 提交规范](#-提交规范)
    - [提交消息格式](#提交消息格式)
    - [提交最佳实践](#提交最佳实践)
  - [🎯 贡献方式](#-贡献方式)
    - [代码贡献](#代码贡献)
    - [文档贡献](#文档贡献)
    - [测试贡献](#测试贡献)
    - [其他贡献](#其他贡献)
  - [💡 开发建议](#-开发建议)
    - [最佳实践](#最佳实践)
    - [避免的陷阱](#避免的陷阱)
    - [沟通渠道](#沟通渠道)
  - [🔗 相关资源](#-相关资源)
    - [项目文档](#项目文档)
    - [外部资源](#外部资源)
    - [工具文档](#工具文档)

---

## 📋 概述

本目录包含项目开发的所有相关信息，包括开发环境配置、代码规范、贡献流程等。

---

## 📚 文档列表

### 1. [贡献指南](./contributing.md)

**内容概要**:

- 详细的贡献流程
- 代码审查标准
- 社区行为准则
- 问题报告指南

**适合人群**: 所有贡献者

---

## 🚀 快速开始

### 环境准备

**必需工具**:

```bash
# Rust 1.90+
rustup update stable
rustc --version

# 格式化工具
rustup component add rustfmt

# 代码检查工具
rustup component add clippy
```

**推荐工具**:

```bash
# 代码覆盖率
cargo install cargo-tarpaulin

# 基准测试
cargo install cargo-criterion

# 文档生成
cargo install mdbook
```

### 获取代码

```bash
# Fork 项目到你的 GitHub 账户，然后克隆
git clone https://github.com/YOUR_USERNAME/rust-lang.git
cd rust-lang/crates/c12_model

# 添加上游仓库
git remote add upstream https://github.com/rust-lang/rust-lang.git
```

### 本地开发

```bash
# 构建项目
cargo build

# 运行测试
cargo test

# 运行特定测试
cargo test --test integration_tests

# 格式化代码
cargo fmt

# 检查代码
cargo clippy -- -D warnings

# 生成文档
cargo doc --open
```

---

## 📖 开发流程

### 1. Fork 和克隆

1. 在 GitHub 上 Fork 项目
2. 克隆你的 Fork
3. 添加上游仓库

### 2. 创建分支

```bash
# 同步主分支
git checkout main
git pull upstream main

# 创建功能分支
git checkout -b feature/your-feature-name
```

**分支命名规范**:

- `feature/xxx` - 新功能
- `fix/xxx` - Bug 修复
- `docs/xxx` - 文档更新
- `refactor/xxx` - 代码重构
- `test/xxx` - 测试改进

### 3. 开发和测试

```bash
# 编写代码...

# 运行测试
cargo test

# 运行格式化
cargo fmt

# 运行 Clippy
cargo clippy

# 构建文档
cargo doc
```

### 4. 提交变更

```bash
# 添加文件
git add .

# 提交（遵循提交规范）
git commit -m "feat: add new feature"

# 推送到你的 Fork
git push origin feature/your-feature-name
```

### 5. 创建 Pull Request

1. 访问 GitHub 仓库
2. 点击 "New Pull Request"
3. 选择你的分支
4. 填写 PR 描述
5. 等待代码审查

---

## 📝 代码规范

### Rust 风格

遵循 [Rust 官方风格指南](https://doc.rust-lang.org/1.0.0/style/):

- 使用 4 空格缩进
- 每行最多 100 字符
- 使用 `snake_case` 命名函数和变量
- 使用 `PascalCase` 命名类型和 trait
- 使用 `SCREAMING_SNAKE_CASE` 命名常量

**自动化**:

```bash
# 格式化所有代码
cargo fmt --all

# 检查格式
cargo fmt --all -- --check
```

### 命名约定

**模块命名**:

- `core/` - 核心数据结构和 trait
- `models/` - 具体模型实现
- `utils/` - 工具函数
- `error/` - 错误类型

**类型命名**:

```rust
// ✅ 好的命名
pub struct MM1Queue { ... }
pub trait ModelValidator { ... }
pub enum ErrorKind { ... }

// ❌ 不好的命名
pub struct mm1queue { ... }
pub trait validator { ... }
pub enum err { ... }
```

### 文档要求

**公共 API 必须有文档**:

```rust
/// M/M/1 排队系统模型
///
/// # 参数
/// - `arrival_rate` - 到达率 (λ)
/// - `service_rate` - 服务率 (μ)
///
/// # 示例
///
/// ```
/// use c12_model::MM1Queue;
///
/// let queue = MM1Queue::new(1.0, 2.0);
/// assert_eq!(queue.utilization(), 0.5);
/// ```
///
/// # 错误
///
/// 如果 `arrival_rate >= service_rate`，返回错误。
pub struct MM1Queue {
    arrival_rate: f64,
    service_rate: f64,
}
```

**文档检查**:

```bash
cargo doc --all --no-deps
```

### 测试要求

**每个公共函数都应该有测试**:

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mm1_queue_utilization() {
        let queue = MM1Queue::new(1.0, 2.0);
        assert_eq!(queue.utilization(), 0.5);
    }

    #[test]
    #[should_panic(expected = "Invalid parameters")]
    fn test_mm1_queue_invalid_params() {
        MM1Queue::new(2.0, 1.0);
    }
}
```

**运行测试**:

```bash
# 所有测试
cargo test --all

# 单个包测试
cargo test -p c12_model

# 带输出
cargo test -- --nocapture

# 测试覆盖率
cargo tarpaulin --out Html
```

---

## 🏗️ 架构与模块

### 项目结构

```text
c12_model/
├── src/
│   ├── lib.rs           # 库入口
│   ├── core/            # 核心模块
│   ├── concurrency/     # 并发模型
│   ├── distributed/     # 分布式模型
│   ├── architecture/    # 架构模式
│   ├── formal/          # 形式化方法
│   ├── error.rs         # 错误类型
│   └── utils.rs         # 工具函数
├── examples/            # 示例代码
├── tests/               # 集成测试
├── benches/             # 性能基准
└── docs/                # 文档
```

### 模块职责

**核心模型层**:

- 形式化模型
- 排队论模型
- 机器学习模型
- 领域模型

**基础设施层**:

- 配置管理
- 错误处理
- 日志追踪
- 性能监控

**适配层**:

- 示例代码
- 使用指南
- 外部集成

**设计原则**:

- ✅ 自底向上依赖
- ✅ 禁止跨层循环依赖
- ✅ 公共类型稳定
- ✅ 内部实现可演进

详见 [架构文档](../architecture/README.md)

### 依赖管理

**添加依赖**:

```toml
[dependencies]
# 仅添加必需的依赖
tokio = { version = "1", features = ["rt", "sync"] }

[dev-dependencies]
# 测试依赖
criterion = "0.5"
```

**依赖原则**:

- 最小化外部依赖
- 优先使用标准库
- 明确标注特性
- 定期更新依赖

---

## ✅ 质量保证

### 代码检查

**Clippy 检查**:

```bash
# 标准检查
cargo clippy

# 严格检查
cargo clippy -- -D warnings

# 所有 target
cargo clippy --all-targets --all-features
```

**常见 Clippy 配置** (`clippy.toml`):

```toml
# 允许的 lint
allow = [
    "clippy::module_inception",
]

# 警告的 lint
warn = [
    "clippy::all",
]

# 禁止的 lint
deny = [
    "clippy::correctness",
]
```

### 测试覆盖

**目标**: 保持 85%+ 的测试覆盖率

```bash
# 生成覆盖率报告
cargo tarpaulin --out Html --output-dir coverage

# 查看报告
open coverage/index.html
```

**测试类型**:

- 单元测试 - `#[test]`
- 集成测试 - `tests/`
- 文档测试 - 文档中的示例
- 基准测试 - `benches/`

### 性能基准

```bash
# 运行基准测试
cargo bench

# 特定基准
cargo bench --bench my_benchmark

# 生成报告
cargo criterion
```

---

## 📋 提交规范

### 提交消息格式

遵循 [Conventional Commits](https://www.conventionalcommits.org/):

```text
<类型>(<范围>): <简短描述>

<详细描述>

<Footer>
```

**类型**:

- `feat`: 新功能
- `fix`: Bug 修复
- `docs`: 文档更新
- `style`: 代码格式（不影响功能）
- `refactor`: 重构
- `perf`: 性能优化
- `test`: 测试相关
- `chore`: 构建/工具相关

**示例**:

```bash
feat(concurrency): add Actor model implementation

Implement basic Actor model with:
- Message passing
- State isolation
- Error handling

Closes #123
```

### 提交最佳实践

- ✅ 原子化提交 - 每个提交完成一个独立功能
- ✅ 清晰的描述 - 说明动机与影响范围
- ✅ 关联 Issue - 使用 `Closes #xxx`
- ✅ 测试通过 - 提交前确保测试通过
- ✅ 代码格式化 - 运行 `cargo fmt`

---

## 🎯 贡献方式

### 代码贡献

- 实现新模型和算法
- 修复 Bug
- 性能优化
- 代码重构

### 文档贡献

- 改进和补充文档
- 编写教程和指南
- 翻译文档
- 修复文档错误

### 测试贡献

- 增加测试用例
- 提高测试覆盖率
- 编写集成测试
- 性能基准测试

### 其他贡献

- 反馈建议
- 报告 Bug
- 参与讨论
- 帮助其他用户

---

## 💡 开发建议

### 最佳实践

- ✅ 阅读现有代码理解风格
- ✅ 从小的贡献开始
- ✅ 及时与维护者沟通
- ✅ 保持代码简洁清晰
- ✅ 编写完善的文档和测试

### 避免的陷阱

- ❌ 不遵循代码规范
- ❌ 提交未测试的代码
- ❌ 缺少文档说明
- ❌ 大规模重构没有讨论
- ❌ 忽略代码审查意见

### 沟通渠道

- **GitHub Issues** - Bug 报告和功能请求
- **GitHub Discussions** - 一般讨论和问答
- **Pull Requests** - 代码审查和讨论

---

## 🔗 相关资源

### 项目文档

- [项目概览](../OVERVIEW.md) - 项目介绍
- [架构设计](../architecture/README.md) - 架构文档
- [贡献指南](./contributing.md) - 详细贡献指南

### 外部资源

- [Rust 官方文档](https://doc.rust-lang.org/)
- [Rust API 指南](https://rust-lang.github.io/api-guidelines/)
- [Rust 风格指南](https://doc.rust-lang.org/1.0.0/style/)
- [Conventional Commits](https://www.conventionalcommits.org/)

### 工具文档

- [Cargo Book](https://doc.rust-lang.org/cargo/)
- [Clippy Lints](https://rust-lang.github.io/rust-clippy/)
- [rustfmt](https://github.com/rust-lang/rustfmt)

---

**开发指南维护**: 项目维护团队  
**最后更新**: 2025-10-19  
**反馈**: [GitHub Issues](https://github.com/rust-lang/rust-lang/issues)

---

**开始贡献**: 从小的改进开始，逐步参与项目开发！ 🚀
