# 自动化（Automation）索引


## 📊 目录

- [目的](#目的)
- [核心自动化类型](#核心自动化类型)
  - [测试自动化](#测试自动化)
  - [构建自动化](#构建自动化)
  - [质量检查自动化](#质量检查自动化)
  - [监控自动化](#监控自动化)
- [自动化工具](#自动化工具)
  - [CI/CD 工具](#cicd-工具)
  - [测试工具](#测试工具)
  - [质量工具](#质量工具)
  - [监控工具](#监控工具)
- [实践与样例](#实践与样例)
  - [文件级清单（精选）](#文件级清单精选)
- [相关索引](#相关索引)
- [导航](#导航)


## 目的

- 介绍 Rust 项目的质量保障自动化工具和流程。
- 提供自动化测试、构建、部署和监控的指南。

## 核心自动化类型

### 测试自动化

- 单元测试自动化
- 集成测试自动化
- 端到端测试自动化
- 性能测试自动化

### 构建自动化

- 编译自动化
- 打包自动化
- 发布自动化
- 部署自动化

### 质量检查自动化

- 代码质量检查
- 安全扫描自动化
- 依赖检查自动化
- 文档生成自动化

### 监控自动化

- 性能监控自动化
- 错误监控自动化
- 日志监控自动化
- 告警自动化

## 自动化工具

### CI/CD 工具

- GitHub Actions
- GitLab CI
- Jenkins
- Azure DevOps

### 测试工具

- cargo test
- cargo-fuzz
- tarpaulin
- criterion

### 质量工具

- clippy
- rustfmt
- cargo-audit
- cargo-deny

### 监控工具

- Prometheus
- Grafana
- Jaeger
- ELK Stack

## 实践与样例

- 自动化：参见 [crates/c122_automation](../../../crates/c122_automation/)
- 测试自动化：[crates/c123_test_automation](../../../crates/c123_test_automation/)
- 构建自动化：[crates/c124_build_automation](../../../crates/c124_build_automation/)

### 文件级清单（精选）

- `crates/c122_automation/src/`：
  - `test_automation.rs`：测试自动化示例
  - `build_automation.rs`：构建自动化示例
  - `quality_automation.rs`：质量检查自动化示例
  - `monitoring_automation.rs`：监控自动化示例

## 相关索引

- 质量保障（指标）：[`../07_metrics/00_index.md`](../07_metrics/00_index.md)
- 质量保障（监控）：[`../09_monitoring/00_index.md`](../09_monitoring/00_index.md)
- 质量保障（改进）：[`../10_improvement/00_index.md`](../10_improvement/00_index.md)

## 导航

- 返回质量保障：[`../00_index.md`](../00_index.md)
- 标准：[`../01_standards/00_index.md`](../01_standards/00_index.md)
- 指南：[`../02_guidelines/00_index.md`](../02_guidelines/00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
