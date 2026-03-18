# 供应链安全指南

## 概述

本文档提供Rust项目的供应链安全管理策略，确保依赖项的可信度和完整性。

---

## 1. 供应链风险模型

### 1.1 风险分类

```
供应链风险:

源代码风险:
├── 恶意代码注入
├── 后门植入
├── 漏洞引入
└── 许可证违规

分发风险:
├── 包篡改
├── 元数据伪造
├── 中间人攻击
└── 镜像污染

维护风险:
├── 维护者变更
├── 项目废弃
├── 所有权转移
└── 政治影响
```

### 1.2 Rust特定风险

| 风险 | 严重性 | 可能性 | 缓解措施 |
|------|--------|--------|----------|
| **构建脚本攻击** | 高 | 中 | 审查build.rs |
| **过程宏风险** | 高 | 中 | 审计proc-macro |
| **依赖混淆** | 中 | 低 | 明确版本 |
| **typosquatting** | 中 | 中 | 拼写检查 |

---

## 2. 依赖管理策略

### 2.1 依赖选择标准

```rust
/// 依赖评估检查表
pub struct DependencyCriteria {
    /// 维护活跃度
    pub last_update_days: u32,
    /// 发布频率
    pub release_frequency: ReleaseFrequency,
    /// 贡献者数量
    pub contributor_count: u32,
    /// 安全历史
    pub security_incidents: u32,
    /// 许可证
    pub license: License,
    /// 代码质量
    pub code_quality_score: u8,
}

impl DependencyCriteria {
    pub fn is_acceptable(&self) -> bool {
        self.last_update_days < 365 &&
        self.security_incidents == 0 &&
        self.contributor_count >= 2 &&
        self.code_quality_score >= 70
    }
}
```

### 2.2 最小依赖原则

```toml
# Cargo.toml - 精简依赖示例
[package]
name = "safety-critical-module"
version = "1.0.0"
edition = "2021"

[dependencies]
# 只使用必要的依赖
# 优先选择标准库或no_std兼容库

cortex-m = { version = "0.7", optional = true }
heapless = "0.7"  # 无分配集合

[dev-dependencies]
# 开发依赖不包含在发布中

[features]
default = []
std = []
embedded = ["cortex-m"]
```

---

## 3. 安全构建流程

### 3.1 可重现构建

```toml
# Cargo.toml
[profile.release]
opt-level = 3
lto = true
codegen-units = 1
strip = false  # 保留符号用于验证

# rust-toolchain.toml
[toolchain]
channel = "1.81.0"
components = ["rust-src"]
profile = "minimal"
```

### 3.2 构建环境锁定

```dockerfile
# Dockerfile - 锁定构建环境
FROM rust:1.81.0-slim

# 锁定工具版本
RUN rustup component add rust-src clippy rustfmt

# 复制Cargo.lock确保依赖一致
COPY Cargo.lock Cargo.lock
COPY Cargo.toml Cargo.toml

# 构建
RUN cargo build --release --locked

# 验证构建产物
RUN sha256sum target/release/my-binary > checksum.txt
```

---

## 4. 依赖验证

### 4.1 校验和验证

```bash
# 验证Cargo.lock完整性
cargo checksum

# 比较依赖树
cargo tree --duplicate

# 验证下载的crate
cargo fetch --locked
find ~/.cargo/registry/cache -name "*.crate" -exec sha256sum {} \;
```

### 4.2 源码审查清单

```
新依赖审查检查表:

基本信息:
□ 项目主页可访问
□ 源代码仓库公开
□ 有明确的维护者
□ 有CHANGELOG
□ 版本标签存在

代码质量:
□ 有测试套件
□ CI配置存在
□ 代码风格一致
□ 文档完整
□ 无unsafe或已审查

安全考虑:
□ 无已公开漏洞
□ 构建脚本审查
□ 过程宏审查
□ 依赖树合理
□ 许可证兼容
```

---

## 5. 私有Registry

### 5.1 搭建私有Registry

```bash
# 使用crates.io-index或自建
# 方案1: 使用Git作为registry

# 创建registry索引
git init --bare my-registry-index.git

# 配置Cargo使用私有registry
# ~/.cargo/config.toml
[registries]
my-company = { index = "https://git.company.com/my-registry-index" }

# 发布到私有registry
cargo publish --registry my-company
```

### 5.2 镜像配置

```toml
# ~/.cargo/config.toml
[registries.crates-io]
protocol = "sparse"

[net]
retry = 3                   # 重试次数
git-fetch-with-cli = true  # 使用系统git

[source.crates-io]
# 使用国内镜像
replace-with = 'ustc'

[source.ustc]
registry = "sparse+https://mirrors.ustc.edu.cn/crates.io-index/"
```

---

## 6. 安全更新管理

### 6.1 更新策略

```
更新分类:

安全更新 (24小时内):
├── 关键漏洞修复
├── 依赖项安全补丁
└── 工具链安全更新

功能更新 (1周内):
├── 新功能
├── 性能改进
└── API变更

维护更新 (1月内):
├── 文档更新
├── 测试改进
└── 代码清理
```

### 6.2 自动化更新流程

```yaml
# .github/workflows/dependency-update.yml
name: Dependency Update

on:
  schedule:
    - cron: '0 0 * * 1'  # 每周一

jobs:
  update:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Check for updates
        run: |
          cargo install cargo-outdated
          cargo outdated -R --format json > outdated.json

      - name: Create update PR
        uses: peter-evans/create-pull-request@v5
        with:
          title: ' chore: Update dependencies'
          body: |
            Automated dependency update

            Security updates: ${{ steps.check.outputs.security }}
            Major updates: ${{ steps.check.outputs.major }}
            Minor updates: ${{ steps.check.outputs.minor }}
          branch: dependency-updates
```

---

## 7. 事件响应

### 7.1 漏洞响应流程

```
发现漏洞:
    │
    ├── 确认影响
    │   ├── 检查是否使用受影响的crate
    │   ├── 评估影响范围
    │   └── 确定严重性
    │
    ├── 立即缓解
    │   ├── 升级依赖
    │   ├── 应用补丁
    │   └── 暂时禁用功能
    │
    ├── 修复验证
    │   ├── 测试修复
    │   ├── 验证漏洞关闭
    │   └── 回归测试
    │
    └── 事后分析
        ├── 根因分析
        ├── 流程改进
        └── 文档更新
```

### 7.2 应急响应检查表

```
应急响应:

立即 (1小时内):
□ 确认漏洞影响
□ 通知相关团队
□ 评估数据泄露风险
□ 启动应急响应团队

短期 (24小时内):
□ 实施临时缓解措施
□ 准备修复补丁
□ 通知客户/用户
□ 监控异常活动

中期 (1周内):
□ 部署永久修复
□ 完整安全审计
□ 更新安全策略
□ 培训相关人员

长期 (1月内):
□ 事后分析
□ 流程改进
□ 工具升级
□ 演练验证
```

---

**文档版本**: 1.0
**最后更新**: 2026-03-18

---

*供应链安全是现代软件开发的关键组成部分。*
