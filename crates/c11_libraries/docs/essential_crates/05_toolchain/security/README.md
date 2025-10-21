# 安全审计工具 (Security Audit Tools)

**类别**: 第5层 - 工具链  
**重要程度**: ⭐⭐⭐⭐  
**更新日期**: 2025-10-20

---

## 📋 目录

- [安全审计工具 (Security Audit Tools)](#安全审计工具-security-audit-tools)
  - [📋 目录](#-目录)
  - [📋 概述](#-概述)
  - [🔧 核心工具](#-核心工具)
    - [1. cargo-audit (必备 ⭐⭐⭐⭐⭐)](#1-cargo-audit-必备-)
      - [基础用法](#基础用法)
      - [audit.toml 配置](#audittoml-配置)
      - [CI 集成](#ci-集成)
      - [漏洞示例](#漏洞示例)
    - [2. cargo-deny (强烈推荐 🌟)](#2-cargo-deny-强烈推荐-)
      - [基础用法1](#基础用法1)
      - [deny.toml 配置](#denytoml-配置)
    - [3. cargo-geiger (可选)](#3-cargo-geiger-可选)
      - [基础用法3](#基础用法3)
      - [输出示例](#输出示例)
    - [4. cargo-outdated (可选)](#4-cargo-outdated-可选)
    - [5. cargo-license (可选)](#5-cargo-license-可选)
  - [💡 最佳实践](#-最佳实践)
    - [1. 安全工作流](#1-安全工作流)
    - [2. CI/CD 集成](#2-cicd-集成)
    - [3. Pre-commit Hook](#3-pre-commit-hook)
  - [📊 安全策略](#-安全策略)
    - [依赖安全等级](#依赖安全等级)
    - [许可证策略](#许可证策略)
  - [🎯 实战场景](#-实战场景)
    - [场景1: 发现漏洞后的处理](#场景1-发现漏洞后的处理)
    - [场景2: 许可证审查](#场景2-许可证审查)
    - [场景3: 减少 unsafe 代码](#场景3-减少-unsafe-代码)
  - [🔗 相关资源](#-相关资源)

## 📋 概述

安全是软件开发的首要任务。Rust 生态提供了多种工具来审计依赖、检查漏洞、验证许可证合规性。

---

## 🔧 核心工具

### 1. cargo-audit (必备 ⭐⭐⭐⭐⭐)

**安装**: `cargo install cargo-audit`  
**用途**: 检查依赖中的已知安全漏洞

#### 基础用法

```bash
# 审计依赖
cargo audit

# JSON 输出
cargo audit --json

# 忽略特定漏洞
cargo audit --ignore RUSTSEC-2021-0001

# 更新漏洞数据库
cargo audit fetch
```

#### audit.toml 配置

```toml
# .cargo/audit.toml
[advisories]
ignore = [
    "RUSTSEC-2021-0001",  # 已知且可接受的风险
]

[database]
path = "~/.cargo/advisory-db"
url = "https://github.com/RustSec/advisory-db.git"

[output]
format = "json"  # or "table"
quiet = false
```

#### CI 集成

```yaml
# .github/workflows/security.yml
name: Security Audit

on:
  push:
    paths:
      - 'Cargo.lock'
  schedule:
    - cron: '0 0 * * *'  # 每天检查

jobs:
  security_audit:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      
      - name: Install cargo-audit
        run: cargo install cargo-audit
      
      - name: Run audit
        run: cargo audit
```

#### 漏洞示例

```text
error: Vulnerable crates found!

ID:       RUSTSEC-2021-0001
Crate:    time
Version:  0.1.45
Date:     2021-01-20
URL:      https://rustsec.org/advisories/RUSTSEC-2021-0001
Title:    Undefined behavior in time crate
Solution:  Upgrade to >= 0.2.23

1 vulnerability found!
```

---

### 2. cargo-deny (强烈推荐 🌟)

**安装**: `cargo install cargo-deny`  
**用途**: 多维度依赖检查（许可证、ban、审计、来源）

#### 基础用法1

```bash
# 初始化配置
cargo deny init

# 检查所有规则
cargo deny check

# 只检查许可证
cargo deny check licenses

# 只检查 ban
cargo deny check bans

# 只检查安全漏洞
cargo deny check advisories

# 只检查来源
cargo deny check sources
```

#### deny.toml 配置

```toml
# deny.toml

# 许可证检查
[licenses]
# 许可证列表
allow = [
    "MIT",
    "Apache-2.0",
    "BSD-3-Clause",
]

deny = [
    "GPL-3.0",
]

# 需要确认的许可证
copyleft = "warn"

# 允许特定 crate 使用特定许可证
[[licenses.clarify]]
name = "ring"
version = "*"
expression = "MIT AND ISC AND OpenSSL"
license-files = [
    { path = "LICENSE", hash = 0xbd0eed23 }
]

# Ban 规则
[bans]
# Lint level for when multiple versions of the same crate are detected
multiple-versions = "warn"

# 禁止特定 crate
deny = [
    { name = "openssl", reason = "Use rustls instead" },
]

# 跳过检查的 crate
skip = [
    { name = "windows-sys" },
]

# 允许的重复依赖
skip-tree = [
    { name = "windows-sys", version = "=0.45" },
]

# 安全漏洞
[advisories]
ignore = []

# 漏洞数据库
db-path = "~/.cargo/advisory-db"
db-urls = ["https://github.com/rustsec/advisory-db"]

vulnerability = "deny"
unmaintained = "warn"
yanked = "warn"
notice = "warn"

# 来源检查
[sources]
# 只允许 crates.io
unknown-registry = "deny"
unknown-git = "deny"

# 允许的 git 仓库
allow-git = [
    "https://github.com/rust-lang/crates.io-index",
]
```

---

### 3. cargo-geiger (可选)

**安装**: `cargo install cargo-geiger`  
**用途**: 检测项目中的 unsafe 代码使用情况

#### 基础用法3

```bash
# 分析 unsafe 代码
cargo geiger

# 详细输出
cargo geiger --all-features

# 只显示有 unsafe 的 crate
cargo geiger --compact
```

#### 输出示例

```text
Metric output format: x/y
    x = unsafe code used by the build
    y = total unsafe code found in the crate

Symbols:
    🔒  = No `unsafe` usage found, declares #![forbid(unsafe_code)]
    ❓  = No `unsafe` usage found, missing #![forbid(unsafe_code)]
    ☢️  = `unsafe` usage found

Functions  Expressions  Impls  Traits  Methods  Dependency

0/0        0/0          0/0    0/0     0/0      🔒  my_crate 1.0.0
0/29       0/1368       0/3    0/0     0/5      ☢️  ├── tokio 1.28.0
0/4        0/18         0/0    0/0     0/0      ☢️  │   └── bytes 1.4.0
0/0        0/0          0/0    0/0     0/0      ❓  └── serde 1.0.163

3/33       0/1386       0/3    0/0     0/5
```

---

### 4. cargo-outdated (可选)

**安装**: `cargo install cargo-outdated`  
**用途**: 检查过期的依赖

```bash
# 检查过期依赖
cargo outdated

# 只显示根依赖
cargo outdated -R

# 按语义版本分类
cargo outdated --format json
```

---

### 5. cargo-license (可选)

**安装**: `cargo install cargo-license`  
**用途**: 列出所有依赖的许可证

```bash
# 列出所有许可证
cargo license

# JSON 格式
cargo license --json

# TSV 格式
cargo license --tsv

# 只显示特定许可证
cargo license | grep MIT
```

---

## 💡 最佳实践

### 1. 安全工作流

```bash
#!/bin/bash
# scripts/security-check.sh

set -e

echo "🔒 运行安全检查..."

# 1. 更新漏洞数据库
echo "更新漏洞数据库..."
cargo audit fetch

# 2. 安全审计
echo "检查已知漏洞..."
cargo audit

# 3. 依赖检查
echo "检查依赖规则..."
cargo deny check

# 4. unsafe 代码检查
echo "检查 unsafe 代码..."
cargo geiger

# 5. 过期依赖
echo "检查过期依赖..."
cargo outdated -R

echo "✅ 安全检查完成"
```

### 2. CI/CD 集成

```yaml
# .github/workflows/security.yml
name: Security Checks

on:
  push:
    branches: [main]
  pull_request:
  schedule:
    - cron: '0 0 * * 0'  # 每周日

jobs:
  security:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      
      - name: Install Rust
        uses: dtolnay/rust-toolchain@stable
      
      - name: Cache cargo tools
        uses: actions/cache@v3
        with:
          path: ~/.cargo/bin
          key: ${{ runner.os }}-cargo-tools
      
      - name: Install tools
        run: |
          cargo install cargo-audit || true
          cargo install cargo-deny || true
          cargo install cargo-geiger || true
      
      - name: Security Audit
        run: cargo audit
      
      - name: Dependency Check
        run: cargo deny check
      
      - name: Unsafe Code Check
        run: cargo geiger
```

### 3. Pre-commit Hook

```bash
#!/bin/sh
# .git/hooks/pre-commit

# 快速安全检查
cargo audit --deny warnings
cargo deny check -s

if [ $? -ne 0 ]; then
    echo "❌ 安全检查失败"
    exit 1
fi

echo "✅ 安全检查通过"
```

---

## 📊 安全策略

### 依赖安全等级

```toml
# deny.toml
[advisories]
# 严格模式：任何漏洞都拒绝
vulnerability = "deny"
unmaintained = "deny"
yanked = "deny"

# 宽松模式：仅警告
vulnerability = "warn"
unmaintained = "warn"
yanked = "warn"
```

### 许可证策略

```toml
# deny.toml
[licenses]
# 企业项目：严格限制
allow = ["MIT", "Apache-2.0", "BSD-3-Clause"]
deny = ["GPL-3.0", "AGPL-3.0"]
copyleft = "deny"

# 开源项目：宽松
allow = ["MIT", "Apache-2.0", "GPL-3.0"]
copyleft = "warn"
```

---

## 🎯 实战场景

### 场景1: 发现漏洞后的处理

```bash
# 1. 发现漏洞
cargo audit
# error: vulnerable crate found

# 2. 查看详情
cargo audit --json | jq '.vulnerabilities'

# 3. 更新依赖
cargo update --package vulnerable_crate

# 4. 如果无法更新，添加到忽略列表
# 在 audit.toml 中：
# ignore = ["RUSTSEC-xxxx-xxxx"]

# 5. 记录原因
# reason = "Waiting for upstream fix, workaround applied"
```

### 场景2: 许可证审查

```bash
# 1. 生成许可证报告
cargo license --json > licenses.json

# 2. 查看所有许可证
cargo license | sort | uniq

# 3. 检查 GPL 许可证
cargo license | grep GPL

# 4. 配置 cargo-deny 规则
# 在 deny.toml 中添加许可证策略
```

### 场景3: 减少 unsafe 代码

```bash
# 1. 检查 unsafe 使用
cargo geiger

# 2. 分析 unsafe 代码
cargo geiger --all-features --output-format Json

# 3. 替换 unsafe 依赖
# 例如：openssl -> rustls

# 4. 验证改进
cargo geiger --compact
```

---

## 🔗 相关资源

- [cargo-audit](https://github.com/rustsec/rustsec/tree/main/cargo-audit)
- [cargo-deny](https://github.com/EmbarkStudios/cargo-deny)
- [cargo-geiger](https://github.com/rust-secure-code/cargo-geiger)
- [RustSec Advisory DB](https://rustsec.org/)
- [SPDX License List](https://spdx.org/licenses/)

---

**导航**: [返回工具链层](../README.md) | [下一类别：发布管理](../release/README.md)
