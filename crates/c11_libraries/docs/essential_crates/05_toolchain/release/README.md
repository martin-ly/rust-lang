# 发布管理工具 (Release Management Tools)

**类别**: 第5层 - 工具链  
**重要程度**: ⭐⭐⭐  
**更新日期**: 2025-10-20

---

## 📋 目录

- [发布管理工具 (Release Management Tools)](#发布管理工具-release-management-tools)
  - [📋 目录](#-目录)
  - [📋 概述](#-概述)
  - [🔧 核心工具](#-核心工具)
    - [1. cargo-release (推荐 🌟)](#1-cargo-release-推荐-)
      - [基础用法](#基础用法)
      - [release.toml 配置](#releasetoml-配置)
    - [2. cargo-dist (推荐 💡)](#2-cargo-dist-推荐-)
      - [初始化](#初始化)
      - [dist.toml 配置](#disttoml-配置)
      - [GitHub Actions 集成](#github-actions-集成)
    - [3. git-cliff (变更日志 💡)](#3-git-cliff-变更日志-)
      - [基础用法3](#基础用法3)
      - [cliff.toml 配置](#clifftoml-配置)
    - [4. semantic-release (可选)](#4-semantic-release-可选)
      - [.releaserc.json 配置](#releasercjson-配置)
  - [💡 最佳实践](#-最佳实践)
    - [1. 发布检查清单](#1-发布检查清单)
    - [2. 语义化版本规范](#2-语义化版本规范)
    - [3. 提交规范](#3-提交规范)
    - [4. CHANGELOG 格式](#4-changelog-格式)
  - [📊 发布工作流](#-发布工作流)
    - [完整发布流程](#完整发布流程)
  - [🎯 实战场景](#-实战场景)
    - [场景1: 首次发布](#场景1-首次发布)
    - [场景2: 工作空间发布](#场景2-工作空间发布)
    - [场景3: 跨平台二进制发布](#场景3-跨平台二进制发布)
  - [🔗 相关资源](#-相关资源)

## 📋 概述

发布管理工具帮助自动化版本发布流程，包括版本号管理、变更日志生成、Git 标签创建、crates.io 发布等。

---

## 🔧 核心工具

### 1. cargo-release (推荐 🌟)

**安装**: `cargo install cargo-release`  
**用途**: 自动化 crate 发布流程

#### 基础用法

```bash
# 发布新版本（自动递增）
cargo release patch   # 0.1.0 -> 0.1.1
cargo release minor   # 0.1.0 -> 0.2.0
cargo release major   # 0.1.0 -> 1.0.0

# 指定版本
cargo release 1.2.3

# 预发布版本
cargo release alpha
cargo release beta
cargo release rc

# 干运行（不实际执行）
cargo release --dry-run

# 跳过某些步骤
cargo release --no-publish      # 不发布到 crates.io
cargo release --no-push         # 不推送到 Git
cargo release --no-tag          # 不创建 Git 标签
```

#### release.toml 配置

```toml
# release.toml
[workspace]
# 工作空间设置
allow-branch = ["main", "master"]
pre-release-commit-message = "chore: Release {{crate_name}} version {{version}}"
post-release-commit-message = "chore: Bump version to {{next_version}}"
tag-message = "Release {{crate_name}} v{{version}}"
tag-prefix = "v"
tag-name = "{{prefix}}{{version}}"

# 发布前检查
pre-release-checks = [
    "cargo test --all-features",
    "cargo clippy -- -D warnings",
    "cargo doc --no-deps",
]

# 发布后操作
post-release-replacements = [
    { file = "CHANGELOG.md", search = "Unreleased", replace = "{{version}}" },
    { file = "README.md", search = "version = \"[^\"]*\"", replace = "version = \"{{version}}\"" },
]

[[package]]
name = "my_crate"
# 包特定设置
pre-release-hook = ["./scripts/pre-release.sh"]
```

---

### 2. cargo-dist (推荐 💡)

**安装**: `cargo install cargo-dist`  
**用途**: 自动生成多平台二进制发布包

#### 初始化

```bash
# 初始化 cargo-dist
cargo dist init

# 生成发布构建
cargo dist build

# 生成 GitHub Release
cargo dist plan
cargo dist build --artifacts all
```

#### dist.toml 配置

```toml
# dist.toml
[dist]
# 目标平台
targets = [
    "x86_64-unknown-linux-gnu",
    "x86_64-apple-darwin",
    "x86_64-pc-windows-msvc",
    "aarch64-apple-darwin",
]

# CI 配置
ci = ["github"]

# 安装器
installers = ["shell", "powershell"]

# 压缩格式
archive-format = "tar.gz"  # or "zip"

# 包含额外文件
include = ["README.md", "LICENSE", "docs/"]
```

#### GitHub Actions 集成

```yaml
# .github/workflows/release.yml
name: Release

on:
  push:
    tags:
      - 'v*'

jobs:
  dist:
    runs-on: ${{ matrix.os }}
    strategy:
      matrix:
        include:
          - os: ubuntu-latest
            target: x86_64-unknown-linux-gnu
          - os: macos-latest
            target: x86_64-apple-darwin
          - os: windows-latest
            target: x86_64-pc-windows-msvc
    
    steps:
      - uses: actions/checkout@v3
      
      - name: Install Rust
        uses: dtolnay/rust-toolchain@stable
      
      - name: Install cargo-dist
        run: cargo install cargo-dist
      
      - name: Build release
        run: cargo dist build --target ${{ matrix.target }}
      
      - name: Upload artifacts
        uses: actions/upload-artifact@v3
        with:
          name: dist-${{ matrix.target }}
          path: target/dist/
```

---

### 3. git-cliff (变更日志 💡)

**安装**: `cargo install git-cliff`  
**用途**: 自动生成变更日志

#### 基础用法3

```bash
# 生成变更日志
git cliff

# 输出到文件
git cliff > CHANGELOG.md

# 指定范围
git cliff v1.0.0..v2.0.0

# 只生成最新版本
git cliff --latest

# 预览下一个版本
git cliff --unreleased
```

#### cliff.toml 配置

```toml
# cliff.toml
[changelog]
# 变更日志标题
header = """
# Changelog

All notable changes to this project will be documented in this file.\n
"""

# 变更日志主体
body = """
{% for group, commits in commits | group_by(attribute="group") %}
    ### {{ group | upper_first }}
    {% for commit in commits %}
        - {{ commit.message | upper_first }} ({{ commit.id | truncate(length=7, end="") }})
    {% endfor %}
{% endfor %}
"""

# 提交解析
[git]
# 常规提交规范
conventional_commits = true
# 过滤提交
filter_commits = true

# 提交分组
commit_parsers = [
    { message = "^feat", group = "Features" },
    { message = "^fix", group = "Bug Fixes" },
    { message = "^doc", group = "Documentation" },
    { message = "^perf", group = "Performance" },
    { message = "^refactor", group = "Refactor" },
    { message = "^style", group = "Styling" },
    { message = "^test", group = "Testing" },
    { message = "^chore", skip = true },
]
```

---

### 4. semantic-release (可选)

**安装**: `npm install -g semantic-release @semantic-release/changelog @semantic-release/git`  
**用途**: 完全自动化的语义化版本发布

#### .releaserc.json 配置

```json
{
  "branches": ["main"],
  "plugins": [
    "@semantic-release/commit-analyzer",
    "@semantic-release/release-notes-generator",
    "@semantic-release/changelog",
    [
      "@semantic-release/exec",
      {
        "prepareCmd": "cargo set-version ${nextRelease.version}",
        "publishCmd": "cargo publish"
      }
    ],
    [
      "@semantic-release/git",
      {
        "assets": ["CHANGELOG.md", "Cargo.toml", "Cargo.lock"],
        "message": "chore(release): ${nextRelease.version} [skip ci]\n\n${nextRelease.notes}"
      }
    ],
    "@semantic-release/github"
  ]
}
```

---

## 💡 最佳实践

### 1. 发布检查清单

```bash
#!/bin/bash
# scripts/pre-release.sh

set -e

echo "🚀 准备发布..."

# 1. 代码检查
echo "运行代码检查..."
cargo fmt -- --check
cargo clippy --all-targets -- -D warnings

# 2. 测试
echo "运行测试..."
cargo test --all-features

# 3. 文档
echo "生成文档..."
cargo doc --no-deps --all-features

# 4. 安全审计
echo "安全审计..."
cargo audit

# 5. 依赖检查
echo "依赖检查..."
cargo deny check

# 6. 构建 release
echo "构建 release..."
cargo build --release

# 7. 打包测试
echo "打包测试..."
cargo package --allow-dirty

echo "✅ 发布前检查完成"
```

### 2. 语义化版本规范

```text
版本格式: MAJOR.MINOR.PATCH

- MAJOR: 不兼容的 API 变更
- MINOR: 向后兼容的功能新增
- PATCH: 向后兼容的问题修复

预发布版本:
- 1.0.0-alpha.1
- 1.0.0-beta.1
- 1.0.0-rc.1

构建元数据:
- 1.0.0+20130313144700
```

### 3. 提交规范

```text
<type>(<scope>): <subject>

<body>

<footer>

Types:
- feat: 新功能
- fix: 修复
- docs: 文档
- style: 格式
- refactor: 重构
- test: 测试
- chore: 构建/工具

Examples:
feat(auth): add JWT authentication
fix(api): resolve null pointer exception
docs(readme): update installation guide
```

### 4. CHANGELOG 格式

```markdown
# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added
- New feature X

### Changed
- Updated feature Y

### Fixed
- Fixed bug Z

## [1.0.0] - 2025-10-20

### Added
- Initial release
- Feature A
- Feature B

### Fixed
- Bug fix C

[Unreleased]: https://github.com/user/repo/compare/v1.0.0...HEAD
[1.0.0]: https://github.com/user/repo/releases/tag/v1.0.0
```

---

## 📊 发布工作流

### 完整发布流程

```bash
#!/bin/bash
# scripts/release.sh

VERSION=$1

if [ -z "$VERSION" ]; then
    echo "Usage: ./release.sh <version>"
    exit 1
fi

echo "🚀 发布版本 $VERSION"

# 1. 确保在正确的分支
BRANCH=$(git branch --show-current)
if [ "$BRANCH" != "main" ]; then
    echo "❌ 必须在 main 分支发布"
    exit 1
fi

# 2. 确保工作区干净
if ! git diff-index --quiet HEAD --; then
    echo "❌ 工作区有未提交的更改"
    exit 1
fi

# 3. 拉取最新代码
git pull origin main

# 4. 运行测试
cargo test --all-features

# 5. 更新版本号
cargo set-version $VERSION

# 6. 生成变更日志
git cliff --tag $VERSION > CHANGELOG.md

# 7. 提交变更
git add Cargo.toml Cargo.lock CHANGELOG.md
git commit -m "chore: Release version $VERSION"

# 8. 创建标签
git tag -a "v$VERSION" -m "Release $VERSION"

# 9. 推送到远程
git push origin main
git push origin "v$VERSION"

# 10. 发布到 crates.io
cargo publish

echo "✅ 发布完成: v$VERSION"
```

---

## 🎯 实战场景

### 场景1: 首次发布

```bash
# 1. 准备发布
cargo package
cargo package --list

# 2. 本地测试
cargo install --path .

# 3. 登录 crates.io
cargo login <api-token>

# 4. 发布
cargo publish --dry-run
cargo publish

# 5. 验证
cargo search my_crate
```

### 场景2: 工作空间发布

```bash
# 发布所有包
cargo release --workspace patch

# 发布特定包
cargo release -p my_crate patch

# 发布顺序（自动处理依赖）
cargo release --workspace --execute
```

### 场景3: 跨平台二进制发布

```bash
# 1. 初始化 cargo-dist
cargo dist init

# 2. 配置目标平台
# 编辑 dist.toml

# 3. 构建所有平台
cargo dist build --artifacts all

# 4. 创建 GitHub Release
gh release create v1.0.0 \
    --title "Release 1.0.0" \
    --notes "Release notes" \
    target/dist/*
```

---

## 🔗 相关资源

- [cargo-release](https://github.com/crate-ci/cargo-release)
- [cargo-dist](https://opensource.axo.dev/cargo-dist/)
- [git-cliff](https://git-cliff.org/)
- [Semantic Versioning](https://semver.org/)
- [Keep a Changelog](https://keepachangelog.com/)
- [Conventional Commits](https://www.conventionalcommits.org/)

---

**导航**: [返回工具链层](../README.md) | [返回主页](../../README.md)
