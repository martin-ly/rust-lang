# CI/CD - 持续集成与部署

## 📋 目录

- [CI/CD - 持续集成与部署](#cicd---持续集成与部署)
  - [📋 目录](#-目录)
  - [概述](#概述)
  - [GitHub Actions](#github-actions)
    - [基础工作流](#基础工作流)
    - [多平台构建](#多平台构建)
  - [GitLab CI](#gitlab-ci)
    - [基础配置](#基础配置)
  - [实战示例](#实战示例)
    - [代码覆盖率](#代码覆盖率)
    - [自动发布](#自动发布)
  - [参考资源](#参考资源)

---

## 概述

CI/CD 自动化构建、测试和部署流程，提高开发效率和代码质量。

---

## GitHub Actions

### 基础工作流

```yaml
# .github/workflows/ci.yml
name: CI

on:
  push:
    branches: [ main ]
  pull_request:
    branches: [ main ]

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - name: 安装 Rust
        uses: dtolnay/rust-toolchain@stable
      
      - name: 缓存
        uses: Swatinem/rust-cache@v2
      
      - name: 检查
        run: cargo check
      
      - name: 测试
        run: cargo test --all-features
      
      - name: Clippy
        run: cargo clippy -- -D warnings
```

### 多平台构建

```yaml
name: Release

on:
  push:
    tags:
      - 'v*'

jobs:
  build:
    strategy:
      matrix:
        os: [ubuntu-latest, windows-latest, macos-latest]
    runs-on: ${{ matrix.os }}
    
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@stable
      
      - name: 构建
        run: cargo build --release
      
      - name: 上传
        uses: actions/upload-artifact@v3
        with:
          name: ${{ matrix.os }}-binary
          path: target/release/my-app
```

---

## GitLab CI

### 基础配置

```yaml
# .gitlab-ci.yml
image: rust:latest

stages:
  - test
  - build
  - deploy

variables:
  CARGO_HOME: $CI_PROJECT_DIR/.cargo

cache:
  paths:
    - .cargo/
    - target/

test:
  stage: test
  script:
    - cargo test --all-features

build:
  stage: build
  script:
    - cargo build --release
  artifacts:
    paths:
      - target/release/my-app

deploy:
  stage: deploy
  script:
    - echo "部署到生产环境"
  only:
    - main
```

---

## 实战示例

### 代码覆盖率

```yaml
name: Coverage

on: [push, pull_request]

jobs:
  coverage:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@stable
      
      - name: 安装 cargo-llvm-cov
        run: cargo install cargo-llvm-cov
      
      - name: 生成覆盖率
        run: cargo llvm-cov --all-features --lcov --output-path lcov.info
      
      - name: 上传到 Codecov
        uses: codecov/codecov-action@v3
        with:
          files: lcov.info
```

### 自动发布

```yaml
name: Publish

on:
  push:
    tags:
      - 'v*'

jobs:
  publish:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@stable
      
      - name: 发布到 crates.io
        run: cargo publish --token ${{ secrets.CARGO_TOKEN }}
```

---

## 参考资源

- [GitHub Actions 文档](https://docs.github.com/actions)
- [GitLab CI 文档](https://docs.gitlab.com/ee/ci/)
