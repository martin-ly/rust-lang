# Rust CI/CD 指南

> **定位**: Rust 项目持续集成与交付最佳实践
> **平台**: GitHub Actions
> **适用**: 库、二进制应用、跨平台发布
> **Rust 版本**: 1.95.0+

---

## 📋 目录

- [Rust CI/CD 指南](#rust-cicd-指南)
  - [📋 目录](#-目录)
  - [🎯 工作流设计原则](#-工作流设计原则)
  - [⚡ 缓存策略](#-缓存策略)
    - [actions/cache 基础配置](#actionscache-基础配置)
    - [Swatinem/rust-cache 推荐配置](#swatinemrust-cache-推荐配置)
  - [🔍 代码质量检查](#-代码质量检查)
    - [cargo test](#cargo-test)
    - [cargo clippy](#cargo-clippy)
    - [cargo audit](#cargo-audit)
    - [cargo fmt](#cargo-fmt)
  - [🌍 交叉编译](#-交叉编译)
    - [cargo-cross 方案](#cargo-cross-方案)
    - [GitHub Actions 矩阵交叉编译](#github-actions-矩阵交叉编译)
  - [📦 多平台发布矩阵](#-多平台发布矩阵)
  - [🔗 参考资源](#-参考资源)

---

## 🎯 工作流设计原则

```text
Rust CI/CD 流水线:
├─ PR 触发
│   ├─ fmt (最快, < 10s)
│   ├─ clippy (静态分析, ~30s-2min)
│   ├─ test (单元/集成测试, ~1-5min)
│   └─ audit (安全审计, ~10s)
│
├─ main 分支合并
│   └─ 运行完整 PR 检查集
│
└─ Tag 推送 (v*)
    ├─ 运行完整测试
    ├─ 交叉编译 (Linux/macOS/Windows)
    └─ 创建 GitHub Release + 上传制品
```

**关键原则**:

1. **快速失败**: fmt / clippy 放在最前面，快速拦截格式和风格问题
2. **并行最大化**: 测试、检查、编译矩阵并行运行
3. **缓存一切**: 目标目录和 registry 缓存是 CI 速度的关键
4. **安全左移**: `cargo audit` 在 PR 阶段即执行，而非发布前

---

## ⚡ 缓存策略

### actions/cache 基础配置

```yaml
# .github/workflows/ci.yml (片段)
- name: Cache cargo registry
  uses: actions/cache@v4
  with:
    path: |
      ~/.cargo/registry/index
      ~/.cargo/registry/cache
      ~/.cargo/git/db
      target/
    key: ${{ runner.os }}-cargo-${{ hashFiles('**/Cargo.lock') }}
    restore-keys: |
      ${{ runner.os }}-cargo-
```

**分层缓存策略**:

| 缓存内容 | 路径 | 说明 |
|----------|------|------|
| Registry Index | `~/.cargo/registry/index` | crates.io 索引 |
| Registry Cache | `~/.cargo/registry/cache` | 下载的 crate 包 |
| Git DB | `~/.cargo/git/db` | git 依赖 |
| Target | `target/` | 编译产物 |

### Swatinem/rust-cache 推荐配置

`Swatinem/rust-cache` 是社区维护的专用缓存 Action，自动处理缓存键和清理：

```yaml
# .github/workflows/ci.yml
name: CI

on:
  push:
    branches: [main]
  pull_request:

env:
  CARGO_TERM_COLOR: always

jobs:
  check:
    name: Check
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Install Rust
        uses: dtolnay/rust-toolchain@stable
        with:
          components: rustfmt, clippy

      - name: Cache dependencies
        uses: Swatinem/rust-cache@v2
        with:
          shared-key: "ci"           # 跨 Job 共享缓存
          cache-targets: true        # 缓存 target/ 目录
          cache-all-crates: true     # 缓存所有依赖，不仅直接依赖

      - name: Check formatting
        run: cargo fmt --all -- --check

      - name: Run clippy
        run: cargo clippy --all-targets --all-features -- -D warnings

      - name: Run tests
        run: cargo test --all-features

      - name: Security audit
        uses: rustsec/audit-check@v1
        with:
          token: ${{ secrets.GITHUB_TOKEN }}
```

**缓存优化对比**:

| 方案 | 首次构建 | 缓存命中构建 | 配置复杂度 |
|------|----------|--------------|------------|
| 无缓存 | ~5-15min | ~5-15min | 低 |
| actions/cache | ~5-15min | ~1-3min | 中 |
| Swatinem/rust-cache | ~5-15min | ~30s-90s | 低 ✅ |

---

## 🔍 代码质量检查

### cargo test

```yaml
- name: Run tests
  run: cargo test --workspace --all-features
  env:
    # 强制单线程测试（避免并发问题）
    RUST_TEST_THREADS: 1
    # 显示测试输出
    RUST_BACKTRACE: 1
```

**测试分层**:

```yaml
jobs:
  unit-tests:
    name: Unit Tests
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@stable
      - uses: Swatinem/rust-cache@v2
      - run: cargo test --lib --all-features

  integration-tests:
    name: Integration Tests
    runs-on: ubuntu-latest
    services:
      postgres:
        image: postgres:16
        env:
          POSTGRES_PASSWORD: postgres
        options: >-
          --health-cmd pg_isready
          --health-interval 10s
        ports:
          - 5432:5432
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@stable
      - uses: Swatinem/rust-cache@v2
      - run: cargo test --test '*' --all-features
        env:
          DATABASE_URL: postgres://postgres:postgres@localhost:5432/test
```

### cargo clippy

```yaml
- name: Run clippy
  run: cargo clippy --all-targets --all-features -- -D warnings
  env:
    # 将警告视为错误
    RUSTFLAGS: "-Dwarnings"
```

**渐进式 lint 策略**:

```yaml
# 新仓库: 先允许警告，逐步修复
- run: cargo clippy --all-targets --all-features

# 成熟仓库: 禁止警告
- run: cargo clippy --all-targets --all-features -- -D warnings -D clippy::pedantic
```

### cargo audit

检查依赖树中的已知安全漏洞：

```yaml
- name: Security audit
  uses: rustsec/audit-check@v1
  with:
    token: ${{ secrets.GITHUB_TOKEN }}

# 或手动方式
- name: Install cargo-audit
  run: cargo install cargo-audit
- name: Run audit
  run: cargo audit
```

**配置忽略** (`.cargo/audit.toml`):

```toml
[advisories]
ignore = ["RUSTSEC-2020-0071"]  # 已知但可接受的风险
```

### cargo fmt

```yaml
- name: Check formatting
  run: cargo fmt --all -- --check
```

---

## 🌍 交叉编译

### cargo-cross 方案

`cross` 利用 Docker 容器提供完整的交叉编译环境：

```bash
# 安装
 cargo install cross --git https://github.com/cross-rs/cross

# 编译 Linux ARM64 (在 macOS/Windows 上)
cross build --target aarch64-unknown-linux-gnu --release

# 编译 Windows (在 Linux 上)
cross build --target x86_64-pc-windows-gnu --release

# 编译 musl (静态链接)
cross build --target x86_64-unknown-linux-musl --release
```

### GitHub Actions 矩阵交叉编译

```yaml
# .github/workflows/release.yml
name: Release

on:
  push:
    tags:
      - 'v*'

jobs:
  build:
    name: Build ${{ matrix.target }}
    runs-on: ${{ matrix.os }}
    strategy:
      fail-fast: false
      matrix:
        include:
          - target: x86_64-unknown-linux-gnu
            os: ubuntu-latest
            use_cross: true
          - target: x86_64-unknown-linux-musl
            os: ubuntu-latest
            use_cross: true
          - target: aarch64-unknown-linux-gnu
            os: ubuntu-latest
            use_cross: true
          - target: x86_64-apple-darwin
            os: macos-latest
            use_cross: false
          - target: aarch64-apple-darwin
            os: macos-latest
            use_cross: false
          - target: x86_64-pc-windows-msvc
            os: windows-latest
            use_cross: false

    steps:
      - uses: actions/checkout@v4

      - name: Install Rust
        uses: dtolnay/rust-toolchain@stable
        with:
          targets: ${{ matrix.target }}

      - name: Cache dependencies
        uses: Swatinem/rust-cache@v2
        with:
          key: ${{ matrix.target }}

      - name: Install cross
        if: matrix.use_cross
        run: cargo install cross --git https://github.com/cross-rs/cross

      - name: Build (cross)
        if: matrix.use_cross
        run: cross build --release --target ${{ matrix.target }}

      - name: Build (native)
        if: ${{ !matrix.use_cross }}
        run: cargo build --release --target ${{ matrix.target }}

      - name: Package
        shell: bash
        run: |
          binary_name="myapp"
          dirname="${binary_name}-${{ matrix.target }}"
          mkdir "$dirname"
          if [ "${{ matrix.os }}" = "windows-latest" ]; then
            cp "target/${{ matrix.target }}/release/${binary_name}.exe" "$dirname/"
          else
            cp "target/${{ matrix.target }}/release/${binary_name}" "$dirname/"
          fi
          tar czvf "${dirname}.tar.gz" "$dirname"

      - name: Upload artifact
        uses: actions/upload-artifact@v4
        with:
          name: ${{ matrix.target }}
          path: '*.tar.gz'
```

---

## 📦 多平台发布矩阵

```yaml
  release:
    name: Create Release
    needs: build
    runs-on: ubuntu-latest
    permissions:
      contents: write
    steps:
      - uses: actions/checkout@v4

      - name: Download all artifacts
        uses: actions/download-artifact@v4

      - name: Create Release
        uses: softprops/action-gh-release@v1
        with:
          files: '**/*.tar.gz'
          generate_release_notes: true
        env:
          GITHUB_TOKEN: ${{ secrets.GITHUB_TOKEN }}
```

**完整 CI/CD 工作流汇总**:

```yaml
# .github/workflows/ci.yml
name: CI

on:
  push:
    branches: [main]
  pull_request:

env:
  CARGO_TERM_COLOR: always

jobs:
  fmt:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@stable
        with:
          components: rustfmt
      - run: cargo fmt --all -- --check

  clippy:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@stable
        with:
          components: clippy
      - uses: Swatinem/rust-cache@v2
      - run: cargo clippy --all-targets --all-features -- -D warnings

  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@stable
      - uses: Swatinem/rust-cache@v2
      - run: cargo test --workspace --all-features

  audit:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: rustsec/audit-check@v1
        with:
          token: ${{ secrets.GITHUB_TOKEN }}
```

---

## 🔗 参考资源

- [GitHub Actions 文档](https://docs.github.com/actions)
- [Swatinem/rust-cache](https://github.com/Swatinem/rust-cache)
- [cross-rs/cross](https://github.com/cross-rs/cross)
- [rustsec/audit-check](https://github.com/rustsec/audit-check)
- [dtolnay/rust-toolchain](https://github.com/dtolnay/rust-toolchain)
- [Cargo 配置文件](https://doc.rust-lang.org/cargo/reference/config.html)

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-05-08
**状态**: ✅ 已完善
