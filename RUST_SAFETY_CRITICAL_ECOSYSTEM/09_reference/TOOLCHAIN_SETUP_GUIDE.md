# 安全关键Rust工具链配置指南

## 概述

本指南提供配置Rust工具链以满足安全关键开发要求的详细步骤，涵盖Ferrocene、Miri、Kani等工具的完整配置。

---

## 工具链架构

### 安全关键工具栈

```
┌─────────────────────────────────────────────────────────────┐
│                      IDE/编辑器层                            │
│  VS Code + rust-analyzer / CLion / vim + coc-rust-analyzer  │
└─────────────────────────────────────────────────────────────┘
                              │
┌─────────────────────────────────────────────────────────────┐
│                    构建与包管理                              │
│    Cargo (冻结版本) + Ferrocene rustc + 自定义registry      │
└─────────────────────────────────────────────────────────────┘
                              │
┌─────────────────────────────────────────────────────────────┐
│                    静态分析层                                │
│  rustc (所有权/借用) + Clippy (lints) + custom lints        │
└─────────────────────────────────────────────────────────────┘
                              │
┌─────────────────────────────────────────────────────────────┐
│                    运行时验证层                              │
│  Unit Tests + Miri (UB检测) + Kani (属性验证)               │
└─────────────────────────────────────────────────────────────┘
                              │
┌─────────────────────────────────────────────────────────────┐
│                    覆盖率与度量                              │
│  cargo-tarpaulin + cargo-llvm-cov + 代码度量                │
└─────────────────────────────────────────────────────────────┘
                              │
┌─────────────────────────────────────────────────────────────┐
│                    文档与报告                                │
│  rustdoc + cargo-deny + SBOM生成 + 安全案例                 │
└─────────────────────────────────────────────────────────────┘
```

---

## 基础环境配置

### 1. Rust工具链安装

```bash
# 安装rustup (如尚未安装)
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
source $HOME/.cargo/env

# 安装稳定版 (用于日常开发)
rustup install stable
rustup default stable

# 安装特定版本 (安全关键项目)
rustup install 1.81.0
rustup default 1.81.0
```

### 2. Ferrocene工具链 (预认证)

```bash
# Ferrocene需要商业许可，以下为配置示例
# 联系Ferrocene获取访问权限

# 添加Ferrocene工具链
rustup toolchain install ferrocene

# 配置项目使用Ferrocene
rustup override set ferrocene

# 验证安装
rustc --version  # 应显示Ferrocene版本
```

### 3. 开发工具安装

```bash
# 安装Clippy (代码质量)
rustup component add clippy

# 安装rustfmt (代码格式化)
rustup component add rustfmt

# 安装rust-src (源代码，用于调试)
rustup component add rust-src

# 安装rust-analyzer (IDE支持)
rustup component add rust-analyzer

# 安装Miri (内存安全检测)
rustup component add miri

# 安装LLVM工具 (覆盖率)
rustup component add llvm-tools-preview
```

---

## 项目配置

### Cargo.toml模板

```toml
[package]
name = "safety-critical-module"
version = "1.0.0"
edition = "2021"
authors = ["Your Name <email@example.com>"]
license = "MIT OR Apache-2.0"
rust-version = "1.70"  # MSRV

[dependencies]
# 仅使用no_std兼容库
cortex-m = "0.7"
cortex-m-rt = "0.7"
panic-halt = "0.2"

# 嵌入式HAL
embedded-hal = "0.2"

# 安全关键特定
static_assertions = "1.1"

[dev-dependencies]
# 测试框架
kani-verifier = "0.40"

# 模拟器
# qemu-system-arm (外部安装)

[profile.dev]
opt-level = 0
debug = true
debug-assertions = true
overflow-checks = true
lto = false
panic = "abort"
incremental = true

[profile.release]
opt-level = 3
debug = false
debug-assertions = false
overflow-checks = false
lto = true
panic = "abort"
codegen-units = 1
strip = true

# 安全关键配置：可重现构建
[profile.reproducible]
inherits = "release"
debug = true
lto = "fat"
codegen-units = 1
strip = false

[features]
default = []
std = []
test = []
# 安全等级特性
asil-d = []
sil-4 = []

[[bin]]
name = "main"
path = "src/main.rs"
```

### rust-toolchain.toml

```toml
[toolchain]
# 固定工具链版本以实现可重现构建
channel = "1.81.0"
components = [
    "rust-src",
    "rustfmt",
    "clippy",
    "miri",
    "llvm-tools-preview",
]
targets = [
    "thumbv7em-none-eabihf",  # ARM Cortex-M4/M7
    "x86_64-unknown-linux-gnu",
    "aarch64-unknown-linux-gnu",
]
profile = "minimal"
```

### .cargo/config.toml

```toml
[build]
# 默认目标 (嵌入式)
target = "thumbv7em-none-eabihf"

# 链接器配置
[target.thumbv7em-none-eabihf]
runner = "probe-run --chip STM32F407VG"
rustflags = [
    "-C", "link-arg=-Tlink.x",
    "-C", "linker=rust-lld",
    "-C", "lto=yes",
]

# x86目标配置
[target.x86_64-unknown-linux-gnu]
rustflags = [
    "-C", "target-cpu=sandybridge",
    "-C", "target-feature=+aes,+avx",
]

[env]
# 设置DEFMT日志级别
DEFMT_LOG = "trace"

[net]
# 离线模式支持
offline = false

[registries]
# 私有registry配置
crates-io = { index = "https://github.com/rust-lang/crates.io-index" }
# company-internal = { index = "https://internal.company.com/git/index" }
```

---

## Clippy配置

### clippy.toml

```toml
# 安全关键特定配置

# 禁止不安全代码 (安全关键项目)
deny = [
    "unsafe_code",
]

# 严格lint级别
warn = [
    "clippy::all",
    "clippy::pedantic",
    "clippy::restriction",
    "clippy::nursery",
]

# 允许特定规则 (根据需要调整)
allow = [
    "clippy::module_name_repetitions",
    "clippy::similar_names",
    "clippy::too_many_lines",
    "clippy::cast_possible_truncation",
    "clippy::cast_sign_loss",
    "clippy::cast_precision_loss",
]

# 复杂度限制
cognitive-complexity-threshold = 15
cyclomatic-complexity-threshold = 10

# 函数长度
too-many-lines-threshold = 50

# 参数数量
too-many-arguments-threshold = 5

# 结构体字段数
struct-field-name-threshold = 5
```

### 自定义Lint规则

```rust
// src/lints.rs
//! 自定义Clippy lint规则

use rustc_lint::{Lint, LintPass};
use rustc_session::{declare_lint, declare_lint_pass};

declare_lint! {
    /// 禁止裸指针解引用
    pub BARE_POINTER_DEREF,
    Deny,
    "dereferencing bare pointers is not allowed in safety-critical code"
}

declare_lint! {
    /// 要求所有unsafe块有文档说明
    pub UNDOCUMENTED_UNSAFE,
    Deny,
    "unsafe blocks must be documented with safety invariants"
}

declare_lint! {
    /// 禁止动态内存分配
    pub DYNAMIC_ALLOCATION,
    Deny,
    "dynamic memory allocation is not allowed in safety-critical contexts"
}

declare_lint_pass!(SafetyCriticalLints => [BARE_POINTER_DEREF, UNDOCUMENTED_UNSAFE, DYNAMIC_ALLOCATION]);

impl LintPass for SafetyCriticalLints {
    fn name(&self) -> &'static str {
        "SafetyCriticalLints"
    }
}
```

---

## 测试配置

### Miri配置

```bash
# 环境变量配置
export MIRIFLAGS="\
    -Zmiri-strict-provenance \
    -Zmiri-symbolic-alignment-check \
    -Zmiri-disable-isolation \
    -Zmiri-backtrace=full \
    -Zmiri-report-progress \
"

# 运行Miri测试
cargo miri test

# 运行特定测试
cargo miri test test_name

# 检查特定文件
cargo miri run --bin binary_name
```

### Kani配置

```bash
# 安装Kani
cargo install --locked kani-verifier
kani-setup

# 基本验证
kani src/lib.rs

# 带展开限制
cargo kani --harness my_proof --unwind 10

# 覆盖率检查
cargo kani --harness my_proof --coverage

# 生成报告
cargo kani --harness my_proof --visualize
```

### Cargo.toml测试配置

```toml
[profile.test]
opt-level = 0
debug = 2
debug-assertions = true
overflow-checks = true

[profile.bench]
opt-level = 3
debug = false
lto = true
codegen-units = 1
```

---

## 覆盖率配置

### cargo-tarpaulin

```bash
# 安装
cargo install cargo-tarpaulin

# 基本覆盖率
cargo tarpaulin --out Html --out Xml

# 行覆盖
cargo tarpaulin --line

# 分支覆盖
cargo tarpaulin --branch

# 排除测试代码
cargo tarpaulin --exclude-files "tests/*" --exclude-files "benches/*"

# 安全关键要求：MC/DC覆盖
cargo tarpaulin --mcdc
```

### tarpaulin.toml

```toml
[default]
# 输出格式
out = ["Html", "Xml", "Lcov"]

# 覆盖率类型
line = true
branch = true

# 排除文件
exclude-files = [
    "tests/*",
    "benches/*",
    "examples/*",
    "target/*",
]

# 排除行
exclude-lines = [
    "#\\[derive",
    "unimplemented!",
    "todo!",
]

# 超时 (秒)
timeout = 300

# 线程数
jobs = 4

# 清理
clean = true

# 引擎 (llvm/llvm-cov)
engine = "llvm"

# 目标目录
run-types = ["Tests", "Doctests"]
```

### llvm-cov配置

```bash
# 安装
cargo install cargo-llvm-cov

# 生成覆盖率报告
cargo llvm-cov --lcov --output-path lcov.info

# HTML报告
cargo llvm-cov --html

# 仅包含特定文件
cargo llvm-cov --html --ignore-filename-regex 'tests/.*'
```

---

## CI/CD配置

### GitHub Actions完整配置

```yaml
# .github/workflows/safety-critical.yml
name: Safety Critical CI

on:
  push:
    branches: [ main, develop ]
  pull_request:
    branches: [ main ]

env:
  CARGO_TERM_COLOR: always
  RUST_BACKTRACE: 1

jobs:
  check:
    name: Check
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Install Rust
        uses: dtolnay/rust-toolchain@stable
        with:
          components: rustfmt, clippy, miri, llvm-tools-preview

      - name: Cache cargo
        uses: actions/cache@v3
        with:
          path: |
            ~/.cargo/registry
            ~/.cargo/git
            target
          key: ${{ runner.os }}-cargo-${{ hashFiles('**/Cargo.lock') }}

      - name: Check formatting
        run: cargo fmt --all -- --check

      - name: Clippy
        run: cargo clippy --all-targets --all-features -- -D warnings

      - name: Check
        run: cargo check --all-targets

  test:
    name: Test Suite
    runs-on: ubuntu-latest
    strategy:
      matrix:
        rust: [stable, 1.81.0]
    steps:
      - uses: actions/checkout@v4

      - name: Install Rust ${{ matrix.rust }}
        uses: dtolnay/rust-toolchain@master
        with:
          toolchain: ${{ matrix.rust }}

      - name: Cache cargo
        uses: actions/cache@v3
        with:
          path: |
            ~/.cargo/registry
            ~/.cargo/git
            target
          key: ${{ runner.os }}-cargo-${{ matrix.rust }}-${{ hashFiles('**/Cargo.lock') }}

      - name: Run tests
        run: cargo test --all-features

      - name: Run doc tests
        run: cargo test --doc

  miri:
    name: Miri Tests
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Install Miri
        run: |
          rustup component add miri
          cargo miri setup

      - name: Run Miri
        run: cargo miri test
        env:
          MIRIFLAGS: -Zmiri-strict-provenance

  coverage:
    name: Code Coverage
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Install Rust
        uses: dtolnay/rust-toolchain@stable
        with:
          components: llvm-tools-preview

      - name: Install cargo-llvm-cov
        uses: taiki-e/install-action@cargo-llvm-cov

      - name: Generate coverage
        run: cargo llvm-cov --all-features --lcov --output-path lcov.info

      - name: Upload coverage
        uses: codecov/codecov-action@v3
        with:
          files: lcov.info
          fail_ci_if_error: true

  kani:
    name: Formal Verification
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Install Kani
        run: |
          cargo install --locked kani-verifier
          kani-setup

      - name: Run Kani proofs
        run: cargo kani --workspace

  audit:
    name: Security Audit
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Run cargo audit
        uses: actions-rust-lang/audit@v1

  build:
    name: Build Release
    runs-on: ubuntu-latest
    needs: [check, test]
    steps:
      - uses: actions/checkout@v4

      - name: Install Rust
        uses: dtolnay/rust-toolchain@stable

      - name: Build release
        run: cargo build --release

      - name: Upload artifact
        uses: actions/upload-artifact@v3
        with:
          name: release-binary
          path: target/release/safety-critical-module
```

---

## 文档生成

### rustdoc配置

```bash
# 生成文档
cargo doc --no-deps --document-private-items

# 包含测试
cargo test --doc

# 生成并打开
cargo doc --open
```

### 文档测试

```rust
/// 安全关键函数
///
/// # Safety
///
/// 调用者必须确保:
/// - `ptr` 是有效的非空指针
/// - `ptr` 指向已初始化的内存
/// - 访问不违反Rust的别名规则
///
/// # Examples
///
/// ```
/// use safety_critical_module::safe_wrapper;
///
/// let value = 42;
/// let ptr = &value as *const i32;
/// unsafe {
///     assert_eq!(safe_wrapper(ptr), 42);
/// }
/// ```
pub unsafe fn safe_wrapper(ptr: *const i32) -> i32 {
    // SAFETY: 调用者已确保ptr有效
    *ptr
}
```

---

## 依赖管理

### cargo-deny配置

```toml
# deny.toml
targets = [
    { triple = "x86_64-unknown-linux-gnu" },
    { triple = "thumbv7em-none-eabihf" },
]

[advisories]
db-path = "~/.cargo/advisory-dbs"
db-urls = ["https://github.com/rustsec/advisory-db"]
vulnerability = "deny"
unmaintained = "warn"
yanked = "deny"
notice = "warn"
ignore = []

[licenses]
unlicensed = "deny"
allow = [
    "MIT",
    "Apache-2.0",
    "Apache-2.0 WITH LLVM-exception",
    "BSD-2-Clause",
    "BSD-3-Clause",
    "ISC",
    "Unicode-DFS-2016",
]
deny = []
copyleft = "deny"
allow-osi-fsf-free = "either"
default = "deny"
confidence-threshold = 0.8

[[licenses.clarify]]
name = "ring"
version = "*"
expression = "MIT AND ISC AND OpenSSL"
license-files = [
    { path = "LICENSE", hash = 0xbd0eed23 },
]

[bans]
multiple-versions = "warn"
wildcards = "deny"
highlight = "all"
allow = []
allow-wildcard-paths = true
deny = [
    # 禁止有安全问题的crate
    { name = "crate-with-vulnerability" },
]
skip = []
skip-tree = []

[sources]
unknown-registry = "deny"
unknown-git = "deny"
allow-registry = [
    "https://github.com/rust-lang/crates.io-index",
]
allow-git = []

[sources.allow-org]
github = ["your-org"]
```

### Cargo.lock管理

```bash
# 冻结依赖
cargo generate-lockfile

# 验证lockfile是最新的
cargo update --workspace --locked

# 在CI中检查
cargo update --workspace --locked --dry-run
```

---

## IDE配置

### VS Code settings.json

```json
{
    "rust-analyzer.cargo.features": "all",
    "rust-analyzer.checkOnSave.command": "clippy",
    "rust-analyzer.checkOnSave.allTargets": true,
    "rust-analyzer.checkOnSave.extraArgs": [
        "--",
        "-D",
        "warnings"
    ],
    "rust-analyzer.cargo.unsetTest": ["core"],
    "rust-analyzer.lens.enable": true,
    "rust-analyzer.lens.implementations.enable": true,
    "rust-analyzer.lens.references.enable": true,
    "rust-analyzer.hover.documentation.enable": true,
    "rust-analyzer.inlayHints.enable": true,
    "rust-analyzer.inlayHints.typeHints.enable": true,
    "rust-analyzer.inlayHints.parameterHints.enable": true,
    "rust-analyzer.inlayHints.closureReturnTypeHints.enable": true,
    "rust-analyzer.inlayHints.lifetimeElisionHints.enable": true,
    "[rust]": {
        "editor.formatOnSave": true,
        "editor.defaultFormatter": "rust-lang.rust-analyzer",
        "editor.tabSize": 4,
        "editor.insertSpaces": true,
    },
    "rust-analyzer.procMacro.enable": true,
    "rust-analyzer.procMacro.attributes.enable": true,
}
```

---

**文档版本**: 1.0
**最后更新**: 2026-03-18
**测试工具链**: Rust 1.81, Ferrocene, Miri latest, Kani 0.40

---

*定期更新此文档以反映工具链的最新发展。*
