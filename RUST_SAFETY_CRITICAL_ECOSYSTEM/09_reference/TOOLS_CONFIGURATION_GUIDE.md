# Rust安全关键系统 - 工具配置指南

## 工具链概述

```
┌─────────────────────────────────────────────────────────────────────┐
│                    Rust安全关键工具链                               │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  开发工具                    验证工具                    认证工具  │
│  ┌──────────┐               ┌──────────┐               ┌──────────┐│
│  │ rust-analyzer         │               │ Miri      │               │ Ferrocene ││
│  │ RustRover │               │ Kani      │               │ AdaCore   ││
│  │ VSCode   │               │ Verus     │               │           ││
│  └──────────┘               │ Proptest  │               └──────────┘│
│                              └──────────┘                           │
│                                                                     │
│  分析工具                    文档工具                    协作工具  │
│  ┌──────────┐               ┌──────────┐               ┌──────────┐│
│  │ clippy   │               │ rustdoc  │               │ cargo-audit││
│  │ cargo-bloat         │               │ mdbook    │               │ GitHub    ││
│  │ cargo-geiger        │               │           │               │ Jira      ││
│  └──────────┘               └──────────┘               └──────────┘│
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

---

## 开发环境配置

### 推荐IDE设置

#### VSCode配置 (.vscode/settings.json)

```json
{
  "rust-analyzer.cargo.features": "all",
  "rust-analyzer.checkOnSave.command": "clippy",
  "rust-analyzer.checkOnSave.allTargets": true,
  "rust-analyzer.cargo.loadOutDirsFromCheck": true,
  "rust-analyzer.procMacro.enable": true,

  "editor.formatOnSave": true,
  "editor.formatOnPaste": false,
  "editor.formatOnType": false,

  "[rust]": {
    "editor.defaultFormatter": "rust-lang.rust-analyzer",
    "editor.formatOnSave": true
  },

  "files.watcherExclude": {
    "**/target/**": true,
    "**/Cargo.lock": true
  },

  "rust-analyzer.lens.enable": true,
  "rust-analyzer.lens.run.enable": true,
  "rust-analyzer.lens.debug.enable": true,
  "rust-analyzer.lens.implementations.enable": true,
  "rust-analyzer.lens.references.adlItem.enable": true
}
```

#### VSCode扩展推荐 (.vscode/extensions.json)

```json
{
  "recommendations": [
    "rust-lang.rust-analyzer",
    "vadimcn.vscode-lldb",
    "serayuzgur.crates",
    "tamasfe.even-better-toml",
    "usernamehw.errorlens",
    "mutantdino.resourcemonitor",
    "ms-vscode.hexeditor"
  ]
}
```

### Rust工具链安装脚本

```bash
#!/bin/bash
# install_rust_toolchain.sh
# Rust安全关键开发环境安装脚本

set -e

echo "=== Installing Rust Safety-Critical Development Environment ==="

# 安装rustup和Rust
if ! command -v rustup &> /dev/null; then
    curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
    source $HOME/.cargo/env
fi

# 更新到最新稳定版
rustup update stable
rustup default stable

# 安装必要组件
rustup component add rustfmt clippy llvm-tools-preview

# 安装目标平台
rustup target add thumbv7em-none-eabihf
rustup target add thumbv8m.main-none-eabihf
rustup target add x86_64-unknown-linux-gnu

echo "=== Installing cargo tools ==="

# 代码分析
cargo install cargo-audit
cargo install cargo-outdated
cargo install cargo-tree
cargo install cargo-bloat
cargo install cargo-geiger
cargo install cargo-modules

# 测试和覆盖
cargo install cargo-tarpaulin
cargo install cargo-nextest

# 文档
cargo install mdbook
cargo install cargo-docgen

# 嵌入式
cargo install cargo-flash
cargo install cargo-embed
cargo install probe-rs-cli

# 验证工具
cargo install cargo-kani
cargo install miri

# 安全
cargo install cargo-vet

echo "=== Installation Complete ==="
echo "Please restart your terminal or run 'source $HOME/.cargo/env'"
```

---

## 静态分析工具

### Clippy配置详解

#### 项目级配置 (clippy.toml)

```toml
# 认知复杂度：函数理解难度
cognitive-complexity-threshold = 15

# 循环复杂度：代码路径数量
cyclomatic-complexity-threshold = 15

# 函数参数数量上限
too-many-arguments-threshold = 7

# 函数行数上限 (不含注释和空行)
function-threshold = 50

# 结构体字段上限
struct-field-threshold = 10

# 枚举变体上限
enum-variant-threshold = 10

# 数组大小上限
array-size-threshold = 512

# 字符常量阈值
# 建议单引号字符，双引号字符串
single-char-binding-names-threshold = 0

# 浮点数精度问题检查
# 在嵌入式中可能产生假阳性
float-cmp-const-margin = "1.0e-6"

# 文档行长度
doc-valid-idents = [
    "KiB", "MiB", "GiB", "TiB", "PiB", "EiB",
    "DirectX", "ECMAScript", "GPLv2", "GPLv3", "GitHub", "GitLab",
    "IPv4", "IPv6", "ClojureScript", "CoffeeScript", "JavaScript",
    "NaN", "NaNs", "OAuth", "GraphQL", "OCaml", "OpenGL", "OpenSSH",
    "OpenSSL", "OpenStreetMap", "TensorFlow", "TrueType",
    "iOS", "macOS", "FreeBSD", "TeX", "LaTeX", "BibTeX", "BibLaTeX",
    "MinGW", "CocoaPods", "JavaHome", "UnixPath", "WindowsPath"
]

# 避免破坏导出API（库开发时设为true）
avoid-breaking-exported-api = false

# 忽略测试中的某些lint
test-stdin-width = 120
```

#### 严格模式配置 (用于ASIL D)

```rust
// 在lib.rs或main.rs顶部添加
#![warn(clippy::all)]
#![warn(clippy::pedantic)]
#![warn(clippy::cargo)]
#![warn(clippy::nursery)]

#![deny(clippy::correctness)]
#![deny(clippy::suspicious)]
#![deny(clippy::complexity)]
#![deny(clippy::perf)]

// 安全关键项目建议
#![deny(unsafe_code)]  // 完全禁止unsafe（可选）

// 允许的lint（根据项目需要）
#![allow(clippy::module_name_repetitions)]
#![allow(clippy::similar_names)]
#![allow(clippy::missing_errors_doc)]
```

### Cargo Audit配置

#### 自动化审计脚本

```bash
#!/bin/bash
# security_audit.sh

echo "=== Running Security Audit ==="

# 更新漏洞数据库
cargo audit --version || cargo install cargo-audit
cargo audit --update-db

# 运行审计
cargo audit \
    --json \
    --file Cargo.lock \
    > audit_report.json

# 检查高危漏洞
if cargo audit 2>&1 | grep -q "Severity: HIGH"; then
    echo "ERROR: High severity vulnerabilities found!"
    exit 1
fi

# 检查中危漏洞
if cargo audit 2>&1 | grep -q "Severity: MEDIUM"; then
    echo "WARNING: Medium severity vulnerabilities found"
fi

echo "=== Audit Complete ==="
```

#### 忽略配置 (.cargo/audit.toml)

```toml
[advisories]
# 忽略的advisory（临时）
ignore = [
    # "RUSTSEC-2023-XXXX",  # 注明原因和计划修复日期
]

# 信息性advisory视为警告
informational_warnings = ["unmaintained", "yanked"]

# 严重程度阈值
severity_threshold = "medium"

[output]
# 安静模式
quiet = false
# 显示依赖树
show_tree = true
```

---

## 测试工具配置

### Miri配置

#### 运行脚本

```bash
#!/bin/bash
# run_miri.sh

set -e

echo "=== Running Miri Tests ==="

# 安装/更新miri
rustup component add miri

# 设置环境
export MIRIFLAGS="-Zmiri-strict-provenance -Zmiri-symbolic-alignment-check"

# 运行测试
cargo miri test --target x86_64-unknown-linux-gnu

# 运行特定测试
cargo miri test --target x86_64-unknown-linux-gnu -- module_name::test_name

echo "=== Miri Tests Complete ==="
```

#### 项目配置 (.cargo/config.toml)

```toml
[env]
MIRIFLAGS = "-Zmiri-strict-provenance -Zmiri-symbolic-alignment-check -Zmiri-disable-isolation"

[target.x86_64-unknown-linux-gnu]
runner = "cargo miri"
```

### Kani配置

#### 验证脚本

```bash
#!/bin/bash
# run_kani.sh

echo "=== Running Kani Verification ==="

# 安装/更新kani
cargo install --locked kani-verifier
kani-setup

# 运行所有proofs
cargo kani --workspace

# 运行特定proof
cargo kani --harness my_proof_function

# 生成报告
cargo kani --visualize

echo "=== Kani Verification Complete ==="
```

#### Kani配置 (kani.toml)

```toml
# Kani模型检查配置
[default]
# 默认unwind次数
unwind = 10

# 包含断言检查
assertion-checks = true

# 溢出检查
overflow-checks = true

# 内存安全检查
memory-safety-checks = true

[proof.my_complex_proof]
# 特定proof的配置
unwind = 20

[proof.another_proof]
timeout = 3600  # 1小时
```

### 测试覆盖率

#### Tarpaulin配置

```bash
#!/bin/bash
# coverage.sh

echo "=== Running Coverage Analysis ==="

# 安装
cargo install cargo-tarpaulin

# 运行测试并收集覆盖率
cargo tarpaulin \
    --out Html \
    --out Xml \
    --output-dir target/coverage \
    --target-dir target/tarpaulin \
    --timeout 300 \
    --fail-under 90 \
    --workspace

echo "=== Coverage Report Generated ==="
echo "Open target/coverage/tarpaulin-report.html"
```

#### 配置文件 (.tarpaulin.toml)

```toml
[default]
# 输出格式
out = ["Html", "Xml", "Lcov"]

# 输出目录
output-dir = "target/coverage"

# 超时时间（秒）
timeout = "300s"

# 覆盖率阈值
fail-under = 90

# 排除路径
exclude-files = [
    "tests/*",
    "examples/*",
    "target/*",
]

# 包含测试（通常不应包含）
run-types = ["Tests", "Doctests"]

# 行覆盖还是分支覆盖
line = true
branch = true

# 清理构建
clean = true
```

---

## 嵌入式开发工具

### 交叉编译配置

#### .cargo/config.toml完整配置

```toml
[build]
# 默认目标
target = "thumbv7em-none-eabihf"

[target.thumbv7em-none-eabihf]
# 链接器
linker = "arm-none-eabi-gcc"

# objcopy
objcopy = "arm-none-eabi-objcopy"

# 大小工具
size = "arm-none-eabi-size"

# GDB
runner = "arm-none-eabi-gdb -q -x openocd.gdb"
# 或使用probe-rs
# runner = "probe-rs run --chip STM32F407VG"

# 编译选项
rustflags = [
    "-C", "link-arg=-Tlink.x",
    "-C", "link-arg=-Tdefmt.x",
    "-C", "linker=arm-none-eabi-gcc",
    "-C", "link-arg=-Wl,--gc-sections",
    "-C", "link-arg=-nostartfiles",
    "-C", "link-arg=-mcpu=cortex-m4",
    "-C", "link-arg=-mthumb",
    "-C", "link-arg=-mfpu=fpv4-sp-d16",
    "-C", "link-arg=-mfloat-abi=hard",
]

[env]
DEFMT_LOG = "info"
```

### 调试配置

#### VSCode调试配置 (.vscode/launch.json)

```json
{
  "version": "0.2.0",
  "configurations": [
    {
      "type": "cortex-debug",
      "request": "launch",
      "name": "Debug Microcontroller",
      "servertype": "openocd",
      "cwd": "${workspaceFolder}",
      "executable": "./target/thumbv7em-none-eabihf/debug/app",
      "device": "STM32F407VG",
      "configFiles": [
        "interface/stlink.cfg",
        "target/stm32f4x.cfg"
      ],
      "svdFile": "${workspaceFolder}/STM32F407.svd",
      "preLaunchTask": "cargo build",
      "runToEntryPoint": "main",
      "showDevDebugOutput": "parsed"
    }
  ]
}
```

---

## CI/CD配置

### GitHub Actions完整配置

```yaml
name: Safety-Critical CI/CD

on:
  push:
    branches: [main, develop]
  pull_request:
  schedule:
    - cron: '0 0 * * 0'  # 每周日

env:
  CARGO_TERM_COLOR: always
  RUST_BACKTRACE: 1

jobs:
  # 代码质量检查
  quality:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - uses: dtolnay/rust-action@stable

      - name: Format check
        run: cargo fmt --all -- --check

      - name: Clippy
        run: |
          cargo clippy --all-targets --all-features -- \
            -D warnings \
            -D clippy::pedantic \
            -D clippy::cargo

      - name: Check documentation
        run: cargo doc --no-deps --document-private-items

  # 测试
  test:
    runs-on: ubuntu-latest
    strategy:
      matrix:
        rust: [stable, nightly]
    steps:
      - uses: actions/checkout@v4

      - uses: dtolnay/rust-action@master
        with:
          toolchain: ${{ matrix.rust }}

      - name: Build
        run: cargo build --all-features

      - name: Test
        run: cargo test --all-features

      - name: Miri test
        if: matrix.rust == 'nightly'
        run: |
          rustup component add miri
          cargo miri test

  # 覆盖率
  coverage:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - uses: dtolnay/rust-action@stable

      - name: Install tarpaulin
        run: cargo install cargo-tarpaulin

      - name: Generate coverage
        run: |
          cargo tarpaulin \
            --out Xml \
            --fail-under 90

      - name: Upload to Codecov
        uses: codecov/codecov-action@v3
        with:
          files: ./cobertura.xml

  # 安全审计
  security:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - uses: dtolnay/rust-action@stable

      - name: Security audit
        uses: actions-rust-lang/audit@v1
        with:
          token: ${{ secrets.GITHUB_TOKEN }}

      - name: Check for outdated dependencies
        run: |
          cargo install cargo-outdated
          cargo outdated --exit-code 1

  # 二进制分析
  analysis:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - uses: dtolnay/rust-action@stable

      - name: Build release
        run: cargo build --release

      - name: Size analysis
        run: |
          cargo install cargo-bloat
          cargo bloat --release --crates

      - name: Check for unsafe code
        run: |
          cargo install cargo-geiger
          cargo geiger --all-features

  # 发布
  release:
    if: startsWith(github.ref, 'refs/tags/')
    needs: [quality, test, coverage, security]
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - uses: dtolnay/rust-action@stable

      - name: Build release
        run: cargo build --release --all-features

      - name: Create release
        uses: softprops/action-gh-release@v1
        with:
          files: |
            target/release/my-binary
            LICENSE
            README.md
```

---

## 工具速查表

| 工具 | 用途 | 常用命令 |
|------|------|----------|
| **cargo build** | 构建 | `cargo build --release` |
| **cargo test** | 测试 | `cargo test --all-features` |
| **cargo clippy** | 静态分析 | `cargo clippy -- -D warnings` |
| **cargo fmt** | 格式化 | `cargo fmt --check` |
| **cargo audit** | 安全审计 | `cargo audit` |
| **cargo miri** | UB检测 | `cargo miri test` |
| **cargo kani** | 模型检查 | `cargo kani` |
| **cargo tarpaulin** | 覆盖率 | `cargo tarpaulin --fail-under 90` |
| **cargo bloat** | 大小分析 | `cargo bloat --release` |
| **cargo geiger** | unsafe统计 | `cargo geiger` |
| **cargo tree** | 依赖树 | `cargo tree -d` |
| **cargo outdated** | 检查更新 | `cargo outdated` |
| **cargo vet** | 供应链审计 | `cargo vet` |

---

**配置指南版本**: 1.0
**最后更新**: 2026-03-18
**维护者**: Rust安全关键系统工作组
