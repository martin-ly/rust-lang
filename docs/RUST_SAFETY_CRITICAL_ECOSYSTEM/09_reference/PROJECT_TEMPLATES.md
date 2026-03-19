# 项目模板

## 概述

本文档提供Rust安全关键项目的完整模板，可直接用于启动新项目。

---

## 1. 嵌入式项目模板

### 1.1 项目结构

```
embedded-safety-project/
├── .cargo/
│   └── config.toml
├── src/
│   ├── main.rs
│   ├── lib.rs
│   ├── hal/
│   │   ├── mod.rs
│   │   ├── gpio.rs
│   │   └── timer.rs
│   ├── safety/
│   │   ├── mod.rs
│   │   ├── watchdog.rs
│   │   └── monitor.rs
│   └── app/
│       ├── mod.rs
│       └── state_machine.rs
├── tests/
│   └── integration_tests.rs
├── examples/
│   └── basic.rs
├── Cargo.toml
├── rust-toolchain.toml
├── clippy.toml
├── deny.toml
├── build.rs
└── memory.x
```

### 1.2 Cargo.toml模板

```toml
[package]
name = "safety-embedded-app"
version = "0.1.0"
edition = "2021"
authors = ["Your Name <email@example.com>"]
license = "MIT OR Apache-2.0"
description = "Safety-critical embedded application"
repository = "https://github.com/yourorg/safety-embedded-app"
keywords = ["safety-critical", "embedded", "no-std"]
categories = ["embedded", "no-std"]
rust-version = "1.81"

[dependencies]
# 核心嵌入式
cortex-m = { version = "0.7", features = ["critical-section-single-core"] }
cortex-m-rt = "0.7"
panic-halt = "0.2"

# HAL层
stm32f4xx-hal = { version = "0.21", features = ["rt", "stm32f407"] }

# 安全关键库
static_assertions = "1.1"
const_format = "0.2"

# 无分配集合
heapless = "0.8"

# 嵌入式日志
defmt = "0.3"
defmt-rtt = "0.4"

# 错误处理
thiserror = { version = "1.0", default-features = false }

[dev-dependencies]
defmt-test = "0.3"

# 文档生成
[package.metadata.docs.rs]
targets = ["thumbv7em-none-eabihf"]

[profile.dev]
opt-level = 1
debug = 2
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

[profile.reproducible]
inherits = "release"
debug = true
lto = "fat"
codegen-units = 1
strip = false
```

### 1.3 rust-toolchain.toml

```toml
[toolchain]
channel = "1.81.0"
components = [
    "rust-src",
    "rustfmt",
    "clippy",
    "llvm-tools-preview",
]
targets = [
    "thumbv7em-none-eabihf",
]
profile = "minimal"
```

### 1.4 .cargo/config.toml

```toml
[build]
target = "thumbv7em-none-eabihf"

[target.thumbv7em-none-eabihf]
runner = "probe-rs run --chip STM32F407VG"
rustflags = [
    "-C", "link-arg=-Tlink.x",
    "-C", "linker=rust-lld",
    "-C", "lto=yes",
]

[env]
DEFMT_LOG = "info"

[net]
retry = 3
```

### 1.5 main.rs模板

```rust
#![no_std]
#![no_main]

use cortex_m_rt::entry;
use defmt::*;
use defmt_rtt as _;
use panic_halt as _;

use stm32f4xx_hal::{
    pac,
    prelude::*,
    timer::Timer,
};

mod safety;
mod app;

use safety::Watchdog;
use app::Application;

#[entry]
fn main() -> ! {
    info!("System starting...");

    // 获取外设
    let dp = pac::Peripherals::take().unwrap();
    let cp = cortex_m::Peripherals::take().unwrap();

    // 配置时钟
    let rcc = dp.RCC.constrain();
    let clocks = rcc.cfgr.sysclk(168.MHz()).freeze();

    // 配置GPIO
    let gpioa = dp.GPIOA.split();
    let led = gpioa.pa5.into_push_pull_output();

    // 配置定时器
    let timer = Timer::new(dp.TIM2, &clocks);

    // 初始化看门狗
    let watchdog = Watchdog::new(dp.IWDG);

    // 创建应用
    let mut app = Application::new(led, timer, watchdog);

    info!("Entering main loop");

    loop {
        app.cycle();
    }
}
```

### 1.6 lib.rs模板

```rust
#![no_std]
#![cfg_attr(test, no_main)]

pub mod safety;
pub mod app;
pub mod hal;

use core::panic::PanicInfo;

/// 安全关键错误类型
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum SafetyError {
    WatchdogTimeout,
    InvalidState,
    CommunicationFailure,
    SensorFault,
}

/// 结果类型别名
pub type Result<T> = core::result::Result<T, SafetyError>;
```

### 1.7 memory.x

```ld
MEMORY
{
  /* STM32F407VG */
  RAM (xrw) : ORIGIN = 0x20000000, LENGTH = 128K

  /* Flash */
  FLASH (rx) : ORIGIN = 0x08000000, LENGTH = 1024K

  /* CCM RAM */
  CCM (xrw) : ORIGIN = 0x10000000, LENGTH = 64K
}

/* Stack top */
_stack_top = ORIGIN(RAM) + LENGTH(RAM);
```

---

## 2. 应用程序模板

### 2.1 项目结构

```
safety-application/
├── src/
│   ├── main.rs
│   ├── config.rs
│   ├── error.rs
│   ├── state_machine.rs
│   ├── safety_logic.rs
│   └── io/
│       ├── mod.rs
│       ├── input.rs
│       └── output.rs
├── tests/
├── benches/
├── docs/
├── Cargo.toml
├── clippy.toml
├── deny.toml
├── tarpaulin.toml
└── .github/
    └── workflows/
        └── ci.yml
```

### 2.2 Cargo.toml

```toml
[package]
name = "safety-application"
version = "0.1.0"
edition = "2021"
rust-version = "1.81"

[dependencies]
# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# 错误处理
thiserror = "1.0"
anyhow = "1.0"

# 日志
tracing = "0.1"
tracing-subscriber = "0.3"

# 异步
tokio = { version = "1.35", features = ["full"] }

# 配置
config = "0.14"

# 验证
validator = { version = "0.16", features = ["derive"] }

[dev-dependencies]
# 测试
mockall = "0.12"
tempfile = "3.8"

# 性能测试
criterion = { version = "0.5", features = ["html_reports"] }

# 属性测试
proptest = "1.4"

# 验证
kani-verifier = "0.40"

[[bench]]
name = "performance"
harness = false
```

### 2.3 state_machine.rs

```rust
//! 类型状态模式的状态机

use crate::error::Error;
use crate::Result;

/// 状态标记
pub struct Init;
pub struct Ready;
pub struct Running;
pub struct ErrorState;

/// 状态机
pub struct StateMachine<S> {
    _state: std::marker::PhantomData<S>,
    data: StateData,
}

struct StateData {
    config: Config,
    metrics: Metrics,
}

impl StateMachine<Init> {
    pub fn new(config: Config) -> Result<Self> {
        config.validate()?;

        Ok(Self {
            _state: std::marker::PhantomData,
            data: StateData {
                config,
                metrics: Metrics::default(),
            },
        })
    }

    pub fn initialize(self) -> Result<StateMachine<Ready>> {
        // 初始化逻辑

        Ok(StateMachine {
            _state: std::marker::PhantomData,
            data: self.data,
        })
    }
}

impl StateMachine<Ready> {
    pub fn start(self) -> StateMachine<Running> {
        StateMachine {
            _state: std::marker::PhantomData,
            data: self.data,
        }
    }
}

impl StateMachine<Running> {
    pub fn process(&mut self, input: Input) -> Result<Output> {
        // 处理逻辑
        Ok(Output::default())
    }

    pub fn stop(self) -> StateMachine<Ready> {
        StateMachine {
            _state: std::marker::PhantomData,
            data: self.data,
        }
    }
}
```

### 2.4 CI/CD配置

```yaml
# .github/workflows/ci.yml
name: Safety Critical CI

on:
  push:
    branches: [main, develop]
  pull_request:
    branches: [main]

env:
  CARGO_TERM_COLOR: always
  RUST_BACKTRACE: 1

jobs:
  check:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - uses: dtolnay/rust-toolchain@stable
        with:
          components: rustfmt, clippy, llvm-tools-preview

      - name: Format check
        run: cargo fmt --all -- --check

      - name: Clippy
        run: cargo clippy --all-targets --all-features -- -D warnings

      - name: Check
        run: cargo check --all-targets

  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - uses: dtolnay/rust-toolchain@stable

      - name: Cache cargo
        uses: actions/cache@v3
        with:
          path: |
            ~/.cargo/registry
            ~/.cargo/git
            target
          key: ${{ runner.os }}-cargo-${{ hashFiles('**/Cargo.lock') }}

      - name: Run tests
        run: cargo test --all-features

      - name: Run doc tests
        run: cargo test --doc

  coverage:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - uses: dtolnay/rust-toolchain@stable
        with:
          components: llvm-tools-preview

      - uses: taiki-e/install-action@cargo-llvm-cov

      - name: Generate coverage
        run: cargo llvm-cov --all-features --lcov --output-path lcov.info

      - name: Upload coverage
        uses: codecov/codecov-action@v3
        with:
          files: lcov.info
          fail_ci_if_error: true

  audit:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Run cargo audit
        uses: actions-rust-lang/audit@v1
        with:
          token: ${{ secrets.GITHUB_TOKEN }}
```

---

## 3. 快速启动命令

### 3.1 创建新项目

```bash
# 使用cargo-generate
cargo install cargo-generate

# 从模板创建
cargo generate --git https://github.com/yourorg/safety-embedded-template

# 或手动复制模板
mkdir my-safety-project
cd my-safety-project
# 复制模板文件
```

### 3.2 初始化检查清单

```bash
#!/bin/bash
# init-check.sh

echo "🔍 Project Initialization Check"
echo "================================"

# 检查Rust版本
echo -n "✓ Rust version... "
rustc --version | grep -q "1.81" && echo "OK" || echo "UPDATE NEEDED"

# 检查工具链
echo -n "✓ Required components... "
rustup component list --installed | grep -q "rust-src" && echo "OK" || echo "MISSING"

# 检查工具
echo -n "✓ cargo-deny... "
which cargo-deny >/dev/null && echo "OK" || echo "INSTALL: cargo install cargo-deny"

echo ""
echo "📋 Next steps:"
echo "   1. Review and update Cargo.toml"
echo "   2. Configure target platform in .cargo/config.toml"
echo "   3. Run 'cargo build' to verify setup"
echo "   4. Run 'cargo test' to run tests"
```

---

**文档版本**: 1.0
**最后更新**: 2026-03-18

---

*使用这些模板快速启动您的安全关键Rust项目。*
