# 工具链生态

> **创建日期**: 2026-02-20
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成

> 内容已整合至： [06_toolchain/](../../06_toolchain/)

- [编译器特性](../../06_toolchain/01_compiler_features.md)
- [Cargo 工作空间](../../06_toolchain/02_cargo_workspace_guide.md)
- [rustdoc 高级用法](../../06_toolchain/03_rustdoc_advanced.md)

[返回主索引](../00_master_index.md)

---

## 工具链核心组件

### Rust 编译器 (rustc)

```bash
# 基本编译
rustc main.rs                    # 编译单个文件
rustc --crate-type lib lib.rs    # 编译为库
rustc --crate-type bin main.rs   # 编译为二进制（默认）

# 优化级别
rustc -C opt-level=0 main.rs     # 无优化（快速编译）
rustc -C opt-level=3 main.rs     # 最大优化
rustc -C opt-level=s main.rs     # 优化大小

# 目标平台
rustc --target x86_64-unknown-linux-gnu main.rs
rustc --target wasm32-unknown-unknown main.rs
```

```rust
// 编译器属性示例
#![feature(...)]  // 启用不稳定特性

// 条件编译
#[cfg(target_os = "linux")]
fn linux_specific() {}

#[cfg(windows)]
fn windows_specific() {}

// 内联属性
#[inline]
fn always_inline() {}

#[inline(never)]
fn never_inline() {}

// 优化提示
#[cold]  // 此分支很少执行
fn error_path() {}
```

### Cargo：构建系统与包管理器

```toml
# Cargo.toml 完整示例
[package]
name = "my-project"
version = "0.1.0"
edition = "2024"
authors = ["Name <email@example.com>"]
license = "MIT OR Apache-2.0"
description = "A brief description"
repository = "https://github.com/user/repo"
rust-version = "1.93"

[dependencies]
# 依赖版本规范
serde = "1.0"                    # 语义化版本
serde = "=1.0.150"               # 精确版本
serde = ">=1.0, <2.0"            # 范围
serde = { version = "1.0", features = ["derive"] }  # 带特性
serde = { git = "https://github.com/serde-rs/serde" }  # Git 依赖
serde = { path = "../serde" }    # 本地路径

[dev-dependencies]
# 仅开发时使用的依赖
mockall = "0.12"

[build-dependencies]
# 构建脚本依赖
cc = "1.0"

[features]
# 条件编译特性
default = ["std"]
std = []
async = ["tokio"]
full = ["std", "async"]

[profile.release]
opt-level = 3
lto = true
codegen-units = 1
panic = "abort"

[profile.dev]
opt-level = 1
incremental = true
```

### 常用 Cargo 命令

```bash
# 项目管理
cargo new my-project         # 创建二进制项目
cargo new --lib my-library   # 创建库项目
cargo init                   # 在当前目录初始化

# 构建
cargo build                  # 调试构建
cargo build --release        # 发布构建
cargo build --all-targets    # 构建所有目标（bin, test, bench）
cargo check                  # 快速检查（不生成代码）

# 测试
cargo test                   # 运行所有测试
cargo test --lib             # 仅库测试
cargo test --doc             # 文档测试
cargo test <filter>          # 运行匹配的测试

# 依赖管理
cargo add serde              # 添加依赖
cargo add --dev mockall      # 添加开发依赖
cargo update                 # 更新 Cargo.lock
cargo tree                   # 显示依赖树
cargo tree -d                # 显示重复依赖

# 文档
cargo doc                    # 生成文档
cargo doc --open             # 生成并打开
cargo doc --no-deps          # 不生成依赖文档

# 其他工具
cargo fmt                    # 格式化代码
cargo clippy                 # 运行 linter
cargo fix                    # 自动修复警告
cargo bench                  # 运行基准测试
cargo publish                # 发布到 crates.io
cargo install <crate>        # 安装二进制 crate
```

### 代码质量工具

```bash
# Clippy：Rust 的 linter
cargo clippy
cargo clippy --all-targets --all-features
cargo clippy -- -D warnings  # 将警告视为错误

# 配置 .clippy.toml 或 clippy.toml
# allow = ["some_lint"]
# warn = ["another_lint"]
# deny = ["dangerous_lint"]

# rustfmt：代码格式化
cargo fmt
cargo fmt -- --check         # CI 中使用

# 配置 rustfmt.toml
# edition = "2024"
# max_width = 100
# tab_spaces = 4
```

### 形式化验证工具

```rust
// MIRI：检测未定义行为
// cargo miri test

// 使用示例
unsafe fn undefined_behavior_demo() {
    let ptr = std::ptr::null::<i32>();
    // let _ = *ptr;  // MIRI 会检测到此 UB
}

// Prusti：基于契约的验证
// #[requires(x > 0)]
// #[ensures(result > x)]
// fn double(x: i32) -> i32 { x * 2 }

// Kani：模型检查器
// #[kani::proof]
// fn check_add() {
//     let x: u32 = kani::any();
//     let y: u32 = kani::any();
//     kani::assume(x < 100 && y < 100);
//     assert!(x + y < 200);
// }
```

---

## 与 research_notes 的链接

| 研究笔记 | 路径 |
| :--- | :--- |
| 编译器优化 | [../../research_notes/experiments/compiler_optimizations.md](../../research_notes/experiments/compiler_optimizations.md) |
| 性能基准 | [../../research_notes/experiments/performance_benchmarks.md](../../research_notes/experiments/performance_benchmarks.md) |
| 形式化验证工具 | [../../research_notes/TOOLS_GUIDE.md](../../research_notes/TOOLS_GUIDE.md) |
| 质量检查清单 | [../../research_notes/QUALITY_CHECKLIST.md](../../research_notes/QUALITY_CHECKLIST.md) |
