# 2026年迁移指南

> **日期**: 2026-04-10
> **目标**: 从旧版Rust工具链迁移到最新生态

## 迁移清单

### 1. 工具链更新

```bash
# 更新Rust到1.96.0
rustup update stable
rustup default 1.96.0

# 安装/更新工具
rustup component add rustfmt clippy rust-analyzer
cargo install cargo-update cargo-tree cargo-outdated
```

### 2. 代码现代化

#### lazy_static → LazyLock

```rust
// 旧代码
use lazy_static::lazy_static;
lazy_static! {
    static ref CONFIG: String = load_config();
}

// 新代码
use std::sync::LazyLock;
static CONFIG: LazyLock<String> = LazyLock::new(|| load_config());
```

#### async-trait → 原生async trait

```rust
// 旧代码
#[async_trait::async_trait]
trait Storage {
    async fn read(&self) -> Vec<u8>;
}

// 新代码 (Rust 1.75+)
trait Storage {
    async fn read(&self) -> Vec<u8>;
}
```

#### 生成器 → gen关键字

```rust
// 旧代码 (不稳定特性)
#![feature(generators)]
|| { yield 1; }

// 新代码 (Edition 2024)
gen fn my_gen() -> i32 { yield 1; }
```

### 3. 配置更新

#### Cargo.toml

```toml
[package]
edition = "2024"  # 升级到2024
rust-version = "1.96"

[lints.clippy]
all = { level = "warn", priority = -1 }
correctness = "deny"

[lints.rust]
unused_tuple_struct_fields = "warn"
redundant_guards = "warn"
```

### 4. CI/CD更新

```yaml
# 更新actions版本
- uses: actions/checkout@v4
- uses: dtolnay/rust-toolchain@stable
  with:
    toolchain: "1.96.0"
    components: rustfmt, clippy
```

---

## Rust 1.96 迁移章节

### 概述

Rust 1.95/1.96 引入了多项重要特性，包括 `if let guards`、Range 类型改进、`PinCoerceUnsized` trait 和元组 coercion。本章节指导您从 1.94 平滑迁移到 1.96。

### 从 1.94 到 1.96 的完整步骤

#### 步骤 1: 环境准备

```bash
# 备份现有工具链
rustup toolchain install 1.94.0 --name backup-194

# 更新到最新稳定版
rustup update stable

# 验证版本
rustc --version  # 应显示 1.96.0 或更高
```

#### 步骤 2: 依赖更新

```bash
# 更新 Cargo.lock
cargo update

# 检查过期的依赖
cargo outdated

# 自动更新兼容版本
cargo update --aggressive
```

#### 步骤 3: 代码迁移

**3.1 启用新 Lint 规则**

在 `Cargo.toml` 中添加新的 lint 配置：

```toml
[lints.rust]
# 新的 lint 规则 (Rust 1.96)
unused_tuple_struct_fields = "warn"
redundant_guards = "warn"
opaque_hidden_inferred_bound = "warn"
```

**3.2 重构 if let 模式**

将嵌套的 `if let` 转换为守卫模式：

```rust
// 迁移前 (Rust 1.94)
match event {
    Event::Message(text) => {
        if let Some(user) = current_user {
            if user.is_active {
                process_message(&user, &text);
            }
        }
    }
    _ => {}
}

// 迁移后 (Rust 1.96)
match event {
    Event::Message(text)
        if let Some(user) = current_user
        && user.is_active =>
    {
        process_message(&user, &text);
    }
    _ => {}
}
```

**3.3 更新 Range 类型使用**

```rust
// 明确使用 RangeInclusive 替代手动边界检查
// 迁移前
for i in 0..11 {  // 意图包含 10
    if i == 10 { /* 特殊处理 */ }
}

// 迁移后
for i in 0..=10 {  // 更清晰
    // 处理逻辑
}
```

**3.4 更新 Pin 相关代码**

```rust
// 使用新的 PinCoerceUnsized trait
use std::pin::Pin;
use std::future::Future;

// 新的转换方式更简洁
fn box_future<T>(f: impl Future<Output = T> + 'static) -> Pin<Box<dyn Future<Output = T>>> {
    Box::pin(f)
}
```

#### 步骤 4: 测试验证

```bash
# 完整构建
cargo build --all-targets

# 运行测试套件
cargo test

# 运行 Clippy 检查
cargo clippy --all-targets --all-features

# 检查文档
cargo doc --no-deps

# 格式化检查
cargo fmt --check
```

#### 步骤 5: 持续集成更新

更新 `.github/workflows/ci.yml`：

```yaml
name: CI

on: [push, pull_request]

jobs:
  build:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Setup Rust
        uses: dtolnay/rust-toolchain@stable
        with:
          toolchain: "1.96.0"  # 更新到 1.96
          components: rustfmt, clippy

      - name: Cache dependencies
        uses: Swatinem/rust-cache@v2

      - name: Check formatting
        run: cargo fmt --check

      - name: Run Clippy
        run: cargo clippy --all-targets --all-features -- -D warnings

      - name: Build
        run: cargo build --all-targets

      - name: Test
        run: cargo test --all-features
```

### 常见问题

#### Q1: if let guards 导致编译错误？

**问题**: 使用 `if let` 守卫时出现 "expected `=>`, found `if`" 错误。

**解决**: 确保 Rust 版本 >= 1.95：

```bash
rustc --version
# 如果版本低于 1.95，更新工具链
rustup update stable
```

#### Q2: RangeInclusive 类型不匹配？

**问题**: `(0..=10)` 与 `Range<i32>` 类型不兼容。

**解决**: 明确使用 `RangeInclusive` 类型：

```rust
use std::ops::RangeInclusive;

fn process(r: RangeInclusive<i32>) { }

// 正确调用
process(0..=10);

// 或者明确标注类型
let range: RangeInclusive<i32> = 0..=10;
```

#### Q3: 新的 lint 警告导致 CI 失败？

**问题**: `unused_tuple_struct_fields` 等 lint 产生大量警告。

**解决**: 逐步修复或在 `Cargo.toml` 中配置：

```toml
[lints.rust]
# 暂时允许，后续逐步修复
unused_tuple_struct_fields = "allow"
redundant_guards = "allow"
```

#### Q4: Pin 转换失败？

**问题**: `Box::pin()` 结果无法转换为 trait object。

**解决**: 确保类型实现了必要的 trait：

```rust
use std::pin::Pin;
use std::future::Future;

// 确保返回类型正确
fn create_future() -> Pin<Box<dyn Future<Output = i32> + Send>> {
    Box::pin(async { 42 })
}
```

#### Q5: 元组 coercion 不生效？

**问题**: 预期的自动类型转换没有发生。

**解决**: 元组 coercion 有特定限制，尝试显式转换：

```rust
let narrow: (i8, i16) = (1, 2);
// 显式转换
let wide: (i32, i32) = (narrow.0 as i32, narrow.1 as i32);
```

### 版本兼容性表

| 特性 | 最低版本 | 说明 |
|------|----------|------|
| if let guards | 1.95 | match 守卫中的嵌套模式匹配 |
| Range 类型优化 | 1.95 | RangeInclusive 性能改进 |
| PinCoerceUnsized | 1.96 | Pin 类型的强制转换 |
| 元组 coercion | 1.96 | 元组类型自动转换 |
| 新 lint 规则 | 1.96 | 额外的代码质量检查 |

### 回滚指南

如果迁移遇到问题，可以回滚到 1.94：

```bash
# 切换回旧版本
rustup default 1.94.0

# 更新 Cargo.lock
cargo update

# 如果使用了新特性，需要回滚代码更改
git checkout -- .
```

---

## 参考资源

- [Rust 1.95 Release Notes](https://blog.rust-lang.org/)
- [Rust 1.96 Release Notes](https://blog.rust-lang.org/)
- [if let guards RFC](https://rust-lang.github.io/rfcs/2294-if-let-guard.html)
- [详细特性文档](./06_toolchain/19_rust_1.96_features.md)
- [特性速查表](./02_reference/quick_reference/rust_196_features_cheatsheet.md)

**详细指南**: [2026_RUST_ECOSYSTEM_COMPREHENSIVE_REVIEW.md](./2026_RUST_ECOSYSTEM_COMPREHENSIVE_REVIEW.md)
