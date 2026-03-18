# 2026年迁移指南

> **日期**: 2026-03-18
> **目标**: 从旧版Rust工具链迁移到最新生态

## 迁移清单

### 1. 工具链更新

```bash
# 更新Rust到1.94.0
rustup update stable
rustup default 1.94.0

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
rust-version = "1.94"

[lints.clippy]
all = { level = "warn", priority = -1 }
correctness = "deny"
```

### 4. CI/CD更新

```yaml
# 更新actions版本
- uses: actions/checkout@v4
- uses: dtolnay/rust-toolchain@stable
  with:
    toolchain: "1.94.0"
    components: rustfmt, clippy
```

---

**详细指南**: [2026_RUST_ECOSYSTEM_COMPREHENSIVE_REVIEW.md](./2026_RUST_ECOSYSTEM_COMPREHENSIVE_REVIEW.md)
