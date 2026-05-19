# Rust 生产安全最佳实践

> **定位**: Rust 项目安全开发与部署指南
> **版本**: Rust 1.95.0+ / Edition 2024
> **适用场景**: 生产服务、安全关键应用、开源项目维护

---

## 📋 目录

- [Rust 生产安全最佳实践](#rust-生产安全最佳实践)
  - [📋 目录](#-目录)
  - [🎯 安全开发原则](#-安全开发原则)
  - [🔐 依赖安全](#-依赖安全)
    - [cargo-audit](#cargo-audit)
    - [依赖最小化](#依赖最小化)
  - [🛡️ 代码安全](#️-代码安全)
    - [Unsafe 代码审计](#unsafe-代码审计)
    - [输入验证](#输入验证)
    - [Secret 管理](#secret-管理)
  - [📦 构建安全](#-构建安全)
    - [Reproducible Builds](#reproducible-builds)
    - [Supply Chain](#supply-chain)
  - [🚀 部署安全](#-部署安全)
  - [🔗 参考资源](#-参考资源)

---

## 🎯 安全开发原则

```
┌─────────────────────────────────────────────┐
│          Rust 安全金字塔                      │
├─────────────────────────────────────────────┤
│                                               │
│     🛡️ 编译期保证                             │
│        所有权、借用、类型系统                    │
│        ─────────────────────                 │
│     🔍 静态分析                               │
│        Clippy、Miri、Semgrep                   │
│        ─────────────────────                 │
│     🧪 动态测试                               │
│        Fuzzing、Property Testing               │
│        ─────────────────────                 │
│     🏗️ 构建安全                               │
│        可复现构建、供应链验证                   │
│        ─────────────────────                 │
│     🚀 运行安全                               │
│        沙箱、能力系统、监控                     │
│                                               │
└─────────────────────────────────────────────┘
```

---

## 🔐 依赖安全

### cargo-audit

```bash
# 安装
cargo install cargo-audit

# 扫描已知漏洞
cargo audit

# 在 CI 中使用
cargo audit --deny warnings
```

**输出示例**:

```
Crate:     regex
Version:   1.5.4
Title:     Regexes with large repetitions on empty sub-expressions take a very long time
Date:      2022-03-08
ID:        RUSTSEC-2022-0013
URL:       https://rustsec.org/advisories/RUSTSEC-2022-0013
Solution:  upgrade to >= 1.5.5
```

### 依赖最小化

```toml
# Cargo.toml - 最小化依赖
[dependencies]
# ✅ 优选: 小而专注的库
serde = { version = "1", default-features = false }

# ❌ 避免: 大而全的依赖
# 不要引入整个框架只为了一个函数

[profile.release]
# 去除 panic 信息减少攻击面
panic = "abort"
```

---

## 🛡️ 代码安全

### Unsafe 代码审计

```rust
#![forbid(unsafe_code)] // 最佳实践: 默认禁止 unsafe

// 如果必须使用 unsafe，隔离到最小模块
mod unsafe_impl {
    /// SAFETY: 调用者必须保证 ptr 有效且对齐
    pub unsafe fn read_unchecked<T>(ptr: *const T) -> T {
        // ...
    }
}
```

**审计清单**:

- [ ] 每个 `unsafe` 块都有 `// SAFETY:` 注释
- [ ] Miri 通过测试
- [ ] 边界条件覆盖
- [ ] 不依赖未定义行为

### 输入验证

```rust
use regex::Regex;

/// 验证用户输入（防止注入攻击）
pub fn validate_username(input: &str) -> Result<String, ValidationError> {
    // 长度限制
    if input.len() > 64 {
        return Err(ValidationError::TooLong);
    }

    // 字符白名单
    let valid = Regex::new(r"^[a-zA-Z0-9_-]+$").unwrap();
    if !valid.is_match(input) {
        return Err(ValidationError::InvalidChars);
    }

    Ok(input.to_lowercase())
}
```

### Secret 管理

```rust
use zeroize::{Zeroize, ZeroizeOnDrop};

/// 自动清零的密钥类型
#[derive(Zeroize, ZeroizeOnDrop)]
pub struct SecretKey([u8; 32]);

impl SecretKey {
    pub fn new(bytes: [u8; 32]) -> Self {
        Self(bytes)
    }

    /// 仅暴露引用的使用窗口
    pub fn with_key<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&[u8; 32]) -> R,
    {
        f(&self.0)
    }
}

// SecretKey 离开作用域时自动 zeroize 内存
```

---

## 📦 构建安全

### Reproducible Builds

```toml
# .cargo/config.toml
[profile.release]
# 确保可复现构建
debug = false
lto = true
```

### Supply Chain

```bash
# 验证依赖签名
cargo vet

# 或使用 cargo-cyclonedx 生成 SBOM
cargo cyclonedx
```

---

## 🚀 部署安全

```dockerfile
# Dockerfile - 多阶段构建最小化攻击面
FROM rust:1.95 as builder
WORKDIR /app
COPY . .
RUN cargo build --release

# 运行时镜像 - 最小化基础镜像
FROM gcr.io/distroless/cc-debian12
COPY --from=builder /app/target/release/myapp /usr/local/bin/
USER nonroot:nonroot
ENTRYPOINT ["/usr/local/bin/myapp"]
```

**安全要点**:

- 使用 distroless 或 Alpine 镜像
- 以非 root 用户运行
- 只读文件系统
- 资源限制 (CPU/内存)

---

## 🔗 参考资源

- [Rust Secure Coding Guidelines](https://anixe.io/rust_secure_coding_guidelines/)
- [cargo-audit](https://github.com/RustSec/rustsec/tree/main/cargo-audit)
- [RustSec Advisory Database](https://rustsec.org/)
- [OWASP Rust Security](https://owasp.org/www-project-developer-guide/draft/foundational-technology-and-programming-languages/rust/)
- [项目 Miri 指南](../../docs/MIRI_GUIDE.md)

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-05-08
**状态**: ✅ 已完善
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
