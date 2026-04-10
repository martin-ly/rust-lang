# Rust 1.96 全面迁移计划

> 制定日期: 2026-04-10
> 当前 Rust 版本: 1.94.1
> 目标 Rust 版本: 1.96.0 (预计 2026-05-28 发布)
> 项目 Edition: 2024

---

## 📋 执行摘要

本计划基于 Rust 1.95/1.96 的最新语言特性，结合网络权威内容，全面梳理本项目的更新任务。
Rust 1.96 带来了多项重要改进，包括新的 Range 类型、`if let` guards、LLVM 21 升级等。

---

## 🎯 Phase 1: Rust 工具链升级 (1.94.1 → 1.96)

### 1.1 工具链版本更新

**文件:** `rust-toolchain.toml`

```toml
[toolchain]
channel = "1.96.0"  # 或 "stable" (当 1.96 成为 stable 后)
components = ["rustfmt", "clippy", "rust-analyzer"]
targets = [
    "x86_64-unknown-linux-gnu",
    "x86_64-pc-windows-msvc",
    "aarch64-unknown-linux-gnu",  # 新增: ARM64 Linux 支持
]
profile = "default"
```

### 1.2 项目最低版本要求更新

**文件:** `Cargo.toml` (workspace root)

```toml
[workspace.package]
rust-version = "1.96.0"  # 从 1.94.1 升级
```

**影响范围:** 所有 crate 的 `Cargo.toml`

---

## 🚀 Phase 2: 语言特性迁移

### 2.1 Rust 1.95 新特性采用

#### 2.1.1 `if let` Guards on Match Arms (稳定化)

**特性描述:** 在 match arms 上使用 `if let` guards

**迁移示例:**

```rust
// 迁移前 (Rust 1.94)
match value {
    Some(x) => {
        if let Ok(y) = parse(x) {
            handle(y);
        }
    }
    _ => {}
}

// 迁移后 (Rust 1.95+)
match value {
    Some(x) if let Ok(y) = parse(x) => handle(y),
    _ => {}
}
```

**任务清单:**

- [ ] 搜索项目中 match + if let 组合模式
- [ ] 重构为新的 guard 语法
- [ ] 更新相关文档和注释

#### 2.1.2 `RangeInclusive` 和 `RangeInclusiveIter` (稳定化)

**特性描述:** 新的 RangeInclusive 类型和迭代器

**迁移示例:**

```rust
use std::ops::RangeInclusive;

// 新的 API
let range: RangeInclusive<i32> = 1..=10;
let iter = range.into_iter(); // RangeInclusiveIter

// 在算法 crate 中的应用
fn process_range(range: RangeInclusive<usize>) {
    for i in range {
        // ...
    }
}
```

**任务清单:**

- [ ] 更新 `c08_algorithms` crate 中的范围处理
- [ ] 检查并替换自定义 RangeInclusive 实现

### 2.2 Rust 1.96 新特性采用

#### 2.2.1 New Range Types (稳定化)

**特性描述:** 新的 Range 类型和迭代器

```rust
// 新的 RangeToInclusive 类型
use std::ops::RangeToInclusive;

let range: RangeToInclusive<i32> = ..=10;
```

**任务清单:**

- [ ] 评估现有代码中 Range 类型的使用
- [ ] 采用新的 Range 类型优化代码

#### 2.2.2 PinCoerceUnsized 要求 Deref

**影响:** 使用 `Pin` 和 `CoerceUnsized` 的代码可能需要调整

**任务清单:**

- [ ] 搜索 `Pin<` 使用情况
- [ ] 检查 `CoerceUnsized` 实现
- [ ] 验证异步代码中的 Pin 使用

#### 2.2.3 元组元素 Coercion Site

**特性描述:** 元组元素现在始终是 coercion site

**迁移示例:**

```rust
// 现在可以自动 coercion
let x: (i32, i64) = (1, 2i32); // i32 -> i64 coercion 在元组元素上
```

---

## 📦 Phase 3: 依赖生态系统升级

### 3.1 核心依赖升级计划

| 依赖 | 当前版本 | 目标版本 | 备注 |
|------|----------|----------|------|
| tokio | 1.51.0 | 1.55+ | 跟进 Rust 1.96 |
| serde | 1.0.228 | 1.0.240+ | 新特性支持 |
| axum | 0.8.7 | 0.9+ | Rust 1.96 兼容 |
| hyper | 1.9.0 | 1.12+ | 性能改进 |
| rustls | 0.23.37 | 0.25+ | 安全更新 |
| hashbrown | 0.17.0 | 0.18+ | 最新稳定版 |
| indexmap | 2.14.0 | 2.15+ | 性能改进 |
| clap | 4.5.61 | 4.7+ | 新特性 |
| tracing | 0.1.43 | 0.1.50+ | 日志改进 |
| regex | - | 1.12+ | 性能优化 |

### 3.2 WebAssembly 目标更新

**Rust 1.96 变化:**

- 停止向 wasm 目标传递 `--allow-undefined`
- 需要检查 wasm-bindgen 版本兼容性

**任务清单:**

- [ ] 更新 `c12_wasm` crate 配置
- [ ] 升级 `wasm-bindgen` 到 0.2.120+
- [ ] 验证 `js-sys` 和 `wasm-bindgen-futures` 兼容性

### 3.3 Cargo.toml 依赖更新脚本

```bash
# 自动化依赖更新
cargo update
cargo outdated  # 使用 cargo-outdated 检查过时依赖
cargo audit     # 安全审计
```

---

## 🔧 Phase 4: 代码现代化重构

### 4.1 Lint 配置更新

**文件:** `Cargo.toml` (workspace lints)

```toml
[workspace.lints.rust]
unsafe_code = "forbid"
double_negations = "warn"           # 新增: Rust 1.86+
irrefutable_let_patterns = "allow"  # 更新: Rust 1.95+

[workspace.lints.clippy]
all = { level = "warn", priority = -1 }
correctness = "deny"
suspicious = "warn"
complexity = "warn"
perf = "warn"
style = "warn"
# 新增 lints
match_wildcard_for_single_variants = "warn"
redundant_closure_for_method_calls = "warn"
```

### 4.2 常量上下文改进 (Rust 1.95+)

**特性:** Const blocks 不再用于隐式常量提升

**迁移任务:**

- [ ] 检查 `const {}` 块的使用
- [ ] 确保显式 `const` 关键字使用

### 4.3 内联汇编更新 (Rust 1.95+)

**特性:** PowerPC 内联汇编稳定化

**任务:** (如项目使用内联汇编)

- [ ] 评估是否采用 PowerPC 内联汇编
- [ ] 更新 `c11_macro_system` 中的相关文档

---

## ⚙️ Phase 5: 构建系统与 CI/CD 优化

### 5.1 LLVM 21 升级准备

**Rust 1.96 更新:** 最低外部 LLVM 版本提升到 21

**任务清单:**

- [ ] 更新 CI 中的 LLVM 版本
- [ ] 验证自定义构建脚本
- [ ] 检查 bindgen 配置

### 5.2 Profile 配置优化

**文件:** `Cargo.toml`

```toml
[profile.release]
# Rust 1.96 推荐配置
opt-level = 3
lto = "fat"
codegen-units = 1
strip = "symbols"
panic = "abort"
# 新增: 分割调试信息 (macOS)
split-debuginfo = "packed"  # 仅在 macOS 上有效

[profile.dev]
opt-level = 0
debug = 1
debug-assertions = true
overflow-checks = true
incremental = true
codegen-units = 256
panic = "unwind"
# 新增: 更快的编译选项
rustflags = ["-C", "link-arg=-fuse-ld=lld"]  # 使用 lld 链接器
```

### 5.3 GitHub Actions 更新

**文件:** `.github/workflows/*.yml`

```yaml
# 更新 Rust 版本矩阵
strategy:
  matrix:
    rust:
      - "1.96.0"      # MSRV
      - "stable"
      - "beta"
      - "nightly"
```

---

## 📝 Phase 6: 文档与示例更新

### 6.1 文档更新任务

- [ ] 更新 README.md 中的 Rust 版本要求
- [ ] 更新 CONTRIBUTING.md 中的开发环境说明
- [ ] 更新各 crate 文档中的版本信息
- [ ] 添加 Rust 1.96 新特性的使用示例

### 6.2 示例代码更新

**文件:** `examples/` 和 `exercises/`

```rust
// 添加 if let guards 示例
pub fn match_with_if_let_guard() {
    let data = vec![Some(1), None, Some(2)];

    for item in data {
        match item {
            Some(x) if let Ok(parsed) = x.to_string().parse::<i32>() => {
                println!("Parsed: {}", parsed);
            }
            _ => println!("No match"),
        }
    }
}
```

### 6.3 rustdoc 配置更新

**Rust 1.95 新特性:**

- "hide deprecated items" 设置
- 不稳定的项目在搜索结果中排名降低

---

## ✅ Phase 7: 测试与质量保证

### 7.1 测试策略

```bash
# 完整测试流程
cargo test --workspace
cargo test --workspace --release
cargo clippy --workspace --all-targets
cargo fmt --check
cargo doc --workspace --no-deps

# Miri 测试 (unsafe 代码)
cargo +nightly miri test

# 基准测试
cargo bench --workspace
```

### 7.2 兼容性检查

```bash
# 检查 MSRV
cargo msrv verify

# 检查废弃 API
cargo audit

# 检查未使用依赖
cargo udeps
```

---

## 📅 执行时间表

| 阶段 | 任务 | 预计时间 | 优先级 |
|------|------|----------|--------|
| Phase 1 | 工具链升级 | 1 天 | P0 |
| Phase 2 | 语言特性迁移 | 3-5 天 | P1 |
| Phase 3 | 依赖升级 | 2-3 天 | P1 |
| Phase 4 | 代码重构 | 5-7 天 | P2 |
| Phase 5 | CI/CD 更新 | 1-2 天 | P2 |
| Phase 6 | 文档更新 | 2-3 天 | P3 |
| Phase 7 | 测试验证 | 2-3 天 | P0 |

**总计: 16-24 天**

---

## 🔍 关键变更检查清单

### 破坏性变更检查

- [ ] JSON target specs 去稳定化 (Rust 1.95)
- [ ] Const blocks 隐式提升行为改变
- [ ] `Eq::assert_receiver_is_total_eq` 废弃
- [ ] PinCoerceUnsized 现在要求 Deref

### 安全相关更新

- [ ] 检查所有 unsafe 代码块
- [ ] 验证 Miri 测试通过
- [ ] 运行 `cargo audit`

### 性能优化机会

- [ ] 采用新的 Range 类型优化迭代
- [ ] 利用元组 coercion 简化代码
- [ ] 更新 hashbrown 到最新版本

---

## 📚 参考资源

1. [Rust 1.95 Release Notes](https://github.com/rust-lang/rust/issues/154711)
2. [Rust 1.96 Release Notes](https://releases.rs/docs/1.96.0/)
3. [Rust 博客](https://blog.rust-lang.org/)
4. [Rust Edition Guide](https://doc.rust-lang.org/edition-guide/)
5. [Cargo Book](https://doc.rust-lang.org/cargo/)

---

## 🆘 回滚计划

如果在迁移过程中遇到无法解决的问题:

1. 保持 `rust-toolchain.toml` 可切换
2. 保留旧版本 Cargo.lock 备份
3. 使用 `cargo +1.94.1` 临时回滚

---

*最后更新: 2026-04-10*
