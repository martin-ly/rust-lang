# ❓ Rust 1.90 升级 FAQ

> **创建日期**: 2026-01-26
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已归档
---

## 📑 目录

- [❓ Rust 1.90 升级 FAQ](#-rust-190-升级-faq)
  - [📑 目录](#-目录)
  - [1. 升级相关](#1-升级相关)
    - [Q1.1: 为什么要升级到 Rust 1.90？](#q11-为什么要升级到-rust-190)
    - [Q1.2: 什么时候应该升级？](#q12-什么时候应该升级)
    - [Q1.3: 升级需要多长时间？](#q13-升级需要多长时间)
  - [2. 迁移指南](#2-迁移指南)
    - [Q2.1: 如何升级到 Rust 1.90？](#q21-如何升级到-rust-190)
      - [步骤 1: 更新 Rust 工具链](#步骤-1-更新-rust-工具链)
      - [步骤 2: 更新 Cargo.toml](#步骤-2-更新-cargotoml)
      - [步骤 3: 处理编译警告](#步骤-3-处理编译警告)
      - [步骤 4: 运行测试](#步骤-4-运行测试)
      - [步骤 5: 更新文档](#步骤-5-更新文档)
    - [Q2.2: 如何处理编译错误？](#q22-如何处理编译错误)
      - [错误 1: `mismatched_lifetime_syntaxes` lint 警告](#错误-1-mismatched_lifetime_syntaxes-lint-警告)
      - [错误 2: const 函数使用](#错误-2-const-函数使用)
    - [Q2.3: 如何处理依赖兼容性问题？](#q23-如何处理依赖兼容性问题)
  - [3. 新特性说明](#3-新特性说明)
    - [Q3.1: Rust 1.90 有哪些重大变化？](#q31-rust-190-有哪些重大变化)
      - [🔧 编译器改进](#-编译器改进)
      - [📦 标准库更新](#-标准库更新)
      - [🔍 Lint 改进](#-lint-改进)
    - [Q3.2: 如何使用新的稳定 API？](#q32-如何使用新的稳定-api)
      - [checked_sub_signed()](#checked_sub_signed)
      - [const 函数增强](#const-函数增强)
      - [const 数学函数](#const-数学函数)
  - [4. 常见问题](#4-常见问题)
    - [Q4.1: rust_189\_\*.rs 文件的作用是什么？](#q41-rust_189_rs-文件的作用是什么)
    - [Q4.2: 是否需要删除 rust_189\_\*.rs 文件？](#q42-是否需要删除-rust_189_rs-文件)
    - [Q4.3: Edition 2024 和 Rust 1.90 的关系？](#q43-edition-2024-和-rust-190-的关系)
    - [Q4.4: 如何在 CI/CD 中使用 Rust 1.90？](#q44-如何在-cicd-中使用-rust-190)
      - [GitHub Actions](#github-actions)
      - [GitLab CI](#gitlab-ci)
  - [5. 故障排除](#5-故障排除)
    - [Q5.1: 链接速度没有提升怎么办？](#q51-链接速度没有提升怎么办)
    - [Q5.2: 遇到 const 函数错误怎么办？](#q52-遇到-const-函数错误怎么办)
      - [情况 1: 函数不支持 const](#情况-1-函数不支持-const)
      - [情况 2: 使用了不稳定特性](#情况-2-使用了不稳定特性)
    - [Q5.3: lint 警告太多怎么办？](#q53-lint-警告太多怎么办)
  - [6. 参考资源](#6-参考资源)
    - [官方文档](#官方文档)
    - [本项目文档](#本项目文档)
    - [社区资源](#社区资源)
  - [🆘 还有问题？](#-还有问题)

---

## 1. 升级相关

### Q1.1: 为什么要升级到 Rust 1.90？

**A**: Rust 1.90 带来了多项重要改进：

✅ **性能提升**

- LLD 链接器在 Linux x86_64 上默认启用
- 链接速度提升约 **2倍**
- 增量编译优化

✅ **新功能**

- 多个新的稳定 API
- const 函数增强
- 更好的类型推断

✅ **开发体验**

- 新的 lint 检查
- 改进的错误信息
- 更好的生命周期推断

✅ **生态系统**

- 支持 Edition 2024
- 与最新工具链兼容

### Q1.2: 什么时候应该升级？

**A**: 建议在以下情况升级：

✅ **立即升级**（推荐）

- 新项目或正在开发的项目
- 需要 Rust 1.90 新特性的项目
- 追求编译性能优化的项目

⚠️ **计划升级**

- 大型生产项目（先在测试环境验证）
- 依赖较多的项目（先检查依赖兼容性）

⏸️ **暂缓升级**

- 稳定运行的生产系统（等待项目维护窗口）
- 使用了大量 nightly 特性的项目

### Q1.3: 升级需要多长时间？

**A**: 取决于项目规模：

| 项目规模     | 预计时间  | 主要工作                   |
| :--- | :--- | :--- || **小型项目** | 10-30分钟 | 更新 Cargo.toml，处理 lint |
| **中型项目** | 1-3小时   | 依赖更新，测试验证         |
| **大型项目** | 半天-1天  | 全面测试，性能验证         |

---

## 2. 迁移指南

### Q2.1: 如何升级到 Rust 1.90？

**A**: 遵循以下步骤：

#### 步骤 1: 更新 Rust 工具链

```bash
# 更新 rustup
rustup update

# 验证版本
rustc --version
# 应显示: rustc 1.90.0 或更高版本
```

#### 步骤 2: 更新 Cargo.toml

```toml
[package]
name = "your_project"
version = "0.1.0"
edition = "2024"           # 更新 edition
rust-version = "1.90"      # 添加或更新 rust-version

[dependencies]
# 更新依赖到兼容 Rust 1.90 的版本
```

#### 步骤 3: 处理编译警告

```bash
# 检查警告
cargo check

# 修复 lint 警告
cargo clippy --fix
```

#### 步骤 4: 运行测试

```bash
# 运行所有测试
cargo test

# 运行基准测试（如果有）
cargo bench
```

#### 步骤 5: 更新文档

- 更新 README.md 中的 Rust 版本要求
- 更新 CI/CD 配置
- 更新部署文档

### Q2.2: 如何处理编译错误？

**A**: 常见编译错误及解决方案：

#### 错误 1: `mismatched_lifetime_syntaxes` lint 警告

```rust
// ❌ 旧代码（会触发警告）
fn items(scores: &[u8]) -> std::slice::Iter<'_, u8> {
    scores.iter()
}

// ✅ 修复方案
fn items<'a>(scores: &'a [u8]) -> std::slice::Iter<'a, u8> {
    scores.iter()
}
```

#### 错误 2: const 函数使用

```rust
// ✅ Rust 1.90 中可用
const fn example() -> i32 {
    let mut x = [1, 2, 3];
    x.reverse();  // 现在可以在 const 中使用
    x[0]
}
```

### Q2.3: 如何处理依赖兼容性问题？

**A**: 依赖更新策略：

1. **检查依赖兼容性**

   ```bash
   cargo update --dry-run
   ```

2. **逐个更新主要依赖**

   ```bash
   cargo update -p <dependency_name>
   ```

3. **解决版本冲突**
   - 查看 `Cargo.lock` 中的版本
   - 使用 `cargo tree` 分析依赖树
   - 必要时固定特定版本

4. **测试验证**

   ```bash
   cargo test --all-features
   ```

---

## 3. 新特性说明

### Q3.1: Rust 1.90 有哪些重大变化？

**A**: Rust 1.90 的主要变化：

#### 🔧 编译器改进

1. **LLD 链接器默认启用** (Linux x86_64)
   - 链接速度提升约 2倍
   - 内存使用更优化

2. **编译性能优化**
   - 增量编译改进
   - 并行化优化

#### 📦 标准库更新

1. **新增 API**
   - `u{n}::checked_sub_signed()` - 带符号减法检查
   - `u{n}::overflowing_sub_signed()` - 溢出检测减法
   - `u{n}::saturating_sub_signed()` - 饱和减法
   - `u{n}::wrapping_sub_signed()` - 环绕减法

2. **const 函数增强**
   - `<[T]>::reverse()` - 数组反转
   - `f32/f64::floor()` - 向下取整
   - `f32/f64::ceil()` - 向上取整
   - `f32/f64::trunc()` - 截断
   - `f32/f64::fract()` - 小数部分
   - `f32/f64::round()` - 四舍五入

3. **trait 实现扩展**
   - `IntErrorKind` 实现 `Copy` 和 `Hash`
   - `CStr`, `CString`, `Cow<CStr>` 的 `PartialEq` 实现

#### 🔍 Lint 改进

1. **mismatched_lifetime_syntaxes**
   - 默认启用
   - 检查生命周期语法一致性
   - 提高代码可读性

### Q3.2: 如何使用新的稳定 API？

**A**: 使用示例：

#### checked_sub_signed()

```rust
// 无符号数与有符号数安全减法
let x: u32 = 10;
let y: i32 = -5;

match x.checked_sub_signed(y) {
    Some(result) => println!("结果: {}", result), // 15
    None => println!("溢出"),
}
```

#### const 函数增强

```rust
const fn process_array<const N: usize>(mut arr: [i32; N]) -> [i32; N] {
    arr.reverse();  // 现在可以在 const 中使用
    arr
}

const REVERSED: [i32; 5] = process_array([1, 2, 3, 4, 5]);
// REVERSED = [5, 4, 3, 2, 1]
```

#### const 数学函数

```rust
const fn calculate() -> f64 {
    let x = 3.7;
    x.floor()  // 现在可以在 const 中使用
}

const RESULT: f64 = calculate();  // 3.0
```

---

## 4. 常见问题

### Q4.1: rust*189*\*.rs 文件的作用是什么？

**A**: 这些是 **历史版本示例文件**：

**用途**:

- 📚 展示 Rust 1.89 特性
- 🔄 对比学习新旧版本差异
- 📖 保留历史特性文档

**使用建议**:

- ✅ 用于学习和参考
- ✅ 对比 1.89 和 1.90 的差异
- ❌ 不要在新项目中直接使用
- ✅ 实际项目使用 Rust 1.90 特性

**版本标识**:
每个 `rust_189_*.rs` 文件头部都有清晰的版本说明：

```rust
//! # Rust 1.89 特性示例 (历史版本)
//!
//! ⚠️ **注意**: 本示例针对 Rust 1.89 版本编写，
//! 部分特性在 Rust 1.90 中已有更新。
//!
//! ## Rust 1.90 主要更新
//! ...
```

### Q4.2: 是否需要删除 rust*189*\*.rs 文件？

**A**: **不需要删除**，建议保留：

**保留原因**:

- 📖 作为历史参考
- 🔄 便于版本对比
- 📚 学习资源
- 🗂️ 已归档到 `docs/archives/`

**清理建议**:
如果确实需要清理：

1. 先确认团队不再需要参考
2. 备份到 Git 历史中
3. 考虑迁移到单独的示例仓库

### Q4.3: Edition 2024 和 Rust 1.90 的关系？

**A**: 两者密切相关但不同：

| 特性         | Rust 1.90  | Edition 2024      |
| :--- | :--- | :--- || **类型**     | 编译器版本 | 语言版次          |
| **发布时间** | 2025年9月  | 2024年            |
| **兼容性**   | 向后兼容   | 可能有破坏性变更  |
| **启用方式** | 自动       | Cargo.toml 中指定 |

**配置方式**:

```toml
[package]
edition = "2024"       # 启用 Edition 2024
rust-version = "1.90"  # 要求 Rust 1.90+
```

### Q4.4: 如何在 CI/CD 中使用 Rust 1.90？

**A**: CI/CD 配置示例：

#### GitHub Actions

```yaml
name: CI

on: [push, pull_request]

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3

      - name: Install Rust
        uses: actions-rs/toolchain@v1
        with:
          toolchain: 1.90.0
          override: true
          components: rustfmt, clippy

      - name: Check
        run: cargo check --all-features

      - name: Test
        run: cargo test --all-features

      - name: Clippy
        run: cargo clippy -- -D warnings
```

#### GitLab CI

```yaml
rust-test:
  image: rust:1.90
  script:
    - cargo check
    - cargo test
    - cargo clippy -- -D warnings
```

---

## 5. 故障排除

### Q5.1: 链接速度没有提升怎么办？

**A**: 检查 LLD 链接器是否启用：

1. **检查系统**

   ```bash
   # LLD 仅在 Linux x86_64 上默认启用
   uname -m  # 应显示 x86_64
   ```

2. **手动启用** (其他平台)

   ```toml
   # .cargo/config.toml
   [target.x86_64-unknown-linux-gnu]
   linker = "clang"
   rustflags = ["-C", "link-arg=-fuse-ld=lld"]
   ```

3. **验证**

   ```bash
   cargo build -v 2>&1 | grep -i lld
   ```

### Q5.2: 遇到 const 函数错误怎么办？

**A**: 常见情况：

#### 情况 1: 函数不支持 const

```rust
// ❌ 错误示例
const fn example() {
    println!("Hello");  // println! 不支持 const
}

// ✅ 解决方案
fn example() {
    println!("Hello");
}
```

#### 情况 2: 使用了不稳定特性

```rust
// 确保使用的是稳定的 const 函数
// 查看文档确认函数是否 const 稳定
```

### Q5.3: lint 警告太多怎么办？

**A**: 分步处理：

1. **按优先级处理**

   ```bash
   # 只显示错误
   cargo clippy -- -D warnings

   # 逐个修复 lint
   cargo clippy --fix
   ```

2. **临时允许特定 lint** (不推荐)

   ```rust
   #[allow(clippy::specific_lint)]
   fn my_function() { }
   ```

3. **配置 clippy**

   ```toml
   # clippy.toml
   too-many-arguments-threshold = 10
   ```

---

## 6. 参考资源

### 官方文档

- 📖 [Rust 1.90.0 Release Notes](https://blog.rust-lang.org/2025/09/18/Rust-1.90.0/)
- 📖 [Rust Edition Guide](https://doc.rust-lang.org/edition-guide/)
- 📖 [Rust API Documentation](https://doc.rust-lang.org/std/)

### 本项目文档

- 📄 [主报告](RUST_190_CONTENT_ALIGNMENT_REPORT_2025_10_26.md)
- 📄 [术语表](RUST_190_GLOSSARY.md)
- 📄 [Phase 2 完成报告](RUST_190_PHASE2_完成报告_2025_10_26.md)
- 📄 [完整会话总结](RUST_190_完整会话总结_2025_10_26.md)

### 社区资源

- 💬 [Rust Users Forum](https://users.rust-lang.org/)
- 💬 [Rust Discord](https://discord.gg/rust-lang)
- 📚 [This Week in Rust](https://this-week-in-rust.org/)

---

## 🆘 还有问题？

如果本 FAQ 没有回答您的问题，请：

1. 📖 查阅 [主报告](RUST_190_CONTENT_ALIGNMENT_REPORT_2025_10_26.md)
2. 📖 查阅 [术语表](RUST_190_GLOSSARY.md)
3. 💬 在项目 issue 中提问
4. 💬 访问 Rust 官方论坛

---

**文档维护**: 本 FAQ 会持续更新
**最后更新**: 2025-10-26
**版本**: 1.0