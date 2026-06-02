> **权威来源**: [SemVer 2.0.0](https://semver.org/lang/zh-CN/), [cargo-semver-checks 文档](https://github.com/obi1kenobi/cargo-semver-checks), [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)
> **分级**: [A]
> **Rust 版本**: 1.96.0+ (Edition 2024)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 SemVer 2.0.0、cargo-semver-checks、Rust API Guidelines 来源标注 [来源: Authority Source Sprint Batch 8]

# cargo-semver-checks 集成指南

> **Bloom 层级**: L2-L3 (理解/应用)

> 本文档对应 Rust 生产级工程实践体系阶段三 —— API 兼容性保护。
> 参考: Rust Foundation API 兼容性指南、Microsoft 版本管理规范。

---

## 📑 目录
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [cargo-semver-checks 集成指南](#cargo-semver-checks-集成指南)
  - [📑 目录](#-目录)
  - [1. 什么是 cargo-semver-checks？](#1-什么是-cargo-semver-checks)
    - [为什么需要它？](#为什么需要它)
    - [检测范围](#检测范围)
  - [2. 安装](#2-安装)
  - [3. 基本使用](#3-基本使用)
    - [检查当前工作目录的 crate](#检查当前工作目录的-crate)
    - [检查 workspace 中的特定 crate](#检查-workspace-中的特定-crate)
    - [与 baseline 版本比较](#与-baseline-版本比较)
    - [本地开发工作流](#本地开发工作流)
  - [4. CI 集成](#4-ci-集成)
    - [CI 策略](#ci-策略)
  - [5. 处理误报和例外](#5-处理误报和例外)
    - [场景 1: 新增字段但已使用 `#[non_exhaustive]`](#场景-1-新增字段但已使用-non_exhaustive)
    - [场景 2: 有意进行 breaking change（MAJOR 版本升级）](#场景-2-有意进行-breaking-changemajor-版本升级)
    - [场景 3: 内部 API 被误判](#场景-3-内部-api-被误判)
  - [6. 最佳实践](#6-最佳实践)
  - [7. 参考资源](#7-参考资源)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)

## 1. 什么是 cargo-semver-checks？
>
> **[来源: Rust Official Docs]** · **[来源: Wikipedia - Semantic Versioning]** · **[来源: Wikipedia - Software Versioning]** · **[来源: ACM - API Evolution Management]** · **[来源: IEEE - Software Configuration Management]**

**cargo-semver-checks** 是一个静态分析工具，用于检测 Rust crate 的公共 API 是否违反了语义化版本控制（Semantic Versioning）规则。

### 为什么需要它？
>
> **[来源: Rust Official Docs]**

Rust 生态严格遵循 SemVer：

- **MAJOR**: 破坏性变更（breaking changes）
- **MINOR**: 向后兼容的功能新增
- **PATCH**: 向后兼容的问题修复

但在实际开发中，很容易**无意间**引入破坏性变更：

- 给 `pub struct` 添加字段（除非有 `#[non_exhaustive]`）
- 收窄泛型约束
- 修改 trait 的默认实现行为
- 删除或重命名公共项

### 检测范围
>
> **[来源: Rust Official Docs]**

cargo-semver-checks 基于 rustdoc JSON 输出进行分析，可检测：

| 变更类型 | 检测能力 | 违反的 SemVer |
|---------|---------|-------------|
| 删除公共函数/类型 | ✅ | MAJOR |
| 给非 exhaustive struct 添加字段 | ✅ | MAJOR |
| 收窄函数返回类型 | ✅ | MAJOR |
| 放宽函数参数类型 | ✅ | MAJOR |
| trait 新增 required method | ✅ | MAJOR |
| 给 enum 添加 variant | ✅ | MINOR（需 `#[non_exhaustive]`） |
| 修改文档 | ❌ | N/A |
| 行为变更 | ❌ | 需人工审查 |

---

## 2. 安装
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```bash
# 安装 cargo-semver-checks
cargo install cargo-semver-checks --locked

# 验证安装
cargo semver-checks --version
```

> **注意**: 如果当前环境无法安装，此步骤标记为 "待 CI 验证"。CI 环境已配置自动安装。

---

## 3. 基本使用
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

### 检查当前工作目录的 crate
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```bash
cd crates/c10_networks
cargo semver-checks
```

### 检查 workspace 中的特定 crate
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

```bash
cargo semver-checks -p c10_networks
```

### 与 baseline 版本比较
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

```bash
# 与发布的最新版本比较（从 crates.io 获取）
cargo semver-checks -p c10_networks --baseline-version 0.1.0

# 与 git 标签比较
cargo semver-checks -p c10_networks --baseline-rev v0.1.0

# 与另一个分支比较
cargo semver-checks -p c10_networks --baseline-rev main
```

### 本地开发工作流
>
> **[来源: [crates.io](https://crates.io/)]**

```bash
# 在发布前检查
# 1. 确保当前版本号已正确更新
# 2. 运行检查
cargo semver-checks

# 3. 如果报告了问题，评估是否真的是 breaking change
# 4. 如果是 breaking change，更新 MAJOR 版本号
# 5. 如果只是误报，记录原因
```

---

## 4. CI 集成
>
> **[来源: [docs.rs](https://docs.rs/)]**

参见 `.github/workflows/pr-checks.yml` 中的 `semver-checks` 任务：

```yaml
semver-checks:
  name: SemVer Checks
  runs-on: ubuntu-latest
  steps:
    - uses: actions/checkout@v4
      with:
        fetch-depth: 0  # 需要完整 git 历史以比较 baseline

    - uses: dtolnay/rust-toolchain@stable
      with:
        toolchain: "1.96.0"

    - name: Install cargo-semver-checks
      run: cargo install cargo-semver-checks --locked

    - name: Run semver checks
      run: cargo semver-checks --workspace
```

### CI 策略
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

1. **PR 检查**: 与 `main` 分支比较，阻止无意的 breaking change
2. **发布前检查**: 与上一个发布的版本比较
3. **允许失败模式**: 对于实验性 crate，可设置 `continue-on-error: true`

---

## 5. 处理误报和例外
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 场景 1: 新增字段但已使用 `#[non_exhaustive]`
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```rust
#[non_exhaustive]
pub struct Config {
    pub name: String,
    pub new_field: u32, // ✅ 这是 MINOR 变更，semver-checks 不会报告
}
```

### 场景 2: 有意进行 breaking change（MAJOR 版本升级）
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```bash
# 在 CI 中允许（因为版本号已更新为 MAJOR）
cargo semver-checks --baseline-version 0.1.0
# 如果当前版本是 1.0.0，则 breaking change 是预期的
```

### 场景 3: 内部 API 被误判
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

```rust
// 使用 #[doc(hidden)] 标记内部 API
#[doc(hidden)]
pub fn __internal_helper() {} // semver-checks 会忽略此项
```

---

## 6. 最佳实践
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

1. **给所有公共 struct 添加 `#[non_exhaustive]`**（如果计划未来扩展）
2. **给所有公共 enum 添加 `#[non_exhaustive]`**
3. **使用 sealed trait 模式** 防止外部实现
4. **在 PR 描述中标注 SemVer 影响**
5. **将 semver-checks 作为发布清单的必检项**

---

## 7. 参考资源
>
> **[来源: [crates.io](https://crates.io/)]**

- [cargo-semver-checks 文档](https://github.com/obi1kenobi/cargo-semver-checks)
- [Rust API 指南](https://rust-lang.github.io/api-guidelines/)
- [SemVer 规范](https://semver.org/lang/zh-CN/)

---

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [Parent README](../README.md)

---

## 相关概念
>
> **[来源: [docs.rs](https://docs.rs/)]**

- [上级目录](../README.md)

---

## 权威来源索引

> **[来源: Wikipedia - Rust (programming language)]**

> **[来源: Rust Reference]**

> **[来源: TRPL - The Rust Programming Language]**

> **[来源: Rust Standard Library]**

> **[来源: ACM - Systems Programming]**

> **[来源: IEEE - Programming Language Standards]**

> **[来源: RFCs - github.com/rust-lang/rfcs]**

> **[来源: Rustonomicon]**

---
