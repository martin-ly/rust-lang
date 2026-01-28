# Cargo 常见问题解答 (FAQ)

## 📊 目录

- [Cargo 常见问题解答 (FAQ)](#cargo-常见问题解答-faq)
  - [📊 目录](#-目录)
    - [基础问题](#基础问题)
    - [依赖管理](#依赖管理)
    - [特性系统](#特性系统)
    - [工作空间](#工作空间)
    - [构建优化](#构建优化)
    - [发布相关](#发布相关)
    - [高级主题](#高级主题)
  - [基础问题1](#基础问题1)
    - [Q1: Cargo.toml 和 Cargo.lock 有什么区别？](#q1-cargotoml-和-cargolock-有什么区别)
    - [Q2: 什么时候应该提交 Cargo.lock？](#q2-什么时候应该提交-cargolock)
    - [Q3: 如何选择依赖版本？](#q3-如何选择依赖版本)
    - [Q4: Package 和 Crate 有什么区别？](#q4-package-和-crate-有什么区别)
    - [Q5: 什么是 Edition？如何选择？](#q5-什么是-edition如何选择)
  - [依赖管理1](#依赖管理1)
    - [Q6: 如何更新依赖版本？](#q6-如何更新依赖版本)
    - [Q7: 如何解决依赖冲突？](#q7-如何解决依赖冲突)
    - [Q8: 什么是 Resolver 3？](#q8-什么是-resolver-3)
    - [Q9: 如何添加本地依赖？](#q9-如何添加本地依赖)
    - [Q10: 如何使用 Git 依赖？](#q10-如何使用-git-依赖)
  - [特性系统1](#特性系统1)
    - [Q11: 什么是 Features？如何使用？](#q11-什么是-features如何使用)
    - [Q12: 如何实现可选依赖？](#q12-如何实现可选依赖)
    - [Q13: Features 如何传播？](#q13-features-如何传播)
    - [Q14: 如何禁用默认特性？](#q14-如何禁用默认特性)
  - [工作空间1](#工作空间1)
    - [Q15: 什么时候应该使用工作空间？](#q15-什么时候应该使用工作空间)
    - [Q16: 如何在工作空间中共享依赖？](#q16-如何在工作空间中共享依赖)
    - [Q17: 工作空间成员如何互相依赖？](#q17-工作空间成员如何互相依赖)
  - [构建优化1](#构建优化1)
    - [Q18: 如何加快编译速度？](#q18-如何加快编译速度)
    - [Q19: 什么是 LTO？何时使用？](#q19-什么是-lto何时使用)
    - [Q20: 如何减小二进制大小？](#q20-如何减小二进制大小)
    - [Q21: Profile 配置如何选择？](#q21-profile-配置如何选择)
  - [发布相关1](#发布相关1)
    - [Q22: 如何发布到 crates.io？](#q22-如何发布到-cratesio)
    - [Q23: 如何撤回已发布的版本？](#q23-如何撤回已发布的版本)
    - [Q24: rust-version 字段的作用？](#q24-rust-version-字段的作用)
  - [高级主题1](#高级主题1)
    - [Q25: 如何编写构建脚本？](#q25-如何编写构建脚本)
    - [Q26: 如何进行交叉编译？](#q26-如何进行交叉编译)
    - [Q27: 如何使用自定义 Registry？](#q27-如何使用自定义-registry)
    - [Q28: 如何进行依赖审计？](#q28-如何进行依赖审计)
  - [🔗 相关资源](#-相关资源)
    - [官方文档](#官方文档)
    - [工具推荐](#工具推荐)
    - [相关文档](#相关文档)

**版本**: Rust 1.92.0 / Cargo 1.92.0
**创建日期**: 2025-10-19
**文档状态**: ✅ 完整

---

### 基础问题

- [Q1: Cargo.toml 和 Cargo.lock 有什么区别？](#q1-cargotoml-和-cargolock-有什么区别)
- [Q2: 什么时候应该提交 Cargo.lock？](#q2-什么时候应该提交-cargolock)
- [Q3: 如何选择依赖版本？](#q3-如何选择依赖版本)
- [Q4: Package 和 Crate 有什么区别？](#q4-package-和-crate-有什么区别)
- [Q5: 什么是 Edition？如何选择？](#q5-什么是-edition如何选择)

### 依赖管理

- [Q6: 如何更新依赖版本？](#q6-如何更新依赖版本)
- [Q7: 如何解决依赖冲突？](#q7-如何解决依赖冲突)
- [Q8: 什么是 Resolver 3？](#q8-什么是-resolver-3)
- [Q9: 如何添加本地依赖？](#q9-如何添加本地依赖)
- [Q10: 如何使用 Git 依赖？](#q10-如何使用-git-依赖)

### 特性系统

- [Q11: 什么是 Features？如何使用？](#q11-什么是-features如何使用)
- [Q12: 如何实现可选依赖？](#q12-如何实现可选依赖)
- [Q13: Features 如何传播？](#q13-features-如何传播)
- [Q14: 如何禁用默认特性？](#q14-如何禁用默认特性)

### 工作空间

- [Q15: 什么时候应该使用工作空间？](#q15-什么时候应该使用工作空间)
- [Q16: 如何在工作空间中共享依赖？](#q16-如何在工作空间中共享依赖)
- [Q17: 工作空间成员如何互相依赖？](#q17-工作空间成员如何互相依赖)

### 构建优化

- [Q18: 如何加快编译速度？](#q18-如何加快编译速度)
- [Q19: 什么是 LTO？何时使用？](#q19-什么是-lto何时使用)
- [Q20: 如何减小二进制大小？](#q20-如何减小二进制大小)
- [Q21: Profile 配置如何选择？](#q21-profile-配置如何选择)

### 发布相关

- [Q22: 如何发布到 crates.io？](#q22-如何发布到-cratesio)
- [Q23: 如何撤回已发布的版本？](#q23-如何撤回已发布的版本)
- [Q24: rust-version 字段的作用？](#q24-rust-version-字段的作用)

### 高级主题

- [Q25: 如何编写构建脚本？](#q25-如何编写构建脚本)
- [Q26: 如何进行交叉编译？](#q26-如何进行交叉编译)
- [Q27: 如何使用自定义 Registry？](#q27-如何使用自定义-registry)
- [Q28: 如何进行依赖审计？](#q28-如何进行依赖审计)

---

## 基础问题1

### Q1: Cargo.toml 和 Cargo.lock 有什么区别？

**简答**:

- `Cargo.toml`: 描述项目的**依赖需求**（版本范围）
- `Cargo.lock`: 记录**具体使用的版本**（精确版本）

**详细解释**:

```toml
# Cargo.toml - 描述需求
[dependencies]
serde = "1.0"  # 表示 "≥1.0.0, <2.0.0"
```

```toml
# Cargo.lock - 锁定版本
[[package]]
name = "serde"
version = "1.0.210"  # 精确版本
```

**为什么需要两个文件？**

- `Cargo.toml`: 灵活的版本需求，允许兼容更新
- `Cargo.lock`: 确保可重现构建，所有人使用相同版本

---

### Q2: 什么时候应该提交 Cargo.lock？

**决策表**:

| 项目类型     | 提交 Cargo.lock | 原因                 |
| ------------ | --------------- | -------------------- |
| **应用程序** | ✅ 是           | 确保部署一致性       |
| **库**       | ❌ 否           | 允许下游灵活选择版本 |
| **工具**     | ✅ 是           | 确保工具行为一致     |

**示例场景**:

```bash
# 应用程序项目
my-app/
├── Cargo.toml
├── Cargo.lock      # ✅ 提交到版本控制
└── src/

# 库项目
my-lib/
├── Cargo.toml
├── Cargo.lock      # ❌ 添加到 .gitignore
└── src/
```

---

### Q3: 如何选择依赖版本？

**版本语法**:

```toml
[dependencies]
# 1. 插入符号 (推荐)
serde = "^1.0"      # ≥1.0.0, <2.0.0

# 2. 波浪符号
tokio = "~1.48"     # ≥1.48.0, <1.49.0

# 3. 通配符
rand = "0.8.*"      # ≥0.8.0, <0.9.0

# 4. 精确版本
lazy_static = "=1.4.0"  # 仅 1.4.0

# 5. 范围
clap = ">=4.0, <5.0"
```

**推荐策略**:

```toml
# ✅ 推荐：使用插入符号
[dependencies]
serde = "1.0"       # 自动添加 ^

# ⚠️ 谨慎：精确版本（特殊情况）
critical-dep = "=1.2.3"

# ❌ 避免：过于宽松
risky = "*"         # 接受任何版本
```

---

### Q4: Package 和 Crate 有什么区别？

**概念对比**:

```text
┌─────────────────────────────────────┐
│         Package (包)                │
│  ┌───────────────────────────────┐  │
│  │   Cargo.toml (元数据)         │  │
│  └───────────────────────────────┘  │
│                                     │
│  ┌───────────────┐ ┌─────────────┐ │
│  │ Library Crate │ │ Binary Crate│ │
│  │   lib.rs      │ │   main.rs   │ │
│  └───────────────┘ └─────────────┘ │
└─────────────────────────────────────┘
```

**实际示例**:

```text
my-project/         ← Package
├── Cargo.toml
├── src/
│   ├── lib.rs      ← Library Crate
│   └── main.rs     ← Binary Crate
```

**关键点**:

- 1 个 Package 最多 1 个 Library Crate
- 1 个 Package 可以有多个 Binary Crates
- Crate 是编译单元

---

### Q5: 什么是 Edition？如何选择？

**Edition 对比**:

| Edition | 发布时间 | 关键特性            | 推荐使用    |
| ------- | -------- | ------------------- | ----------- |
| 2015    | 2015     | 基础 Rust           | ❌ 不推荐   |
| 2018    | 2018     | 模块系统改进        | ⚠️ 维护模式 |
| 2021    | 2021     | 闭包捕获改进        | ✅ 稳定选择 |
| 2024    | 2024     | Async trait, RPITIT | ⭐ 最新推荐 |

**配置示例**:

```toml
# Cargo.toml - Rust 1.92.0 项目
[package]
name = "my-project"
version = "1.0.0"
edition = "2024"        # 🎯 使用最新 Edition
rust-version = "1.93"   # 指定最低 Rust 版本
```

---

## 依赖管理1

### Q6: 如何更新依赖版本？

**常用命令**:

```bash
# 1. 更新到兼容的最新版本
cargo update

# 2. 更新特定依赖
cargo update -p serde

# 3. 精确更新到指定版本
cargo update -p tokio --precise 1.48.0

# 4. 检查过时依赖 (需要 cargo-outdated)
cargo outdated

# 5. 升级到最新版本 (需要 cargo-edit)
cargo upgrade
```

**手动更新流程**:

```bash
# 步骤 1: 修改 Cargo.toml
[dependencies]
serde = "1.0.210"  # 从 1.0.200 更新

# 步骤 2: 更新 Cargo.lock
cargo update -p serde

# 步骤 3: 测试
cargo test

# 步骤 4: 提交
git add Cargo.toml Cargo.lock
git commit -m "Update serde to 1.0.210"
```

---

### Q7: 如何解决依赖冲突？

**问题诊断**:

```bash
# 查看依赖树
cargo tree

# 查看重复依赖
cargo tree --duplicates

# 输出示例:
tokio v1.40.0
└── package-a v1.0.0

tokio v1.48.0
└── package-b v2.0.0
```

**解决方案**:

**方案 1: 使用 Resolver 3**:

```toml
# Cargo.toml
[package]
resolver = "3"  # 自动统一版本
```

**方案 2: 手动统一版本**:

```toml
[dependencies]
tokio = "1.48"  # 强制使用特定版本
package-a = "1.0"
package-b = "2.0"
```

**方案 3: 使用 Patch**:

```toml
[patch.crates-io]
tokio = { version = "1.48" }
```

---

### Q8: 什么是 Resolver 3？

**版本对比**:

```text
Resolver 1 (Edition 2015/2018):
├── 特性不统一
├── 依赖可能重复
└── 构建时间较长

Resolver 2 (Edition 2021):
├── 特性统一
├── 依赖解析改进
└── 构建性能提升 10%

Resolver 3 (Edition 2024):
├── 智能特性统一
├── 更好的冲突检测
├── 构建缓存优化
└── 构建性能提升 15-20%
```

**配置方式**:

```toml
# Cargo.toml
[package]
name = "my-project"
edition = "2024"
resolver = "3"    # 🎯 启用 Resolver 3
```

---

### Q9: 如何添加本地依赖？

**方式 1: 相对路径**:

```toml
[dependencies]
my-lib = { path = "../my-lib" }
```

**方式 2: 工作空间**:

```toml
# workspace/Cargo.toml
[workspace]
members = ["my-app", "my-lib"]

# workspace/my-app/Cargo.toml
[dependencies]
my-lib = { path = "../my-lib" }
# 或使用工作空间依赖
my-lib.workspace = true
```

**方式 3: 覆盖依赖**:

```toml
[patch.crates-io]
serde = { path = "/path/to/local/serde" }
```

---

### Q10: 如何使用 Git 依赖？

**基本语法**:

```toml
[dependencies]
# 1. 使用主分支
my-crate = { git = "https://github.com/user/repo" }

# 2. 指定分支
my-crate = { git = "https://github.com/user/repo", branch = "develop" }

# 3. 指定 tag
my-crate = { git = "https://github.com/user/repo", tag = "v1.0.0" }

# 4. 指定 commit
my-crate = { git = "https://github.com/user/repo", rev = "abc123" }

# 5. 指定子目录
my-crate = { git = "https://github.com/user/repo", package = "sub-crate" }
```

**⚠️ 注意事项**:

- Git 依赖不能发布到 crates.io
- 建议使用 tag 或 rev 而不是 branch
- 可能导致构建时间增加

---

## 特性系统1

### Q11: 什么是 Features？如何使用？

**定义 Features**:

```toml
# Cargo.toml
[features]
default = ["std"]
std = []
alloc = []
async = ["dep:tokio"]
full = ["std", "async", "serde-support"]

# 可选依赖
[dependencies]
tokio = { version = "1.48", optional = true }
serde = { version = "1.0", optional = true }
```

**使用 Features**:

```bash
# 使用默认特性
cargo build

# 禁用默认特性
cargo build --no-default-features

# 启用特定特性
cargo build --features async

# 启用多个特性
cargo build --features "async,serde-support"

# 启用所有特性
cargo build --all-features
```

---

### Q12: 如何实现可选依赖？

**配置示例**:

```toml
# Cargo.toml
[dependencies]
# 必需依赖
anyhow = "1.0"

# 可选依赖
tokio = { version = "1.48", optional = true }
serde = { version = "1.0", optional = true }

[features]
# 特性关联可选依赖
async = ["dep:tokio"]
serde-support = ["dep:serde"]
```

**代码中使用**:

```rust
// src/lib.rs
#[cfg(feature = "async")]
pub mod async_support {
    use tokio::runtime::Runtime;
    // 异步功能实现
}

#[cfg(feature = "serde-support")]
use serde::{Serialize, Deserialize};

#[cfg_attr(feature = "serde-support", derive(Serialize, Deserialize))]
pub struct MyData {
    pub value: String,
}
```

---

### Q13: Features 如何传播？

**传播规则**:

```text
根包 (启用 feature "full")
  │
  ├─> 依赖 A (启用 feature "async")
  │     │
  │     └─> tokio (启用 feature "full")
  │
  └─> 依赖 B (启用 feature "std")
        │
        └─> tokio (启用 feature "rt")

结果: tokio 特性合并 = ["full", "rt"]
```

**Resolver 3 优化**:

- 更智能的特性统一
- 避免不必要的特性激活
- 减少编译时间和二进制大小

---

### Q14: 如何禁用默认特性？

**方法 1: 单个依赖**:

```toml
[dependencies]
tokio = { version = "1.48", default-features = false, features = ["rt"] }
```

**方法 2: 工作空间级别**:

```toml
[workspace.dependencies]
tokio = { version = "1.48", default-features = false }
```

**方法 3: 构建时**:

```bash
cargo build --no-default-features --features minimal
```

---

## 工作空间1

### Q15: 什么时候应该使用工作空间？

**使用场景**:

✅ **推荐使用工作空间**:

- 多个相关的包
- 需要共享依赖版本
- 库 + 多个示例应用
- 微服务项目

❌ **不需要工作空间**:

- 单一简单项目
- 独立的小工具
- 学习示例

**示例场景**:

```text
场景 1: Web 服务
web-service/
├── api/        # HTTP API
├── core/       # 业务逻辑
├── db/         # 数据库层
└── models/     # 数据模型
→ ✅ 使用工作空间

场景 2: 简单 CLI 工具
my-cli/
└── src/
    └── main.rs
→ ❌ 不需要工作空间
```

---

### Q16: 如何在工作空间中共享依赖？

**配置工作空间依赖**:

```toml
# workspace/Cargo.toml
[workspace]
members = ["crate-a", "crate-b"]

[workspace.dependencies]
tokio = { version = "1.48", features = ["full"] }
serde = { version = "1.0", features = ["derive"] }
```

**成员包使用**:

```toml
# workspace/crate-a/Cargo.toml
[dependencies]
tokio.workspace = true
serde.workspace = true
```

**优势**:

- ✅ 版本统一
- ✅ 减少重复
- ✅ 简化更新
- ✅ 确保兼容性

---

### Q17: 工作空间成员如何互相依赖？

**配置示例**:

```toml
# workspace/Cargo.toml
[workspace]
members = ["core", "cli", "utils"]

[workspace.dependencies]
my-core = { path = "core" }
my-utils = { path = "utils" }
```

```toml
# workspace/cli/Cargo.toml
[dependencies]
my-core.workspace = true
my-utils.workspace = true
```

**依赖图**:

```text
cli → core
cli → utils
utils → core
```

**构建顺序**:

```bash
# Cargo 自动按依赖顺序构建
cargo build --workspace
# 顺序: 1. core → 2. utils → 3. cli
```

---

## 构建优化1

### Q18: 如何加快编译速度？

**优化策略**:

**1. 使用增量编译** (默认启用)

```toml
[profile.dev]
incremental = true
```

**2. 增加并行度**:

```toml
[profile.dev]
codegen-units = 16  # 更多并行单元
```

**3. 降低优化级别**:

```toml
[profile.dev]
opt-level = 0  # 无优化，快速编译
```

**4. 使用 sccache**:

```bash
# 安装
cargo install sccache

# 配置
export RUSTC_WRAPPER=sccache
```

**5. 优化依赖**:

```toml
[profile.dev.package."*"]
opt-level = 2  # 依赖使用更高优化
```

**性能对比**:

```text
优化前:  ████████████  完整构建 120秒
增量编译: ███          重编译 30秒
sccache:  █            缓存命中 5秒
```

---

### Q19: 什么是 LTO？何时使用？

**LTO (Link-Time Optimization) 介绍**:

```text
无 LTO:
  编译 → 目标文件 A.o
  编译 → 目标文件 B.o
  链接 → 二进制 (优化局限)

有 LTO:
  编译 → 中间表示 A.bc
  编译 → 中间表示 B.bc
  链接 + 全局优化 → 二进制 (更好优化)
```

**配置选项**:

```toml
[profile.release]
# 不使用 LTO
lto = false

# 轻量 LTO (推荐)
lto = "thin"

# 完整 LTO (最佳性能)
lto = "fat"
```

**性能对比**:

| 配置           | 编译时间 | 运行性能 | 二进制大小 |
| -------------- | -------- | -------- | ---------- |
| `lto = false`  | 1x       | 1.0x     | 1.0x       |
| `lto = "thin"` | 1.5x     | 0.85x    | 0.90x      |
| `lto = "fat"`  | 3.0x     | 0.75x    | 0.80x      |

**使用建议**:

- 开发: `lto = false`
- 测试: `lto = "thin"`
- 发布: `lto = "fat"`

---

### Q20: 如何减小二进制大小？

**优化配置**:

```toml
[profile.release]
opt-level = "z"        # 优化大小
lto = "fat"            # 链接时优化
codegen-units = 1      # 单编译单元
strip = true           # 去除符号
panic = "abort"        # Panic 中止
```

**高级优化**:

```bash
# 使用 cargo-bloat 分析
cargo install cargo-bloat
cargo bloat --release --crates

# 使用 UPX 压缩 (可选)
upx --best --lzma target/release/my-app.exe
```

**大小对比**:

```text
默认配置:    ████████████  5.2 MB
strip = true: ██████████    4.1 MB
opt-level=z:  ████████      3.5 MB
LTO + strip:  ██████        2.8 MB
UPX 压缩:     ███           1.2 MB
```

---

### Q21: Profile 配置如何选择？

**场景对比**:

| 场景         | Profile   | 配置要点               |
| ------------ | --------- | ---------------------- |
| **日常开发** | `dev`     | 快速编译，保留调试信息 |
| **CI 测试**  | `test`    | 平衡编译和运行速度     |
| **性能测试** | `bench`   | 最大优化，接近生产环境 |
| **生产发布** | `release` | 最大优化，最小体积     |

**推荐配置**:

```toml
# 开发：快速迭代
[profile.dev]
opt-level = 1
debug = true
incremental = true

# 测试：适度优化
[profile.test]
opt-level = 1

# 发布：最佳性能
[profile.release]
opt-level = 3
lto = "fat"
codegen-units = 1
strip = true
panic = "abort"
```

---

## 发布相关1

### Q22: 如何发布到 crates.io？

**发布流程**:

```bash
# 步骤 1: 登录
cargo login <your-api-token>

# 步骤 2: 准备 Cargo.toml
# [package]
# name = "my-package"
# version = "1.0.0"
# edition = "2024"
# description = "A great package"
# license = "MIT"
# repository = "https://github.com/user/repo"

# 步骤 3: 测试构建
cargo build --release
cargo test --all-features

# 步骤 4: 预发布检查
cargo publish --dry-run

# 步骤 5: 发布
cargo publish

# 步骤 6: 验证
# 访问 https://crates.io/crates/my-package
```

**必需字段**:

```toml
[package]
name = "my-package"
version = "1.0.0"
edition = "2024"
description = "Package description"  # 必需
license = "MIT"                      # 必需
```

---

### Q23: 如何撤回已发布的版本？

**撤回 (Yank) 版本**:

```bash
# 撤回特定版本
cargo yank --vers 1.0.0

# 取消撤回
cargo yank --vers 1.0.0 --undo
```

**重要说明**:

- ✅ 撤回后，新项目无法使用该版本
- ✅ 已锁定该版本的项目仍可使用
- ❌ 无法删除已发布的版本
- ❌ 无法修改已发布的版本

---

### Q24: rust-version 字段的作用？

**配置示例**:

```toml
[package]
name = "my-package"
version = "1.0.0"
rust-version = "1.93"  # 指定最低 Rust 版本
```

**作用**:

- ✅ 明确最低 Rust 版本要求
- ✅ Cargo 自动检查版本兼容性
- ✅ CI/CD 可验证版本要求
- ✅ 用户提前知道版本需求

**最佳实践**:

```toml
# 库: 保守设置
rust-version = "1.70"  # 支持更多用户

# 应用: 使用最新
rust-version = "1.93"  # 使用最新特性
```

---

## 高级主题1

### Q25: 如何编写构建脚本？

**基本示例**:

```rust
// build.rs
fn main() {
    // 1. 环境变量
    let target = std::env::var("TARGET").unwrap();
    println!("cargo:warning=Building for {}", target);

    // 2. 条件编译
    if cfg!(feature = "async") {
        println!("cargo:rustc-cfg=has_async");
    }

    // 3. 链接库
    println!("cargo:rustc-link-lib=static=mylib");

    // 4. 重新运行条件
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-env-changed=MY_VAR");

    // 5. 设置环境变量
    println!("cargo:rustc-env=BUILD_TIME={}",
             std::time::SystemTime::now()
                 .duration_since(std::time::UNIX_EPOCH)
                 .unwrap()
                 .as_secs());
}
```

**使用构建输出**:

```rust
// src/lib.rs
#[cfg(has_async)]
pub mod async_support {
    // 异步功能
}

pub const BUILD_TIME: &str = env!("BUILD_TIME");
```

---

### Q26: 如何进行交叉编译？

**安装目标平台**:

```bash
# 查看可用目标
rustup target list

# 安装目标
rustup target add x86_64-pc-windows-gnu
rustup target add x86_64-unknown-linux-musl
rustup target add aarch64-unknown-linux-gnu
```

**交叉编译**:

```bash
# 编译到目标平台
cargo build --target x86_64-pc-windows-gnu

# 发布构建
cargo build --release --target x86_64-unknown-linux-musl
```

**配置交叉编译器**:

```toml
# .cargo/config.toml
[target.aarch64-unknown-linux-gnu]
linker = "aarch64-linux-gnu-gcc"

[target.x86_64-unknown-linux-musl]
linker = "x86_64-linux-musl-gcc"
```

---

### Q27: 如何使用自定义 Registry？

**配置示例**:

```toml
# .cargo/config.toml
[source.my-registry]
registry = "https://my-registry.com/index"

[source.crates-io]
replace-with = "my-registry"  # 替换默认源

# 或添加额外源
[registries.my-registry]
index = "https://my-registry.com/index"
```

**使用私有 Registry**:

```toml
# Cargo.toml
[dependencies]
private-crate = { version = "1.0", registry = "my-registry" }
```

**发布到私有 Registry**:

```bash
cargo publish --registry my-registry
```

---

### Q28: 如何进行依赖审计？

**使用 cargo-audit**:

```bash
# 安装
cargo install cargo-audit

# 审计依赖
cargo audit

# 输出 JSON
cargo audit --json

# 自动修复
cargo audit fix
```

**集成 CI**:

```yaml
# .github/workflows/security.yml
name: Security Audit
on: [push, pull_request]

jobs:
  audit:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: actions-rust-lang/audit@v1
```

**定期检查**:

```bash
# 添加到 package.json scripts (如果使用)
{
  "scripts": {
    "audit": "cargo audit"
  }
}
```

---

## 🔗 相关资源

### 官方文档

- [The Cargo Book](https://doc.rust-lang.org/cargo/)
- [Cargo Reference](https://doc.rust-lang.org/cargo/reference/)
- [crates.io](https://crates.io/)

### 工具推荐

- [cargo-edit](https://github.com/killercup/cargo-edit) - 依赖管理
- [cargo-audit](https://github.com/RustSec/rustsec/tree/main/cargo-audit) - 安全审计
- [cargo-outdated](https://github.com/kbknapp/cargo-outdated) - 检查过时依赖
- [cargo-bloat](https://github.com/RazrFalcon/cargo-bloat) - 分析二进制大小

### 相关文档

- [依赖管理详解](./03_依赖管理详解.md)
- [特性系统详解](./04_特性系统详解.md)
- [工作空间管理](./05_工作空间管理.md)
- [构建系统详解](./06_构建系统详解.md)
- [最佳实践指南](./08_最佳实践指南.md)

---

**维护状态**: 🟢 活跃维护中
**最后更新**: 2026-01-26

_有新问题？欢迎提交 Issue 或 Pull Request！_ 🦀📦
