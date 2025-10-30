# Cargo Workspace Profile 配置指南

## 📋 问题说明

### 遇到的警告

```
warning: profiles for the non root package will be ignored, specify profiles at the workspace root:
package:   E:\_src\rust-lang\crates\c12_wasm\Cargo.toml
workspace: E:\_src\rust-lang\Cargo.toml
```

### 问题原因

在 Cargo workspace 环境中，**`[profile.*]` 配置只能在工作区根目录的 `Cargo.toml` 中定义**。如果在子 crate 的 `Cargo.toml` 中定义 profile 配置，这些配置会被 Cargo 忽略，并产生警告。

## 🔧 解决方案

### 1. 移除子 crate 中的 profile 配置

**错误做法：** 在 `crates/c12_wasm/Cargo.toml` 中定义

```toml
[profile.release]
opt-level = "z"      # ❌ 这会被忽略
lto = true           # ❌ 这会被忽略
codegen-units = 1    # ❌ 这会被忽略
strip = true         # ❌ 这会被忽略
panic = "abort"      # ❌ 这会被忽略
```

**正确做法：** 在根目录 `Cargo.toml` 中统一定义

```toml
[profile.release]
opt-level = 3        # ✅ 工作区级别的优化
lto = "fat"          # ✅ 链接时优化
codegen-units = 1    # ✅ 单一代码生成单元
strip = "symbols"    # ✅ 去除调试符号
panic = "abort"      # ✅ panic 时立即终止
```

### 2. WASM 特定优化的处理

如果某个 crate（如 c12_wasm）需要特殊的编译选项，有以下几种方案：

#### 方案 A：使用 `.cargo/config.toml`（推荐）

在项目根目录创建 `.cargo/config.toml`：

```toml
[target.wasm32-unknown-unknown]
rustflags = [
    "-C", "opt-level=z",           # 最小化 WASM 体积
    "-C", "lto=fat",                # 全局链接时优化
    "-C", "embed-bitcode=yes",      # 嵌入 LLVM 位码
]
```

编译时：
```bash
cargo build --release --target wasm32-unknown-unknown
```

#### 方案 B：使用环境变量

```bash
# 临时设置优化级别
RUSTFLAGS="-C opt-level=z" cargo build --release --target wasm32-unknown-unknown
```

#### 方案 C：使用自定义 profile（Rust 1.90+）

在根目录 `Cargo.toml` 中：

```toml
[profile.release-wasm]
inherits = "release"
opt-level = "z"      # WASM 专用：最小化体积
```

编译时：
```bash
cargo build --profile release-wasm --target wasm32-unknown-unknown
```

## 📝 Workspace Profile 配置规则

### ✅ 允许的配置位置

| 配置项 | 根目录 Cargo.toml | 子 crate Cargo.toml |
|--------|-------------------|---------------------|
| `[profile.*]` | ✅ 有效 | ❌ 被忽略 |
| `[workspace.dependencies]` | ✅ 有效 | ❌ 不允许 |
| `[dependencies]` | ❌ 不适用 | ✅ 有效 |
| `[features]` | ❌ 不适用 | ✅ 有效 |
| `[[bin]]` | ❌ 不适用 | ✅ 有效 |
| `[lib]` | ❌ 不适用 | ✅ 有效 |

### 📋 当前项目的 Profile 配置

我们的项目在根目录 `Cargo.toml` 中定义了以下 profile：

```toml
[profile.release]        # 发布优化
[profile.dev]            # 开发环境
[profile.test]           # 测试环境
[profile.bench]          # 基准测试
```

所有子 crate 都会自动继承这些配置。

## 🎯 最佳实践

### 1. 统一管理依赖版本

使用 `[workspace.dependencies]`：

```toml
[workspace.dependencies]
tokio = { version = "1.48.0", features = ["full"] }
serde = { version = "1.0.228", features = ["derive"] }
```

在子 crate 中引用：

```toml
[dependencies]
tokio = { workspace = true }
serde = { workspace = true }
```

### 2. 保持配置一致性

- ✅ 在根目录定义所有 profile 配置
- ✅ 使用 workspace dependencies 统一版本
- ✅ 使用 `.cargo/config.toml` 处理特定目标的编译选项
- ❌ 不要在子 crate 中定义 profile
- ❌ 不要在不同 crate 中使用不同版本的依赖

### 3. 特殊需求的处理

如果某个 crate 需要特殊的编译配置：

1. **优先考虑** `.cargo/config.toml` 中的 target-specific 配置
2. **其次考虑** 自定义 profile（`[profile.custom]`）
3. **最后考虑** 环境变量和编译参数

## 🔍 验证配置

检查 workspace 配置是否正确：

```bash
# 检查特定 crate
cargo check -p c12_wasm

# 检查整个 workspace
cargo check --workspace

# 查看实际使用的编译选项
cargo build --release --verbose
```

## 📚 参考资料

- [Cargo Book - Workspaces](https://doc.rust-lang.org/cargo/reference/workspaces.html)
- [Cargo Book - Profiles](https://doc.rust-lang.org/cargo/reference/profiles.html)
- [Rust WASM Book](https://rustwasm.github.io/docs/book/)

---

**更新日期：** 2025-10-30  
**维护者：** Rust Learning Community

