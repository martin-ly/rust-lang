# Cargo 1.94 新特性指南

> **Cargo 版本**: 1.94.0
> **Rust 版本**: 1.94.0
> **发布日期**: 2026-03-05
> **最后更新**: 2026-03-13
> **状态**: ✅ 活跃维护

---

## 概述

Cargo 1.94 带来了多项重要改进，包括配置文件包含、TOML 1.1 支持、发布时间记录等功能。

---

## 一、Config Inclusion（配置文件包含）

### 1.1 特性描述

Cargo 现在在配置文件（`.cargo/config.toml`）中支持 `include` 键，允许加载额外的配置文件，从而更好地跨项目和环境组织、共享和管理 Cargo 配置。

### 1.2 基本用法

```toml
# .cargo/config.toml
include = [
    "frodo.toml",
    "samwise.toml",
]
```

### 1.3 高级用法（带可选标记）

```toml
# .cargo/config.toml
include = [
    { path = "required.toml" },
    { path = "optional.toml", optional = true },
]
```

如果设置了 `optional = true`，当文件不存在时不会报错。

### 1.4 实际应用场景

#### 团队共享配置

```toml
# .cargo/config.toml
include = [
    # 团队共享的配置（版本控制）
    { path = "team.toml" },
    # 个人本地配置（不在版本控制中）
    { path = "local.toml", optional = true },
]
```

#### 环境特定配置

```toml
# .cargo/config.toml
include = [
    # CI 环境配置
    { path = "ci.toml", optional = true },
    # 开发环境配置
    { path = "dev.toml", optional = true },
]
```

### 1.5 配置合并规则

- 后续配置可以覆盖前面的配置
- 当前文件的配置优先级最高
- 环境变量仍然具有最高优先级

---

## 二、TOML 1.1 支持

### 2.1 支持的特性

Cargo 1.94 现在解析 TOML v1.1，包含以下新特性：

| 特性 | 描述 | 示例 |
|------|------|------|
| 多行内联表 | 内联表可以跨多行 | 见下方 |
| 尾部逗号 | 允许尾部逗号 | `features = ["a",]` |
| `\xHH` 转义 | 十六进制字符转义 | `\x41` = 'A' |
| `\e` 转义 | Escape 字符 | `\e` = ESC |
| 可选秒 | 时间中的秒可选 | `12:30` |

### 2.2 多行内联表示例

```toml
[dependencies]
# 旧格式（单行）
serde = { version = "1.0", features = ["derive"] }

# 新格式（多行）
serde = {
    version = "1.0",
    features = ["derive",],
}

# 复杂的依赖配置
tokio = {
    version = "1.49",
    features = [
        "rt-multi-thread",
        "macros",
        "sync",
    ],
}
```

### 2.3 MSRV 注意事项

使用 TOML 1.1 特性会提高开发时的 MSRV（最低支持 Rust 版本），但：

- Cargo 在发布时会自动重写清单，保持与旧解析器的兼容性
- 第三方工具可能需要更新其解析器

```toml
# Cargo.toml
[package]
name = "my-crate"
version = "0.1.0"
rust-version = "1.94"  # 需要 1.94+ 来解析 TOML 1.1
```

---

## 三、pubtime 字段

### 3.1 特性描述

Cargo registry 索引现在包含 `pubtime` 字段，记录 crate 版本的发布时间。这支持未来的基于时间的依赖解析。

### 3.2 使用场景

```bash
# 未来可能支持的时间范围依赖
cargo add serde --time "2026-01-01..2026-03-01"
```

### 3.3 注意事项

- crates.io 将逐步回填现有包的发布时间
- 不是所有 crate 都有 `pubtime`（取决于发布时间和 registry）

---

## 四、`CARGO_BIN_EXE_<crate>` 运行时可用

### 4.1 特性描述

`CARGO_BIN_EXE_<crate>` 环境变量现在在运行时也可用，而不仅限于构建脚本。

### 4.2 使用示例

```rust
// 在测试中查找工具二进制文件
let tool_path = std::env::var("CARGO_BIN_EXE_my-tool")
    .expect("CARGO_BIN_EXE_my-tool not set");

let output = std::process::Command::new(tool_path)
    .arg("--version")
    .output()
    .expect("Failed to run tool");
```

### 4.3 测试示例

```rust
#[test]
fn test_cli_tool() {
    let exe = env!("CARGO_BIN_EXE_my-cli");
    let output = std::process::Command::new(exe)
        .args(["--input", "test.txt"])
        .output()
        .unwrap();

    assert!(output.status.success());
}
```

---

## 五、性能改进

### 5.1 cargo clean 优化

`cargo clean -p` 和 `cargo clean --workspace` 现在更快了。

```bash
# 清理特定包（更快）
cargo clean -p my-package

# 清理整个工作区（更快）
cargo clean --workspace
```

---

## 六、完整配置示例

```toml
# .cargo/config.toml
# ==================

# 包含其他配置文件
include = [
    { path = "team.toml" },
    { path = "local.toml", optional = true },
    { path = "ci.toml", optional = true },
]

[build]
rustflags = ["-C", "target-cpu=native"]
jobs = 8

[profile.release]
opt-level = 3
lto = "thin"

[profile.dev]
opt-level = 1
incremental = true

# 使用 TOML 1.1 特性（多行内联表）
[target.'cfg(unix)'.dependencies]
libc = {
    version = "0.2",
    features = ["extra_traits",],
}

[registries.crates-io]
protocol = "sparse"
```

---

## 七、迁移指南

### 7.1 从旧版本迁移

1. **更新 Rust**: `rustup update stable`
2. **验证配置**: `cargo check`
3. **使用新特性**: 逐步采用 TOML 1.1 和 config inclusion

### 7.2 兼容性

| 特性 | 向后兼容 | 说明 |
|------|----------|------|
| Config inclusion | ✅ | 可选使用 |
| TOML 1.1 | ⚠️ | 提高开发 MSRV |
| pubtime | ✅ | 自动处理 |
| CARGO_BIN_EXE | ✅ | 新增功能 |

---

## 八、相关资源

- [Cargo 1.94 开发周期报告](https://blog.rust-lang.org/inside-rust/2026/02/18/this-development-cycle-in-cargo-1.94/)
- [Cargo 官方文档](https://doc.rust-lang.org/cargo/)
- [TOML 1.1 规范](https://toml.io/en/v1.1.0)
- [Rust 1.94 特性分析](./RUST_194_COMPREHENSIVE_ANALYSIS.md)

---

**文档版本**: 1.0
**创建日期**: 2026-03-13
**维护者**: Rust 学习项目团队
