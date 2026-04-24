# Cargo Script 单文件脚本指南

> **最后更新日期**: 2026-04-24  
> **适用版本**: Rust 1.79+ (cargo script 功能已稳定)  
> **文档类型**: 实用指南

---

## 1. 什么是 Cargo Script？

**Cargo Script** 是 Rust 从 1.79 版本开始稳定化的功能，允许在**单个 `.rs` 文件**中编写完整的 Rust 程序，包括外部依赖声明。

### 1.1 为什么需要它？

在 Cargo Script 之前，运行一个依赖外部 crate 的 Rust 程序需要：

```bash
# 传统方式: 需要完整项目结构
cargo new my_script --bin
cd my_script
# 编辑 Cargo.toml 添加依赖
# 编辑 src/main.rs
cargo run
```

Cargo Script 简化为：

```bash
# 直接运行单个文件
cargo run --manifest-path my_script.rs
```

### 1.2 适用场景

| 场景 | 传统项目 | Cargo Script |
|------|---------|-------------|
| 快速原型验证 | ❌ 过重 | ✅ 轻量 |
| 一次性数据处理 | ❌ 繁琐 | ✅ 便捷 |
| 系统管理脚本 | ⚠️ 可行 | ✅ 更合适 |
| 教学示例 | ❌ 分散 | ✅ 自包含 |
| 大型项目开发 | ✅ 合适 | ❌ 不适合 |
| 多文件模块 | ✅ 合适 | ❌ 不支持 |

---

## 2. 文件格式规范

### 2.1 基本结构

```rust
#!/usr/bin/env cargo
```cargo
[dependencies]
clap = "4"
```

// 正常的 Rust 代码
fn main() {
    println!("Hello from cargo script!");
}
```

### 2.2 格式要求

1. **Shebang (可选但推荐)**
   - 首行: `#!/usr/bin/env cargo`
   - 仅在 Unix/Linux/macOS 上有意义
   - 允许直接 `./script.rs` 执行

2. **Cargo 清单块**
   - 必须紧跟 shebang 或文件开头
   - 使用 Markdown 代码块语法: ` ```cargo ` ... ` ``` `
   - 内部语法与 `Cargo.toml` 相同

3. **Rust 代码**
   - 清单块之后是正常的 Rust 源代码
   - 可以包含 `fn main()`、模块、测试等

### 2.3 完整清单示例

```rust
#!/usr/bin/env cargo
```cargo
[package]
name = "my-script"
version = "1.0.0"
edition = "2021"
authors = ["Your Name <you@example.com>"]

[dependencies]
serde = { version = "1", features = ["derive"] }
serde_json = "1"
reqwest = { version = "0.11", features = ["blocking"] }

[profile.release]
opt-level = 3
```
//! 文档注释...

use serde::{Deserialize, Serialize};

fn main() {
    // 代码...
}
```

---

## 3. 运行方式

### 3.1 使用 cargo 直接运行 (推荐)

```bash
# Rust 1.79+ 稳定方式
cargo run --manifest-path script.rs

# 传递参数
cargo run --manifest-path script.rs -- --help
```

### 3.2 作为可执行脚本 (Unix)

```bash
# 添加执行权限
chmod +x script.rs

# 直接运行
./script.rs
```

### 3.3 使用 Rust 解释器模式

```bash
# 某些环境支持
rust-script script.rs
```

### 3.4 Windows 环境

Windows 不支持 shebang，因此：

```powershell
# PowerShell
cargo run --manifest-path script.rs

# 或创建批处理包装器
# run-script.bat:
#   cargo run --manifest-path %~dp0script.rs -- %*
```

---

## 4. 依赖管理

### 4.1 基本依赖

```cargo
[dependencies]
clap = "4"
rand = "0.8"
```

### 4.2 带特性的依赖

```cargo
[dependencies]
tokio = { version = "1", features = ["full"] }
serde = { version = "1", features = ["derive"] }
```

### 4.3 路径依赖 (同目录下的本地 crate)

```cargo
[dependencies]
my_local_lib = { path = "../my_local_lib" }
```

### 4.4 工作区依赖

Cargo Script 目前**不支持**直接引用工作区依赖。需要显式声明版本：

```cargo
[dependencies]
# ❌ 不支持: common = { workspace = true }
# ✅ 显式声明:
common = { path = "../../crates/common" }
```

---

## 5. 实际示例

### 示例 1: JSON 数据处理

```rust
#!/usr/bin/env cargo
```cargo
[dependencies]
serde = { version = "1", features = ["derive"] }
serde_json = "1"
```

use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
struct User {
    name: String,
    age: u32,
}

fn main() {
    let json = r#"{"name":"Alice","age":30}"#;
    let user: User = serde_json::from_str(json).unwrap();
    println!("{:?}", user);
}
```

### 示例 2: HTTP 请求

```rust
#!/usr/bin/env cargo
```cargo
[dependencies]
reqwest = { version = "0.11", features = ["blocking"] }
```

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let body = reqwest::blocking::get("https://api.github.com/users/rust-lang")?
        .text()?;
    println!("{}", body);
    Ok(())
}
```

### 示例 3: 本项目的演示文件

参见项目根目录: `examples/cargo_script_demo.rs`

---

## 6. 注意事项与限制

### 6.1 当前限制

| 限制 | 说明 |  workaround |
|------|------|------------|
| 单文件 | 不支持多文件模块 (`mod foo;`) | 使用宏或内联所有代码 |
| 工作区 | 不支持 `workspace = true` 依赖 | 显式路径或版本 |
| 构建脚本 | 不支持 `build.rs` | 使用普通项目 |
| 过程宏 | 可作为依赖使用 | 正常使用 |

### 6.2 缓存

Cargo Script 会自动缓存编译结果。缓存位置：

```
# Unix/Linux
~/.cargo/target/

# Windows
%USERPROFILE%\.cargo\target\
```

### 6.3 性能提示

- 第一次运行会下载依赖并编译，耗时较长
- 后续运行（无修改）会直接使用缓存
- 可以使用 `--release` 标志编译优化版本

---

## 7. 调试与测试

### 7.1 运行测试

Cargo Script 文件中的 `#[cfg(test)]` 模块可以通过以下方式测试：

```bash
# 提取为临时项目后测试
cargo test --manifest-path script.rs
```

### 7.2 调试输出

```bash
# 详细输出
cargo run --manifest-path script.rs -v

# 释放模式
cargo run --manifest-path script.rs --release
```

---

## 8. 参考文献

1. **Rust Official Documentation**. "Cargo Script".  
   <https://doc.rust-lang.org/cargo/reference/unstable.html#script>

2. **The Rust Programming Language Blog**. "Rust 1.79.0 Release Notes". 2024.

3. **cargo-script Community**. "cargo-run-script: Enhanced script support".  
   <https://github.com/fornwall/rust-script>

---

> 📌 **复查记录**
> - 2026-04-24: 初始创建，基于 Rust 1.96 的 cargo script 稳定功能
> - 下次复查: 随 Rust 版本更新时复查
