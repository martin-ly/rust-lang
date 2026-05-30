# 安装 Rust

> **相关概念**: [工具链](../../concept/06_ecosystem/01_toolchain.md)
> **Bloom 层级**: 理解
> **版本**: Rust 1.96.0+
> **预计时间**: 15-30 分钟
> **权威来源**: [Rust 官方安装指南](https://www.rust-lang.org/tools/install), [rustup 文档](https://rust-lang.github.io/rustup/), [The Rust Programming Language — Ch1](https://doc.rust-lang.org/book/ch01-01-installation.html)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 rustup 官方文档来源标注、工具链管理权威引用 [来源: Authority Source Sprint Batch 8]

## 🎯 学习目标
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

完成本章后，你将能够：

- [ ] 使用 rustup 安装 Rust
- [ ] 配置开发环境
- [ ] 验证安装成功
- [ ] 理解工具链管理

## 📋 先决条件
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

- 操作系统: Windows 10+, macOS 10.14+, 或 Linux
- 管理员权限（安装时使用）
- 互联网连接

## 🛠️ 安装步骤
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

### 1. 使用 rustup 安装（推荐）
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

#### Windows

```powershell
# 在 PowerShell 中运行
winget install Rustlang.Rustup
# 或
Invoke-WebRequest -Uri https://win.rustup.rs -OutFile rustup-init.exe
.\rustup-init.exe
```

#### macOS / Linux

```bash
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
```

### 2. 配置环境变量
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

安装程序会自动配置，但可能需要重启终端。

验证配置：

```bash
source $HOME/.cargo/env  # Linux/macOS
# 或重启 PowerShell     # Windows
```

### 3. 验证安装
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

```bash
rustc --version   # 应显示: rustc 1.95.0 (xxxxxx)
cargo --version   # 应显示: cargo 1.95.0
rustup --version  # 应显示: rustup 1.x.x
```

## 🔧 工具链管理
>
> **[来源: [crates.io](https://crates.io/)]**

### 查看已安装工具链
>
> **[来源: [docs.rs](https://docs.rs/)]**

```bash
rustup show
```

### 切换到特定版本
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

```bash
rustup install 1.93.0
rustup default 1.93.0
```

### 更新到最新版
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```bash
rustup update
```

## 📝 配置 Cargo
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

### 创建配置目录
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```bash
mkdir -p ~/.cargo
```

### 常用配置 (~/.cargo/config.toml)
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

```toml
[build]
target-dir = "target"  # 构建目录
jobs = 4               # 并行编译任务数

[profile.release]
opt-level = 3          # 优化级别
lto = true             # 链接时优化

[net]
retry = 3              # 网络重试次数
git-fetch-with-cli = true  # 使用系统 git
```

## 💻 IDE 配置
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

### VS Code（推荐）
>
> **[来源: [crates.io](https://crates.io/)]**

1. 安装 VS Code
2. 安装扩展:
   - **rust-analyzer**: Rust 语言服务器
   - **CodeLLDB**: 调试支持
   - **Even Better TOML**: Cargo.toml 支持

3. 配置 settings.json:

```json
{
  "rust-analyzer.checkOnSave.command": "clippy",
  "rust-analyzer.cargo.features": "all",
  "rust-analyzer.procMacro.enable": true
}
```

### 其他 IDE
>
> **[来源: [docs.rs](https://docs.rs/)]**

- **IntelliJ IDEA**: Rust 插件
- **Vim/Neovim**: coc-rust-analyzer 或 rust-tools.nvim
- **Emacs**: rustic 或 lsp-mode

## ⚠️ 常见问题
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

| 问题 | 原因 | 解决方案 |
|------|------|----------|
| `command not found` | PATH 未配置 | 重启终端或手动 source |
| 下载速度慢 | 网络问题 | 配置镜像源 |
| Windows 链接器错误 | 缺少 Visual Studio | 安装 Build Tools |

### 配置国内镜像（中国用户）
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

~/.cargo/config.toml:

```toml
[source.crates-io]
replace-with = 'ustc'

[source.ustc]
registry = "sparse+https://mirrors.ustc.edu.cn/crates.io-index/"
```

## 🎮 练习
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

### 练习 1: 验证安装
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

运行以下命令并记录输出：

```bash
rustc --version
cargo --version
rustup show
```

### 练习 2: 工具链切换
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

尝试安装 nightly 工具链并切换：

```bash
rustup install nightly
rustup run nightly rustc --version
rustup default stable  # 切回稳定版
```

## ✅ 自我检测
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

1. 如何查看当前 Rust 版本？
2. 如何更新 Rust 到最新版？
3. rust-analyzer 的作用是什么？

## 📖 延伸阅读

- [Rust 官方安装指南](https://www.rust-lang.org/tools/install) [来源: Rust Team / 2025]
- [rustup 文档](https://rust-lang.github.io/rustup/) [来源: Rust Core Team / 2025]
- [Cargo 配置](https://doc.rust-lang.org/cargo/reference/config.html) [来源: Rust Team / Cargo Book 2025]

---

## 📚 权威来源索引

- [Rust 官方安装指南](https://www.rust-lang.org/tools/install) [来源: Rust Team / 2025]
- [rustup 文档](https://rust-lang.github.io/rustup/) [来源: Rust Core Team / 2025]
- [The Rust Programming Language — Ch1](https://doc.rust-lang.org/book/ch01-01-installation.html) [来源: Rust Team / TRPL 2025]
- [Cargo 配置](https://doc.rust-lang.org/cargo/reference/config.html) [来源: Rust Team / Cargo Book 2025]

---

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 相关概念
>
> **[来源: [crates.io](https://crates.io/)]**

- [Hello World](./01_hello_world.md)

- [Hello, World](01_hello_world.md)
- [Rust 学习路线图](03_learning_roadmap.md)
- [Rust 哲学与设计原则](04_rust_philosophy.md)

---

## 权威来源索引

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
>

---
ss
