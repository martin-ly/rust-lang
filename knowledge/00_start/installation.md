# 安装 Rust

> **版本**: Rust 1.94.0
> **预计时间**: 15-30 分钟

## 🎯 学习目标

完成本章后，你将能够：

- [ ] 使用 rustup 安装 Rust
- [ ] 配置开发环境
- [ ] 验证安装成功
- [ ] 理解工具链管理

## 📋 先决条件

- 操作系统: Windows 10+, macOS 10.14+, 或 Linux
- 管理员权限（安装时使用）
- 互联网连接

## 🛠️ 安装步骤

### 1. 使用 rustup 安装（推荐）

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

安装程序会自动配置，但可能需要重启终端。

验证配置：

```bash
source $HOME/.cargo/env  # Linux/macOS
# 或重启 PowerShell     # Windows
```

### 3. 验证安装

```bash
rustc --version   # 应显示: rustc 1.94.0 (xxxxxx)
cargo --version   # 应显示: cargo 1.94.0
rustup --version  # 应显示: rustup 1.x.x
```

## 🔧 工具链管理

### 查看已安装工具链

```bash
rustup show
```

### 切换到特定版本

```bash
rustup install 1.93.0
rustup default 1.93.0
```

### 更新到最新版

```bash
rustup update
```

## 📝 配置 Cargo

### 创建配置目录

```bash
mkdir -p ~/.cargo
```

### 常用配置 (~/.cargo/config.toml)

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

### VS Code（推荐）

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

- **IntelliJ IDEA**: Rust 插件
- **Vim/Neovim**: coc-rust-analyzer 或 rust-tools.nvim
- **Emacs**: rustic 或 lsp-mode

## ⚠️ 常见问题

| 问题 | 原因 | 解决方案 |
|------|------|----------|
| `command not found` | PATH 未配置 | 重启终端或手动 source |
| 下载速度慢 | 网络问题 | 配置镜像源 |
| Windows 链接器错误 | 缺少 Visual Studio | 安装 Build Tools |

### 配置国内镜像（中国用户）

~/.cargo/config.toml:

```toml
[source.crates-io]
replace-with = 'ustc'

[source.ustc]
registry = "sparse+https://mirrors.ustc.edu.cn/crates.io-index/"
```

## 🎮 练习

### 练习 1: 验证安装

运行以下命令并记录输出：

```bash
rustc --version
cargo --version
rustup show
```

### 练习 2: 工具链切换

尝试安装 nightly 工具链并切换：

```bash
rustup install nightly
rustup run nightly rustc --version
rustup default stable  # 切回稳定版
```

## ✅ 自我检测

1. 如何查看当前 Rust 版本？
2. 如何更新 Rust 到最新版？
3. rust-analyzer 的作用是什么？

## 📖 延伸阅读

- [Rust 官方安装指南](https://www.rust-lang.org/tools/install)
- [rustup 文档](https://rust-lang.github.io/rustup/)
- [Cargo 配置](https://doc.rust-lang.org/cargo/reference/config.html)

---

**文档版本**: 1.0
**对应 Rust 版本**: 1.94.0
**最后更新**: 2026-03-19
