# Cargo 编译速度优化指南

本文档提供针对大型 Rust 项目（2000+ 依赖）的编译速度优化方案。

## 🚀 快速开始

### 1. 安装优化工具

**Windows (PowerShell):**

```powershell
./scripts/cargo-build-optimized.ps1 install-tools
```

**Linux/macOS:**

```bash
./scripts/cargo-build-optimized.sh install-tools
chmod +x ./scripts/cargo-build-optimized.sh
```

### 2. 使用优化脚本编译

```powershell
# 快速检查（最快）
./scripts/cargo-build-optimized.ps1 check

# 开发构建
./scripts/cargo-build-optimized.ps1 build dev

# 运行测试
./scripts/cargo-build-optimized.ps1 test

# 查看统计
./scripts/cargo-build-optimized.ps1 stats
```

## ⚙️ 环境变量配置

将以下内容添加到你的 PowerShell 配置文件 (`$PROFILE`) 或 `.bashrc`/`.zshrc`：

### Windows (PowerShell)

```powershell
# 编译性能优化
$env:CARGO_BUILD_JOBS = "16"  # 根据CPU核心数调整
$env:RUSTC_WRAPPER = "sccache"  # 启用sccache缓存

# 链接器优化
$env:CARGO_TARGET_X86_64_PC_WINDOWS_MSVC_LINKER = "rust-lld.exe"

# 内存优化 - 限制LLVM内存使用
$env:LLVM_SYS_170_PREFIX = ""

# 更快的编译设置
$env:CARGO_PROFILE_DEV_OPT_LEVEL = "0"
$env:CARGO_PROFILE_DEV_DEBUG = "1"
$env:CARGO_PROFILE_DEV_CODEGEN_UNITS = "256"
$env:CARGO_PROFILE_DEV_LTO = "off"

# 发布构建优化
$env:CARGO_PROFILE_RELEASE_LTO = "thin"
$env:CARGO_PROFILE_RELEASE_CODEGEN_UNITS = "16"
```

### Linux/macOS (Bash/Zsh)

```bash
# 编译性能优化
export CARGO_BUILD_JOBS=$(($(nproc) - 1))
export RUSTC_WRAPPER="sccache"

# 链接器优化
export CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_LINKER="clang"
export RUSTFLAGS="-C link-arg=-fuse-ld=lld"

# 更快的编译设置
export CARGO_PROFILE_DEV_OPT_LEVEL="0"
export CARGO_PROFILE_DEV_DEBUG="1"
export CARGO_PROFILE_DEV_CODEGEN_UNITS="256"
export CARGO_PROFILE_DEV_LTO="off"

# 发布构建优化
export CARGO_PROFILE_RELEASE_LTO="thin"
export CARGO_PROFILE_RELEASE_CODEGEN_UNITS="16"
```

## 📊 优化效果对比

| 优化项 | 预期效果 | 配置位置 |
|--------|----------|----------|
| sccache 缓存 | 减少 30-50% 重复编译时间 | 环境变量/配置 |
| lld 链接器 | 减少 20-40% 链接时间 | .cargo/config.toml |
| codegen-units=256 | 减少 15-25% 编译时间 | Cargo.toml |
| debug=1 | 减少 10-15% 编译时间 | Cargo.toml |
| 并行编译 | 充分利用多核CPU | 环境变量 |

## 🔧 配置文件说明

### .cargo/config.toml

主要优化配置：

```toml
[build]
rustc-wrapper = "sccache"  # 编译缓存
target-dir = "target"

# 链接器优化
[target.x86_64-pc-windows-msvc]
linker = "rust-lld.exe"

# 稀疏索引加速依赖下载
[registries.crates-io]
protocol = "sparse"
```

### Cargo.toml Profile 配置

```toml
[profile.dev]
opt-level = 0          # 无优化 = 最快编译
debug = 1              # 仅行表 = 更快
codegen-units = 256    # 高并行度
incremental = true     # 增量编译

# 超快速检查 Profile
[profile.check-fast]
inherits = "dev"
opt-level = 0
debug = 0
codegen-units = 1024
```

## 🛠️ 推荐工具

| 工具 | 用途 | 安装命令 |
|------|------|----------|
| sccache | 编译缓存 | `cargo install sccache` |
| cargo-bloat | 分析二进制大小 | `cargo install cargo-bloat` |
| cargo-tree | 依赖树分析 | `cargo install cargo-tree` |
| cargo-cache | 缓存管理 | `cargo install cargo-cache` |
| cargo-expand | 宏展开 | `cargo install cargo-expand` |

## 📈 性能监控

### 查看编译时间

```bash
# 使用 cargo 内置计时
cargo build --timings

# 查看历史编译时间
cat .cargo-build-times

# 使用脚本查看统计
./scripts/cargo-build-optimized.ps1 stats
```

### sccache 统计

```bash
sccache --show-stats
```

## 🧹 清理和重置

当遇到编译问题时：

```powershell
# 清理所有缓存
./scripts/cargo-build-optimized.ps1 clean-cache

# 或者手动清理
cargo clean
Remove-Item -Recurse -Force target
sccache --stop-server
```

## 🔬 进阶优化

### 使用 Nightly 工具链（可选）

```bash
rustup default nightly
```

启用实验性优化：

```toml
[unstable]
incremental-parallel = true
fast-debuginfo = true
parallel-frontend = true
```

### 内存优化（大型项目）

如果遇到内存不足：

```bash
# 减少并行度
export CARGO_BUILD_JOBS=4

# 减少代码生成单元
export CARGO_PROFILE_DEV_CODEGEN_UNITS=64
```

## ⚠️ 注意事项

1. **sccache 磁盘空间**：默认使用 10GB，可通过 `SCCACHE_CACHE_SIZE` 调整
2. **增量编译**：极少数情况下可能出现问题，可尝试 `cargo clean` 后重试
3. **链接器**：lld 不适用于所有场景，如有问题可回退到默认链接器
4. **CI/CD**：在 CI 中建议使用 `CARGO_INCREMENTAL=0` 禁用增量编译

## 📚 参考资源

- [Cargo Profile 文档](https://doc.rust-lang.org/cargo/reference/profiles.html)
- [sccache 文档](https://github.com/mozilla/sccache)
- [Rust 编译时间优化](https://matklad.github.io/2021/09/04/fast-rust-builds.html)
