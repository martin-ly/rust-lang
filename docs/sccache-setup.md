# sccache 配置指南

本文档说明如何在项目中配置和使用 sccache 来加速 Rust 编译。

## 什么是 sccache?

`sccache` 是 Mozilla 开发的编译缓存工具，支持:
- **磁盘缓存**: 本地快速重用编译结果
- **远程缓存**: S3, Azure Blob, GCS, Redis 等
- **CI/CD 集成**: GitHub Actions 原生支持

## 安装

### 方式 1: 使用 cargo 安装 (推荐)

```bash
cargo install sccache --locked
```

### 方式 2: 使用包管理器

**Windows (winget):**
```powershell
winget install sccache
```

**macOS (Homebrew):**
```bash
brew install sccache
```

**Linux:**
```bash
# Ubuntu/Debian
sudo apt-get install sccache

# Arch
sudo pacman -S sccache

# 其他发行版使用 cargo 安装
```

### 方式 3: GitHub Releases

下载预编译二进制文件:
https://github.com/mozilla/sccache/releases

## 验证安装

```bash
sccache --version
```

## 配置

### 1. Cargo 配置 (已完成)

`.cargo/config.toml` 已配置:

```toml
[build]
rustc-wrapper = "sccache"

[env]
SCCACHE_CACHE_SIZE = "50G"
SCCACHE_DIR = "D:\\_cache\\sccache"  # Windows
# SCCACHE_DIR = "${HOME}/.cache/sccache"  # Linux/macOS
SCCACHE_GHA_ENABLED = "true"
```

### 2. 环境变量 (可选)

```bash
# Windows PowerShell
$env:SCCACHE_CACHE_SIZE = "50G"
$env:SCCACHE_DIR = "D:\_cache\sccache"

# Linux/macOS
export SCCACHE_CACHE_SIZE="50G"
export SCCACHE_DIR="$HOME/.cache/sccache"
```

## 使用方法

配置完成后，正常使用 cargo 命令即可，sccache 自动生效:

```bash
cargo build
cargo test
cargo check
```

## 监控缓存状态

```bash
# 查看缓存统计
sccache --show-stats

# 示例输出:
# Compile requests                    1,024
# Compile requests executed             980
# Cache hits                            850 (86.7%)
# Cache misses                          130 (13.3%)
# Cache timeouts                          0
```

## 清理缓存

```bash
# 手动清理
sccache --stop-server
rm -rf $SCCACHE_DIR  # Linux/macOS
# 或删除 D:\_cache\sccache  # Windows

# 自动清理 (达到 SCCACHE_CACHE_SIZE 时自动清理)
# 无需手动操作
```

## CI/CD 配置

GitHub Actions 已配置 (`.github/workflows/ci.yml`):

```yaml
- name: Setup sccache
  uses: mozilla-actions/sccache-action@v0.0.4

- name: Cache sccache
  uses: actions/cache@v4
  with:
    path: ~/.cache/sccache
    key: ${{ runner.os }}-sccache-${{ hashFiles('**/Cargo.lock') }}
```

## 性能基准

| 场景 | 时间 | 说明 |
|------|------|------|
| 首次构建 | ~X min | 无缓存，创建缓存 |
| 缓存命中 | ~Y min | 约 60-80% 时间节省 |
| CI 缓存 | ~Z min | 跨构建共享缓存 |

运行 `scripts/benchmark-sccache.ps1` 进行本地基准测试。

## 故障排除

### sccache 未生效

```bash
# 检查环境变量
echo $env:RUSTC_WRAPPER  # Windows
echo $RUSTC_WRAPPER      # Linux/macOS

# 应该输出: sccache
```

### 缓存目录权限问题

```bash
# Windows - 确保目录存在并有写权限
mkdir D:\_cache\sccache -Force

# Linux/macOS
mkdir -p ~/.cache/sccache
chmod 755 ~/.cache/sccache
```

### 清理并重启

```bash
sccache --stop-server
sccache --start-server
```

## 参考

- [sccache GitHub](https://github.com/mozilla/sccache)
- [Rust Cargo 缓存](https://doc.rust-lang.org/cargo/guide/build-cache.html)
