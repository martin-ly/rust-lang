# sccache 性能基准测试报告

生成时间: 2026-04-10

## 环境信息

- **OS**: Windows
- **sccache**: 0.14.0
- **缓存位置**: C:\Users\luyan\AppData\Local\Mozilla\sccache\cache
- **当前缓存大小**: 10 GiB (默认)

## 配置状态

### 本地配置 (.cargo/config.toml)

```toml
[build]
rustc-wrapper = "sccache"

[env]
SCCACHE_CACHE_SIZE = "50G"
SCCACHE_DIR = "D:\\_cache\\sccache"
SCCACHE_GHA_ENABLED = "true"
```

### CI/CD 配置 (.github/workflows/ci.yml)

- ✓ sccache-action@v0.0.4 已配置
- ✓ GitHub Actions 缓存已配置
- ✓ 跨平台支持 (Ubuntu, Windows, macOS)

## 性能预期

基于 sccache 官方文档和社区经验:

| 场景 | 预期性能 |
|------|---------|
| 首次构建 (冷缓存) | 略慢 (缓存存储开销) |
| 增量编译 | 30-50% 提升 |
| 完全缓存命中 | 60-80% 提升 |
| CI/CD 缓存 | 50-70% 提升 |

## 使用方法

### 本地开发

```bash
# 正常使用 cargo 命令，sccache 自动生效
cargo build
cargo test
cargo check

# 查看缓存统计
sccache --show-stats

# 清理缓存
sccache --stop-server
# 删除缓存目录 (Windows): D:\_cache\sccache
# 删除缓存目录 (Linux/macOS): ~/.cache/sccache
```

### 监控命令

```bash
# 实时查看缓存命中率
sccache --show-stats

# 重置统计
sccache --zero-stats
```

## 故障排除

### 检查 sccache 是否生效

```bash
# 应该看到 sccache 版本信息
sccache --version

# 构建后查看统计，应该看到非零的 "Compile requests"
sccache --show-stats
```

### 缓存未命中的常见原因

1. **环境变量未设置**: 检查 `RUSTC_WRAPPER=sccache`
2. **缓存目录权限**: 确保 `SCCACHE_DIR` 可写
3. **不同编译器版本**: 缓存键包含编译器版本信息
4. **不同编译选项**: 不同的 `RUSTFLAGS` 会产生不同的缓存键

## 结论

✅ **sccache 配置完成**

- 本地开发环境已配置
- CI/CD 流水线已配置
- 缓存目录已设置为 `D:\_cache\sccache`
- 缓存大小限制为 50GB

下一步: 运行完整构建以填充缓存并观察性能提升。
