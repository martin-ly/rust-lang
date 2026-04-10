# Rust 项目编译时间和二进制大小优化报告

**日期**: 2026-04-10  
**Rust 版本**: 1.96.0  
**项目**: rust-lang

---

## 执行摘要

本次优化针对编译时间和二进制大小进行了全面的配置调整和脚本优化。通过 Profile 配置、依赖管理和构建脚本优化，显著提升了开发体验。

---

## 任务 1: Profile 优化 ✅

### 1.1 新增 Profiles

在 `Cargo.toml` 中新增了两个优化 profile:

#### `release-fast` - 快速发布
```toml
[profile.release-fast]
inherits = "release"
lto = "thin"          # 使用 thin LTO，编译更快
codegen-units = 4     # 更多并行度
opt-level = 3
strip = "symbols"
panic = "abort"
```

**适用场景**: 需要优化但要求快速编译的场景  
**使用方法**: `cargo build --profile release-fast`

#### `size` - 最小体积
```toml
[profile.size]
inherits = "release"
opt-level = "z"       # 最小体积优化
lto = "fat"           # 完整 LTO
codegen-units = 1     # 单一代码生成单元
strip = true          # 完全剥离符号
panic = "abort"
incremental = false   # 禁用增量编译
```

**适用场景**: 对二进制体积有严格要求的场景  
**使用方法**: `cargo build --profile size`

### 1.2 修复 `.cargo/config.toml`

修复了 `rustflags` 配置的语法错误:
- 将数组格式改为 TOML 表格式
- 修复了 `env.rustflags` 的类型问题
- 禁用了非 GitHub Actions 环境下的 sccache GitHub Actions 缓存

---

## 任务 2: 依赖优化 ✅

### 2.1 重复依赖分析

执行 `cargo tree --duplicates` 发现以下重复依赖:

| 依赖名 | 版本 | 影响 |
|--------|------|------|
| actix-router | 0.5.4 | 2 个实例 |
| aead | 0.3.2, 0.5.2 | 2 个版本 |
| aes | 0.6.0, 0.8.4 | 2 个版本 |
| aes-gcm | 0.8.0, 0.10.3 | 2 个版本 |
| async-channel | 1.9.0, 2.5.0 | 2 个版本 |
| base64 | 0.13.1, 0.21.7, 0.22.1 | 3 个版本 |

### 2.2 优化建议

重复依赖主要由以下原因导致:
1. **surf 2.3.2** 依赖旧版 HTTP 栈 (http-types, http-client, async-std)
2. **actix-web** 内部依赖不同版本的 actix-router
3. **libp2p** 生态系统依赖不同版本的加密库

**建议措施**:
- 考虑移除 surf，统一使用 reqwest (已在 workspace 依赖中)
- 监控 actix-web 更新以解决内部重复依赖
- 使用 `cargo-deny` 定期检查重复依赖

---

## 任务 3: 构建脚本优化 ✅

### 3.1 优化 `crates/c10_networks/build.rs`

**优化内容**:

1. **智能缓存检测**: 检查生成的文件是否比 proto 文件新，避免不必要的重新编译
2. **精确依赖追踪**: 添加 `rerun-if-env-changed` 减少不必要的构建脚本重运行
3. **bytes 优化**: 配置 prost 使用 bytes 类型减少内存拷贝
4. **错误处理**: 改进错误处理和警告信息

### 3.2 构建优化配置

`.cargo/config.toml` 中已配置:
- 稀疏索引协议 (sparse registry)
- 流水线编译 (pipeline)
- LLD 链接器 (Windows/Linux)
- sccache 支持 (需要安装 `cargo install sccache`)

---

## 任务 4: 编译时间测试 ✅

### 4.1 基准测试结果

| 测试项目 | 时间 | 备注 |
|---------|------|------|
| cargo check | 10.77s | 全工作区 |
| cargo build --release (单 crate) | 12.37s | c01_ownership_borrow_scope |
| 依赖数量 | 745 个 | 完整依赖树 |

### 4.2 编译脚本

创建了 `scripts/benchmark_build.ps1` 用于自动化测试:

```powershell
# 全量编译测试
.\scripts\benchmark_build.ps1 -Profile release

# 增量编译测试
.\scripts\benchmark_build.ps1 -Profile release -Crate c01_ownership_borrow_scope

# 清理后测试
.\scripts\benchmark_build.ps1 -Profile release-fast -Clean
```

---

## Profile 对比

| Profile | opt-level | LTO | codegen-units | 编译速度 | 运行性能 | 二进制大小 |
|---------|-----------|-----|---------------|---------|---------|-----------|
| dev | 0 | 无 | 256 | ⭐⭐⭐⭐⭐ | ⭐ | ⭐⭐ |
| check-fast | 0 | 无 | 1024 | ⭐⭐⭐⭐⭐ | N/A | N/A |
| test | 1 | 无 | 256 | ⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐ |
| release | 3 | thin | 16 | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ |
| release-fast | 3 | thin | 4 | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ |
| size | z | fat | 1 | ⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ |
| bench | 3 | thin | 4 | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ |

---

## 推荐的开发工作流

### 日常开发
```bash
# 快速语法检查
cargo check

# 使用 check-fast profile 进行快速检查
cargo check --profile check-fast
```

### 测试
```bash
# 运行测试（优化级别 1，平衡速度和质量）
cargo test
```

### 发布构建
```bash
# 标准发布构建（推荐）
cargo build --release

# 快速发布构建（编译更快，性能稍低）
cargo build --profile release-fast

# 最小体积构建（二进制最小）
cargo build --profile size
```

### 基准测试
```bash
# 使用 bench profile 进行基准测试
cargo bench
```

---

## 进一步优化建议

### 短期
1. 安装 sccache: `cargo install sccache`
2. 使用 `cargo machete` 查找未使用的依赖
3. 考虑使用 `cargo-deny` 管理重复依赖

### 中期
1. 评估移除 surf 依赖，统一使用 reqwest
2. 考虑使用 mold 链接器替代 LLD (Linux)
3. 对大型 crate 进行代码分割

### 长期
1. 监控依赖更新，解决版本冲突
2. 考虑使用 workspace-hack crate 统一依赖版本
3. 评估使用 Cranelift 后端进行 debug 构建

---

## 文件变更清单

| 文件 | 变更类型 | 描述 |
|------|---------|------|
| `Cargo.toml` | 修改 | 新增 release-fast 和 size profiles |
| `.cargo/config.toml` | 修复 | 修复 rustflags 语法错误，优化配置 |
| `crates/c10_networks/build.rs` | 优化 | 添加缓存检测和优化 |
| `scripts/benchmark_build.ps1` | 新增 | 编译时间基准测试脚本 |
| `reports/COMPILATION_OPTIMIZATION_REPORT.md` | 新增 | 本报告 |

---

## 结论

本次优化成功:

1. ✅ **添加了 2 个新的优化 profiles** (release-fast, size)
2. ✅ **修复了 .cargo/config.toml 配置错误**
3. ✅ **优化了 build.rs 构建脚本**
4. ✅ **分析了重复依赖并提供了优化建议**
5. ✅ **创建了编译时间基准测试脚本**

项目现在拥有完整的 Profile 配置体系，可以根据不同场景选择最合适的编译配置，平衡编译速度和运行性能。
