# 依赖更新检查指南

**创建日期**: 2025-12-11
**最后更新**: 2025-12-11
**Rust 版本**: 1.92.0

## 概述

本文档提供了项目依赖更新的检查流程和迁移指南。

## 快速检查命令

```bash
# 检查可用更新
cargo update --dry-run

# 详细检查可用更新
cargo update --verbose

# 更新所有依赖
cargo update

# 检查特定包的依赖树
cargo tree -p <package-name>

# 检查过时的依赖
cargo outdated
```

## 定期检查流程

### 1. 每周检查

```bash
# 1. 检查可用更新
cargo update --dry-run

# 2. 检查安全漏洞
cargo audit

# 3. 检查过时依赖
cargo outdated
```

### 2. 每月全面检查

1. **检查所有依赖的可用更新**

   ```bash
   cargo update --verbose
   ```

2. **评估重大版本更新**
   - 检查 CHANGELOG
   - 评估 API 变更
   - 评估迁移成本

3. **更新安全补丁**

   ```bash
   cargo update
   cargo audit
   ```

4. **测试更新后的代码**

   ```bash
   cargo test --workspace
   cargo build --workspace
   ```

## 待迁移的依赖

### 1. bincode 3.0.0

**当前版本**: 2.0.1
**目标版本**: 3.0.0
**状态**: 待迁移

**影响文件**:

- `crates/c10_networks/benches/network_benchmarks.rs`

**需要更新的 API**:

- `bincode::encode_to_vec()` → 新 API
- `bincode::decode_from_slice()` → 新 API
- `bincode::config::standard()` → 新配置 API
- `bincode::Encode` 和 `bincode::Decode` traits → 可能变更

**迁移步骤**:

1. 查看 bincode 3.0.0 的 CHANGELOG
2. 更新 API 调用
3. 测试基准测试功能
4. 更新 Cargo.toml

### 2. hickory-proto 0.25.x

**当前版本**: 0.24.4
**目标版本**: 0.25.2
**状态**: 待评估

**影响文件**:

- `crates/c10_networks/src/protocol/dns/mod.rs`
- `crates/c10_networks/examples/dns_custom_ns.rs`

**使用的 API**:

- `hickory_resolver::TokioAsyncResolver`
- `hickory_resolver::config::{ResolverConfig, ResolverOpts}`
- `hickory_resolver::error::ResolveErrorKind`
- `hickory_resolver::name_server::{GenericConnector, TokioRuntimeProvider}`
- `hickory_resolver::proto::rr::rdata::SRV`

**评估步骤**:

1. 检查 0.25.x 的 CHANGELOG 和迁移指南
2. 评估 API 变更影响范围
3. 测试新版本的 API 兼容性
4. 规划迁移时间表

### 3. hickory-resolver 0.25.x

**当前版本**: 0.24.4
**目标版本**: 0.25.2
**状态**: 待评估

**影响**: DNS 解析相关代码（与 hickory-proto 一起使用）

**评估步骤**:

1. 检查 0.25.x 的 CHANGELOG
2. 评估 API 变更影响范围
3. 规划迁移时间表
4. 注意：hickory-proto 和 hickory-resolver 需要同时更新

## 自动检查脚本

创建 `scripts/check_dependencies.sh` 和 `scripts/check_dependencies.bat` 用于自动化检查。

## 更新日志

所有依赖更新记录在 `Cargo.toml` 文件的更新日志部分。

## 注意事项

1. **重大版本更新**: 需要仔细评估 API 变更和迁移成本
2. **安全更新**: 优先更新安全补丁
3. **测试**: 每次更新后必须运行完整测试套件
4. **文档**: 更新相关文档和示例代码
