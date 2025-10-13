# Rust 依赖更新策略指南

## 当前问题分析

### 1. 版本冲突严重

- 多个库存在不同版本同时使用
- 主要冲突：rustls、tokio-rustls、rand系列、http等
- 影响：编译时间增加、二进制体积增大、潜在运行时问题

### 2. 过时依赖

- generic-array: 0.14.8 → 1.3.3 (重大版本升级)
- hickory-proto: 0.24.4 → 0.25.2
- hickory-resolver: 0.24.4 → 0.25.2
- lru: 0.12.5 → 0.16.1

### 3. 已移除依赖

- 大量依赖已被移除或合并到其他库
- 需要清理Cargo.toml中的过时引用

## 更新策略

### 阶段1：安全更新（高优先级）

```bash
# 1. 更新rustls相关依赖
cargo update rustls tokio-rustls rustls-webpki rustls-pemfile

# 2. 更新rand系列
cargo update rand rand_chacha rand_core

# 3. 更新http相关
cargo update http http-body http-body-util
```

### 阶段2：功能更新（中优先级）

```bash
# 1. 更新DNS相关
cargo update hickory-proto hickory-resolver

# 2. 更新缓存库
cargo update lru

# 3. 更新generic-array（需要测试兼容性）
cargo update generic-array
```

### 阶段3：清理（低优先级）

```bash
# 1. 移除过时依赖
cargo update --precise <version> <crate>

# 2. 清理重复依赖
cargo tree --duplicates
```

## 自动化脚本

### 1. 依赖冲突检测

```bash
#!/bin/bash
# scripts/check_dependency_conflicts.sh

echo "=== 检测依赖冲突 ==="
cargo tree --duplicates

echo "=== 检测过时依赖 ==="
cargo outdated

echo "=== 检测安全漏洞 ==="
cargo audit
```

### 2. 安全更新脚本

```bash
#!/bin/bash
# scripts/safe_dependency_update.sh

echo "=== 开始安全依赖更新 ==="

# 备份当前状态
cp Cargo.lock Cargo.lock.backup

# 更新安全相关依赖
echo "更新rustls相关..."
cargo update rustls tokio-rustls rustls-webpki rustls-pemfile

echo "更新rand系列..."
cargo update rand rand_chacha rand_core

echo "更新http相关..."
cargo update http http-body http-body-util

# 测试编译
echo "测试编译..."
cargo check

if [ $? -eq 0 ]; then
    echo "✅ 安全更新成功"
else
    echo "❌ 编译失败，回滚更改"
    mv Cargo.lock.backup Cargo.lock
    exit 1
fi
```

### 3. 完整更新脚本

```bash
#!/bin/bash
# scripts/full_dependency_update.sh

set -e

echo "=== 完整依赖更新 ==="

# 备份
cp Cargo.lock Cargo.lock.backup
cp Cargo.toml Cargo.toml.backup

# 阶段1：安全更新
echo "阶段1：安全更新"
cargo update rustls tokio-rustls rustls-webpki rustls-pemfile
cargo update rand rand_chacha rand_core
cargo update http http-body http-body-util

# 测试
cargo check || { echo "安全更新失败"; exit 1; }

# 阶段2：功能更新
echo "阶段2：功能更新"
cargo update hickory-proto hickory-resolver
cargo update lru

# 测试
cargo check || { echo "功能更新失败"; exit 1; }

# 阶段3：generic-array更新（需要特别测试）
echo "阶段3：generic-array更新"
cargo update generic-array

# 全面测试
echo "全面测试..."
cargo test
cargo build --release

echo "✅ 依赖更新完成"
```

## 注意事项

### 1. 测试策略

- 每次更新后运行 `cargo check`
- 重要更新后运行 `cargo test`
- 发布前运行 `cargo build --release`

### 2. 回滚策略

- 保留Cargo.lock备份
- 使用git管理Cargo.toml变更
- 准备快速回滚脚本

### 3. 监控指标

- 编译时间变化
- 二进制体积变化
- 测试通过率
- 性能基准测试结果

## 推荐工具

### 1. 依赖管理工具

```bash
# 安装cargo-outdated
cargo install cargo-outdated

# 安装cargo-audit
cargo install cargo-audit

# 安装cargo-tree
cargo install cargo-tree
```

### 2. 自动化工具

```bash
# 使用cargo-edit进行依赖管理
cargo install cargo-edit

# 使用cargo-update进行批量更新
cargo install cargo-update
```

## 执行计划

### 第1周：安全更新

- 更新rustls相关依赖
- 更新rand系列
- 更新http相关
- 全面测试

### 第2周：功能更新

- 更新DNS相关库
- 更新缓存库
- 更新generic-array
- 性能测试

### 第3周：清理和优化

- 移除过时依赖
- 清理重复依赖
- 优化编译配置
- 文档更新

## 风险评估

### 高风险

- generic-array 0.14 → 1.x (重大版本变更)
- rustls 0.21 → 0.23 (API变更)

### 中风险

- hickory-proto 0.24 → 0.25
- rand 0.8 → 0.9

### 低风险

- lru 0.12 → 0.16
- 其他小版本更新

## 成功标准

1. ✅ 所有测试通过
2. ✅ 编译时间不显著增加
3. ✅ 二进制体积不显著增加
4. ✅ 性能基准测试通过
5. ✅ 无安全漏洞
6. ✅ 依赖冲突解决
