# Rust 1.92.0 全项目对齐计划 / Rust 1.92.0 All Crates Update Plan

**创建日期**: 2025-12-11
**目标版本**: Rust 1.92.0
**状态**: 📋 计划阶段
**预计工作量**: 11 个 crates，419+ 文件需要检查

---

## 📋 执行摘要

本计划旨在将所有 12 个 crates 的文档、代码和配置全面对齐到 Rust 1.92.0，确保：

- ✅ 所有 `Cargo.toml` 中的 `rust-version = "1.92"`
- ✅ 所有 README 中的版本引用更新为 "Rust 1.92.0+"
- ✅ 所有文档中的历史版本引用（1.90/1.91）更新或标记为历史参考
- ✅ 代码示例和注释中的版本引用更新
- ✅ 创建 Rust 1.92.0 特性实现和文档（如适用）

---

## 📊 当前状态概览

### ✅ 已完成对齐的 Crates

| Crate | Cargo.toml | README | 文档 | 代码 | 状态 |
|-------|-----------|--------|------|------|------|
| **c12_wasm** | ✅ 1.92 | ✅ 1.92.0+ | ✅ 已更新 | ✅ 已更新 | ✅ **完全对齐** |

### ⚠️ 需要更新的 Crates (11 个)

| Crate | Cargo.toml | README | 文档状态 | 代码状态 | 优先级 |
|-------|-----------|--------|---------|---------|--------|
| **c01_ownership_borrow_scope** | ✅ 1.92 | ⚠️ 部分 | ⚠️ 有 1.91 引用 | ⚠️ 有 1.91 引用 | 🔴 高 |
| **c02_type_system** | ✅ 1.92 | ⚠️ 部分 | ⚠️ 有 1.90 引用 | ⚠️ 有 1.90 引用 | 🔴 高 |
| **c03_control_fn** | ✅ 1.92 | ✅ 1.92.0+ | ⚠️ 需检查 | ⚠️ 需检查 | 🟡 中 |
| **c04_generic** | ✅ 1.92 | ✅ 1.92.0+ | ⚠️ 需检查 | ⚠️ 需检查 | 🟡 中 |
| **c05_threads** | ✅ 1.92 | ⚠️ 部分 | ⚠️ 有 1.90 引用 | ⚠️ 有 1.90 引用 | 🔴 高 |
| **c06_async** | ✅ 1.92 | ⚠️ 1.91.1 | ⚠️ 大量 1.90 引用 | ⚠️ 有 1.91 引用 | 🔴 高 |
| **c07_process** | ✅ 1.92 | ⚠️ 部分 | ⚠️ 有 1.90 引用 | ⚠️ 需检查 | 🔴 高 |
| **c08_algorithms** | ✅ 1.92 | ⚠️ 部分 | ⚠️ 有 1.90/1.91 引用 | ⚠️ 需检查 | 🔴 高 |
| **c09_design_pattern** | ✅ 1.92 | ⚠️ 部分 | ⚠️ 有 1.90 引用 | ⚠️ 需检查 | 🟡 中 |
| **c10_networks** | ✅ 1.92 | ⚠️ 部分 | ⚠️ 有 1.90/1.91 引用 | ⚠️ 需检查 | 🔴 高 |
| **c11_macro_system** | ✅ 1.92 | ✅ 1.92.0+ | ⚠️ 需检查 | ⚠️ 需检查 | 🟡 中 |

---

## 🎯 详细更新计划

### Phase 1: 高优先级 Crates (6 个) 🔴

#### 1. c01_ownership_borrow_scope

**当前状态**:

- ✅ `Cargo.toml`: `rust-version = "1.92"`
- ⚠️ `README.md`: 标题显示 1.92.0，但内容提到 "Rust 1.91+"
- ⚠️ 文档: `RUST_191_OWNERSHIP_BORROWING_LIFETIME_IMPROVEMENTS.md` 存在
- ⚠️ 代码: `src/rust_191_features.rs` 存在

**需要完成的任务**:

- [ ] 更新 `README.md` 中所有 "Rust 1.91" 引用为 "Rust 1.92.0"
- [ ] 创建 `RUST_192_OWNERSHIP_BORROWING_LIFETIME_IMPROVEMENTS.md`（如果适用）
- [ ] 更新或重命名 `src/rust_191_features.rs` 为 `src/rust_192_features.rs`（如果适用）
- [ ] 检查所有文档中的版本引用（约 50+ 文件）
- [ ] 更新示例代码中的版本注释

**预计工作量**: 2-3 小时

---

#### 2. c02_type_system

**当前状态**:

- ✅ `Cargo.toml`: `rust-version = "1.92"`
- ⚠️ `README.md`: 显示 "Rust 1.92.0+"，但内容提到 "Rust 1.90"
- ⚠️ 文档: 多处提到 "Rust 1.90" 和 "Rust 1.89"
- ⚠️ 代码: 示例文件名包含 `rust_189_*` 和 `rust_190_*`

**需要完成的任务**:

- [ ] 更新 `README.md` 中所有 "Rust 1.90" 引用
- [ ] 检查并更新 `docs/tier_03_references/03_分派机制参考.md` 中的版本对比表
- [ ] 检查并更新 `docs/tier_04_advanced/03_类型系统形式化.md` 中的版本引用
- [ ] 更新示例文件名或添加 Rust 1.92.0 示例
- [ ] 检查所有文档中的版本引用（约 59+ 文件）

**预计工作量**: 3-4 小时

---

#### 3. c05_threads

**当前状态**:

- ✅ `Cargo.toml`: `rust-version = "1.92"`
- ⚠️ `README.md`: 显示 "Rust 1.92.0+"，但内容提到 "Rust 1.90 Edition 2024"
- ⚠️ 文档: 多处提到 "Rust 1.90" 特性
- ⚠️ 代码: `rust_190_features` 模块存在

**需要完成的任务**:

- [ ] 更新 `README.md` 中所有 "Rust 1.90" 引用
- [ ] 更新 `docs/tier_01_foundations/01_项目概览.md` 中的版本引用
- [ ] 检查并更新所有文档中的 "Rust 1.90" 引用（约 30+ 文件）
- [ ] 更新代码示例中的版本注释
- [ ] 考虑创建 `rust_192_features` 模块（如果适用）

**预计工作量**: 2-3 小时

---

#### 4. c06_async

**当前状态**:

- ✅ `Cargo.toml`: `rust-version = "1.92"`
- ⚠️ `README.md`: 显示 "Rust 1.91.1 异步特性更新"
- ⚠️ 文档: 大量文档提到 "Rust 1.90+"（约 20+ 文件）
- ⚠️ 代码: `src/rust_191_features.rs` 存在
- ⚠️ 示例: `actor_pattern_comprehensive_2025.rs` 提到 "Rust 1.90+"

**需要完成的任务**:

- [ ] 更新 `README.md` 标题和内容为 "Rust 1.92.0"
- [ ] 更新所有 `docs/tier_02_guides/*.md` 中的版本引用（约 6 文件）
- [ ] 更新所有 `docs/tier_03_references/*.md` 中的版本引用（约 6 文件）
- [ ] 更新所有 `docs/tier_04_advanced/*.md` 中的版本引用（约 5 文件）
- [ ] 更新示例代码中的版本注释（约 10+ 文件）
- [ ] 创建 `RUST_192_ASYNC_IMPROVEMENTS.md`（如果适用）
- [ ] 更新或重命名 `src/rust_191_features.rs`

**预计工作量**: 4-5 小时

---

#### 5. c07_process

**当前状态**:

- ✅ `Cargo.toml`: `rust-version = "1.92"`
- ⚠️ `README.md`: 显示 "Rust 1.92.0+"，但内容提到 "Rust 1.90"
- ⚠️ 文档: `docs/01_process_model_and_lifecycle.md` 提到 "Rust 1.90 进程增强"
- ⚠️ 代码: `rust_190_features_demo` 和 `rust_192_features_demo` 都存在

**需要完成的任务**:

- [ ] 更新 `README.md` 中所有 "Rust 1.90" 引用
- [ ] 更新 `docs/01_process_model_and_lifecycle.md` 中的版本引用
- [ ] 检查并更新所有文档中的版本引用（约 54+ 文件）
- [ ] 验证 `rust_192_features_demo` 是否完整
- [ ] 更新代码示例中的版本注释

**预计工作量**: 2-3 小时

---

#### 6. c08_algorithms

**当前状态**:

- ✅ `Cargo.toml`: `rust-version = "1.92"`
- ⚠️ `README.md`: 显示 "Rust 1.92.0+"，但内容提到 "Rust 1.90/1.91"
- ⚠️ 文档: 多处提到 "Rust 1.90" 和 "Rust 1.91"
- ⚠️ 代码: `docs/leetcode_with_rust191.md` 存在

**需要完成的任务**:

- [ ] 更新 `README.md` 中所有版本引用
- [ ] 更新 `docs/leetcode_with_rust191.md` 为 `docs/leetcode_with_rust192.md`（如果适用）
- [ ] 更新 `docs/tier_03_references/01_算法分类参考.md` 中的版本引用
- [ ] 更新 `docs/tier_03_references/02_数据结构参考.md` 中的版本引用
- [ ] 检查并更新所有文档中的版本引用（约 43+ 文件）

**预计工作量**: 3-4 小时

---

#### 7. c10_networks

**当前状态**:

- ✅ `Cargo.toml`: `rust-version = "1.92"`
- ⚠️ `README.md`: 显示 "Rust 1.92.0+"，但标题提到 "Rust 1.91.1"
- ⚠️ 文档: 多处提到 "Rust 1.90" 和 "Rust 1.91.1"
- ⚠️ 代码: 需要检查

**需要完成的任务**:

- [ ] 更新 `README.md` 标题和所有版本引用
- [ ] 更新 `docs/tier_03_references/01_网络协议分类参考.md` 中的版本引用
- [ ] 更新 `docs/tier_04_advanced/01_形式化网络协议理论.md` 中的版本引用
- [ ] 检查并更新所有文档中的版本引用（约 41+ 文件）
- [ ] 更新代码示例中的版本注释

**预计工作量**: 2-3 小时

---

### Phase 2: 中优先级 Crates (4 个) 🟡

#### 8. c03_control_fn

**当前状态**:

- ✅ `Cargo.toml`: `rust-version = "1.92"`
- ✅ `README.md`: 显示 "Rust 1.92.0+"
- ⚠️ 文档: 需要全面检查
- ⚠️ 代码: 需要检查

**需要完成的任务**:

- [ ] 全面检查所有文档中的版本引用（约 43+ 文件）
- [ ] 检查代码中的版本注释
- [ ] 更新示例代码中的版本引用

**预计工作量**: 1-2 小时

---

#### 9. c04_generic

**当前状态**:

- ✅ `Cargo.toml`: `rust-version = "1.92"`
- ✅ `README.md`: 显示 "Rust 1.92.0+"
- ⚠️ 文档: 需要全面检查
- ⚠️ 代码: `src/rust_189_*` 文件存在

**需要完成的任务**:

- [ ] 全面检查所有文档中的版本引用（约 29+ 文件）
- [ ] 检查代码中的版本注释
- [ ] 考虑更新或重命名 `rust_189_*` 文件

**预计工作量**: 1-2 小时

---

#### 10. c09_design_pattern

**当前状态**:

- ✅ `Cargo.toml`: `rust-version = "1.92"`
- ⚠️ `README.md`: 显示 "Rust 1.92.0+"，但内容提到 "Rust 1.90"
- ⚠️ 文档: `docs/tier_04_advanced/*.md` 提到 "Rust 1.90+"

**需要完成的任务**:

- [ ] 更新 `README.md` 中的版本引用
- [ ] 更新 `docs/tier_04_advanced/*.md` 中的版本引用（约 5 文件）
- [ ] 检查并更新所有文档中的版本引用（约 40+ 文件）

**预计工作量**: 1-2 小时

---

#### 11. c11_macro_system

**当前状态**:

- ✅ `Cargo.toml`: `rust-version = "1.92"`
- ✅ `README.md`: 显示 "Rust 1.92.0+"
- ⚠️ 文档: 需要全面检查
- ⚠️ 代码: 需要检查

**需要完成的任务**:

- [ ] 全面检查所有文档中的版本引用（约 36+ 文件）
- [ ] 检查代码中的版本注释
- [ ] 更新示例代码中的版本引用

**预计工作量**: 1-2 小时

---

## 📝 通用更新任务

### 文档更新模式

对于所有 crates，需要执行以下通用任务：

1. **README.md 更新**:
   - 更新标题中的版本号
   - 更新 "Rust版本" 字段
   - 更新 "最后更新" 日期
   - 更新所有版本引用

2. **文档头部更新**:
   - 更新文档版本元数据
   - 更新日期信息
   - 更新适用版本说明

3. **代码注释更新**:
   - 更新文件头部的版本注释
   - 更新示例代码中的版本说明

4. **历史文档处理**:
   - 保留历史版本文档作为参考（标记为历史）
   - 或更新为当前版本（如果内容仍然适用）

---

## 🎯 执行策略

### 策略 1: 批量替换（推荐）

对于明确的版本引用，使用批量替换：

- `Rust 1.90` → `Rust 1.92.0`（在适用的情况下）
- `Rust 1.91` → `Rust 1.92.0`（在适用的情况下）
- `1.90+` → `1.92.0+`
- `1.91+` → `1.92.0+`

**注意**: 需要区分：

- 历史参考文档（保留原版本号，添加标记）
- 当前功能文档（更新为 1.92.0）

### 策略 2: 创建新文档

对于重要的特性文档：

- 保留历史版本文档（如 `RUST_191_*.md`）
- 创建新版本文档（如 `RUST_192_*.md`）
- 在 README 中链接到最新版本

### 策略 3: 代码模块更新

对于特性实现代码：

- 评估是否需要创建新的 `rust_192_features.rs`
- 或更新现有的特性模块
- 更新示例代码

---

## 📊 工作量估算

| Phase | Crates | 预计时间 | 优先级 |
|-------|--------|---------|--------|
| Phase 1 | 7 个 | 18-24 小时 | 🔴 高 |
| Phase 2 | 4 个 | 4-8 小时 | 🟡 中 |
| **总计** | **11 个** | **22-32 小时** | |

---

## ✅ 验证检查清单

每个 crate 更新完成后，需要验证：

- [ ] `Cargo.toml` 中 `rust-version = "1.92"`
- [ ] `README.md` 中版本引用已更新
- [ ] 所有核心文档中的版本引用已更新
- [ ] 代码示例中的版本注释已更新
- [ ] 编译通过：`cargo check --package <crate_name>`
- [ ] 测试通过：`cargo test --package <crate_name>`
- [ ] 示例运行正常：`cargo run --example <example_name> --package <crate_name>`

---

## 📅 建议执行顺序

### 第一轮（高优先级，预计 1-2 天）

1. c06_async（工作量最大）
2. c02_type_system
3. c01_ownership_borrow_scope
4. c05_threads
5. c07_process
6. c08_algorithms
7. c10_networks

### 第二轮（中优先级，预计 0.5-1 天）

1. c03_control_fn
2. c04_generic
3. c09_design_pattern
4. c11_macro_system

---

## 🔍 查找需要更新的文件

使用以下命令查找需要更新的文件：

```bash
# 查找所有包含 Rust 1.90/1.91 引用的文件
grep -r "Rust 1\.9[01]" crates/ --include="*.md" --include="*.rs"
grep -r "rust 1\.9[01]" crates/ --include="*.md" --include="*.rs" -i
grep -r "1\.9[01]\+" crates/ --include="*.md" --include="*.rs"
```

---

## 📚 参考资源

- [Rust 1.92.0 Release Notes](https://releases.rs/docs/1.92.0/)
- [c12_wasm 更新报告](./crates/c12_wasm/RUST_192_COMPREHENSIVE_UPDATE_REPORT.md) - 参考已完成的对齐工作
- [迁移指南](./MIGRATION_GUIDE_1.91.1_TO_1.92.0.md)

---

## 📝 更新日志

- **2025-12-11**: 创建初始计划文档
- 待更新...

---

**维护者**: Rust-Lang 项目团队
**状态**: 📋 计划阶段，等待执行
