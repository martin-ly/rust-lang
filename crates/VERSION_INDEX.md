# Rust 学习项目版本索引

> **当前活跃版本**: Rust 1.94.0
> **发布日期**: 2026-03-05
> **最后更新**: 2026-03-13
> **状态**: ✅ 100% 完成

---

## 版本归档结构

本工作区采用版本化内容管理，每个 crate 的 `src/archive/` 目录包含历史版本特性实现。

### 目录结构

```text
crates/
├── c01_ownership_borrow_scope/src/archive/
│   ├── mod.rs
│   ├── rust_190_features.rs  # Rust 1.90 (2024-04)
│   ├── rust_191_features.rs  # Rust 1.91 (2024-06)
│   └── rust_192_features.rs  # Rust 1.92 (2024-07)
├── c02_type_system/src/archive/
│   ├── mod.rs
│   ├── rust_191_features.rs
│   └── rust_192_features.rs
├── c03_control_fn/src/archive/
│   ├── mod.rs
│   ├── rust_189_features.rs  # Rust 1.89 (2024-02)
│   ├── rust_190_features.rs
│   ├── rust_191_features.rs
│   └── rust_192_features.rs
... (其他 crate 类似)
```

### 版本历史时间线

| 版本 | 发布日期 | 状态 | 归档位置 |
|------|----------|------|----------|
| Rust 1.89 | 2024-02 | 已归档 | `*/src/archive/rust_189_features.rs` |
| Rust 1.90 | 2024-04 | 已归档 | `*/src/archive/rust_190_features.rs` |
| Rust 1.91 | 2024-06 | 已归档 | `*/src/archive/rust_191_features.rs` |
| Rust 1.92 | 2024-07 | 已归档 | `*/src/archive/rust_192_features.rs` |
| Rust 1.93 | 2024-09 | 已归档 | `*/src/archive/rust_193_features.rs` |
| **Rust 1.94** | **2026-03-05** | **活跃** | `*/src/rust_194_features.rs` |
| 权威来源 | [releases.rs](https://releases.rs/docs/1.94.0/) | - | - |

---

## 使用指南

### 访问当前版本特性 (推荐)

```rust
// 使用最新 1.94 特性
use c01_ownership_borrow_scope::rust_194_features::*;
use c02_type_system::rust_194_features::*;
```

### 访问历史版本特性

```rust
// 方式1: 通过 archive 模块
use c01_ownership_borrow_scope::archive::rust_190_features::*;

// 方式2: 直接访问 (向后兼容)
use c01_ownership_borrow_scope::rust_190_features::*;
```

---

## 版本化策略

### 版本生命周期

1. **活跃版本 (Active)**
   - 当前稳定版本 (Rust 1.94)
   - 位于 `src/rust_194_features.rs`
   - 积极维护和更新

2. **归档版本 (Archived)**
   - 旧版本 (1.89-1.93)
   - 位于 `src/archive/rust_*.rs`
   - 只读保留，供参考学习

3. **废弃版本 (Deprecated)**
   - 已弃用的特性
   - 移至 `docs/archive/deprecated/`
   - 不再维护

### 更新流程

```text
Rust 新版本发布
       ↓
创建 rust_XX_features.rs
       ↓
将旧版本移至 archive/
       ↓
更新版本索引
       ↓
验证编译和测试
```

---

## Crate 版本覆盖情况

| Crate | 1.89 | 1.90 | 1.91 | 1.92 | 1.93 | 1.94 (活跃) |
|-------|------|------|------|------|------|-------------|
| c01_ownership_borrow_scope | - | ✅ | ✅ | ✅ | - | ✅ |
| c02_type_system | - | - | ✅ | ✅ | - | ✅ |
| c03_control_fn | ✅ | ✅ | ✅ | ✅ | - | ✅ |
| c04_generic | ✅ | ✅ | ✅ | ✅ | - | ✅ |
| c05_threads | - | ✅ | ✅ | ✅ | - | ✅ |
| c06_async | - | ✅ | ✅ | ✅ | - | ✅ |
| c07_process | - | ✅ | ✅ | ✅ | - | ✅ |
| c08_algorithms | - | - | ✅ | ✅ | - | ✅ |
| c09_design_pattern | ✅ | ✅ | ✅ | ✅ | - | ✅ |
| c10_networks | - | - | ✅ | ✅ | - | ✅ |
| c11_macro_system | - | - | ✅ | ✅ | - | ✅ |
| c12_wasm | - | - | ✅ | ✅ | ✅ | ✅ |

---

## 相关文档

- [Rust 1.94 特性分析](../docs/research_notes/RUST_194_COMPREHENSIVE_ANALYSIS.md) (待创建)
- [版本化文档模板](../docs/templates/versioned_doc_template.md) (待创建)
- [项目路线图](./CRITICAL_ANALYSIS_AND_ROADMAP_2026_03_12.md)

---

**维护者**: Rust 学习项目团队
**文档版本**: 1.0
**创建日期**: 2026-03-12
