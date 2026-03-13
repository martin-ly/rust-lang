# Rust 学习项目 - 版本化内容索引

> **当前活跃版本**: Rust 1.94.0+ (Edition 2024)
> **最后更新**: 2026-03-13
> **文档性质**: 活文档 (Living Document)
> **对齐状态**: ✅ 100% 完成

---

## 📊 版本状态总览

| 版本 | 状态 | 发布日期 | 特性数量 | 归档位置 |
|------|------|----------|----------|----------|
| 1.94 | 🟢 活跃维护 | 2026-02 | 5+ | crates/*/src/rust_194_features.rs |
| 1.93 | 🟡 已归档 | 2025-12 | 8+ | crates/*/src/archive/ |
| 1.92 | 🟡 已归档 | 2025-11 | 6+ | crates/*/src/archive/ |
| 1.91 | 🟡 已归档 | 2025-10 | 4+ | crates/*/src/archive/ |
| 1.90 | 🟡 已归档 | 2025-09 | 5+ | crates/*/src/archive/ |
| 1.89 | 🟡 已归档 | 2025-08 | 4+ | crates/*/src/archive/ |

### 归档统计

| 版本 | 归档文件数 | 主要路径 |
|------|-----------|----------|
| 1.89 | 10 | crates/*/src/archive/ |
| 1.90 | 15 | crates/*/src/archive/ |
| **合计** | **25** | - |

---

## 📁 版本化目录结构

```text
rust-lang/
├── crates/
│   └── c01_ownership_borrow_scope/
│       ├── src/
│       │   ├── lib.rs                    # 当前稳定版 (1.94)
│       │   ├── rust_194_features.rs      # 1.94 特性 (活跃维护)
│       │   └── archive/                  # 旧版本特性归档
│       │       ├── rust_189_features.md  # 1.89 特性 (只读)
│       │       ├── rust_190_features.md  # 1.90 特性 (只读)
│       │       ├── rust_191_features.md  # 1.91 特性 (只读)
│       │       └── rust_192_features.md  # 1.92 特性 (只读)
│       └── docs/
│           ├── current/                  # 当前版本文档
│           └── archive/                  # 历史版本文档
│
└── docs/
    ├── 06_toolchain/                     # 工具链版本文档
    │   ├── 16_rust_1.94_release_notes.md
    │   ├── 17_rust_1.93_vs_1.94_comparison.md
    │   └── ...
    │
    └── research_notes/                   # 研究笔记
        ├── RUST_194_RESEARCH_UPDATE.md
        ├── RUST_194_195_FEATURE_MATRIX.md
        └── archive/                      # 归档研究笔记
            ├── RUST_191_RESEARCH_UPDATE_2025_11_15.md
            └── RUST_192_RESEARCH_UPDATE_2025_12_11.md
```

---

## 🔗 快速导航

### 按版本导航

#### Rust 1.94 (当前版本)

- [1.94 完整发布说明](docs/06_toolchain/16_rust_1.94_release_notes.md)
- [1.94 迁移指南](docs/05_guides/RUST_194_MIGRATION_GUIDE.md)
- [1.94 研究笔记](docs/research_notes/RUST_194_RESEARCH_UPDATE.md)
- [1.94 综合应用指南](guides/RUST_194_COMPREHENSIVE_GUIDE.md)
- [1.94 对齐完成报告](RUST_194_ALIGNMENT_COMPLETE_REPORT.md)
- [1.93 vs 1.94 对比](docs/06_toolchain/17_rust_1.93_vs_1.94_comparison.md)

#### Rust 1.93

- [1.93 vs 1.92 对比](docs/06_toolchain/05_rust_1.93_vs_1.92_comparison.md)
- [1.93 兼容说明](docs/06_toolchain/06_rust_1.93_compatibility_notes.md)
- [1.93 完整变更日志](docs/06_toolchain/07_rust_1.93_full_changelog.md)

#### 历史版本 (归档)

- [1.91 vs 1.90 对比](docs/06_toolchain/04_rust_1.91_vs_1.90_comparison.md)
- [1.89-1.93 累积特性](docs/06_toolchain/10_rust_1.89_to_1.93_cumulative_features_overview.md)

### 按 Crate 导航

| Crate | 1.94 特性 | 归档 |
|-------|-----------|------|
| C01 所有权 | [rust_194_features](crates/c01_ownership_borrow_scope/src/rust_194_features.rs) | [archive/](crates/c01_ownership_borrow_scope/src/archive/) |
| C02 类型系统 | [rust_194_features](crates/c02_type_system/src/rust_194_features.rs) | [archive/](crates/c02_type_system/src/archive/) |
| C03 控制流 | [rust_194_features](crates/c03_control_fn/src/rust_194_features.rs) | [archive/](crates/c03_control_fn/src/archive/) |
| C04 泛型 | [rust_194_features](crates/c04_generic/src/rust_194_features.rs) | [archive/](crates/c04_generic/src/archive/) |
| C05 线程 | [rust_194_features](crates/c05_threads/src/rust_194_features.rs) | [archive/](crates/c05_threads/src/archive/) |
| C06 异步 | [rust_194_features](crates/c06_async/src/rust_194_features.rs) | [archive/](crates/c06_async/src/archive/) |
| C07 进程 | [rust_194_features](crates/c07_process/src/rust_194_features.rs) | [archive/](crates/c07_process/src/archive/) |
| C08 算法 | [rust_194_features](crates/c08_algorithms/src/rust_194_features.rs) | [archive/](crates/c08_algorithms/src/archive/) |
| C09 设计模式 | [rust_194_features](crates/c09_design_pattern/src/rust_194_features.rs) | [archive/](crates/c09_design_pattern/src/archive/) |
| C10 网络 | [rust_194_features](crates/c10_networks/src/rust_194_features.rs) | [archive/](crates/c10_networks/src/archive/) |
| C11 宏系统 | [rust_194_features](crates/c11_macro_system/src/rust_194_features.rs) | [archive/](crates/c11_macro_system/src/archive/) |
| C12 WASM | [rust_194_features](crates/c12_wasm/src/rust_194_features.rs) | [archive/](crates/c12_wasm/src/archive/) |

---

## 📋 版本化内容规范

### 活跃版本 (Active)

- **定义**: 当前稳定版及前一个大版本
- **维护状态**: 活跃更新，代码可运行
- **文档位置**: `crates/*/src/rust_194_features.rs`
- **更新频率**: 每 Rust 新版本发布时更新

### 归档版本 (Archived)

- **定义**: 超过两个版本的旧版本
- **维护状态**: 只读归档，保留历史价值
- **文档位置**: `crates/*/src/archive/rust_1XX_features.rs`
- **更新频率**: 不再更新，仅保留

---

## 🔄 版本更新流程

```text
Rust 新版本发布
       ↓
[Week 1] 特性扫描与评估
  - 阅读官方发布说明
  - 识别影响本项目的特性
  - 评估优先级
       ↓
[Week 2] 内容开发
  - 实现 rust_XXX_features.rs
  - 编写文档和测试
  - 验证代码可运行
       ↓
[Week 3] 归档旧版本
  - 将 1.9(X-2) 版本移至 archive/
  - 更新版本索引
  - 添加归档标记
       ↓
[Week 4] 发布与通知
  - 更新 VERSION_INDEX.md
  - 发布社区通知
  - 规划下版本任务
```

---

## 📈 版本统计

| 指标 | 数值 |
|------|------|
| 活跃版本数 | 1 (1.94) |
| 归档版本数 | 4 (1.89-1.92) |
| 版本化文件总数 | 约 60+ |
| 归档文件总数 | 约 50+ |
| 覆盖率 | 100% (12 crate) |

---

## 🔮 即将发布的版本

| 版本 | 预计发布 | 主要特性 | 准备状态 |
|------|----------|----------|----------|
| 1.95 | 2026-04 | 待定 | 🔍 监控中 |
| 1.96 | 2026-06 | 待定 | ⏳ 等待中 |

---

*最后更新: 2026-03-12*
*维护者: Rust 学习项目团队*
