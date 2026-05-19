# 文档中心

> **项目**: Rust系统化学习项目
> **版本**: 2026.05
> **Rust 版本**: 1.95.0+ (Edition 2024)
> **最后更新**: 2026-05-08

---

## 📚 文档导航

### 核心文档

| 文档 | 描述 | 推荐人群 |
|------|------|---------|
| [00_MASTER_INDEX.md](00_MASTER_INDEX.md) | 文档总索引 | 所有人 |
| [2026_RUST_ECOSYSTEM_COMPREHENSIVE_REVIEW_WITH_CITATIONS.md](2026_RUST_ECOSYSTEM_COMPREHENSIVE_REVIEW_WITH_CITATIONS.md) | **2026生态梳理（权威引用版）** | 所有开发者 |
| [AUTHORITATIVE_SOURCES_AND_CITATIONS.md](AUTHORITATIVE_SOURCES_AND_CITATIONS.md) | 学术论文引用汇总 | 研究人员 |
| [MIGRATION_GUIDE_2026.md](MIGRATION_GUIDE_2026.md) | 2026迁移指南 | 升级用户 |
| [TERMINOLOGY_STANDARD.md](TERMINOLOGY_STANDARD.md) | 术语标准 | 所有人 |

### 学习文档

| 文档 | 描述 | 位置 |
|------|------|------|
| 学习路径指南 | 学习路线规划 | [01_learning/](01_learning/) |
| 跨模块导航 | 模块间导航 | [01_learning/](01_learning/) |
| 跨模块学习路线图 | 详细学习路线 | [01_learning/](01_learning/) |
| 跨模块实战项目 | 实践项目指南 | [03_practice/](03_practice/) |

### 前沿特性文档 (Rust 1.95–1.96+)

| 文档 | 描述 | 版本 |
|------|------|------|
| Miri 实战指南 | UB 检测与内存安全验证 | [05_guides/MIRI_PRACTICAL_GUIDE.md](05_guides/MIRI_PRACTICAL_GUIDE.md) |
| Cranelift 后端指南 | 快速调试编译后端 | [06_toolchain/CRANELIFT_BACKEND_GUIDE.md](06_toolchain/CRANELIFT_BACKEND_GUIDE.md) |
| TOML v1.1 Cargo 指南 | Cargo.toml 新语法 | [06_toolchain/TOML_V11_CARGO_GUIDE.md](06_toolchain/TOML_V11_CARGO_GUIDE.md) |
| Polonius 下一代 Borrow Checker | 基于 Datalog 的生命周期推断 | [04_research/POLONIUS_NEXT_GEN_BORROW_CHECKER.md](04_research/POLONIUS_NEXT_GEN_BORROW_CHECKER.md) |
| VerusBelt (PLDI 2026) | 形式化验证语义基础 | [04_research/VERUSBELT_PLDI_2026.md](04_research/VERUSBELT_PLDI_2026.md) |
| Unsafe Fields 预览 | 更细粒度的 unsafe 声明 | [05_guides/UNSAFE_FIELDS_PREVIEW.md](05_guides/UNSAFE_FIELDS_PREVIEW.md) |
| 下一代 Trait Solver | 基于逻辑编程的类型推断 | [04_research/NEXT_GENERATION_TRAIT_SOLVER.md](04_research/NEXT_GENERATION_TRAIT_SOLVER.md) |
| C++ ↔ Rust 互操作评估 | `cxx`/`bindgen` 安全 FFI 实践 | [05_guides/CXX_RUST_INTEROP_EVALUATION.md](05_guides/CXX_RUST_INTEROP_EVALUATION.md) |
| Rust for Linux 工具链 | 内核模块开发与工具链 | [06_toolchain/RUST_FOR_LINUX_TOOLING_GUIDE.md](06_toolchain/RUST_FOR_LINUX_TOOLING_GUIDE.md) |
| Endangered by Language (POPL 2026) | 编译器如何"拯救"危险语言模式 | [04_research/ENDANGERED_BY_LANGUAGE_SAVED_BY_COMPILER_POPL_2026.md](04_research/ENDANGERED_BY_LANGUAGE_SAVED_BY_COMPILER_POPL_2026.md) |

### 子目录分类

| 目录 | 内容类型 | 文件数 |
|------|---------|--------|
| [01_learning/](01_learning/) | 学习规划 | 7 |
| [02_reference/](02_reference/) | 参考资料 | 31 |
| [03_practice/](03_practice/) | 实践练习 | 2 |
| [04_thinking/](04_thinking/) | 思维方法 | 7 |
| [05_guides/](05_guides/) | 使用指南 | 30 |
| [06_toolchain/](06_toolchain/) | 工具链 | 21 |
| [07_project/](07_project/) | 项目管理 | 14 |

---

## 🎯 快速开始

### 新用户推荐路径

```
1. [项目README](../README.md)
   ↓
2. [2026_RUST_ECOSYSTEM_COMPREHENSIVE_REVIEW_WITH_CITATIONS.md](2026_RUST_ECOSYSTEM_COMPREHENSIVE_REVIEW_WITH_CITATIONS.md)
   ↓
3. [01_learning/LEARNING_PATH_GUIDE_2025_10_24.md](01_learning/LEARNING_PATH_GUIDE_2025_10_24.md)
   ↓
4. [MIGRATION_GUIDE_2026.md](MIGRATION_GUIDE_2026.md)
```

### 研究人员路径

```
1. [2026_RUST_ECOSYSTEM_COMPREHENSIVE_REVIEW_WITH_CITATIONS.md](2026_RUST_ECOSYSTEM_COMPREHENSIVE_REVIEW_WITH_CITATIONS.md)
   ↓
2. [AUTHORITATIVE_SOURCES_AND_CITATIONS.md](AUTHORITATIVE_SOURCES_AND_CITATIONS.md)
   ↓
3. [04_thinking/](04_thinking/) 和 [research_notes/](research_notes/)
```

---

## 📁 文档组织

```
docs/
├── 核心文档 (6个)          # 放在根目录，快速访问
│   ├── 00_MASTER_INDEX.md
│   ├── 2026_RUST_ECOSYSTEM_COMPREHENSIVE_REVIEW_WITH_CITATIONS.md
│   ├── AUTHORITATIVE_SOURCES_AND_CITATIONS.md
│   ├── MIGRATION_GUIDE_2026.md
│   ├── TERMINOLOGY_STANDARD.md
│   └── README.md
│
├── 01_learning/            # 学习规划
├── 02_reference/           # 参考资料
├── 03_practice/            # 实践练习
├── 04_thinking/            # 思维方法
├── 05_guides/              # 使用指南
├── 06_toolchain/           # 工具链
├── 07_project/             # 项目管理
├── archive/                # 归档
├── backup/                 # 备份
├── research_notes/         # 研究笔记
├── rust-formal-engineering-system/  # 形式化工程
├── rust-ownership-decidability/     # 所有权可判定性
└── templates/              # 模板
```

---

## 🔬 权威来源

本项目引用以下权威来源：

### 学术论文

- **Tree Borrows**: PLDI 2025 Distinguished Paper (DOI: 10.1145/3735592)
- **Miri**: POPL 2026 (DOI: 10.1145/3704904)

### 官方来源

- Rust官方博客 (blog.rust-lang.org)
- Rust Edition Guide
- Miri官方文档

详见 [AUTHORITATIVE_SOURCES_AND_CITATIONS.md](AUTHORITATIVE_SOURCES_AND_CITATIONS.md)

---

## 📝 文档维护

### 命名规范

- 核心文档: 大写 snake_case
- 子目录文档: 使用连字符或下划线
- 日期标记: YYYY_MM_DD 格式

### 更新策略

1. **跟随Rust发布**: 每6周更新工具链文档
2. **学术跟踪**: 关注PLDI/POPL/ICFP等顶会
3. **定期归档**: 过时报告移入archive/

---

**返回项目主页**: [../README.md](../README.md)
**贡献指南**: [../CONTRIBUTING.md](../CONTRIBUTING.md)
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
