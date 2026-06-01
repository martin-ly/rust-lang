# 文档中心

> **分级**: [B]
> **Bloom 层级**: L2-L3 (理解/应用)

> **项目**: Rust系统化学习项目
> **版本**: 2026.05
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **最后更新**: 2026-05-08

---

## 📚 文档导航
>
> **[来源: Rust Official Docs]**

### 核心文档
>
> **[来源: Rust Official Docs]**

| 文档 | 描述 | 推荐人群 |
|------|------|---------|
| [10_00_master_index.md](./00_master_index.md) | 文档总索引 | 所有人 |
| [10_2026_rust_ecosystem_comprehensive_review_with_citations.md](./10_2026_rust_ecosystem_comprehensive_review_with_citations.md) | **2026生态梳理（权威引用版）** | 所有开发者 |
| [10_authoritative_sources_and_citations.md](./10_authoritative_sources_and_citations.md) | 学术论文引用汇总 | 研究人员 |
| [10_migration_guide_2026.md](./10_migration_guide_2026.md) | 2026迁移指南 | 升级用户 |
| [10_terminology_standard.md](./10_terminology_standard.md) | 术语标准 | 所有人 |

### 学习文档
>
> **[来源: Rust Official Docs]**

| 文档 | 描述 | 位置 |
|------|------|------|
| 学习路径指南 | 学习路线规划 | [01_learning/](01_learning/) |
| 跨模块导航 | 模块间导航 | [01_learning/](01_learning/) |
| 跨模块学习路线图 | 详细学习路线 | [01_learning/](01_learning/) |
| 跨模块实战项目 | 实践项目指南 | [03_practice/](03_practice/) |

### 前沿特性文档 (Rust 1.95–1.96+)

| 文档 | 描述 | 版本 |
|------|------|------|
| Miri 实战指南 | UB 检测与内存安全验证 | [05_guides/05_miri_practical_guide.md](05_guides/05_miri_practical_guide.md) |
| Cranelift 后端指南 | 快速调试编译后端 | [06_toolchain/06_cranelift_backend_guide.md](06_toolchain/06_cranelift_backend_guide.md) |
| TOML v1.1 Cargo 指南 | Cargo.toml 新语法 | [06_toolchain/06_toml_v11_cargo_guide.md](06_toolchain/06_toml_v11_cargo_guide.md) |
| Polonius 下一代 Borrow Checker | 基于 Datalog 的生命周期推断 | [04_research/04_polonius_next_gen_borrow_checker.md](04_research/04_polonius_next_gen_borrow_checker.md) |
| VerusBelt (PLDI 2026) | 形式化验证语义基础 | [04_research/04_verusbelt_pldi_2026.md](04_research/04_verusbelt_pldi_2026.md) |
| Unsafe Fields 预览 | 更细粒度的 unsafe 声明 | [05_guides/05_unsafe_fields_preview.md](05_guides/05_unsafe_fields_preview.md) |
| 下一代 Trait Solver | 基于逻辑编程的类型推断 | [04_research/04_next_generation_trait_solver.md](04_research/04_next_generation_trait_solver.md) |
| C++ ↔ Rust 互操作评估 | `cxx`/`bindgen` 安全 FFI 实践 | [05_guides/05_cxx_rust_interop_evaluation.md](05_guides/05_cxx_rust_interop_evaluation.md) |
| Rust for Linux 工具链 | 内核模块开发与工具链 | [06_toolchain/06_rust_for_linux_tooling_guide.md](06_toolchain/06_rust_for_linux_tooling_guide.md) |
| Endangered by Language (POPL 2026) | 编译器如何"拯救"危险语言模式 | [04_research/04_endangered_by_language_saved_by_compiler_popl_2026.md](04_research/04_endangered_by_language_saved_by_compiler_popl_2026.md) |

### 子目录分类

| 目录 | 内容类型 | 文件数 |
|------|---------|--------|
| [01_learning/](01_learning/) | 学习规划 | 10 |
| [02_reference/](02_reference/) | 参考资料 | 38 |
| [03_practice/](03_practice/) | 实践练习 | 17 |
| [04_thinking/](04_thinking/) | 思维方法 | 7 |
| [05_guides/](05_guides/) | 使用指南 | 36 |
| [06_toolchain/](06_toolchain/) | 工具链 | 17 |
| [07_project/](07_project/) | 项目管理 | 16 |

---

## 🎯 快速开始

### 新用户推荐路径

```
1. [项目README](../README.md)
   ↓
2. [10_2026_rust_ecosystem_comprehensive_review_with_citations.md](./10_2026_rust_ecosystem_comprehensive_review_with_citations.md)
   ↓
3. [01_learning/01_learning_path_guide_2025_10_24.md](01_learning/01_learning_path_guide_2025_10_24.md)
   ↓
4. [10_migration_guide_2026.md](./10_migration_guide_2026.md)
```

### 研究人员路径

```
1. [10_2026_rust_ecosystem_comprehensive_review_with_citations.md](./10_2026_rust_ecosystem_comprehensive_review_with_citations.md)
   ↓
2. [10_authoritative_sources_and_citations.md](./10_authoritative_sources_and_citations.md)
   ↓
3. [04_thinking/](04_thinking/) 和 [research_notes/](research_notes/)
```

---

## 📁 文档组织

```
docs/
├── 核心文档 (6个)          # 放在根目录，快速访问
│   ├── 10_00_master_index.md
│   ├── 10_2026_rust_ecosystem_comprehensive_review_with_citations.md
│   ├── 10_authoritative_sources_and_citations.md
│   ├── 10_migration_guide_2026.md
│   ├── 10_terminology_standard.md
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

详见 [10_authoritative_sources_and_citations.md](./10_authoritative_sources_and_citations.md)

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
**贡献指南**: 10_contributing.md
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 权威来源索引

> **[来源: Wikipedia - Rust (programming language)]**

> **[来源: Rust Reference - doc.rust-lang.org/reference]**

> **[来源: TRPL - The Rust Programming Language]**

> **[来源: Rust Standard Library - doc.rust-lang.org/std]**

> **[来源: ACM - Systems Programming Languages]**

> **[来源: IEEE - Programming Language Standards]**

> **[来源: RFCs - github.com/rust-lang/rfcs]**

> **[来源: Rustonomicon - doc.rust-lang.org/nomicon]**
