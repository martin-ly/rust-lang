# 更新日志 (Changelog)

> **最后更新**: 2026-05-18

---

## [2.1.0] - 2026-05-18 — 全面对齐 2026 Project Goals + 供应链安全强化

### 🔒 供应链安全（Phase 1）

- **`deny.toml`**: 新增 cargo-deny 策略文件，管理漏洞响应、许可证白名单、crate 来源限制
- **`SECURITY_RESPONSE.md`**: 建立供应链安全响应流程（P0-P4 分级、24h/72h/1w SLA）
- **依赖修复**:
  - `bincode` 2.0.1 (unmaintained, RUSTSEC-2025-0141) → `postcard` 1.1.3
  - `rustls-pemfile` 2.2.0 (unmaintained, RUSTSEC-2025-0134) → `rustls-pki-types::pem::PemObject`
- **风险登记册**: 登记 15 项活跃 RUSTSEC，分级跟踪至 2026-06-30

### 🎯 2026 Project Goals 对齐（Phase 2）

- **`docs/07_future/rust_project_goals_2026_matrix.md`**: 50 项官方目标 → 项目内容映射矩阵，识别 12 项 🔴 缺失、8 项 🟡 待深化
- **`concept/07_future/rust_version_tracking.md`**: 更新 1.96 跟踪表，新增 `next_solver`、`adt_const_params`、`cargo_script`、`public_private_deps` 等 6 项跟踪项

### 🔬 前沿深度建设（Phase 3）

- **`concept/02_intermediate/01_traits.md` §12**: 新增 Next-generation Trait Solver 补充章节（coherence 改进、解锁效应、迁移准备）
- **`crates/c04_generic/src/next_solver_preview.rs`**: Next Solver 预览模块（Implied Bounds、Negative Impls、Coherence、GATs/TAIT 解锁、迁移指南）
- **`crates/c04_generic/src/const_generics_extended_preview.rs`**: Const Generics 扩展预览模块（`adt_const_params`、`min_generic_const_args`、组合架构模式、稳定化路线图）

---

## [2.0.0] - 2026-05-13 — 知识体系 v1.0 发布

### 🏛️ 知识体系重构（Wave 11-16）

从 "代码示例集合" 进化为 "分层概念知识体系"，覆盖 L0-L7 七个层级：

- **L0 元层**: `semantic_space.md`（表征空间理论）、`learning_guide.md`（4条学习路径）、`quick_reference.md`（A-Z概念速查）、`self_assessment.md`（80题自测题库）
- **L1 基础**: 所有权/借用/生命周期/类型系统 — 定理链 + 反命题 + 认知路径全覆盖
- **L2 进阶**: Trait/泛型/内存管理/错误处理 — Auto trait推导、GATs、Const Generics进阶
- **L3 高级**: 并发/异步/unsafe/宏 — Polonius内容、Tree Borrows对比、Pin语义
- **L4 形式化**: 线性逻辑/类型论/所有权形式化/RustBelt — 定理一致性矩阵、分离逻辑
- **L5 对比**: Rust vs C++/Go、范式矩阵、安全边界 — 跨语言对照表
- **L6 生态**: 工具链/模式/核心crate/应用领域 — Cargo工作空间、crate选型
- **L7 未来**: AI集成/形式化方法/演进 — Edition路线图、Effects System

### 🔧 质量基础设施

- **`kb_auditor.py`**: 37个文件的自动化审计（定理链、代码块、来源、交叉引用、死链检测）
- **`concept_kb.json`**: 结构化知识导出，支持搜索索引构建
- **`concept_search_index.json`**: 452个概念的倒排索引
- **GitHub Actions CI**: `.github/workflows/kb_audit.yml` — PR自动审计
- **质量仪表盘**: `reports/kb_quality_dashboard.md` — 0风险文件、0死链、100%认知路径

### 📊 质量指标

| 指标 | v1.0 | 目标 |
|:---|:---|:---|
| 文件数 | 37 | 27 ✅ |
| 定理链 | 277 | ≥270 ✅ |
| 反命题 | 98 | ≥40 ✅ |
| Mermaid图 | 178 | ≥50 ✅ |
| 代码块 | 319 | ≥150 ✅ |
| 死链 | 0 | 0 ✅ |
| 认知路径 | L1-L7: 100% | 100% ✅ |

### 🔍 Wave 17 — 代码块编译验证 + 概念一致性审计（2026-05-13）

- **`code_block_compiler.py`**: 新增编译验证工具，167 个 `rust` 代码块 100% 编译通过
- **跨文件引用修复**: 发现并修复 7 处段落编号不准确的交叉引用
- **`concept_consistency_report.md`**: 概念一致性审计报告，关键概念（Send/Sync/所有权/生命周期）定义无矛盾

---

## [1.3.0] - 2026-05-08

### 🚀 模块深度扩展（13 个 crate）

...
