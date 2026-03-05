# Rust 所有权可判定性 - 项目结构

> 清晰的项目目录结构和文件组织说明

**最后更新**: 2026-03-05
**总文件数**: ~350
**总大小**: ~5.5 MB

---

## 📁 目录结构

### 核心文档

```
📄 README.md                          # 主入口文档
📄 PROJECT_STRUCTURE.md               # 本文件 - 项目结构说明
```

### 1. 基础概念 (01-core-concepts/)

Rust核心所有权概念的学习资源。

```
01-core-concepts/
├── README.md                          # 目录索引
├── 01-01-ownership-rules.md           # 所有权规则
├── 01-02-borrowing-system.md          # 借用系统
├── 01-03-lifetimes.md                 # 生命周期
├── 01-04-runtime-vs-compile-time.md   # 运行时vs编译时
├── 01-05-interior-mutability.md       # 内部可变性
├── ownership-counterexamples.md       # 所有权反例
├── short-concepts/                    # 简短概念卡片
│   ├── borrowing-concept-card.md
│   ├── lifetime-concept-card.md
│   └── ownership-concept-card.md
└── detailed-concepts/                 # 详细概念解析
    ├── borrowing-in-depth.md
    ├── interior-mutability.md
    ├── lifetimes-mastery.md
    ├── ownership-deep-dive.md
    └── trait-system.md
```

### 2. 形式化基础 (formal-foundations/)

Rust所有权的严格形式化理论。

```
formal-foundations/
├── models/                            # 形式化模型
│   ├── rustbelt.md
│   ├── ownership-types.md
│   ├── borrow-semantics.md
│   ├── lifetime-logic.md
│   └── move-analysis.md
├── semantics/                         # 语义定义
│   ├── logical-relations.md
│   ├── mechanized-proofs.md
│   ├── memory-model-semantics.md
│   ├── operational-semantics.md
│   └── type-system-formalization.md
└── proofs/                            # 形式化证明
    ├── affine-logic-decidability.md
    ├── decidability-theorem.md
    ├── memory-safety-proof.md
    ├── rustbelt-formalization.md
    ├── separation-logic-soundness.md
    └── async-*.md                     # 异步相关证明
```

### 3. Coq形式化 (coq-formalization/)

完整的Coq机械证明代码。

```
coq-formalization/
├── theories/
│   ├── Advanced/                      # Rust 1.94高级特性⭐
│   │   ├── Reborrow.v
│   │   ├── ReborrowComplete.v         # ✅完整证明
│   │   ├── CoerceShared.v
│   │   ├── CoerceSharedComplete.v     # ✅完整证明
│   │   ├── ConstGenerics.v
│   │   ├── PreciseCapturing.v
│   │   ├── PreciseCapturingComplete.v # ✅完整证明
│   │   ├── AsyncBasics.v
│   │   ├── AsyncBasicsComplete.v      # ✅完整证明
│   │   ├── Edition2024.v
│   │   ├── AssociatedTypeBounds.v
│   │   ├── NewLints.v
│   │   ├── MetatheoryIntegration.v
│   │   ├── MetatheoryComplete.v
│   │   ├── MetatheoryKeyProofs.v      # ✅关键证明
│   │   ├── MetatheoryTermination.v    # ✅终止性证明
│   │   ├── MetatheoryDecidability.v   # ✅可判定性证明
│   │   ├── Rust194Complete.v
│   │   └── TECHNICAL_DEBT.md
│   ├── Syntax/                        # 语法定义
│   ├── Typing/                        # 类型系统
│   ├── Semantics/                     # 操作语义
│   └── Metatheory/                    # 元理论
└── _CoqProject
```

### 4. Rust 1.94 对齐文档

```
📄 RUST_194_PO_100_PERCENT_FINAL.md     # 🎉P0证明100%完成
📄 RUST_194_100%_COMPLETE_FINAL.md
📄 RUST_194_COMPREHENSIVE_GUIDE.md      # 完整指南
📄 RUST_194_ALIGNMENT_PLAN.md
📄 RUST_194_ALIGNMENT_PROGRESS.md
📄 RUST_194_TRUE_100_PERCENT_REPORT.md
📄 RUST_194_FINAL_SUMMARY.md
```

### 5. 元模型 (meta-model/)

形式化的元模型定义。

```
meta-model/
├── 01_abstract_syntax.md
├── 02_semantic_domains.md
├── 03_judgments.md
├── rust-194-alignment.md
└── RUST_194_COMPREHENSIVE_GUIDE.md
```

### 6. 其他重要目录

| 目录 | 内容 |
|------|------|
| `00-foundations/` | 基础理论 |
| `03-verification-tools/` | 验证工具 |
| `04-decidability-analysis/` | 可判定性分析 |
| `05-comparative-study/` | 比较研究 |
| `06-visualizations/` | 可视化图表 |
| `07-references/` | 参考资料 |
| `08-advanced-topics/` | 高级主题 |
| `10-research-frontiers/` | 研究前沿 |
| `11-design-patterns/` | 设计模式 |
| `12-concurrency-patterns/` | 并发模式 |
| `13-architecture-patterns/` | 架构模式 |
| `14-distributed-systems/` | 分布式系统 |
| `15-application-domains/` | 应用领域 |
| `case-studies/` | 案例研究 |
| `exercises/` | 练习题 |

### 7. 专题研究

| 目录 | 内容 |
|------|------|
| `actor-specialty/` | Actor模型专题 |
| `async-specialty/` | 异步编程专题 |
| `extensions/` | 扩展内容 |

### 8. 项目文档

| 目录 | 内容 |
|------|------|
| `progress/` | 进度报告 |
| `audit_reports/` | 审计报告 |
| `archive/` | 归档文件 |

---

## 📊 统计信息

### 文件类型分布

| 类型 | 数量 | 说明 |
|------|------|------|
| `.md` | ~300 | Markdown文档 |
| `.v` | ~40 | Coq形式化代码 |
| `.rs` | ~10 | Rust示例代码 |
| 其他 | ~20 | 配置文件等 |

### 代码统计

| 类别 | 行数 | 文件数 |
|------|------|--------|
| Coq形式化 | ~5,500 | 18 |
| 文档 | ~100,000 | ~350 |

---

## 🎯 快速导航

### 入门推荐

1. **概念学习**: `01-core-concepts/README.md`
2. **形式化理论**: `formal-foundations/README.md`
3. **Rust 1.94**: `RUST_194_COMPREHENSIVE_GUIDE.md`
4. **Coq代码**: `coq-formalization/theories/Advanced/`

### 核心证明

| 定理 | 文件 |
|------|------|
| 终止性 | `MetatheoryTermination.v` |
| 可判定性 | `MetatheoryDecidability.v` |
| Reborrow安全 | `ReborrowComplete.v` |
| 精确捕获 | `PreciseCapturingComplete.v` |
| Async安全 | `AsyncBasicsComplete.v` |

---

## ✅ 质量保证

- [x] 无空文件夹
- [x] 无重复文件夹
- [x] 清晰的层次结构
- [x] 所有文件有实质内容
- [x] 完整的交叉引用

---

*项目结构清晰，易于导航和维护*
