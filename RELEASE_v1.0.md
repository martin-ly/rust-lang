# Rust 知识体系 v1.0 发布说明

> **发布日期**: 2026-05-13
> **版本**: v1.0.0
> **状态**: 正式发布

---

## 什么是 Rust 知识体系？

一个**分层、可验证、可搜索**的 Rust 概念知识库，覆盖从入门到形式化验证的完整学习路径。

区别于传统的"代码示例集合"，本体系采用**七层认知架构**：

```text
L0 元层 ──→ 学习指南、速查卡片、自测题库、质量仪表盘
L1 基础 ──→ 所有权、借用、生命周期、类型系统
L2 进阶 ──→ Trait、泛型、内存管理、错误处理
L3 高级 ──→ 并发、异步、unsafe、宏
L4 形式化 ─→ 线性逻辑、类型论、所有权形式化、RustBelt
L5 对比 ──→ 多语言范式对比、安全边界分析
L6 生态 ──→ 工具链、设计模式、核心 crate、应用领域
L7 未来 ──→ AI 集成、形式化方法、语言演进
```

---

## 核心特性

### 📚 四层可用化文件

| 文件 | 用途 | 规模 |
|:---|:---|:---|
| [`learning_guide.md`](concept/00_meta/learning_guide.md) | 4条学习路径（系统/面试/学术/问题驱动） | ~300行 |
| [`quick_reference.md`](concept/00_meta/quick_reference.md) | A-Z概念速查 + 17个错误码 + 跨语言对照 | ~630行 |
| [`self_assessment.md`](concept/00_meta/self_assessment.md) | 80道自测题（L1-L6覆盖，含折叠答案） | ~850行 |
| [`kb_quality_dashboard.md`](reports/kb_quality_dashboard.md) | 自动化质量审计仪表盘 | 实时生成 |

### 🔍 可搜索索引

- `concept_search_index.json`：452个概念的倒排索引
- 支持概念 → 文件/章节/相关度 的精准定位

### ✅ 自动化质量门禁

```bash
python scripts/kb_auditor.py
```

输出：
- 37个文件的7项质量检查
- 死链检测、风险文件识别
- 定理链/反命题/代码块/Mermaid图统计
- `concept_kb.json` 结构化导出

### 🔗 跨层映射

每个核心概念文件包含：
- **认知路径**：从直觉到形式化的学习递进
- **过渡段**：跨层映射（L3 → L4 形式化、L4 → L5 对比）
- **来源标注**：Wikipedia、CMU课程、POPL论文可追溯
- **定理链**：⟹ 推理链标注
- **反命题**：边界决策树

---

## 快速开始

```bash
# 1. 克隆仓库
git clone <repo-url>
cd rust-lang

# 2. 运行质量审计
python scripts/kb_auditor.py

# 3. 查看仪表盘
cat reports/kb_quality_dashboard.md

# 4. 构建搜索索引
python scripts/build_search_index.py
```

### 学习路径建议

| 目标 | 起点 | 时长 |
|:---|:---|:---|
| 系统掌握 | `learning_guide.md` → L1 → L2 → L3 | 40-60h |
| 面试准备 | `quick_reference.md` + `self_assessment.md` | 8-12h |
| 学术深入 | L4 形式化层 + `semantic_space.md` | 20-30h |
| 问题驱动 | `self_assessment.md` 错题 → 对应章节 | 按需 |

---

## 质量基线

| 指标 | 数值 | 状态 |
|:---|:---|:---|
| 总文件数 | 37 | ✅ |
| 定理链 (⟹) | 277 | ✅ |
| 反命题 | 98 | ✅ |
| Mermaid图 | 178 | ✅ |
| 代码块 | 319 | ✅ |
| 死链 | 0 | ✅ |
| 风险文件（非L0）| 0 | ✅ |
| 认知路径覆盖率 | 100% | ✅ |

---

## 致谢

- **Rust 社区**: The Rust Programming Language、Rustonomicon、Rust Reference
- **学术来源**: RustBelt (POPL 2018)、Oxide (PLDI)、Tree Borrows (POPL 2019)
- **教育资源**: CMU 17-363、Stanford CS340R、TRPL

---

> **许可证**: MIT
> **维护者**: rust-lang 知识体系项目组
> **问题反馈**: 通过 GitHub Issues 提交
