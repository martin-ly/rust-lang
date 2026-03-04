# Rust所有权与可判定性 - 总体脉络索引

> **本文档提供完整的论证体系导航，使用多种思维表征方式呈现**

---

## 📚 文档体系结构

```text
rust-ownership-decidability/
│
├── 📊 思维表征文档 (本索引)
│   ├── MASTER_INDEX.md (本文档) - 总体导航
│   ├── OVERVIEW_MINDMAP.md - 思维导图与主线脉络
│   ├── ARGUMENTATION_FRAMEWORK.md - 论证推理树与概念矩阵
│   └── VISUALIZATION_GUIDE.md - 详细可视化图表
│
├── 📖 核心内容文档
│   ├── 00-foundations/ - 理论基础 (线性逻辑/仿射类型/分离逻辑)
│   ├── 01-core-concepts/ - 核心概念 (所有权/借用/生命周期)
│   ├── 02-formal-models/ - 形式化模型 (RustBelt/类型系统)
│   ├── 03-verification-tools/ - 验证工具 (Creusot等)
│   ├── 04-decidability-analysis/ - 可判定性分析
│   ├── 08-advanced-topics/ - 高级主题 (async/FFI/const泛型)
│   └── case-studies/ - 39个库案例研究
│
└── 📑 报告文档
    ├── FINAL_COMPLETION_REPORT.md
    ├── 100_PERCENT_COMPLETION_REPORT.md
    └── ...
```

---

## 🗺️ 导航地图

### 按学习目标导航

| 你的目标 | 推荐阅读 |
|:---------|:---------|
| **快速了解全貌** | 本索引 → OVERVIEW_MINDMAP.md |
| **深入理论论证** | ARGUMENTATION_FRAMEWORK.md → 00-foundations/ |
| **掌握核心概念** | 01-core-concepts/ → VISUALIZATION_GUIDE.md |
| **学习形式化验证** | 02-formal-models/ → 03-verification-tools/ |
| **解决实际问题** | case-studies/ → ARGUMENTATION_FRAMEWORK.md (决策树) |
| **研究前沿方向** | 10-research-frontiers/ |

---

## 🧠 思维表征方式总览

### 1. 思维导图 (Mind Map)

**文档**: [OVERVIEW_MINDMAP.md](./OVERVIEW_MINDMAP.md)

展示整体知识结构，从理论基础到工程应用的分层组织：

- 理论基础层 (线性逻辑/仿射类型/分离逻辑)
- 核心机制层 (所有权/借用/生命周期)
- 形式化验证层 (RustBelt/分离逻辑/协议验证)
- 工程应用层 (39个库案例/模式/最佳实践)

### 2. 论证推理树 (Argumentation Tree)

**文档**: [ARGUMENTATION_FRAMEWORK.md](./ARGUMENTATION_FRAMEWORK.md)

逻辑推导结构：

```text
内存安全保证
    ├── 所有权系统 (独占访问)
    │       ├── RAII/drop保证
    │       └── 移动语义
    ├── 借用检查器 (引用安全)
    │       ├── 共享借用 &T
    │       └── 独占借用 &mut T
    └── 类型系统 (约束传播)
            ├── 生命周期
            └── Send/Sync trait
```

### 3. 多维概念矩阵 (Concept Matrix)

**文档**: [ARGUMENTATION_FRAMEWORK.md](./ARGUMENTATION_FRAMEWORK.md)

对比分析不同概念维度：

- 类型系统维度矩阵 (所有权 vs 借用 vs 生命周期)
- 形式化方法对比矩阵 (RustBelt vs Creusot vs Prusti)
- 库案例形式化深度矩阵

### 4. 应用场景决策树 (Decision Tree)

**文档**: [ARGUMENTATION_FRAMEWORK.md](./ARGUMENTATION_FRAMEWORK.md)

实际选择指南：

- 类型选择决策树 (何时使用 Cell/RefCell/Mutex)
- 并发模型选择决策树 (rayon vs tokio vs actix)
- 验证工具选择决策树

### 5. 流程与状态图 (Flow & State Diagrams)

**文档**: [VISUALIZATION_GUIDE.md](./VISUALIZATION_GUIDE.md)

动态过程可视化：

- 借用检查流程图
- 类型状态转换图 (Owned → Borrowed → Moved → Dropped)
- 生命周期包含关系图

### 6. 层次金字塔 (Hierarchy Pyramid)

**文档**: [VISUALIZATION_GUIDE.md](./VISUALIZATION_GUIDE.md)

安全保证层次：

```text
Level 4: 形式化验证 (定理证明)
Level 3: 工具验证 (模型检测)
Level 2: 类型系统 (编译检查)
Level 1: 运行时检查 (panic)
Level 0: 硬件保护 (MMU)
```

### 7. 时间线与演化 (Timeline)

**文档**: [VISUALIZATION_GUIDE.md](./VISUALIZATION_GUIDE.md)

历史发展脉络：

- 1970s: 线性逻辑诞生
- 1990s: 分离逻辑发展
- 2010s: RustBelt项目
- 2015: Rust 1.0发布
- 2018: NLL引入
- 2020s: 形式化工具成熟

---

## 🔑 核心论证脉络

### 主线论证链

```mermaid
graph LR
    A[线性逻辑<br/>资源敏感] --> B[仿射类型<br/>使用≤1次]
    B --> C[所有权系统<br/>独占访问]
    C --> D[借用检查器<br/>引用安全]
    D --> E[Rust编译器<br/>类型检查]
    E --> F[39个库案例<br/>工程验证]

    style A fill:#f9f
    style C fill:#bbf
    style F fill:#bfb
```

### 三条核心定理链

1. **所有权正确性**: 线性逻辑资源敏感 → 所有权独占 → RAII → 无悬垂指针
2. **借用安全性**: 仿射类型弱化 → 引用规则 → NLL → 无数据竞争
3. **形式化保证**: 分离逻辑 → RustBelt → Iris框架 → 数学正确性

---

## 📊 关键数据一览

| 指标 | 数量 | 说明 |
|:-----|:-----|:-----|
| 总文档数 | 50+ | 覆盖理论与应用 |
| 形式化定义 | 200+ | 跨39个库 |
| 安全定理 | 145+ | 多层次保证 |
| 代码示例 | 100+ | 可运行验证 |
| 案例研究 | 39个 | 15嵌入式+24应用级 |

---

## 🎯 快速开始指南

### 路径1: 理论学习 (适合研究者)

```text
00-foundations/ (线性逻辑/仿射类型)
    ↓
02-formal-models/ (RustBelt/类型系统)
    ↓
ARGUMENTATION_FRAMEWORK.md (论证推理树)
```

### 路径2: 工程实践 (适合开发者)

```text
01-core-concepts/ (所有权/借用/生命周期)
    ↓
case-studies/ (39个库分析)
    ↓
ARGUMENTATION_FRAMEWORK.md (决策树)
```

### 路径3: 快速概览 (适合管理者)

```text
OVERVIEW_MINDMAP.md (思维导图)
    ↓
VISUALIZATION_GUIDE.md (图表汇总)
    ↓
FINAL_COMPLETION_REPORT.md (完成报告)
```

---

## 📈 可视化图表索引

| 图表类型 | 位置 | 用途 |
|:---------|:-----|:-----|
| 思维导图 | OVERVIEW_MINDMAP.md | 整体结构 |
| 论证推理树 | ARGUMENTATION_FRAMEWORK.md | 逻辑推导 |
| 概念对比矩阵 | ARGUMENTATION_FRAMEWORK.md | 概念辨析 |
| 应用场景决策树 | ARGUMENTATION_FRAMEWORK.md | 实践指南 |
| 借用检查流程图 | VISUALIZATION_GUIDE.md | 编译过程 |
| 类型状态图 | VISUALIZATION_GUIDE.md | 状态转换 |
| 层次金字塔 | VISUALIZATION_GUIDE.md | 安全层级 |
| 演化时间线 | VISUALIZATION_GUIDE.md | 历史脉络 |
| 学习路径图 | VISUALIZATION_GUIDE.md | 进阶路线 |

---

## 🔗 相关资源

- **Rust官方**: <https://www.rust-lang.org/>
- **RustBelt项目**: <https://plv.mpi-sws.org/rustbelt/>
- **Creusot**: <https://github.com/creusot-rs/creusot>
- **The Rust Book**: <https://doc.rust-lang.org/book/>

---

**维护者**: Rust Formal Methods Team
**更新日期**: 2026-03-05
**状态**: ✅ 100% 完成
