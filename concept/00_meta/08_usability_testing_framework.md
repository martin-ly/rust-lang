# Rust 知识体系可用性测试框架（Usability Testing Framework）

> **EN**: Rust Knowledge Base Usability Testing Framework
> **Summary**: Defines a continuous learner-feedback loop for the knowledge base, moving from content output to validated learning outcomes.
> **内容分级**: [综述级]
> **受众**: [专家]
> **定位**: 为项目建立持续的学习者反馈闭环，从"输出内容"转向"验证学习效果"。
> **对应 Rust 版本**: 1.96.0+ (Edition 2024)
> **权威来源**: 本文件为 `concept/` 元层方法页；学习路径对照 [The Rust Programming Language](https://doc.rust-lang.org/book/) · [Rust By Example](https://doc.rust-lang.org/rust-by-example/)

---

## 测试目标

1. 验证 MVP 学习路径是否能在 40-60 小时内完成
2. 识别初学者在所有权、借用、生命周期等核心概念上的困惑点
3. 收集对嵌入式测验、导航、代码示例的反馈
4. 为内容迭代提供数据驱动的依据

---

## 测试者招募

| 组别 | 人数 | 背景要求 | 测试重点 |
|:---|:---:|:---|:---|
| **G1: 零基础** | 3 人 | 有编程意愿但无系统编程经验 | 入门门槛、术语理解、MVP 路径可行性 |
| **G2: 有经验迁移者** | 2 人 | 有 Python/Go/Java/C++ 经验 | 概念迁移、认知悬崖、L3→L4 导航 |
| **G3: 中高级 Rust** | 2 人 | 已用 Rust 写过生产代码 | 内容深度、技术准确性、专家级内容价值 |

---

## 测试任务设计

### 任务 1：MVP 路径完成度（G1 + G2）

| # | 任务 | 预计时间 | 成功标准 |
|:---|:---|:---:|:---|
| 1.1 | 完成 Day 1-3：所有权、借用、生命周期 | 6h | 能独立解释 move vs copy |
| 1.2 | 完成 Day 7-9：Trait、错误处理 | 6h | 能编写含 `Result` 的函数 |
| 1.3 | 完成 Day 13-16：并发 + CLI 项目 | 8h | 能运行多线程 CLI 工具 |
| 1.4 | 完成所有嵌入式测验 | 2h | 准确率 ≥80% |

### 任务 2：有声思维测试（G1 + G2）

要求测试者在学习 `01_ownership.md`、`02_borrowing.md`、`03_lifetimes.md` 时**出声思考**，记录：

- 首次遇到困惑的段落
- 重复阅读 ≥2 次的段落
- 认为"缺少示例"的位置
- 测验答错时的推理过程

### 任务 3：专家审阅（G3）

| 文件 | 审阅重点 |
|:---|:---|
| `03_advanced/03_unsafe.md` | Unsafe 心智模型是否准确 |
| `03_advanced/02_async.md` | Future/Pin/Waker 解释是否清晰 |
| `04_formal/03_ownership_formal.md` | Tree Borrows 表述是否最新 |
| `06_ecosystem/47_compiler_infrastructure.md` | 编译器基础设施覆盖是否完整 |

---

## 数据收集模板

```markdown
## 测试者档案

- **组别**: G1 / G2 / G3
- **编程背景**:
- **Rust 经验**: 0h / 1-50h / 50-200h / 200h+
- **测试日期**: YYYY-MM-DD

## 任务 1 完成记录

| 任务 | 完成时间 | 是否独立完成 | 遇到困难 |
|:---|:---:|:---:|:---|
| 1.1 | | | |
| 1.2 | | | |
| 1.3 | | | |
| 1.4 | | | |

## 困惑点记录（有声思维）

| 文件 | 段落/概念 | 困惑描述 | 建议改进 |
|:---|:---|:---|:---|
| | | | |

## 总体评分

- 内容有用性: 1-5
- 导航清晰度: 1-5
- 代码示例质量: 1-5
- 测验有效性: 1-5
- 是否会推荐给他人: 1-5
```

---

## 自动化度量

除人工测试外，项目还可通过脚本收集以下指标：

| 指标 | 脚本 | 用途 |
|:---|:---|:---|
| 代码块编译通过率 | `scripts/check_concept_code_blocks.py` | 验证代码可运行性 |
| 嵌入式测验覆盖率 | `scripts/check_quiz_system.py` | 确保核心概念有测验 |
| 平均阅读路径长度 | `scripts/analyze_navigation_paths.py` | 识别导航断点 |
| 僵尸内容比例 | `scripts/quarterly_zombie_audit.py` | 识别低价值内容 |
| 学习者反馈评分 | mdBook 内嵌评分组件 | 收集主观体验 |

---

## 迭代闭环

```mermaid
graph LR
    A[收集测试数据] --> B[识别 TOP 10 困惑点]
    B --> C[优先修改 01_ownership/02_borrowing/03_lifetimes]
    C --> D[重新运行可用性测试]
    D --> E{困惑点减少?}
    E -->|否| B
    E -->|是| F[发布改进版本]
```

---

> **来源**: [Brown University — Profiling Programming Language Learning](https://rust-book.cs.brown.edu/) · [Cognitive Load Theory — Sweller 1988]
> **状态**: 框架已建立，待招募测试者执行首轮测试
