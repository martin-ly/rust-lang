# Rust 所有权与可判定性：视频课程大纲（20 集）

> 面向「想真正吃透 Rust 所有权系统 + 可判定性理论」的开发者与研究者  
> 课程严格对齐本知识库已有文档与练习，只做「提炼与编排」，不重复造轮子。

---

## 1. 课程定位与学习路径

- **目标人群**
  - 有一定 Rust 基础，希望系统理解所有权 / 借用 / 生命周期背后原理的开发者
  - 做编译器 / 形式化验证 / PL 研究的工程师和学生
  - 维护大型 Rust 工程、希望「和编译器对话」的人

- **整体结构（4 个模块，共 20 集）**
  - **模块 A（1–5 集）**: 所有权系统总览与直觉打底
  - **模块 B（6–10 集）**: 形式语义与可判定性理论
  - **模块 C（11–16 集）**: 工具链与实践（Miri / Prusti / Creusot / Async / Unsafe）
  - **模块 D（17–20 集）**: 对比研究、研究前沿与综合案例

- **和现有文档的映射**
  - 每一集都**显式关联**到现有的 1～2 篇主文档 + 1 份练习/反例库
  - 课程只提供「讲解与引导」，**技术细节仍以文档为权威来源**

---

## 2. 模块 A：直觉与全景（第 1–5 集）

### 第 1 集：Rust 所有权系统全景速览（30 分钟）
- **核心问题**: Rust 为什么需要所有权系统？和「可判定性」有什么关系？
- **内容要点**
  - 所有权、借用、生命周期的「三角关系」
  - 本知识库 4 层结构快速导览：实践 → 可视化 → 理论 → 形式化
  - 编译器在做什么：从源码到 MIR 再到 borrow check
- **对应文档**
  - `rust_ownership_semantics_complete_analysis.md`（总览部分）
  - `文档索引与关联指南.md`

### 第 2 集：所有权与仿射逻辑直觉（30 分钟）
- **核心问题**: 「一个值只能被用一次」背后的逻辑是什么？
- **内容要点**
  - 线性逻辑 vs 仿射逻辑：为什么 Rust 选择「仿射」
  - 资源视角下的变量：`Move` / `Copy` / `Drop`
  - 表驱动讲解：操作 vs 资源守恒/丢弃
- **对应文档**
  - `rust_ownership_semantics_complete_analysis_v2.md`（逻辑直觉章节）
  - `术语表.md`（线性/仿射相关条目）

### 第 3 集：借用状态机与生命周期视图（35 分钟）
- **核心问题**: 编译器如何「看见」借用与生命周期？
- **内容要点**
  - 借用状态机：`Free/Shared/Mut/Reserved`
  - 生命周期作为「控制流路径集合」而不是时间线
  - 图解 `&T` / `&mut T` 的合法/非法组合
- **对应文档与可视化**
  - `visuals/mermaid/03_借用状态机.mmd`
  - `visuals/svg/borrow_checker_flow.svg`
  - `补充材料：详细实例与反例库.md`（借用相关反例）

### 第 4 集：错误诊断与反例驱动学习（35 分钟）
- **核心问题**: 如何系统化理解「这些编译错误到底在说什么」？
- **内容要点**
  - 典型错误模式：moved value / multiple mutable borrows / dangling reference
  - 从错误信息回溯到「形式语义」中的不变式破坏
  - 使用反例库做「错误分类」而不是逐例记忆
- **对应文档**
  - `extended_examples_and_counterexamples.md`
  - `FAQ.md`（错误相关问题）

### 第 5 集：从实践到形式化：为什么要谈可判定性（30 分钟）
- **核心问题**: 「可判定」这件事对一线开发者有什么现实意义？
- **内容要点**
  - 类型检查一定要终止：编译器不能变成定理证明器
  - 「表达力」与「算法可判定性」之间的 trade-off
  - Rust 在实践中如何在两者之间做折中
- **对应文档**
  - `Rust所有权系统的形式语义分析：静态检查与动态判断的边界.md`
  - `multi_dimensional_analysis.md`（表达力 vs 可判定性维度）

---

## 3. 模块 B：形式语义与可判定性（第 6–10 集）

### 第 6 集：核心语法与判断形式（40 分钟）
- **核心问题**: 「一门语言的形式语义」具体长什么样？
- **内容要点**
  - 抽象语法 `meta-model/01_abstract_syntax.md` 导读
  - 判断形式：`has_type` / `eval` / `ownership_safe` / `subregion`
  - 如何从自然语言规则抽象成推导规则
- **对应文档**
  - `meta-model/01_abstract_syntax.md`
  - `supplementary_formal_definitions.md`

### 第 7 集：借用安全性定理与分离逻辑（45 分钟）
- **核心问题**: 「借用一定安全」在数学上怎么表达和证明？
- **内容要点**
  - 借用安全性定理结构拆解：前提 / 结论 / 不变式
  - 分离逻辑直观解释：为什么 `*` 和所有权这么搭
  - 示例推导：简单函数的 Hoare triple 到 Rust 代码
- **对应文档**
  - `guides/formal-proofs-supplement.md`
  - `papers/rustbelt-deep-dive.md`（RustBelt 概览部分）

### 第 8 集：类型推断的 PSPACE 完全性（45 分钟）
- **核心问题**: 为什么 Rust 的类型推断既「可判定」又「理论上很难」？
- **内容要点**
  - 从 HM 系统一步步加：lifetime / traits / associated types
  - 类型推断问题的约束生成 + 求解视角
  - PSPACE 上下界证明思路（直观版）：TQBF 归约
- **对应文档**
  - `04-decidability-analysis/04-01-type-inference.md`
  - `theorems/decidability_theorems.md` 中相关条目

### 第 9 集：借用检查的 P 完全性（40 分钟）
- **核心问题**: 为什么借用检查在理论上「刚好够快」？
- **内容要点**
  - 区域约束求解 ≈ 图可达性问题
  - NLL / Polonius 的算法视角（数据流 vs Datalog）
  - AND-OR 图可达性 → 借用约束 的直观归约
- **对应文档**
  - `04-decidability-analysis/04-02-borrow-checking.md`
  - `visuals/svg/decidability_layers.svg`

### 第 10 集：可判定性边界与不可判定区域（40 分钟）
- **核心问题**: Rust 在语言设计上刻意「不做」哪些事情？
- **内容要点**
  - System F / 依赖类型为何走向不可判定
  - Rust 对「表达力」的取舍：宏 / const generics / unsafe
  - Halting Problem / Rice 定理在本项目中的具体落点
- **对应文档**
  - `rust_ownership_semantics_complete_analysis_v2.md`（边界章节）
  - `补充材料：详细实例与反例库.md`（不可判定相关反例）

---

## 4. 模块 C：工具链与实践（第 11–16 集）

### 第 11 集：Miri 与 Stacked/Tree Borrows（40 分钟）
- **核心问题**: 如何用 Miri 把「未定义行为」变成可以观察的对象？
- **内容要点**
  - Miri 运行模型与常见 UB 模式
  - Stacked Borrows & Tree Borrows 的直觉图解
  - 用 Miri 验证本知识库中的典型示例
- **对应文档**
  - `guides/miri-tutorial.md`
  - `papers/stacked-tree-borrows-analysis.md`

### 第 12 集：Prusti：从注解到证明（45 分钟）
- **核心问题**: 如何在 Rust 代码上写出「可验证规格」？
- **内容要点**
  - 前置/后置条件、循环不变式、数据结构不变式
  - 将「所有权直觉」转为 Prusti 注解的套路
  - 一个小项目：账户系统的安全性证明
- **对应文档**
  - `guides/prusti-tutorial.md`
  - `exercises/src/advanced_patterns.rs`（可改写为带规格的示例）

### 第 13 集：Creusot 与 Why3 管线（40 分钟）
- **核心问题**: 如何把 Rust 代码送进 Why3 / SMT 求解器？
- **内容要点**
  - Creusot 注解语法与思维模式
  - 典型数据结构（栈/队列/二分查找）的形式化规格
  - 与 RustBelt / Oxide 在目标上的差异与互补
- **对应文档**
  - `guides/creusot-tutorial.md`
  - `papers/oxide-detailed-analysis.md`

### 第 14 集：Async/Await 所有权形态（45 分钟）
- **核心问题**: `async fn` 之后，所有权和生命周期「去哪了」？
- **内容要点**
  - Future 状态机展开：堆上闭包 + Pin
  - 跨 `await` 点的借用与自引用问题
  - 典型陷阱：`!Send` / `Mutex` / 任务取消
- **对应文档**
  - `扩展主题：async-await所有权分析.md`
  - `case-studies/std-future-stream-formal-analysis.md`

### 第 15 集：Unsafe Rust 的形式边界（45 分钟）
- **核心问题**: Unsafe 到底允许你「突破」哪些编译器保证？
- **内容要点**
  - Unsafe 的三层边界：别名 / 生命周期 / 内存模型
  - RustBelt 等项目如何在逻辑层面「重新收回」这些保证
  - 典型 unsafe 模式的安全封装策略（FFI / 自定义指针 / 手写容器）
- **对应文档**
  - `17-unsafe-rust/` 目录下各专题
  - `visuals/svg/unsafe_safety_boundaries.svg`

### 第 16 集：练习与项目串讲：从练习到小型验证项目（40 分钟）
- **核心问题**: 如何把零散练习升维成系统性的训练路径？
- **内容要点**
  - `exercises/exercises.md` 题型分类与推荐做题顺序
  - 三个渐进式小项目：
    - 借用检查器玩具实现
    - 小型内存安全库规范 + Prusti 校验
    - Miri + 反例库驱动的「错误诊断训练」
- **对应文档**
  - `exercises/exercises.md`
  - `exercises/src/*` 与 `exercises/tests/*`

---

## 5. 模块 D：对比、前沿与综合（第 17–20 集）

### 第 17 集：线性 vs 仿射 vs Rust（35 分钟）
- **核心问题**: Rust 在各种「资源敏感类型系统」中处于什么位置？
- **内容要点**
  - 线性 / 仿射 / 相关逻辑 的直观对比
  - 表格维度：可复制性 / 丢弃性 / 结构规则
  - Rust 的所有权系统如何嵌入这张版图
- **对应文档**
  - `05-comparative-study/05-01-linear-vs-affine.md`
  - `visuals/svg/decidability_layers.svg`

### 第 18 集：Rust vs C/C++/Go/Java/Swift（45 分钟）
- **核心问题**: 在「内存安全 + 可判定性 + 性能」三角里，Rust 和其它语言有何本质差异？
- **内容要点**
  - C/C++: 手动管理 + 未定义行为
  - Go/Java: GC 与类型系统边界
  - Swift: ARC 与所有权语义
  - 多维矩阵：所有权显式性 / 静态保证力度 / 工程复杂度
- **对应文档**
  - `comprehensive_analysis_c_go_rust.md`
  - `05-comparative-study/*.md`

### 第 19 集：研究前沿与开放问题（40 分钟）
- **核心问题**: 这套体系未来 5–10 年还有哪些值得做的工作？
- **内容要点**
  - RustBelt / Oxide / Aeneas / Ferrocene 等项目的后续方向
  - 类型系统扩展：GAT / specialization / effect system / dependent-ish features
  - AI + 形式化：LLM 辅助验证与代码搜索
- **对应文档**
  - `10-research-frontiers/README.md`
  - `guides/complete-formal-proofs.md`（可与研究方向呼应）

### 第 20 集：总结：从「能写」到「能证明」的 Rust 思维（40 分钟）
- **核心问题**: 学完全套内容后，日常写代码应该有什么明显变化？
- **内容要点**
  - 「编译器会怎么想」视角写代码：显式不变式 / 明确所有权交接点
  - 如何在团队内推广：代码评审 checklist / 练习路径推荐
  - 后续学习路线：Coq/Lean / PL 课程 / 研究论文
- **对应文档**
  - `00_完成总结报告_最终版.md`
  - `FINAL_100_PERCENT_COMPLETION.md`

---

## 6. 课程制作与使用建议

- **节奏建议**
  - 每集控制在 **30–45 分钟**，理论 + 示例 + 练习推荐三段式
  - 每两集为一个「学习单元」，配套 3–5 道练习题

- **配套资源**
  - 所有代码统一放在现有 `exercises/` 与案例目录，不另起仓库
  - 每集结尾给出：
    - 推荐阅读文档（本库中的具体文件）
    - 推荐练习题（`exercises/exercises.md` 中的题号）

- **更新策略**
  - 当 Rust 版本或工具链有重要变更时：
    - 优先更新文档与练习
    - 视频层面以「补充更新说明」形式追加，而不是重录全套

---

**状态**: 课程大纲已与当前知识库完成度对齐，可直接用于录制或组织线下/线上读书会。后续若知识库结构调整，本大纲可按模块微调，但整体 4×5 的结构建议保持不变。 

