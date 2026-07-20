# TRPL 3rd Ed / Brown University Interactive Book 对齐审计

> **审计日期**: 2026-06-19
> **审计版本**: Rust 1.96.0+ (Edition 2024)
> **对比来源**:
>
> - [The Rust Programming Language, 3rd Edition](https://doc.rust-lang.org/book/)（官方稳定版，Rust 1.90.0+ / Edition 2024）
> - [Brown University Interactive Rust Book](https://rust-book.cs.brown.edu/)（Aquascope 可视化 + 嵌入式测验）
> - 本项目 `concept/`、`knowledge/`、`book/` 目录

---

## 一、执行摘要

| 维度 | 状态 | 说明 |
|:---:|:---:|:---|
| **TRPL 3rd Ed 全覆盖** | ✅ | 项目概念体系覆盖 TRPL 全部 22 章，并在形式化、生态、未来特性方向大幅扩展 |
| **Edition 2024 对齐** | ✅ | 项目工具链与示例已升级至 Edition 2024；TRPL 3rd Ed 同样以 Edition 2024 为基准 |
| **Async 章节位置差异** | ⚠️ | TRPL 3rd Ed 将 Async 置于 Ch 17（OOP/Patterns/Advanced 之前），本项目 Async 位于 `concept/03_advanced/02_async.md`，建议在学习路径中标注 TRPL 的渐进式安排 |
| **Brown 所有权可视化** | ⚠️ | Brown 书的 Aquascope 所有权动画和嵌入式测验是独特资产；本项目已有嵌入式测验，但缺少运行时/编译时状态可视化 |
| **TRPL 官方来源引用** | ⚠️ | 部分 `concept/` 文件引用 TRPL 2nd Ed 或旧链接，需统一更新至 3rd Ed |

---

## 二、TRPL 3rd Ed 章节目录 → 本项目映射

| TRPL 3rd Ed 章节 | 本项目对应文件 | 覆盖状态 |
|:---|:---|:---:|
| Ch 1: Getting Started | `concept/01_foundation/00_start.md` · `concept/06_ecosystem/01_toolchain.md` | ✅ |
| Ch 2: Guessing Game | `concept/01_foundation/03_control_flow.md` · `exercises/rustlings_style/` | ✅ |
| Ch 3: Common Concepts | `concept/01_foundation/20_variable_model.md` · `concept/01_foundation/04_type_system.md` | ✅ |
| Ch 4: Understanding Ownership | `concept/01_foundation/01_ownership.md` · `concept/01_foundation/02_borrowing.md` | ✅ |
| Ch 4.3 (Brown): Fixing Ownership Errors | `concept/01_foundation/02_borrowing.md`（边界测试） | ⚠️ 可强化 |
| Ch 5: Structs | `concept/01_foundation/04_type_system.md` · `concept/02_intermediate/03_structs.md` | ✅ |
| Ch 6: Enums / Pattern Matching | `concept/01_foundation/04_type_system.md` · `concept/02_intermediate/04_pattern_matching.md` | ✅ |
| Ch 7: Modules | `concept/02_intermediate/07_modules.md` | ✅ |
| Ch 8: Common Collections | `concept/01_foundation/08_collections.md` · `concept/02_intermediate/04_collections.md` | ✅ |
| Ch 9: Error Handling | `concept/01_foundation/10_error_handling_basics.md` · `concept/02_intermediate/15_error_handling_deep_dive.md` | ✅ |
| Ch 10: Generics / Traits / Lifetimes | `concept/02_intermediate/01_traits.md` · `concept/02_intermediate/02_generics.md` · `concept/03_advanced/01_lifetimes.md` | ✅ |
| Ch 11: Testing | `concept/06_ecosystem/12_testing_strategies.md` · `exercises/tests/` | ✅ |
| Ch 12: I/O Project (CLI) | `concept/00_meta/learning_mvp_path.md` · `examples/` | ✅ |
| Ch 13: Iterators / Closures | `concept/02_intermediate/15_iterator_patterns.md` · `concept/02_intermediate/14_closures.md` | ✅ |
| Ch 14: Cargo / Crates.io | `concept/06_ecosystem/01_toolchain.md` · `Cargo.toml` | ✅ |
| Ch 15: Smart Pointers | `concept/03_advanced/05_smart_pointers.md` | ✅ |
| Ch 16: Fearless Concurrency | `concept/03_advanced/01_concurrency.md` · `concept/03_advanced/02_parallelism.md` | ✅ |
| Ch 17: Async Programming | `concept/03_advanced/02_async.md` · `crates/c06_async/` | ✅ |
| Ch 18: OOP Features | `concept/05_comparative/01_rust_vs_cpp.md` · `concept/03_advanced/06_trait_objects.md` | ✅ |
| Ch 19: Patterns | `concept/02_intermediate/04_pattern_matching.md` | ✅ |
| Ch 20: Advanced Features | `concept/04_formal/` · `concept/03_advanced/` | ✅ |
| Ch 21: Multithreaded Web Server | `examples/comprehensive_web_server.rs` · `crates/c10_networks/` | ✅ |
| Appendix | `concept/00_meta/terminology_glossary.md` · `docs/02_reference/` | ✅ |

---

## 三、Brown University 交互式书的独特价值

Brown 书是 TRPL 3rd Ed 的研究分支，核心差异：

1. **Aquascope 可视化**：在代码行旁展示变量在**编译时**（ownership / borrow 状态）和**运行时**（堆栈 / 堆）的演化。
2. **嵌入式测验（Embedded Quiz）**：每章末尾有选择题，答错后提示重试，针对常见误解设计。
3. **Ownership Inventory #1-4**：在 Ch 6 / Ch 8 / Ch 10 / Ch 18 后设置「所有权盘点」，强制复习所有权转移场景。
4. **Fixing Ownership Errors 小节**：Ch 4 新增 4.3 节，专门教读者如何根据编译器错误修复所有权问题。

> **研究支撑**：
>
> - *A Grounded Conceptual Model for Ownership Types in Rust* (Crichton et al., OOPSLA 2023, SIGPLAN/ACM Research Highlight)
> - *Profiling Programming Language Learning* (Crichton & Krishnamurthi, OOPSLA 2024, Distinguished Paper)

---

## 四、差距分析

### 4.1 学习路径差距

| 差距 | 影响 | 优先级 |
|:---|:---|:---:|
| TRPL 3rd Ed 的 Async 位于 OOP/Patterns 之前，暗示 async 是「中级核心」而非「高级选修」 | 本项目 MVP 路径将 async 标为选修，可能让初学者误以为 async 离自己很远 | 中 |
| Brown 书的 Ownership Inventory 机制未被引入 | 学员容易在泛型、trait、smart pointers 后遗忘所有权细节 | 中 |
| 缺少 Aquascope 风格的运行时/编译时状态图 | 所有权和借用是 Rust 最大学习障碍，可视化可显著降低认知负荷 | 高（长期） |

### 4.2 内容来源差距

| 差距 | 位置 | 优先级 |
|:---|:---|:---:|
| 部分 `concept/` 文件引用旧版 TRPL 链接或 2nd Ed 内容 | `concept/01_foundation/`、`concept/02_intermediate/` 等 | 低 |
| Brown 书研究成果未被引用 | `concept/01_foundation/01_ownership.md` | 中 |
| TRPL 3rd Ed 新增/改写章节的 cross-reference 缺失 | `concept/03_advanced/02_async.md`（对应 Ch 17） | 中 |

### 4.3 测验与练习差距

| 差距 | 说明 | 优先级 |
|:---|:---|:---:|
| 已存在嵌入式测验 | 本项目部分文件已有 `<details>` 折叠测验，覆盖率需统计 | 低 |
| 缺少 Brown 式「诊断性测验」 | 不直接给答案，而是根据选择跳转到对应概念补全 | 高（长期） |
| 缺少 Aquascope 交互式代码可视化 | 需要前端/图片支持，非纯 Markdown 可实现 | 高（长期） |

---

## 五、建议措施

### 5.1 短期可执行（本轮冲刺）

1. **在学习路径中标注 TRPL 3rd Ed 对应章节**
   - 修改 `concept/00_meta/learning_mvp_path.md`，为每个 Day 增加「TRPL 3rd Ed 参考章节」列。
   - 在 `concept/03_advanced/02_async.md` 顶部添加指向 TRPL Ch 17 的链接。
2. **在所有权文档中引用 Brown 研究**
   - 在 `concept/01_foundation/01_ownership.md` 和 `02_borrowing.md` 的「来源与延伸阅读」中补充 Brown 书及其两篇 OOPSLA 论文。
   - 新增「Fixing Ownership Errors」小节，总结 Brown 书中常见的 5 种错误模式与修复策略。
3. **统一 TRPL 来源链接至 3rd Ed**
   - 扫描 `concept/` 中对 `doc.rust-lang.org/book/` 的引用，确保指向稳定版 3rd Ed 的对应章节（而非 2nd Ed 或特定旧版本）。

### 5.2 中期规划（下一季度）

1. **引入 Ownership Inventory 机制**
   - 在 `concept/02_intermediate/` 和 `concept/03_advanced/` 的关键节点（collections / generics / smart pointers / concurrency）后增加「所有权盘点」复习页。
   - 形式：5 道诊断题 + 错误模式索引。
2. **评估 Aquascope 可视化集成**
   - Aquascope 是 Rust 生态工具，可生成 SVG 展示代码行的权限变化。
   - 调研是否可在本项目的 mdBook/GitHub Pages 构建流程中集成 Aquascope，或先用静态图片替代。

### 5.3 长期方向

1. **与 Brown 书内容同步机制**
   - Brown 书每数月与 TRPL 同步一次。建议本项目每 6 个月审计一次 Brown 书的测验/可视化更新，吸收已被验证有效的教学改进。

---

## 六、本轮已执行动作

- [x] 获取 TRPL 3rd Ed 完整目录（2026-06-19）
- [x] 获取 Brown University Interactive Book 目录与差异化说明
- [x] 与本项目 `concept/` 目录完成初步映射
- [x] 生成本审计报告

## 七、待执行动作

- [ ] 修改 `concept/00_meta/learning_mvp_path.md`：增加 TRPL 3rd Ed 章节对照
- [ ] 修改 `concept/01_foundation/01_ownership.md` / `02_borrowing.md`：引用 Brown 书及研究成果
- [ ] 修改 `concept/03_advanced/02_async.md`：标注 TRPL Ch 17 对应关系
- [ ] 扫描并修复 `concept/` 中旧版 TRPL 链接
- [ ] （可选）设计 4 个 Ownership Inventory 复习页

---

> **审计者**: 本项目知识库团队
> **下次审计**: 2026-12-19（Brown 书通常每数月与 TRPL 同步一次，半年后复核）
