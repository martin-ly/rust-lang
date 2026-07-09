# 项目整改执行方案 2026-07-09

> **确认状态**：待用户确认
> **执行策略**：选项 A — 按推荐计划执行，并附详细整改方案
> **预计周期**：阶段 1（1 周）+ 阶段 2（2 周）+ 阶段 3（Q3 持续推进）

---

## 一、目标与范围

本次整改覆盖以下 4 个维度：

1. **工具链同步**：完成 Rust 1.97.0 发布日清单，确保项目与最新 stable 对齐。
2. **合规修复**：修复 AGENTS.md 高优先级违规（EN/Summary 缺失、重复文件、命名违规）。
3. **质量验证**：全量 workspace 编译/测试/clippy/审计通过。
4. **结构治理**：启动 `crates/*/docs/` 概念迁移、`concept/` 结构优化、P2-Q3 计划执行。

---

## 二、阶段 1：立即完成（2026-07-09 ~ 07-13）

### 任务 1.1：Rust 1.97.0 发布日清单

| 子任务 | 操作文件 | 具体动作 | 验收标准 |
|---|---|---|---|
| 1.1.1 | `rust-toolchain.toml` | 将 `channel = "stable"` 改为 `channel = "1.97.0"` | `rustc --version` 输出 `1.97.0` |
| 1.1.2 | `scripts/probe_rust_197_apis.rs` | 运行并收集 1.97 API 可用性结果 | 生成探测报告 |
| 1.1.3 | `crates/c08_algorithms/src/rust_197_features.rs` | 激活已稳定 API；对 `VecDeque::truncate_front` / `retain_back` 保留 fallback | 文件编译通过 |
| 1.1.4 | `concept/07_future/rust_1_97_preview.md` | 刷新为稳定版内容 | 无 nightly-only 描述 |
| 1.1.5 | `docs/06_toolchain/06_21_rust_1_97_features.md` | 从 concept 迁移/复制稳定内容，作为工具链参考页 | 仅保留摘要+链接或操作步骤 |
| 1.1.6 | `crates/c08_algorithms/examples/` 或 `exercises/` | 新增/更新 1.97 特性练习 | 至少 1 个可运行示例 |
| 1.1.7 | `CHANGELOG.md` | 完善 `[3.1.0]` 条目，记录 1.97 相关变更 | 条目完整、日期正确 |
| 1.1.8 | `.kimi/archive/EXECUTION_RUST_1_97_RELEASE_2026_07_09.md` | 勾选完成项并归档 |  checklist 完整 |

### 任务 1.2：提交当前 dirty 文件

当前 6 个未提交文件：

| 文件 | 变更内容 | 是否需要同步更新文档 |
|---|---|---|
| `Cargo.lock` | 依赖版本锁定 | 否 |
| `Cargo.toml` | `bytes` 1.12.0 → 1.12.1 | 更新注释日期 |
| `crates/c08_algorithms/Cargo.toml` | `tract-onnx` 0.23.1→0.23.4, `eframe` 0.34.3→0.35.0 | 否 |
| `crates/c08_algorithms/examples/gui_calculator_demo.rs` | `show_inside` → `show` | 否 |
| `concept/00_meta/04_navigation/concept_index.md` | 链接引用格式 | 否 |
| `concept/00_meta/04_navigation/self_assessment.md` | 来源归属 | 否 |

**验收标准**：`cargo check --workspace` 通过后一次性提交。

### 任务 1.3：修复高优先级 AGENTS.md 违规

| 子任务 | 文件 | 整改动作 | 验收标准 |
|---|---|---|---|
| 1.3.1 | `concept/00_meta/02_sources/topic_authority_alignment_map.md` | 在文件顶部添加 `> **EN**: ...` 和 `> **Summary**: ...` | `scripts/add_bilingual_annotations.py` 不再报错 |
| 1.3.2 | `docs/research_notes/10_distributed_patterns_matrix.md` 与 `docs/research_notes/10_distributed_pattern_matrix.md` | 合并为单一权威页；另一文件改为重定向 stub | 两文件不重复保留正文 |
| 1.3.3 | `docs/research_notes/10_workflow_engine_matrix.md` 与 `docs/research_notes/formal_methods/10_workflow_engines_matrix.md` | 同上，保留 `formal_methods/` 或根目录一份 | 同上 |
| 1.3.4 | `concept/archive/Rust vs C++：形式系统模型 vs 机制工程模型 —— 核心论点索引.md` | 重命名为 snake_case 或移入 archive/deprecated/ | 文件名符合 AGENTS.md 规范 |
| 1.3.5 | `content/README.md` | 补充 EN + Summary，或改为索引/重定向 stub | 符合规范 |

---

## 三、阶段 2：7 月上半月（2026-07-14 ~ 07-20）

### 任务 2.1：全量 workspace 回归验证

| 子任务 | 命令 | 验收标准 |
|---|---|---|
| 2.1.1 | `cargo check --workspace` | 0 错误、0 与本次修改相关的 warning |
| 2.1.2 | `cargo test --workspace` | 所有测试通过（允许已知 nightly-only 忽略项） |
| 2.1.3 | `cargo clippy --workspace` | 0 deny/correctness 级别错误 |
| 2.1.4 | `cargo audit --no-fetch` | 0 新安全漏洞 |
| 2.1.5 | `cargo vet` | supply-chain 审计通过或更新 exemptions |
| 2.1.6 | `python scripts/kb_auditor.py --link-check` | 0 死链 |
| 2.1.7 | `python scripts/detect_content_overlap.py` | 0 新增跨目录重复 |

### 任务 2.2：启动 P2-Q3 关键任务（建议先做 2 项）

| 子任务 | 文件 | 具体动作 | 验收标准 |
|---|---|---|---|
| 2.2.1 | `concept/03_advanced/01_async/02_async.md` | 增加 TRPL Ch17 注释与交叉引用 | 文件末尾或专门章节包含 TRPL 映射 |
| 2.2.2 | `concept/04_formal/19_rustc_query_system.md` | 增加动手实践章节（查询系统图 + 代码示例） | 新增 ≥1 个可运行/可验证示例 |

### 任务 2.3：修复 14 个知识库质量风险文件

来源：`reports/kb_quality_dashboard.md`

重点文件（示例）：

- `concept/01_foundation/07_modules_and_items/12_functions.md`
- `concept/01_foundation/07_modules_and_items/13_use_declarations.md`
- `concept/01_foundation/07_modules_and_items/14_structs.md`
- `concept/01_foundation/07_modules_and_items/15_enumerations.md`
- `concept/01_foundation/07_modules_and_items/16_implementations.md`

**整改动作**：补充认知路径段落（cognitive path）、过渡句（transition paragraphs）、定理链（theorem chains）和逆向推理（backward reasoning）标记。

**验收标准**：重新运行 `python scripts/kb_auditor.py` 后风险文件数 ≤ 5。

---

## 四、阶段 3：Q3 持续推进（2026-07-21 ~ 09-30）

### 任务 3.1：执行 P2-Q3 2026 深化计划

详见 `.kimi/P2_Q3_2026_EXECUTION_PLAN.md`，共 11 项任务，按月推进：

| 月份 | 重点任务 |
|---|---|
| 7 月下旬 | P2-1 rustc query system、P2-11 async TRPL 注释 |
| 8 月 | P2-2 trait solver 对比、P2-3 Cargo resolver v3 / public = true 示例、P2-4 MIR/codegen/LLVM |
| 9 月 | P2-5 Kani 扩展、P2-7 Sea-ORM 2.0 评估、P2-8 AFIDT/dynosaur 状态更新 |

### 任务 3.2：`concept/` 结构治理

| 子任务 | 动作 | 验收标准 |
|---|---|---|
| 3.2.1 | 将未链接页面加入 `concept/SUMMARY.md` | `mdbook build` 无 orphan page 警告 |
| 3.2.2 | 修复编号断层 | 目录编号连续 |
| 3.2.3 | 处理 6 组重复文件（如 `concept/archive/` 与活跃页） | 保留一份权威页，其余改为 stub |

### 任务 3.3：`crates/*/docs/` 合规整改（详细方案见第五章）

| 子任务 | 动作 | 验收标准 |
|---|---|---|
| 3.3.1 | 制定 `crates/*/docs/` 内容边界规范 | 写入 `AGENTS.md` 或 `crates/README.md` |
| 3.3.2 | 识别并迁移通用概念解释到 `concept/` | 完成高优先级 crate 文档整改 |
| 3.3.3 | 将 `crates/*/docs/` 中非 crate 特定内容改为摘要/链接 | 抽样检查无大段概念重复 |

### 任务 3.4：Q4 准备

| 子任务 | 动作 | 验收标准 |
|---|---|---|
| 3.4.1 | 评估 `mdbook-i18n-helpers` vs 当前 EN-metadata 方案 | 输出决策文档 |
| 3.4.2 | 规划 506 个外部死链批量修复 | 输出分批修复计划 |
| 3.4.3 | Brown Book inventory 练习国际化准备 | 8 个 inventory 完成双语标注 |

---

## 五、`crates/*/docs/` 详细整改方案

### 5.1 问题定义

- `crates/*/docs/*.md` 共 **206 个文件**，其中 166 个 >100 行，大量文件包含通用 Rust 概念解释。
- 根据 AGENTS.md §6 红线 #4：`crates/*/docs/` 不应复制通用概念解释，应链接到 `concept/`。
- 抽样显示这些文档几乎没有链接到 `concept/` 权威页。

### 5.2 整改原则

| 文档类型 | 允许内容 | 禁止内容 | 示例 |
|---|---|---|---|
| **crate API 文档** | crate 特定 API 用法、示例代码、构建说明 | 通用 Rust 概念讲解 | `c10_networks` 的 QUIC 示例配置 |
| **学习指南** | 学习路径、练习任务、链接到 `concept/` | 重复 `concept/` 中的完整解释 | 算法练习步骤 |
| **速查页** | 关键命令、决策树、链接 | 长篇理论推导 | 网络协议选择表 |
| **重定向 stub** | 一句话说明 + 权威页链接 | 保留重复正文 | 通用并发概念 → `concept/03_advanced/00_concurrency/` |

### 5.3 优先级队列

#### P0：高重复风险（立即整改）

| crate | 文件 | 估算行数 | 重复内容 | 建议动作 |
|---|---|---:|---|---|
| c05_threads | `docs/01_basic_threading.md` | 932 | `Send`/`Sync`、scoped threads | 迁移通用部分到 `concept/03_advanced/00_concurrency/`，本文改为摘要+练习 |
| c05_threads | `docs/06_parallel_algorithms.md` | 1,678 | 并行算法/并发模式 | 同上 |
| c07_process | `docs/01_process_model_and_lifecycle.md` | 1,014 | 进程/IPC 概念 | 迁移到 `concept/03_advanced/02_process_ipc/`，本文保留 API 示例 |
| c09_design_pattern | `docs/rust_design_patterns_comprehensive_guide_theory_practice_formal_verification.md` | 875 | 设计模式理论 | 迁移到 `concept/06_ecosystem/03_design_patterns/`，本文保留 Rust 实现示例 |
| c10_networks | `docs/rust_190_examples_part3_advanced_protocols.md` | 2,975 | 协议/并发叙述 | 拆分：通用协议理论进 `concept/`，本文仅保留 c10_networks API 示例 |

#### P1：中等重复风险（阶段 3 处理）

| crate | 文件 | 估算问题 |
|---|---|---|
| c02_type_system | `docs/tier_03_references/04_safety_reference.md` | 类型系统安全概念 |
| c04_generic | `docs/tier_04_advanced/01_advanced_type_techniques.md` | 高级类型技巧 |
| c06_async | `docs/` 下多份 async 入门文档 | 与 `concept/03_advanced/01_async/` 重复 |
| c08_algorithms | `docs/interactive_learning_guide.md` | 算法导论 |
| c10_networks | `docs/tier_03_references/01_network_protocol_categories_reference.md` | 协议分类 |

#### P2：低风险/保留

- `crates/c11_macro_system_proc/docs/`（crate 特定宏实现）
- `crates/c13_embedded/docs/`（硬件相关）
- `crates/c15_verification_tools/docs/`（工具链特定）
- 短的 README/构建说明文件

### 5.4 执行流程（每个文件）

1. **查重**：运行 `python scripts/detect_content_overlap.py` 定位重复段落。
2. **迁移**：将通用概念段落移动到 `concept/` 对应权威页。
3. **改写**：在 `crates/*/docs/` 中用 1-3 段摘要 + `> **权威来源**: [concept/xxx.md](...)` 替代。
4. **验证**：重新运行重叠检测，确认该文件相似度低于阈值。
5. **链接**：确保 `concept/SUMMARY.md` 包含迁移后的权威页。

### 5.5 验收标准

- `crates/*/docs/` 中 >500 行的通用概念文件数量减少 ≥50%。
- 每个整改后的文件顶部或相关位置包含指向 `concept/` 的权威来源链接。
- `python scripts/detect_content_overlap.py` 无新增跨目录重复。

---

## 六、工具与命令清单

```bash
# 质量审计
python scripts/kb_auditor.py
python scripts/kb_auditor.py --link-check
python scripts/detect_content_overlap.py

# 构建验证
cargo check --workspace
cargo test --workspace
cargo clippy --workspace

# 安全/供应链
cargo audit --no-fetch
cargo vet

# i18n 检查
python scripts/add_bilingual_annotations.py --check-only
```

---

## 七、风险与依赖

| 风险 | 影响 | 缓解措施 |
|---|---|---|
| Rust 1.97.0 某些 API 实际未稳定 | 编译失败 | 先运行 probe 脚本，保留 fallback |
| `cargo test --workspace` 耗时过长 | 阻塞提交 | 可分批运行，或先 `cargo check` + 关键 crate 测试 |
| `crates/*/docs/` 迁移引发大量文件变更 | review 困难 | 分 crate、分 PR 处理 |
| Sea-ORM 2.0 stable 仍未发布 | P2-7 阻塞 | 改为 rc 预览评估报告 |

---

## 八、确认事项

请确认以下问题：

1. **是否按此方案执行阶段 1 ~ 阶段 3？**
2. **阶段 1 中，Rust 1.97.0 工具链切换后，是否允许使用 `channel = "1.97.0"` 而不是继续用 `stable`？**
3. **`crates/*/docs/` 整改是否按本方案第五章的优先级队列执行？**
4. **是否需要我在开始执行前，先为阶段 1 创建一个更细粒度的每日执行清单？**
