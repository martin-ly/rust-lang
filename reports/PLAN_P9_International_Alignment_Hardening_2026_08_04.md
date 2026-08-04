# P9 国际权威对齐加固计划

**目标**: 在 P8 全绿基线上，修复季度审计发现的 P1 术语/链接漂移，持续对齐 Rust 1.98+ 前沿语义，并将 AI 语义检索与企业架构模式推进到可生产验证阶段。

**基线**: 2026-08-04，23 阻断门 + 5 观察门全部通过（见 `reports/P8_Next_Wave_Semantic_Deep_Dive_COMPLETION_2026_08_04.md`）。

---

## P9 任务清单

### P9-1: 修复季度审计 P1 发现

- 更新 `concept/02_intermediate/00_traits/01_traits.md`：术语“对象安全 / Object Safety”→“dyn 兼容性 / dyn compatibility”。
- 补充 dyn compatibility 判定矩阵（关联常量禁止、`AsyncFn*` 不兼容、Pin receiver 允许、supertrait 必须 dyn compatible）。
- 修正 `concept/03_advanced/01_async/08_pin_unpin.md`：RFC 2592 → RFC 2349。
- 修复死链：
  - Pin 页 Rustonomicon 链接 → `https://doc.rust-lang.org/std/pin/index.html`
  - Lifetimes 页 `reference/lifetimes.html` → `https://doc.rust-lang.org/reference/lifetime-elision.html`
- 验证: `python scripts/kb_auditor.py --link-check`

### P9-2: Rust 1.98.0 stable 语义注入（发布后）

- 跟踪 Rust 1.98.0 stable Release Notes。
- 将 1.98 beta 特性转为稳定特性并更新权威页。
- 新建/更新 `concept/07_future/00_version_tracking/rust_1_98_stabilized.md`。
- 验证: `python scripts/check_version_semantic_injection.py --strict`

### P9-3: no_std / 嵌入式硬件实测验证

- 新增/增强：
  - `concept/06_ecosystem/05_systems_and_embedded/50_embedded_hardware_test_matrix.md`
  - `concept/06_ecosystem/05_systems_and_embedded/51_probe_rs_and_embedded_debugging.md`
- 对齐：probe-rs、defmt、RTIC/Embassy 硬件 CI 实践。
- 验证: 代码块针对 `thumbv7em-none-eabihf` 可编译。

### P9-4: AI 语义检索生产化

- 增强 `tools/kg_rag/semantic_alignment_pipeline.py`：
  - 支持本地模型 / OpenAI 兼容 API
  - 添加 RAG 评估指标（recall@k、MRR、NDCG）
  - 生成 `reports/RAG_EVALUATION_BASELINE_2026_08.md`
- 新增 `concept/00_meta/05_ai_semantic_engineering/03_rag_evaluation_for_rust_kg.md`
- 验证: KG 谓词精度保持 0%

### P9-5: 形式方法与计算模型深化

- 新增：
  - `concept/04_formal/11_computational_models/10_category_theory_and_rust.md`
  - `concept/04_formal/11_computational_models/11_modal_logic_and_rust_effects.md`
- 对齐：Category Theory for Programmers、MLTT、Iris modal logic。

### P9-6: 企业架构模式案例库

- 新增：
  - `concept/06_ecosystem/14_enterprise_architecture/16_rust_in_financial_services.md`
  - `concept/06_ecosystem/14_enterprise_architecture/17_rust_in_iot_and_edge.md`
- 对齐：Jon Gjengset、Ferrous Systems、Oxide 等生产案例。

### P9-7: 国际权威来源持续对齐

- 每月运行 `python scripts/check_authority_freshness.py`。
- 建立 `reports/INTERNATIONAL_ALIGNMENT_FRESHNESS_2026_08.md`。

### P9-8: 全量质量门最终验证

- 跑 `bash scripts/run_quality_gates.sh`
- 目标：23 阻断 + 5 观察全部通过

---

## 预期产出

| 产出 | 数量/目标 |
|---|---|
| 修复 P1 审计发现 | 4 项 |
| 新增/增强 concept 权威页 | 8+ |
| 工具脚本增强 | 1-2 |
| 全量质量门 | 28/28 通过 |

## 决策选项

请确认如何推进：

1. **全部推进**（推荐）：并行启动 P9-1 至 P9-8，持续冲刺直到 100%。
2. **优先修复**：只做 P9-1（审计 P1 修复）+ P9-8（质量门），其余后延。
3. **暂停规划**：先输出更详细的子任务分解与依赖图，再开始执行。
