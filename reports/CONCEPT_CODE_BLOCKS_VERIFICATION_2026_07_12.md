# concept/ 代码块批量编译实测报告（2026-07-12）

> 任务：concept/ ```rust 代码块提取→分类→抽样编译实测→腐烂修复→门禁化。
> 范围控制：仅 std-only 块编译；超 300 块分层抽样；仅修复权威页明确腐烂 ≤15 处。

## 1. 提取与分类

脚本：`scripts/check_concept_code_blocks.py`（482 个 md，4641 个 ```rust 块）。

| 分类 | 数量 | 说明 |
|---|---:|---|
| flag_skip | 2337 | fence 标注 ignore/compile_fail/no_run/should_panic |
| pseudo | 7 | 含 todo!()/unimplemented!()/占位省略 |
| nightly | 17 | 含 `#![feature(...)]` |
| nostd | 9 | no_std/no_main |
| dep_skip | 19 | 嵌入式/wasm/验证工具等不可用环境 |
| dep_untested | 99 | 外部依赖（workspace 外） |
| dep | 279 | workspace 内依赖（可经 --with-deps 实测，本轮不做） |
| candidate | 1874 | 无依赖 std-only 编译候选 |
| **合计** | **4641** | |

## 2. 抽样方法

候选 1874 > 300，**按文件分层随机抽样**：

- 每层 = 一个源文件；层名额按该文件候选占比 × 300 分配，最大余数法取整补足 300；
- 层内 `random.Random(seed=20260712)` 抽取，固定 seed 保证可复现；
- 抽到 300/1874 块，覆盖多个层级目录与文件。

## 3. 编译实测（修复前）

- 工具：`rustc 1.97.0 --edition 2024 --emit=metadata`，无 `fn main` 的块自动包装（inner attribute 提到顶部；bin 失败回退 lib 模式），8 并发，60s/块超时。
- 结果：**pass=267 / fail=33 / timeout=0，通过率 89.0%**。
- 明细 JSON：`tmp/concept_code_blocks_2026_07_12.json`（临时文件，不入库）。

## 4. 腐烂修复清单（5 处，均权威页、原因明确；远低于 15 处上限）

| # | 文件 | 行 | 问题 | 修复 |
|---|---|---:|---|---|
| 1 | `concept/03_advanced/06_low_level_patterns/09_variables.md` | 53 | 闭包参数无类型且未调用，E0282 推断失败 | 显式标注 `a: i32, b: i32` |
| 2 | `concept/03_advanced/07_unsafe_internals/01_unsafe_collections_internals.md` | 210 | `std::sync::Guard` 不存在（E0432） | 改为真实类型 `MutexGuard` |
| 3 | `concept/07_future/00_version_tracking/migration_197_decision_tree.md` | 111 | "迁移前"故意失败代码未标注（export_name 空） | fence 改 `rust,compile_fail` |
| 4 | `concept/07_future/00_version_tracking/rust_1_91_stabilized.md` | 858 | `fn infer_type -> String` 返回 `&str`（E0308） | 返回类型改 `&'static str` |
| 5 | `concept/06_ecosystem/03_design_patterns/11_formal_design_pattern_theory.md` | 579/664 | 悬空 `///` 文档注释 ×2（E0585） | 改 `//` 普通注释 |

5 处均经 `rustc --edition 2024` 单独复测通过（compile_fail 块确认按预期失败）。

## 5. 未修失败块分类登记（28 处，不逐块修）

| 类别 | 数量 | 典型实例 |
|---|---:|---|
| 上下文依赖片段（引用同页前文块定义的类型/函数） | 10 | `04_future_and_executor_mechanisms.md:421/967`（SimpleExecutor/MyFuture）、`09_destructors.md:81`（PrintOnDrop）、`rust_1_92_stabilized.md:723` |
| 虚构/示意宏与 crate | 7 | `06_macro_glossary.md:292/407/617`（sql/my_macro/compute_size）、`07_macro_faq.md:182/574`、`09_macro_hygiene.md:921` |
| 未登记外部 crate（KNOWN_CRATES 未覆盖） | 4 | `18_api_design_patterns.md:538`（utoipa_axum）、`08_high_performance_network_service_architecture.md:700`（tokio_uring）、`08_algorithm_engineering_practice.md:332`（bit_vec）、`08_syn_quote_reference.md:606`（quote 宏未 use） |
| nightly/实验特性 | 3 | `12_frontier_research_and_innovative_patterns.md:868`（try blocks E0658）、`rust_1_92_stabilized.md:1764`（trusted_len）、`09_macro_hygiene.md:964`（proc-macro crate type） |
| 示意伪代码 | 2 | `07_macro_faq.md:564`（空 macro_rules）、`01_process_model_and_lifecycle.md:234`（顶层 `?` 片段） |
| quiz 题设故意不编译（非权威页，按范围规则不修） | 1 | `00_meta/04_navigation/12_self_assessment.md:1048`（E0382 问答题，建议后续标 compile_fail） |
| 待人工核实 | 1 | `rust_1_95_stabilized.md:86`（`use std::keyword as kw` 在 1.97 不可解析，疑似文档杜撰 API，需对照 release notes 核实） |

后续治理建议：上下文片段类可在 fence 标 `rust,ignore` 或在块内补 `#` 隐藏上下文行；未登记 crate 可补入脚本 KNOWN_CRATES；quiz 故意失败块统一标 `compile_fail`。

## 6. 门禁化

- 脚本默认观察模式 exit 0（输出通过率）；`--strict` 通过率 <95% exit 1。
- `scripts/run_quality_gates.sh`：追加到 "Examples Compile Check (observe)" 段输出之后（同段附加小节，不计入门数，AGENTS.md §5 保持 20 门表述不变），`bash -n` 通过。
- `scripts/README.md` 已登记一行。

## 7. 修复后复测

固定 seed=20260712 重跑（迁移前块转入 flag_skip 后候选 1874→1873，重抽样 300）：

```text
[extract] files=482 blocks=4641
[sample] （分层抽样 300/1873，seed=20260712）
[result] pass=272 fail=28 timeout=0 pass_rate=90.7%
[gate] 观察模式：exit 0
```

失败 28 块与 §5 登记清单一一对应，5 处修复全部生效（89.0% → 90.7%，+5 块）。

## 8. 验证

- `python scripts/kb_auditor.py`（死链）：0 新增死链（详见终验输出）。
- `mdbook build`：通过。
