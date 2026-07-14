# MINDMAP_HIGH_LAYERS_S3：04/05/07 高层 mindmap + 8 例待应用反例落地（2026-07-14）

> 范围：concept/ 04_formal / 05_comparative / 07_future 三层 mindmap 补建 30 页；R3 报告 §4 待办登记的 8 例已实测反例落地。
> 执行约束：只追加新节（mindmap 节 / 反例节），不改既有节正文（与 05/06/07 层两个并行代理避让；mindmap 主体配额落在无并行代理的 04_formal）。
> 生成脚本：`tmp/gen_mindmaps_s3.py`、`tmp/fix_mindmap_len_s3.py`、`tmp/apply_ce_s3.py`（tmp/ 不入库）。

## 1. 任务 1：mindmap +30 页

| 层 | 新增 | 该层覆盖率变化 |
|---|---|---|
| 04_formal | 24 | 0/55 → **24/55 = 43.6%** |
| 05_comparative | 4 | 0/20 → **4/20 = 20.0%** |
| 07_future | 2 | 3/66 → **5/66 = 7.6%** |
| **合计** | **30** | 全库 M1：109/429 = 25.3% → **139/430 = 32.3%** |

质量约束（全部满足）：

- 每页 1 个真 ```` ```mermaid mindmap ```` 图，root + 3–5 个一级分支、每分支 1–3 个叶子（30/30 结构校验通过）；
- 节点文本从该页 H1/H2/H3 提炼，去除 mermaid 特殊字符（括号/冒号/引号等），无需引号包裹即合法；
- 节长 ≤25 行（首轮 12 页 26–29 行，经 `fix_mindmap_len_s3.py` 按 body ≤16 行截尾重建后 30/30 ≤25 行）；
- 30/30 经 `mmdc` 本地渲染验证 0 失败；
- 结构不足（有效 H2/H3 分支 <3）跳过 21 页，未强行生成，名单见 `tmp/gen_mindmaps_s3.py` dry-run 输出。

30 页名单：04_formal 24 页（00_type_theory 5、01_ownership_logic 3、02_separation_logic 1、03_operational_semantics 5、04_model_checking 7、05_rustc_internals 3）；05_comparative 4 页（00_paradigms 2、01_systems_languages 2）；07_future 2 页（00_version_tracking：`04_nightly_rust.md`、`migration_197_decision_tree.md`）。

## 2. 任务 2：8 例待应用反例落地

按 `reports/MINDMAP_DEEPEN_R3_2026_07_14.md` §4 待办名单，8/8 全部落地（追加前 8 页均无既有「⚠️ 反例与陷阱」节，无需合并去重）：

| 页面 | 反例 | 标注 |
|---|---|---|
| 01_foundation/00_start/07_operators_and_symbols.md | 链式比较 `a == b == c` | 无错误码（comparison operators cannot be chained） |
| 01_foundation/07_modules_and_items/11_crates_and_source_files.md | 引用不存在的 crate 路径 | E0432 |
| 03_advanced/06_low_level_patterns/09_variables.md | 给不可变变量赋值 | E0384 |
| 03_advanced/06_low_level_patterns/10_visibility_and_privacy.md | 重导出私有项 | E0603 |
| 06_ecosystem/01_cargo/20_cargo_manifest_targets.md | `harness = false` 测试目标缺 main | E0601 |
| 06_ecosystem/09_testing_and_quality/03_testing.md | 测试中浮点精确相等 | 运行时 panic（`--test` 编译验证） |
| 06_ecosystem/11_domain_applications/12_formal_algorithm_theory.md | 二分中点 `(low+high)/2` 溢出 | 运行时 panic（debug 溢出检查） |
| 07_future/00_version_tracking/02_editions.md | 2018+ edition `async` 成关键字 | 无错误码（解析错误） |

追加前全部经 rustc 1.97 `--edition 2024` 复验：compile 类 6 例确认编译失败且错误码与标注一致；runtime 类 2 例确认编译通过（浮点例以 `--test` 模式验证）；8 个修正版均编译通过。

反例覆盖 M2：345/429 = 80.2% → **353/430 = 82.1%**。

## 3. 验证数字（2026-07-14 实跑）

| 检查 | 结果 |
|---|---|
| `check_mindmap_coverage.py` M1 | **139/430 = 32.3%**（基线 25.3%，+30 页；04_formal 0%→43.6%、05_comparative 0%→20.0%、07_future 4.5%→7.6%） |
| `check_mindmap_coverage.py` M2 | **353/430 = 82.1%**（基线 80.2%，+8 页） |
| `kb_auditor.py` | 死链 0 / 跨层问题 0 / 模板化 ⟹ 0 |
| `check_mermaid_syntax.py` | 1115 mermaid 块，无关键语法问题；30 个新 mindmap 另经 mmdc 全量渲染 0 失败 |
| `mdbook build` | 通过（exit 0） |

## 4. 过程勘误（透明记录）

- 首轮 mindmap 生成后 12/30 页节长 26–29 行（超 ≤25 行约束），经截尾重建（5 分支时叶子封顶 2 个、body ≤16 行）全部压回 ≤25 行，重建后 mmdc 复验 0 失败、结构（3–5 分支 × 1–3 叶子）复验 0 违规。
- 执行期间 `tmp/gen_mindmaps.py`、`tmp/gen_counterexamples.py` 被并行活动删除；S3 脚本已内联所需提炼逻辑，反例用例数据取自本会话早先读取的完整 CASES 表，且落地前全部重新 rustc 实测，不依赖被删脚本。

## 5. 后续建议（R4+）

1. 04_formal 仍有 21 页因结构不足跳过（多为清单/矩阵/参考页），需人工补结构性章节后再生成 mindmap。
2. 03_advanced 层 mindmap 覆盖率仍仅 3.1%（2/65），为当前最低层，建议下轮配额转向。
3. 07_future 反例覆盖 68.2% 为各层最低，可作为后续反例补建重点。
