# Canonical 唯一性门 WARN 系统性梳理与分类处置建议（2026-10-13）

> 只读梳理报告。本次任务未修改任何既有文件、未做 git 操作；仅新建本报告。
> 数据来源：`python scripts/check_canonical_uniqueness.py --strict` 现场重跑（与
> `reports/QUALITY_GATES_BASELINE_2026-10-13.txt` Canonical 段一致：WARN 明细 384 条，exit 0）。

---

## 1. 总体数字

| 指标 | 数值 |
|---|---|
| 扫描页面 | 745 |
| ERROR | 0（门通过，--strict exit 0） |
| WARN 总数 | **384**（与基线存档一致） |
| WARN 类型构成 | `same_dir_topic_duplicate` 343 + `dual_canonical` 41 |
| 涉及文件 | 263 个 |
| 主题簇（按 WARN 边做连通分量聚类） | **70 簇** |
| 簇规模分布 | 30×1、15×2、11×3、8×3、5×1、4×4、3×13、2×43 |
| 涉及目录 | 42 个 concept/ 子目录 |

**关键发现（先于一切分类）**：384 条 WARN 边**全部是同目录内**的文件对（跨目录边 = 0）。
脚本横幅文案「疑似跨层同主题」与实际不符——41 条 `dual_canonical` warn 命中的对也恰好
都在同一目录内。真正的跨层双权威页（check_a 设计针对的场景）当前为 0。WARN 的实质是
**同目录文件名词干相似度 ≥ 0.6 触发的噪音**，而非跨层主题重复。

## 2. WARN 判定逻辑（读脚本确认）

`scripts/check_canonical_uniqueness.py` 两条检测路径：

- **check_a（dual_canonical）**：两个非 stub 文件都声明「本文件为 concept/ 权威页」，
  且 EN 或中文标题 difflib 相似度 ≥ 0.85、文件名词干相似度 ≥ 0.6 → warn。
- **check_b（same_dir_topic_duplicate）**：同一目录内两文件词干（去 `NN_` 编号前缀）
  相似度 ≥ 0.6 → warn（词干完全相同则升级为 error）。

已有豁免机制（均存在于脚本内）：
1. `IGNORE_PAIRS`：人工复核白名单，`frozenset({file1, file2})`，支持完整路径与
   basename 对、容忍 `NN_` 重编号。判定在相似度比较之前。当前仅 2 对（2026-08-01 复核）。
2. `PROGRESSION_SUFFIXES = (basics, basic, advanced, deep_dive)`：词干 = 基础词干 +
   进阶后缀视为合法分层，自动豁免。
3. 结构性排除：archive/、sources/、placeholder、stub、template/atlas/glossary/quiz、
   readme/summary/index。

**没有**模式级（正则/后缀级）豁免机制——豁免只能逐对登记。

## 3. 聚类统计（70 簇，按规模降序，前 25）

| 簇 | 文件数 | WARN 边数 | 目录 |
|---|---|---|---|
| C1 | 30 | 58 | 07_future/02_preview_features |
| C2 | 15 | 92 | 07_future/00_version_tracking |
| C3 | 15 | 22 | 06_ecosystem/05_systems_and_embedded |
| C4 | 11 | 44 | 05_comparative/02_managed_languages |
| C5 | 11 | 10 | 06_ecosystem/01_cargo |
| C6 | 11 | 13 | 06_ecosystem/03_design_patterns |
| C7 | 8 | 10 | 04_formal/03_operational_semantics |
| C8 | 8 | 25 | 05_comparative/01_systems_languages |
| C9 | 8 | 14 | 06_ecosystem/16_algorithm_patterns |
| C10 | 5 | 4 | 04_formal/00_type_theory |
| C11 | 4 | 4 | 04_formal/10_architecture_semantics |
| C12 | 4 | 3 | 06_ecosystem/00_toolchain |
| C13 | 4 | 5 | 06_ecosystem/14_enterprise_architecture |
| C14 | 4 | 4 | 06_ecosystem/16_algorithm_patterns |
| C15 | 3 | 4 | 03_advanced/08_process_ipc |
| C16–C25 | 3 | 2–3 各 | 02_intermediate/00_traits、02_intermediate/01_generics、03_advanced/02_unsafe、04_formal/05_rustc_internals、04_formal/07_concurrency_semantics、04_formal/09_system_semantics、06_ecosystem/05_systems_and_embedded ×2、06_ecosystem/06_data_and_distributed、06_ecosystem/07_security_and_cryptography |
| C26–C70 | 2 | 1–2 各 | 其余 45 个目录（长尾） |

按触发原因对 384 条边做机械归因：

| 触发模式 | 边数 | 占比 |
|---|---|---|
| 版本号系列撞词干（`rust_1_9x_stabilized/preview`、`feature_domain_matrix_19x`、`migration_19x_decision_tree`、`cargo_19x_features`） | 98 | 25.5% |
| `rust_vs_*` 前缀互撞 | 69 | 18.0% |
| 泛后缀互撞（`_preview` 58、`_semantics` 16、`_patterns` 12、`_algorithms` 12、其余长尾 ~24） | 122 | 31.8% |
| 其它词干相似（含真近重复候选与合法分层对） | 95 | 24.7% |

## 4. 十大簇深查判定（读页面头部元数据 + 正文摘要 + 章节标题对照）

判定类别：**(a) 真重复**（应合并/改 stub）；**(b) 合理分层/互补**（AGENTS.md §2 允许，应登记豁免）；**(c) 门误报**（词干过于宽泛）。

### C1 — 02_preview_features（30 文件 / 58 边）→ **(c) 门误报**
全部为各自独立的 nightly 预览特性跟踪页（MC/DC coverage、safety tags、ferrocene、
autoverus、complex numbers……），仅共享 `_preview` 后缀。标题/EN 完全不同主题。
先例：脚本 IGNORE_PAIRS 已于 2026-08-01 复核登记 W317（open_enums vs complex_numbers），
确认此类为「仅共享 `_preview` 后缀，主题无重叠，属词干误判」。
**处置**：整簇豁免，不逐对登记（58 对太多）；见 §6 建议的模式级豁免。

### C2 — 00_version_tracking（15 文件 / 92 边）→ **(c) 门误报**
`rust_1_90…1_99_stabilized/preview` 版本系列页 + `feature_domain_matrix_197/198` +
`migration_197/198_decision_tree`。每个版本号是独立权威页（AGENTS.md 版本跟踪惯例），
词干仅差一个数字，difflib ratio 0.95–0.96 全部命中。92 边是全互撞组合爆炸。
**处置**：整簇豁免；版本系列应加模式级豁免（正则 `rust_1_\d+_(preview|stabilized)` 等）。

### C3 — 05_systems_and_embedded（15 文件 / 22 边）→ 混合：多数 (c)，1 对 (a) 候选
大部分为不同嵌入式子主题（embedded_graphics / embedded_hal / memory allocators /
protocol drivers…）共享 `embedded_`/`no_std_` 词干 → (c)。
**深查例外**：`23_no_std_and_bare_metal_idioms.md` vs `38_no_std_bare_metal_rust.md`——
两页都声明「本文件为 concept/ 权威页」，同覆盖 `#![no_std]` 与裸机 Rust，38 的 Summary
自称 "A canonical reference for no_std and bare-metal Rust"。章节对照重叠度低（共享仅
模板性标题），内容侧重不同（23=惯用法/工具链，38=语义边界/启动流程/决策树），但
**双权威声明 + 同主题域**构成 AGENTS.md §2 意义上的双权威页风险。
**处置**：此对列为 (a) 候选——建议人工裁决：保留 38 为 canonical，23 收敛为惯用法
专题页并在头部声明「权威来源见 38」或反向互链定位；若裁决为互补分层，则登记
IGNORE_PAIRS。

### C4 — 05_comparative/02_managed_languages（11 文件 / 44 边）→ **(c) 门误报**
`rust_vs_java/python/javascript/kotlin/scala/csharp/elixir/typescript/haskell/ocaml/fsharp`
——11 个不同语言的对比页，仅共享 `rust_vs_` 前缀。全互撞 44 边。
**处置**：整簇豁免（模式级）。

### C5 — 06_ecosystem/01_cargo（11 文件 / 10 边）→ **(c) 为主，1 对 (b)**
cargo_script / build_scripts / registries / profiles / subcommands / security_cves /
configuration / commands_reference 等各自独立 → (c)。
`10_cargo_manifest_reference.md` vs `20_cargo_manifest_targets.md`：前者是 Cargo.toml
全字段速查（自称权威页），后者是其中 targets 子域的权威页——(b) 合法分层（总览 vs
子域），建议头部互链 + 登记 IGNORE_PAIRS。

### C6 — 06_ecosystem/03_design_patterns（11 文件 / 13 边）→ **(b) 为主**
`33_anti_patterns.md` vs `51_anti_patterns_and_pitfalls.md`：51 头部**已显式声明**
「与 33 形成互补：后者覆盖日常常见反模式，本页覆盖 Unsafe/API/异步/性能深坑」——
教科书式 (b) 合法分层，但词干不匹配 PROGRESSION_SUFFIXES（`_and_pitfalls_atlas` 不在
豁免后缀表），故仍被报。→ 登记 IGNORE_PAIRS。
`18_api_design_patterns.md` vs `39_api_design_and_semver_idioms.md`：42 个 API 模式
总览 vs SemVer 兼容性惯用法专题，主题域不同 → (b)，登记豁免。
其余（patterns/microservice/architecture/ecs/anti_patterns 长尾）→ (c) `_patterns`
后缀撞键。

### C7 — 04_formal/03_operational_semantics（8 文件 / 10 边）→ **(c) 门误报**
denotational / operational / axiomatic / observational equivalence / aeneas / async
state machine / pin / in-place init——语义学不同分支，仅共享 `_semantics` 后缀。
**处置**：整簇豁免（模式级）。

### C8 — 05_comparative/01_systems_languages（8 文件 / 25 边）→ **(c) 门误报**
`rust_vs_cpp/go/ruby/swift/zig/ada_spark/d/nim`，同 C4。

### C9 — 06_ecosystem/16_algorithm_patterns（8 文件 / 14 边）→ **(c) 为主，1 对 (b)**
graph/cache-friendly/greedy/randomized/online/parallel 各独立 → (c) `_algorithms` 撞键。
`07_string_algorithms_in_rust.md` vs `13_advanced_string_algorithms.md`：经典算法
(KMP/Rabin-Karp/Trie) vs 高级算法(Z-function/Aho-Corasick/后缀自动机)——(b) 合法
basics→advanced 分层；但词干 `string_algorithms_in_rust` vs `advanced_string_algorithms`
不满足 PROGRESSION_SUFFIXES 的「基础词干+后缀」形态（advanced 在前缀位、in_rust 在后缀位），
豁免机制漏网。→ 登记 IGNORE_PAIRS，或未来重命名时统一为 `string_algorithms` /
`string_algorithms_advanced` 形态。

### C10 — 04_formal/00_type_theory（5 文件 / 4 边）→ **(b) 为主**
`03_type_inference`（HM 理论，受众[研究者]）vs `07_type_checking_and_inference`
（rustc typeck 实现，受众[专家]）vs `08_type_inference_complexity`（PSPACE 复杂度）——
同一主题域的理论/实现/复杂度三个切面，各自声明权威页且互有前置/后置链 → (b) 合法
分层，建议登记豁免并在三页头部补互链定位声明（AGENTS.md §2 要求分层页互链）。
`02_subtype_variance` vs `03_type_inference` → (c) `type_` 泛词撞键。

## 5. 三类情形占比（抽样外推）

深查覆盖：前 10 簇 = 122/263 文件（46%）、292/384 边（76%）。

| 情形 | 判定依据 | 边数估计 | 占比 |
|---|---|---|---|
| **(c) 门误报**（泛前后缀撞键、版本号系列） | C1/C2/C4/C7/C8 整簇 + C3/C5/C9 多数 + 机械归因表 | ~300 | **≈78%** |
| **(b) 合理分层/互补**（应登记豁免） | C6 两对、C9 一对、C10 三对、C5 一对 + 长尾中同类 | ~70 | **≈18%** |
| **(a) 真重复候选**（需人工裁决合并/改 stub） | C3 的 23/38 no_std 对；另 `04_compiler_internals` vs `05_compiler_infrastructure`（C12，两页 Summary 行完全相同「Compiler Internals: Rust ecosystem tools…」疑似注入的样板摘要，且都声明权威页；章节重叠低，倾向 (b) 但需人工确认） | ~2–4 对 | **≈1%** |

结论：**不存在需要批量合并的真重复潮**；384 条 WARN 的主体是词干相似度算法对
「同目录、同后缀惯例、不同主题」文件的系统性误报。

## 6. 处置建议

### 6.1 豁免机制现状
脚本已有 `IGNORE_PAIRS`（逐对、支持 basename 容忍重编号）与 `PROGRESSION_SUFFIXES`
（后缀级）。**没有**正则/模式级豁免。逐对登记无法覆盖 ~300 条误报边（需 ~300 个
frozenset，不可维护）。

### 6.2 建议（按优先级；均为未来变更建议，本次未执行）
1. **给脚本增加模式级豁免**（如 `STEM_PATTERN_EXEMPTIONS`，登记正则 + 复核理由注释），
   一次性豁免四类模式：`rust_1_\d+_(preview|stabilized)`、`rust_vs_*`、目录内共享
   `_preview` 后缀对、`_stabilized` 后缀对。预计消除 ~250–300 边，WARN 从 384 降到
   ~80–130，进入可人工复核规模。
2. **扩充 PROGRESSION_SUFFIXES 或词干归一化**：处理 `advanced_` 前缀位形态
   （`advanced_string_algorithms`）与 `_in_rust` 尾缀剥离，可自动豁免 C9/C10 类分层对。
3. **IGNORE_PAIRS 逐对登记**剩余 (b) 类：至少 C6 两对（33/51、18/39）、C5 一对
   （10/20）、C9 一对（07/13）、C10 三对——每对附复核日期与理由（沿用 2026-08-01 先例格式）。
4. **(a) 候选人工裁决**（唯一需要动内容的一对）：`23_no_std_and_bare_metal_idioms` vs
   `38_no_std_bare_metal_rust`——裁决为「38 为 canonical、23 头部加权威来源指向 + 收敛
   重叠章节」或「互补分层 + 登记豁免」。`04/05 compiler_internals/infrastructure` 一对
   顺带核查 Summary 是否样板注入。
5. **修正脚本横幅文案**：「疑似跨层同主题」→「疑似同目录同主题」（实测 384 条全部
   同目录），避免后续误读。
6. **长尾 60 簇批量处置**：43 个 2-文件簇 + 13 个 3-文件簇中，绝大多数为目录内
   共享泛后缀对（`_map`/`_index`/`_reference`/`_idioms`/`_safety`…），随 6.2-1 模式级
   豁免一并处理；豁免后仍残留的对再逐簇人工过一遍（预计 <30 对，一次复核可完成）。

### 6.3 红线合规
本报告为只读梳理产物（reports/ 下唯一新增文件）。§6.2 各项均为建议，未执行任何
文件修改、移动或 git 操作；(a) 类合并动作在人工裁决前不得自动执行（AGENTS.md 红线
§6：禁未验证完成声明；文件只移动不删除）。

---

*生成：2026-10-13；数据快照 = 提交 e44fc0ff9 后工作区（现场重跑与 QUALITY_GATES_BASELINE_2026-10-13.txt 一致）。*
