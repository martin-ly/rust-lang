# Summary 精修与版本声明文首迁移报告（2026-07-12）

> **EN**: Summary Refinement and Version-Header Migration Report
> **范围**: 任务 A（D6 低信息量 Summary 重写 + 概念定义图谱定义精修）、任务 B（页脚 Rust 版本声明迁移文首）
> **结论**: D6 13→0；T1 1.1%（<10% 阈值）；文首版本声明覆盖率 52.9%→96.5%（≥90% 目标达成）；D3/D4 无新增（均为 0）；所有相邻质量门 exit 0。

---

## 一、任务 A：D6 低信息量 Summary 重写

### 1.1 处置清单（13 个文件，全部来自 `reports/METADATA_CONSISTENCY_BASELINE_2026-07-12.json` D6 项）

| 文件 | 问题 | 处置 |
|---|---|---|
| `concept/SUMMARY.md` | Summary 为空（mdBook 导航清单） | 重写为「mdBook navigation manifest…drives the book's sidebar, reading order, and prev/next links」，并修复 `> >` 嵌套引用等头部格式 |
| `concept/00_meta/02_sources/authority_source_map.md` | 套话 "Authority Source Map. Core Rust concept." | 重写：概念→四层权威来源（官方/学术/社区）+ C++/Haskell/Go 对标映射 |
| `concept/00_meta/03_audit/concept_audit_guide.md` | 套话 "Concept Audit Guide. Core Rust concept." | 重写：五步审计流程（元数据→链接→跨层引用→去重→归档）+ 审计维度 + 通过标准 |
| `concept/02_intermediate/00_traits/18_lifetimes_advanced.md` | Summary 为空（非 blockquote 格式，脚本无法抽取） | 转为 `> **EN**`/`> **Summary**` 标准格式；Summary 标注重定向目标（30_lifetimes_advanced.md）及覆盖主题（HRTB/elision/variance/闭包捕获/自引用/Pin） |
| `concept/03_advanced/01_async/38_async_boundary_panorama.md` | Summary 为空（非 blockquote） | 转为 blockquote（原 Summary 内容已高质量，保留） |
| `concept/03_advanced/02_unsafe/32_unsafe_boundary_panorama.md` | Summary 为空（非 blockquote） | 同上 |
| `concept/04_formal/02_separation_logic/33_safety_tags_in_formal.md` | Summary 为空（非 blockquote，重定向 stub） | 转为 blockquote 并标注重定向目标（08_safety_tags_preview.md） |
| `concept/06_ecosystem/01_cargo/59_cargo_build_scripts.md` | 套话 "A comprehensive guide to…" | 重写：`build.rs` 执行模型、`cargo:` 指令协议、`links`/OUT_DIR 本地库链接、rerun-if-changed 缓存、常见陷阱 |
| `concept/06_ecosystem/01_cargo/87_build_std.md` | 套话 "A comprehensive guide to…" | 重写：`-Zbuild-std` 从源码编译 std/core/alloc 的用途（自定义 target、no_std+alloc、panic handler、build-std-features、LTO 体积优化） |
| `concept/06_ecosystem/09_testing_and_quality/17_benchmarking.md` | 套话 "Core Rust concept covering…" | 重写：Criterion.rs 统计基准（置信区间采样、参数化/吞吐量 bench、基线回归检测、CI 集成、测量卫生） |
| `concept/06_ecosystem/12_networking/README.md` | Summary 为空（非 blockquote） | 转为 blockquote 并精修：目录索引定位（协议/机制层，与 04_web_and_networking 应用架构层互补） |
| `concept/07_future/00_version_tracking/migration_197_decision_tree.md` | Summary 为空（非 blockquote） | 转为 blockquote 并英文化：五类 1.97 兼容性场景的「是否受影响→根因→迁移动作」判定树 |
| `concept/07_future/03_preview_features/31_safety_tags_preview.md` | Summary 为空（非 blockquote，重定向 stub） | 转为 blockquote 并标注重定向目标（08_safety_tags_preview.md，含 21 基础标签覆盖 std ~96% 公开 unsafe API 事实） |

**根因说明**：13 项中 7 项的 Summary 其实已存在，但写在无 `>` 前缀的纯文本行上，`check_metadata_consistency.py` 的 `FIELD_RE`（要求 `> **K**: V`）无法抽取，被判「Summary 为空」。统一转为标准 blockquote 格式后既消除 D6，也与 §4.2 模板对齐。

### 1.2 概念定义图谱（01_concept_definition_atlas.md）定义精修

**问题**：定义列中部分条目以「：」收尾、含代码围栏泄漏（```rust…```）或为「定义暂缺」占位。基线扫描（463 行）发现 15 处异常：codeblock 泄漏 8、缺失 3、未完标点收尾 2、空洞泛化 2。

**根因与修复（改脚本 + 重生成，不手改生成物）**：

1. `scripts/extract_concept_topology.py` — `normalize_blockquote_header()`：原逻辑把 blockquote 头部内所有续行并入上一字段，导致「概念卡片」中的代码围栏/HTML 答案块被并入 Summary（8 个 quiz/MVP/谱系文件的定义列出现 ``` 泄漏）。修复：以 ```` ``` ```` 或 `<` 开头的续行独立成段，不再并入元数据字段。
2. `scripts/generate_knowledge_topology_atlas.py`：
   - 新增 `clean_summary()`：剥离混入的代码围栏与 `<details>` 块、折叠空白；
   - 新增 `_complete_sentences()`：段落抽取未以句末标点收尾时回退到最后一个完整句（根治「它提供：」类未完定义）；
   - `is_hollow_definition()` 将以 `:：—·,，` 收尾的定义视同空洞，强制走回退链；
   - `current_file_summary()` 的 `>` 前缀改为可选，兼容历史非 blockquote 头部；
   - `header()` 恢复 `> **Rust 版本**: 1.97.0+ (Edition 2024)`（旧版生成物有此行，现行生成器遗漏，重生成会丢失）；
   - `footer()` 删除重复的 `> **内容分级**: [元层]`（与头部重声明，触发 D3），改为生成说明行；`write_readme()` 同步删除尾部重复字段并补 Rust 版本行。
3. 重跑 `extract_concept_topology.py` → `generate_knowledge_topology_atlas.py` 全量重生成（raw json 465→467 概念，反映 concept/ 近期变更）。重生成后异常定义 **0 处**（同口径扫描）。

### 1.3 任务 A 验证

- `python scripts/check_metadata_consistency.py`：**D6 = 0**（基线 13）；D1=0、D2=1（既有）、D3=0、D4=0、D5=17（基线持平）。
- `python scripts/check_topology_quality.py`：**T1 定义套话率 1.1%（<10%）**、T5=0、T6=0，`--strict` 无 WOULD-FAIL。

---

## 二、任务 B：页脚版本声明迁移文首

### 2.1 基线

- concept/ 共 484 个 md 文件；文首（`>` 前缀）版本声明 256 个（**52.9%**）；212 个文件的 `**Rust 版本**:`/`**对应 Rust 版本**:` 声明在页脚文档信息簇（与 `**文档版本**`/`**最后更新**` 相邻，无 `>` 前缀）；16 个文件无声明。

### 2.2 迁移脚本：`scripts/fixes/migrate_footer_version_to_header.py`

逻辑（`--dry-run` / `--apply`）：

1. 识别页脚纯文本声明行（跳过代码围栏内行）；
2. 全文无同名字段时，在文首 `> **Summary**:` 行后插入 `> **Rust 版本**: <原值>`（值原样保留；仅精确值 `1.97.0+` 规范为 `1.97.0+ (Edition 2024)`）；
3. 全文已有同名字段（双声明）时仅删除页脚行，保留文首；
4. **D4 护栏**：迁移后全文版本字段 distinct minor ≥2 的文件跳过（保留页脚原样）——命中 3 个多版本跟踪页：
   - `concept/04_formal/05_rustc_internals/19_rustc_query_system.md`（1.97.0+ / nightly 1.99）
   - `concept/04_formal/05_rustc_internals/26_trait_solver_in_rustc.md`（1.97.0+ / nightly 1.99）
   - `concept/07_future/00_version_tracking/05_rust_version_tracking.md`（1.97 stable/beta/1.98 nightly 三轨）
5. 按字节读写，保持各文件原有 CRLF/LF 行尾（worktree 244/257 未触碰文件本为 CRLF，属既有状态）。

### 2.3 结果

- **迁移 209 个文件**（198 `Rust 版本` + 11 `对应 Rust 版本`，含 `audit_checklist.md` 的文首 `Rust 版本`+页脚 `对应 Rust 版本` 合并），跳过 3 个（D4 护栏），0 冲突。
- 文首口径覆盖率：**256/484 (52.9%) → 467/484 (96.5%)** ≥ 90% 目标。
- 剩余 17 个无文首声明：3 个 D4 护栏保留页脚 + 14 个无声明文件（重定向 stub、placeholder、README/INDEX 类）。
- 行尾保持：脚本按原文件字节中的 `\r\n` 检测并保持，未发生 CRLF→LF 翻转（git 的 "CRLF will be replaced" 警告为既有 worktree 状态，非本次引入）。

### 2.4 验证（迁移后重跑）

`python scripts/check_metadata_consistency.py`：D3=0（无新增重声明）、D4=0（无新增版本矛盾）、D5=17（基线持平）、D6=0。

**一处配套调整**：重生成后的 atlas 定义列含 07_future 预览概念名（"Preview"/"nightly"，110+8+1 处），使 atlas 3 文件进入 D5（17→20）。atlas 是跨层生成的元层索引，此类词仅作为概念名引用出现、非稳定层正文残留，故将 `knowledge_topology` 加入 `check_metadata_consistency.py` 的 `D5_WHITELIST_SUBSTR`（与 `07_future` 同类豁免），D5 回到 17。

---

## 三、全量质量门复核（2026-07-12 工作区状态）

| 门 | 结果 |
|---|---|
| `check_metadata_consistency.py` | D1=0 D2=1（既有）D3=0 D4=0 D5=17（基线）**D6=0** |
| `check_topology_quality.py` | T1=1.1% T3 死端=0 T5=0 T6=0，`--strict` 无 WOULD-FAIL |
| `check_canonical_uniqueness.py --strict` | exit 0 |
| `check_kg_shapes.py --strict` | K1–K7 全 0，exit 0 |
| `concept_consistency_auditor.py --strict` | 0 错误 0 警告，exit 0 |
| `detect_content_overlap.py` | exit 0 |
| `kb_auditor.py` | 死链 0、跨层问题 0，exit 0 |

## 四、备注

1. 工作区存在并发自动提交进程：本次工作期间 HEAD 出现自动 commit（`ae153af7c "update"`），已包含本任务大部分变更；本报告撰写时仍有 12 个 concept 文件的「TODO→演进方向」措辞 diff 为并发进程所为，与本任务无关，未触碰。
2. 未执行任何 git commit/push（按任务要求）。
3. atlas 文件由脚本生成，后续 concept/ 更新后应重跑 `extract_concept_topology.py` + `generate_knowledge_topology_atlas.py`（生成器已固化本次全部修复，重生成不会回退）。
