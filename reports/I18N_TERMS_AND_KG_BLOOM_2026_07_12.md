# i18n 术语双语标注补齐 + KG bloomLevel 回填报告

> 日期：2026-07-12
> 范围：任务 A（gate 9 双语标注）、任务 B（KG K1b bloomLevel）
> 执行方式：可机器复核（脚本输出附于各节）

---

## 任务 A — i18n 术语双语标注补齐

### A.1 基线核实（重要勘误）

背景材料引用的是 `reports/BILINGUAL_COVERAGE.md`（内容生成于 2026-07-04，未覆盖术语种类 32，
TOP 缺口 crate=17 / trait=13 / 一致性=11 / Vec=9 / 不可变引用=8）。
**该基线已过时**：07-04 之后的多轮标注已将存量大部分补齐。

本次任务开始时实跑 gate 9：

```
$ python scripts/add_bilingual_annotations.py --mode check-only
扫描文件数: 419
缺少 EN 字段: 0
缺少 Summary 字段: 0
未覆盖术语种类: 12
```

实际未覆盖 12 种术语、13 个文件 × 19 处独立出现（用脚本同一判定逻辑
`(?<![A-Za-z0-9_一-鿿])术语(?![A-Za-z0-9_一-鿿])` 逐一定位，全部确认为每文件唯一独立出现处）：

| 术语 | 英文（依 `scripts/add_bilingual_annotations.py` TERMS，与术语表一致） | 文件 |
|---|---|---|
| 类型系统 | Type System | `01_foundation/06_strings_and_text/46_formatting_and_display.md` |
| 错误处理 | Error Handling | `02_intermediate/00_traits/28_*.md`、`.../05_modules_and_visibility/29_*.md`、`.../06_macros_and_metaprogramming/26_*.md` |
| 宏 | Macro | `28_*.md`、`29_*.md`、`25_rtti_and_dynamic_typing.md`、`40_generic_associated_types.md`、`07_future/.../migration_197_decision_tree.md` |
| 闭包 | Closures | `40_generic_associated_types.md`、`03_advanced/00_concurrency/17_send_sync_auto_traits.md`、`.../01_async/38_async_boundary_panorama.md` |
| 枚举 | Enum | `03_advanced/01_async/37_async_cancellation_safety.md` |
| 生命周期 | Lifetimes | `38_async_boundary_panorama.md` |
| 单态化 | Monomorphization | `38_async_boundary_panorama.md` |
| 所有权 | Ownership | `03_advanced/02_unsafe/32_unsafe_boundary_panorama.md` |
| 智能指针 | Smart Pointer | `32_unsafe_boundary_panorama.md` |
| 内联汇编 | Inline Assembly | `32_unsafe_boundary_panorama.md` |
| 过程宏 | Procedural Macro | `05_comparative/README.md` |
| 引用 | Reference | `07_future/00_version_tracking/feature_domain_matrix_197.md` |

译名核对：`concept/00_meta/01_terminology/terminology_glossary.md` 对应条目为
Ownership / Lifetimes / Reference / Enum / Closures / Error Handling / Smart Pointers /
Inline Assembly / Procedural Macros / Monomorphization。
gate 9 的判定要求英文与脚本 TERMS 表逐词匹配（`\b` 边界），故采用单数形式
（Smart Pointer / Procedural Macro / Macro），与术语表为同一词条的单复数变体。

### A.2 修改方式

- 手工逐处编辑 13 个文件、19 处首次（且唯一）独立出现位置，加 `中文（English）` 括注；
- 标题、代码块、mermaid 块内出现不受影响（检查器本就跳过）；
- 典型位置：L2 跨语言对比专题样板行「（类型/宏（Macro）/错误处理（Error Handling）/构造/可见性）」（4 文件）、
  表格行、修复策略 blockquote、链接文本（`[智能指针（Smart Pointer）](...)`）。

### A.3 验证

```
$ python scripts/add_bilingual_annotations.py --mode check-only
扫描文件数: 419
缺少 EN 字段: 0
缺少 Summary 字段: 0
未覆盖术语种类: 0          # 12 → 0（目标 <5 达成，无需豁免）

$ python scripts/check_template_cliches.py --strict
[check_template_cliches] OK: concept 未发现模板套话
```

---

## 任务 B — KG bloomLevel 补齐（K1b）

### B.1 基线

`python scripts/check_kg_shapes.py`：K1b = 55 个实体缺 `ex:bloomLevel`（K1–K7 其余均为 0）。
55 个实体按 `ex:layer` 分布：L0×29（00_meta 框架/导航/索引页）、L3×2、L4×4、L6×11、L7×9。

### B.2 回填规则（优先级）

1. 文件显式声明 `**Bloom 层级**: X` → 用 X（9 个：rust_1_9x 版本页 ×7→`L2-L3`、
   ergonomic_ref_counting→`L4-L5`、ebpf→`L5-L7`）；
2. 文件声明 `**层次定位**: Lx ...` → 用 Lx（3 个 04_formal 文件→`L4`）；
3. 目录推断（AGENTS.md 分层约定）：03_advanced→`L3-L5`（2）、04_formal→`L4-L7`（1）、
   06_ecosystem→`L6`（11）；00_meta 及 concept/ 根导航页（ex:layer=L0）→`Meta`（29，
   与既有 11 个 meta 实体取值一致）。

### B.3 变更

| 文件 | 变更 |
|---|---|
| `concept/00_meta/kg_data_v3.json` | 55 个实体补 `ex:bloomLevel`；git diff 确认仅 bloomLevel 行新增（+逗号），无其他字段变化 |
| `concept/00_meta/kg_index.json` | 同步补齐 50 个 `bloom` 字段（保持两产物一致；另 5 个根导航页无 index 条目） |
| `scripts/generate_kg_index.py` | 新增 `infer_bloom()`：`Bloom 层级` 声明 → `层次定位` 回退 → 目录映射回退，防止再生成时回退 |
| `scripts/fixes/backfill_kg_bloom_level.py` | 新增幂等回填脚本（已有 bloomLevel 不覆盖；二次运行回填 0 个，幂等验证通过） |

### B.4 验证

```
$ python scripts/check_kg_shapes.py --strict
[P3-4] entities=474 relations=5807
  K1=0 K1b(no_bloom)=0 K2=0 K3=0 K4=0 K5=0 K6=0 K7=0     # K1b: 55 → 0

$ python scripts/semantic_health.py
[P4] semantic health total=93.6 grade=OK (meta=96.3 topo=90.7 dedup=85.0 kg=100.0)
                                                          # kg 维度 90 → 100，未下降
```

---

## 附：本次修改文件清单（未做 git commit）

- 任务 A（13）：`concept/01_foundation/06_strings_and_text/46_formatting_and_display.md`、
  `concept/02_intermediate/00_traits/{28_construction_and_initialization,40_generic_associated_types}.md`、
  `concept/02_intermediate/04_types_and_conversions/25_rtti_and_dynamic_typing.md`、
  `concept/02_intermediate/05_modules_and_visibility/29_friend_vs_module_privacy.md`、
  `concept/02_intermediate/06_macros_and_metaprogramming/26_c_preprocessor_vs_rust_macros.md`、
  `concept/03_advanced/00_concurrency/17_send_sync_auto_traits.md`、
  `concept/03_advanced/01_async/{37_async_cancellation_safety,38_async_boundary_panorama}.md`、
  `concept/03_advanced/02_unsafe/32_unsafe_boundary_panorama.md`、
  `concept/05_comparative/README.md`、
  `concept/07_future/00_version_tracking/{feature_domain_matrix_197,migration_197_decision_tree}.md`
- 任务 B（4）：`concept/00_meta/kg_data_v3.json`、`concept/00_meta/kg_index.json`、
  `scripts/generate_kg_index.py`、`scripts/fixes/backfill_kg_bloom_level.py`（新增）
- 自动再生成：`reports/KG_SHAPES_VALIDATION_2026-07-12.{md,json}`、`reports/SEMANTIC_HEALTH_2026-07-12.md`

> 注：工作区中另有一些本次未触碰的既有修改（如 `concept/02_intermediate/00_traits/18_lifetimes_advanced.md` 等），
> 系其他会话/前序工作遗留，与本任务无关。
