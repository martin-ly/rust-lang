# Rust 版本声明覆盖率提升报告（2026-07-12）

> **范围**: `concept/` 内容页（排除 `archive/`、`sources/`、`placeholders/`、`README.md` 及重定向 stub——含"本文件保留为重定向"或"已合并至"的文件）
> **基线**: Rust 1.97.0 stable / Edition 2024
> **目标**: 版本声明覆盖率 ≥ 90%；L7（07_future）Bloom 层级标注补齐；不新增 D1/D2/D3/D4 标记

---

## 1. 覆盖率前后对比

### 口径说明

任务书给定基线为约 57%（269/470）。本次以两种可机器复核的口径重新测量（统计脚本：`tmp/version_decl_analyze.py`，全量变更日志：`tmp/version_decl_changes.json`）：

- **口径 A（声明行，含页脚块）**: 文件中存在 `**(对应 )?Rust ?版本**:` 或 `**Rust Version**:` 声明行（`>` 前缀可选，含文件尾部"权威来源对齐"页脚块）。
- **口径 B（严格文首字段）**: 仅统计 `> **Rust 版本**:` 标准引用块字段。

与任务书基线的差异来自统计口径与统计时点（仓库当日有并发重构），此处以同一口径的前后对比为准。

### 总体

| 口径 | 前 | 后 | 目标 |
|---|---|---|---|
| A（声明行） | 333/457（72.9%） | **457/457（100.0%）** | ≥90% ✅ |
| B（严格文首字段） | 142/457（31.1%） | 256/457（56.0%） | — |

> 口径 B 未达 100% 的原因：213 个文件的声明位于文件尾部"权威来源对齐"页脚块（`**文档版本** / **Rust 版本** / **最后更新** / **状态**` 风格，无 `>` 前缀）。按"改动最小化"原则仅统一字段名、保留其页脚块风格，未迁移为文首引用块。

### 分层明细（口径 A）

| 层级 | 前 | 后 |
|---|---|---|
| 00_meta | 35/59（59%） | 59/59（100%） |
| 01_foundation（L1） | 37/55（67%） | 55/55（100%） |
| 02_intermediate（L2） | 29/39（74%） | 38/38（100%）¹ |
| 03_advanced（L3） | 48/61（79%） | 60/60（100%）¹ |
| 04_formal（L4） | 51/51（100%） | 51/51（100%） |
| 05_comparative（L5） | 17/19（89%） | 19/19（100%） |
| 06_ecosystem（L6） | 79/113（70%） | 113/113（100%） |
| 07_future（L7） | 37/60（62%） | 62/62（100%）¹ |

¹ 分层总数在统计窗口内因并发进程移动 4 个文件而变化（见 §4.5）；最终状态以移动后位置统计。

## 2. L7（07_future）Bloom 层级补齐

- **前**: 07_future 60 个内容页中 9 个缺 `Bloom 层级` 标注（85% 覆盖）。
- **后**: **62/62（100%）**。

补齐规则与 D1/D2 兼容性（按目录语义 + 既有 `层级`/`A/S/P` 约束取交集）：

| 文件 | Bloom | 依据 |
|---|---|---|
| `00_version_tracking/rust_1_95_stabilized.md` | L2-L3 | 版本追踪类，与同目录 1.90–1.94 页一致 |
| `00_version_tracking/rust_1_96_stabilized.md` | L2-L3 | 同上 |
| `00_version_tracking/rust_1_97_stabilized.md` | L2-L3 | 同上 |
| `00_version_tracking/rust_1_97_preview.md` | L2-L3 | 版本追踪类（预览归档） |
| `00_version_tracking/rust_1_98_preview.md` | L2-L3 | 版本追踪类 |
| `01_edition_roadmap/19_rust_edition_preview.md` | L2-L3 | 需同时满足 `层级=L3`（D1）与 `A/S/P=A`→{L1,L2}（D2），L2-L3 为唯一兼容区间 |
| `01_edition_roadmap/23_rust_edition_guide.md` | L2-L3 | Edition 指南，与版本追踪类同级 |
| `03_preview_features/40_ergonomic_ref_counting_preview.md` | L4-L5 | preview 特性 L3-L5 区间，与同目录多数 preview 页一致 |
| `04_research_and_experimental/29_ebpf_rust.md` | L5-L7 | 研究前沿类 |

## 3. 变更统计（共 405 个文件）

| 动作 | 文件数 | 说明 |
|---|---|---|
| 插入 `Rust 版本` 声明 | 124 | 锚点：`> **Summary**:` 之后（无则 EN / H1），`> **Rust 版本**: 1.97.0+ (Edition 2024)` |
| 变体字段名统一 | 249 | `对应 Rust 版本`（239）/`Rust Version`（10）→ `Rust 版本`，保留原位置与前缀风格 |
| 合并双字段 | 31 | 文件已有标准字段时删除页脚变体行（避免 D3 重声明） |
| D4 值修复 | 1 | 见 §4.4 |
| Bloom 插入 | 9 | 见 §2 |

插入声明的分层分布：00_meta 24、01_foundation 18、02_intermediate 9、03_advanced 12、05_comparative 2、06_ecosystem 34、07_future 25。

## 4. 特殊处理清单

### 4.1 特定版本页（不用 1.97 默认值）

| 文件 | 声明值 |
|---|---|
| `07_future/00_version_tracking/rust_1_97_preview.md` | `1.97.0 (Edition 2024) 预览归档` |
| `07_future/00_version_tracking/rust_1_98_preview.md` | `1.98.0 (nightly preview)` |
| `06_ecosystem/00_toolchain/77_rustdoc_196_changes.md` | `1.96.0+ (Edition 2024)` |
| `06_ecosystem/01_cargo/76_cargo_196_features.md` | `1.96.0+ (Edition 2024)` |

版本追踪页（rust_1_90–1_97_stabilized 等）在字段名统一时**保留各自版本值**（如 `1.90+`、`**1.96.1 stable**`），未改为 1.97。

### 4.2 版本值冲突合并（潜在 D3/D4 前置清理）

- `07_future/00_version_tracking/rust_1_90_stabilized.md`: 文首 `Rust 版本: 1.90+` 与页脚变体 `对应 Rust 版本: 1.96.1+` 冲突 → 保留 1.90+，删除页脚变体。
- `07_future/00_version_tracking/rust_1_94_stabilized.md`: 文首 `1.94.0` 与 3 处页脚变体 `1.96.1+` 冲突 → 保留 1.94.0，删除全部变体。

### 4.3 英文字段名统一

`03_advanced/08_process_ipc/*.md`（10 个文件）的 `**Rust Version**: 1.97.0+` → `**Rust 版本**: 1.97.0+`。

### 4.4 D4 修复

`02_intermediate/00_traits/40_generic_associated_types.md`: 字段值 `1.97.0+ (Edition 2024) · GATs MVP 自 **1.65** (2022-11) 稳定` 含两个 distinct minor → 裁剪为 `1.97.0+ (Edition 2024)`（1.65 稳定化历史在「定位」字段与正文中已有记载，无信息丢失）。

### 4.5 并发文件移动（执行期间）

批处理期间另一进程移动了 4 个文件（声明已随内容携带，已逐一验证）：

| 原路径 | 新路径 |
|---|---|
| `02_intermediate/00_traits/32_editions.md` | `07_future/00_version_tracking/32_editions.md` |
| `02_intermediate/00_traits/33_rust_release_process.md` | `07_future/00_version_tracking/33_rust_release_process.md` |
| `03_advanced/02_unsafe/30_rust_runtime.md` | `03_advanced/06_low_level_patterns/30_rust_runtime.md` |
| `03_advanced/02_unsafe/31_panic.md` | `02_intermediate/03_error_handling/31_panic.md` |

### 4.6 行尾（CRLF）

批处理脚本初版因 `read_text()` 的通用换行转换将 405 个文件写成 LF；已全部还原为 CRLF（`tmp/version_decl_changes.json` 记录的每个文件逐一修复并验证：CRLF 1904/1904、0 bare LF 等抽样通过）。仓库 `.gitattributes` 为 `* text=auto eol=lf` 且 `core.autocrlf=true`，git 层面 diff 不受行尾影响。注：极少数原本在 working tree 即为 LF 的文件（如 `04_formal/00_type_theory/02_type_theory.md` 页脚）本次一并转为 CRLF，与仓库 checkout 约定一致。

## 5. 质量门验证

### `scripts/check_metadata_consistency.py`

| 指标 | 执行前 | 执行后 | 判定 |
|---|---|---|---|
| D1 Bloom 互斥 | 0 | 0 | 未新增 ✅ |
| D2 A/S/P 脱节 | 97 | 1 | 下降 ✅（剩余 1 处为 `00_meta/04_navigation/foundations_gap_closure_index.md` 既有问题：Bloom L0 vs A/S/P=S，非本次改动引入） |
| D3 字段重声明 | 0 | 0 | 未新增 ✅ |
| D4 版本自矛盾 | 1 | **0** | 修复 ✅ |
| flagged files | 121 | 30 | 持续下降 ✅ |

> 说明：D2 大幅下降主要受益于当日并发重构；本次 9 处 Bloom 插入均经 D1/D2 约束校验，未引入新标记。

### `scripts/check_template_cliches.py --strict`

通过（exit 0，未发现模板套话）✅

## 6. 产物

- 变更日志：`tmp/version_decl_changes.json`（405 文件全量动作记录）
- 统计脚本：`tmp/version_decl_analyze.py`、批处理脚本：`tmp/version_decl_batch.py`
- 元数据基线报告：`reports/METADATA_CONSISTENCY_BASELINE_2026-07-12.{md,json}`（脚本自动更新）

## 7. 遗留事项（非本次范围）

1. 口径 B（严格文首 `> **Rust 版本**:` 字段）为 56%：213 个页脚块风格声明未迁移。如需统一为文首字段，需另立迁移任务并评估对页脚"权威来源对齐"块风格的影响。
2. D5（稳定层 nightly/preview 残留 17 处）与 D6（Summary 套话 13 处）为既有观察项，本次未触碰正文。
3. 剩余 D2 1 处（`foundations_gap_closure_index.md` Bloom L0 vs A/S/P=S）建议后续单独裁决。
