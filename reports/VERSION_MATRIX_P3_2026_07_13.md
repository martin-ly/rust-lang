# 版本页矩阵化与 1.98 跟踪（P3）执行报告

> 日期：2026-07-14（任务日期标注 2026-07-13 计划 P3）
> 依据：`.kimi/FOLLOW_UP_PLAN_P1_P5_2026_07_13.md` P3
> 范围：`concept/07_future/00_version_tracking/` 1.90–1.96 stabilized 页 + 1.98 preview 页 + 13 个 concept 权威页反向注记

---

## 1. 任务 1：1.90–1.96 版本页矩阵化

**统一结构**：每页在元数据块后插入「§0 特性 × 影响面 × 受益场景 × 权威源矩阵」节，对齐 `rust_1_97_stabilized.md` 范式（矩阵列：特性 / 影响面 / 受益场景 / 权威源），并附官方发布说明可访问性实测行。

**官方来源实测（2026-07-14 curl）**：`releases.rs/docs/1.90.0`–`1.96.0` 全部 HTTP 200；`blog.rust-lang.org` 对应 7 篇 Release Blog 全部 HTTP 200，无不可达需标注项。

| 版本 | 文件 | 矩阵行数 | 处置要点 | 改动量 |
|:---|:---|:---:|:---|:---|
| 1.90 | `rust_1_90_stabilized.md` | 6 | 页内正文为网络场景应用（既有特性），矩阵补齐 1.90 **本列车**真实特性（lld 默认链接器、`sub_signed` 系列、`CStr` 互比、浮点 const、Cargo 多包发布、macOS 降级 Tier 2），并指引 §11 既有版本事实对齐表 | +30 行 |
| 1.91 | `rust_1_91_stabilized.md` | 7 | 已有 P1-a 深化（2719 行），仅加矩阵节，不改写正文（variadic ABI、`dangling_pointers_from_locals`、`strict_*`、原子 `fetch_*`、`with_exposed_provenance`、`build.build-dir`、LLVM 21） | +31 行 |
| 1.92 | `rust_1_92_stabilized.md` | 7 | 同 1.91，仅矩阵对齐（MaybeUninit 有效性文档化、`&raw` 联合体字段、关联项多边界、`new_zeroed`、`RwLockWriteGuard::downgrade`、`Repeat::last/count` panic、`file_as_c_str`） | +31 行 |
| 1.93 | `rust_1_93_stabilized.md` | 8 | 正文 §三 已覆盖 7 条 std API，矩阵补齐遗漏特性（`asm_cfg`、system ABI variadic、`-Cjump-tables`、`cargo clean --workspace`）并交叉指引 §3.x | +30 行 |
| 1.94 | `rust_1_94_stabilized.md` | 7 | 原页为 c10 迁移的泛化骨架，矩阵首次给出 1.94 真实特性（29 个 RISC-V target feature、`array_windows`、`LazyCell/LazyLock::get*`、`mul_add`、Cargo `include`+TOML v1.1、std 宏 prelude 导入兼容变更、数学常量） | +30 行 |
| 1.95 | `rust_1_95_stabilized.md` | 8 | 正文覆盖齐全，矩阵做索引对齐（`cfg_select!`、if-let guards、关键字重命名导入、`core::range`、原子 `update/try_update`、`*_mut` 插入、`as_ref_unchecked`、`--remap-path-scope`） | +30 行 |
| 1.96 | `rust_1_96_stabilized.md` | 7 | 正文覆盖齐全，矩阵做索引对齐（`assert_matches!`、`expr` metavariable→`cfg`、`core::range` Copy、NonZero 迭代、`From<T>` 扩展、valid-for-read/write 重构、Cargo git+registry 共存/CVE） | +29 行 |

各页改动均 ≤80 行（实际 29–31 行/页）。遗漏特性补齐对照 releases.rs 全量条目核对：1.93 补 4 条、1.94 补 7 条（原页无实质特性清单）、1.90 补 6 条（原页无 1.90 本列车特性），1.91/1.92/1.95/1.96 无核心遗漏。

## 2. 任务 2：下沉反向链接

共 **17 处版本注记**（≤25 上限），全部落在已存在的 concept 权威页，格式统一为
`> **Rust 1.XX 起**：…稳定，详见 [版本页](../../07_future/00_version_tracking/rust_1_XX_stabilized.md) §0 矩阵。`

| 版本 | 注记特性 | 目标权威页 |
|:---|:---|:---|
| 1.90 | `sub_signed` 系列 + 浮点 const | `concept/01_foundation/02_type_system/03_numerics.md` |
| 1.90/1.93 | 多包发布 + `cargo clean --workspace` | `concept/06_ecosystem/01_cargo/19_cargo_commands_reference.md` |
| 1.91/1.93 | variadic ABI + `into_raw_parts` | `concept/03_advanced/04_ffi/01_rust_ffi.md` |
| 1.91/1.95 | 原子 `fetch_*` + `update/try_update` | `concept/03_advanced/00_concurrency/05_atomics_and_memory_ordering.md` |
| 1.91/1.96 | `with_exposed_provenance` + valid-for-read/write | `concept/03_advanced/02_unsafe/06_memory_model.md` |
| 1.92 | MaybeUninit 有效性 + `&raw` 联合体 + `new_zeroed` | `concept/03_advanced/02_unsafe/01_unsafe.md` |
| 1.92 | `RwLockWriteGuard::downgrade` | `concept/03_advanced/00_concurrency/03_concurrency_patterns.md` |
| 1.93 | `fmt::from_fn` / `FromFn` | `concept/01_foundation/06_strings_and_text/03_formatting_and_display.md` |
| 1.94/1.96 | `array_windows` + `core::range` Copy | `concept/02_intermediate/07_iterators_and_closures/01_iterator_patterns.md` |
| 1.94 | Cargo `include` + TOML v1.1 | `concept/06_ecosystem/01_cargo/18_cargo_configuration.md` |
| 1.95 | `cfg_select!` | `concept/01_foundation/09_macros_basics/01_attributes_and_macros.md` |
| 1.95 | if-let guards + 关键字重命名导入 | `concept/01_foundation/04_control_flow/01_control_flow.md` |
| 1.96 | `assert_matches!` | `concept/02_intermediate/06_macros_and_metaprogramming/01_assert_matches.md` |

死链验证：kb_auditor 全库死链 0（见 §4）。

## 3. 任务 3：1.98 跟踪清单

`rust_1_98_preview.md` 已存在且维护良好（含 §1.7 新近合并 RFC 表）。本次更新：

1. **新增「§零 1.98 周期跟踪清单」**（12 行表）：特性 × 状态 × 跟踪链接。
   - `stabilized in 1.98 beta`（4 条，源自 [releases.rs 1.98.0 beta](https://releases.rs/docs/1.98.0/)，curl 200 实测）：`Panic[Hook]Info` 的 `Location<'static>`、mingw-w64 工具链更新、Solaris `File::lock` 移除、`-Zemscripten-wasm-eh` 移除；
   - `RFC merged`（4 条）：#3955 Named Fn parameters、#3808 register_tool、#3928 todo!/unreachable_code、#3516 public/private deps（RFC Book 链接均实测 200）；
   - `FCP`（1 条）：Safety Tags #3842；
   - `nightly only`（3 条）：Pin Ergonomics、Async Drop、RTN，链接至 `03_preview_features/` 既有预览页。
2. **事实勘误**：元数据「预计稳定时间 2026-09-04」更正为 **1.98.0 = 2026-08-20**（releases.rs 实测：2026-07-03 分支入 beta），并补充 beta 状态行。
3. 维护约定：1.98.0 发布后将 beta 行迁移至新建 `rust_1_98_stabilized.md`，本页滚动为 1.99+。

## 4. 验证结果（2026-07-14 实跑）

| 门 | 命令 | 结果 |
|:---|:---|:---|
| 死链/跨层 | `python scripts/kb_auditor.py` | ✅ 死链 **0** / 跨层 **0** / 模板化 ⟹ 0，exit 0（495 文件 / 4901 代码块） |
| canonical 唯一性 | `python scripts/check_canonical_uniqueness.py --strict` | ✅ **ERROR 0**（WARN 227 为既有跨层同主题提示，非本次引入，不阻断），exit 0 |
| mdbook | `mdbook build` | ✅ 通过，exit 0 |

> 注：本轮仅触及 markdown 文档，未改动 crate 代码；`cargo check/clippy/test` 阻断门不受本轮影响。语义观察门（metadata consistency 等）未全量重跑，新增注记均为块引用+链接，不含 nightly 标记/占位语。

## 5. 遗留与后续登记

1. 1.90/1.94 页正文仍为迁移期场景化内容（网络视角），§0 矩阵已承担版本事实权威职责；后续轮次（P1-a C 档）可将正文标题与结构进一步对齐版本页范式。
2. 1.90 页内目录（TOC）未含新增 §0 节（保持 ≤80 行约束下的最小改动），mdbook 构建不受影响。
3. 1.98 跟踪清单需按 §7.1 双周频率滚动；2026-08-20 发布时需新建 `rust_1_98_stabilized.md` 并同步 SUMMARY/导航（登记给 P5 机制）。
