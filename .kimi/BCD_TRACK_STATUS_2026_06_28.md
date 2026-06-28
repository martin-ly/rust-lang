# BCD 轨道状态总览 — 2026-06-28

> **统计日期**: 2026-06-28
> **Rust 1.97.0 发布日**: 2026-07-09（剩余 11 天）
> **主控来源**: `.kimi/EXECUTION_CHECKLIST_2026_06_26_CONFIRMED.md`

---

## B 轨道 — 结构债务清理（P3）

| 编号 | 任务 | 状态 | 交付物 |
|---|---|---|---|
| B1 | 清理空 `.gitkeep` 与空/占位 `.rs` 文件 | ✅ | 56 个文件删除 |
| B2 | 更新 `crates/README.md` 补全全部 workspace crate | ✅ | 10 个 README.md |
| B3 | 实现 `unsafe_rust/` 练习主题 | ✅ | 7 个练习 + 17 个集成测试 |
| B4 | 复查重复/编号冲突文件 | ✅ | BorrowSanitizer 等 |
| B5 | 补全 `crates/common` examples/tests | ✅ | 2 examples + 1 integration test |
| B6 | 处理 `BorrowSanitizer` 文件重叠 | ✅ | 删除冗余预览文件 |
| B7 | 清理 9 个 crates `src/lib.rs` 中英文混杂注释 | ✅ | 9 个 crate 顶层文档重写 |
| B8 | 模板化 per-crate boilerplate docs | ✅ | 7 个模板 + 生成脚本 |
| B9 | 批量生成缺失 boilerplate 文档 | ✅ | 56 个新文件，17/17 crate 全覆盖 |

**B 轨道结论**: 🎉 **全部完成**

---

## C 轨道 — Rust 1.97.0 发布日准备

| 编号 | 任务 | 状态 | 交付物 |
|---|---|---|---|
| C1 | 复核 `rust-toolchain.toml`、1.97 特性代码、preview 文档 | ✅ | 工具链保持 nightly 策略确定 |
| C2 | 创建发布日自动检查脚本 | ✅ | `scripts/rust_197_release_day.sh` |
| C3 | 准备 `VecDeque::truncate_front` / `retain_back` fallback 切换策略 | ✅ | 等效实现 + 激活指南 |
| C3b | 扩展 API 探测脚本至 12 项并生成探测报告 | ✅ | `scripts/probe_rust_197_apis.rs` + `reports/RUST_197_API_PROBE_2026_06_28.md` |
| C3c | 更新术语表 1.97 候选术语状态 | ✅ | 17 项候选术语分组 |
| C3d | 准备 `CHANGELOG.md [3.1.0]` 1.97 特性条目草稿 | ✅ | 草稿已写入 CHANGELOG |
| C3e | 扩展 `exercises/tests/l3_rust_197_alignment.rs` 至 13 个测验 | ✅ | 13 个可运行测验 |
| C3f | 全 workspace 回归测试 | ✅ | `cargo test --workspace` 通过 |
| C3g | 整理发布日人工决策清单 | ✅ | `.kimi/RUST_197_RELEASE_DAY_DECISIONS.md` |
| C3h | 修正 `box_vec_non_null` API 名称 | ✅ | 统一为 `into_non_null` |
| C4 | 预演 `rust-toolchain.toml` → `1.97.0` 切换 | ⏳ | 2026-07-08 执行 |
| C5 | 发布日执行 `.kimi/EXECUTION_RUST_1_97_RELEASE_2026_07_09.md` | ⏳ | 2026-07-09 执行 |

**C 轨道结论**: ✅ **准备就绪**，进入等待上游发布阶段

### 当前 nightly 探测结果（2026-06-26，rustc 1.98.0）

- **9/12 API 已可用**（无需 feature gate）
- **3/12 仍不可用**:
  - `VecDeque::truncate_front`（仍需 feature gate）
  - `VecDeque::retain_back`（方法不存在）
  - `Vec::into_non_null`（方法不存在）

---

## D 轨道 — 排期与跟踪

| 编号 | 任务 | 状态 | 交付物 |
|---|---|---|---|
| D1 | 生成本周进度报告（06-28） | ✅ | `.kimi/WEEKLY_PROGRESS_2026_06_28.md` |
| D2 | 生成下周计划文件（07-05） | ✅ | `.kimi/WEEKLY_PROGRESS_2026_07_05.md` |
| D3 | 发布日倒计时排期 | ✅ | `.kimi/RUST_197_RELEASE_COUNTDOWN_2026_06_28.md` |
| D4 | 每日检查 releases.rs / 官方博客（07-04 ~ 07-08） | ⏳ | `scripts/rust_197_upstream_monitor.sh` 已创建，待每日执行 |
| D5 | 发布日后归档倒计时排期与执行清单 | ⏳ | 2026-07-10 ~ 11 |

**D 轨道结论**: ✅ **排期完成**，进入观察期

---

## E 轨道 — Rust 1.98.0 跟踪（新增）

| 编号 | 任务 | 状态 | 交付物 |
|---|---|---|---|
| E1 | 创建 1.98 API 探测脚本并生成报告 | ✅ | `scripts/probe_rust_198_apis.rs` + `reports/RUST_198_NIGHTLY_PROBE_2026_06_28.md` |
| E2 | 扩展 1.98 对齐测验 | ✅ | `exercises/tests/l3_rust_198_alignment.rs`（12 个测验） |
| E3 | 更新 1.98 概念预览与跟踪文档 | ✅ | `concept/07_future/rust_1_98_preview.md` + `.kimi/RUST_198_TRACKING_2026_06_28.md` |
| E4 | 清理并扩展 `rust_198_features.rs` 代码示例 | ✅ | 7 个 API demo + 单元测试 |

**E 轨道结论**: ✅ **基础设施就绪**，待 1.98 beta cutoff 后细化

---

## F 轨道 — 内部链接治理收尾（新增）

| 编号 | 任务 | 状态 | 交付物 |
|---|---|---|---|
| F1 | 修复 docs 下损坏内部链接 | ✅ | 5 + 2 = 7 个链接修复 |
| F2 | 更新链接检查报告 | ✅ | `docs/LINK_CHECK_REPORT.md` 损坏数从 19 降至 0（I 轨道清零） |

**F 轨道结论**: ✅ **docs 内部链接损坏数已清零**

---

## G 轨道 — i18n 双语标注基线（新增）

| 编号 | 任务 | 状态 | 交付物 |
|---|---|---|---|
| G1 | 增强双语标注脚本 | ✅ | `scripts/add_bilingual_annotations.py` 新增 `--report` |
| G2 | 生成 concept/ 全量基线 | ✅ | `reports/I18N_BILINGUAL_BASELINE_2026_06_28.md` |

**G 轨道结论**: ✅ **基线建立**，321 文件 / 39 种未覆盖术语，大规模标注仍按 Q4 计划执行

---

---

## H 轨道 — 安全审计（新增）

| 编号 | 任务 | 状态 | 交付物 |
|---|---|---|---|
| H1 | 运行 cargo audit | ✅ | `reports/CARGO_AUDIT_2026_06_28.md` |

**H 轨道结论**: ✅ **无已知安全漏洞**

---

## I 轨道 — 历史归档锚点修复（新增）

| 编号 | 任务 | 状态 | 交付物 |
|---|---|---|---|
| I1 | 修复 rust-ownership-decidability 12 个锚点问题 | ✅ | 12 个归档文件 TOC/锚点修复 |
| I2 | 清零 docs/LINK_CHECK_REPORT.md 损坏链接 | ✅ | 损坏链接从 12 降至 **0** |
| I3 | 顺手修复 1 个 archive 文件路径错误 | ✅ | `docs/archive/c_class_audit_2026_06_08/content/README.md` Coq 链接路径修正 |

**I 轨道结论**: ✅ **docs 内部链接损坏数清零**

---

## J 轨道 — Rust 1.98.0 代码示例扩展（新增）

| 编号 | 任务 | 状态 | 交付物 |
|---|---|---|---|
| J1 | 在 `rust_198_features.rs` 补充 1.98 候选 API 示例 | ✅ | 新增 `NonZero::from_str_radix`、`Box::as_ptr/as_mut_ptr`、`int::format_into` 3 个 demo |
| J2 | 更新对应单元测试 | ✅ | `test_198_api_demos` 覆盖 10 个 demo |
| J3 | 更新 1.98 跟踪文档 | ✅ | `.kimi/RUST_198_TRACKING_2026_06_28.md` |

**J 轨道结论**: ✅ **1.98 代码示例已扩展至 10 个 API demo**

---

## 当前阻塞与风险

| 风险 | 可能性 | 影响 | 缓解措施 |
|---|---|---|---|
| Rust 1.97.0 延迟发布 | 低 | 发布日计划顺延 | 密切关注 releases.rs 与官方博客 |
| `VecDeque::truncate_front` 未进入 1.97.0 | 中 | 保留等效实现 | 决策清单已明确 fallback |
| `VecDeque::retain_back` 未进入 1.97.0 | 高 | 保留等效实现 | nightly 已不存在该方法，大概率推迟 |
| `Box::as_ptr` / `int::format_into` 因 beta cutoff 未进 1.97.0 | 中 | 保留等效实现 | 发布日按 Release Notes 核对 |

---

## 下一步建议

1. **2026-07-03 ~ 07-07**: 每日检查上游发布动态，记录任何变化。
2. **2026-07-08**: 执行最终预检清单。
3. **2026-07-09**: 执行发布日清单，根据 Release Notes 激活真实 API。
4. **2026-07-10 ~ 11**: 发布后稳定化收尾。

---

*本报告基于 2026-06-28 18:00 状态生成。*

---

**提交记录**: 本状态对应的变更已推送至 `main` 分支：
- `B3: 结构债务清理收尾`
- `C/D: Rust 1.97.0 发布准备与排期`
- `E: 启动 Rust 1.98.0 跟踪`
- `E2: 扩展 Rust 1.98.0 对齐测验`
- `F: 修复剩余 2 个 Coq 内部链接并更新链接报告`
- `G: i18n 双语标注基线扫描`
- `H: 运行 cargo audit 并生成报告`
- `I: 修复 rust-ownership-decidability 归档锚点链接`
- `J: 扩展 Rust 1.98.0 代码示例`
