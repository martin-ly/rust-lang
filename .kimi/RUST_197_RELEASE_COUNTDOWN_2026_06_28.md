# Rust 1.97.0 发布倒计时排期（2026-06-28 ~ 2026-07-09）

> **硬截止**: 2026-07-09 Rust 1.97.0 stable 发布日
> **当前日期**: 2026-06-28
> **剩余天数**: 11 天
> **主控来源**: `.kimi/EXECUTION_CHECKLIST_2026_06_26_CONFIRMED.md`

---

## 已完成的发布前准备

| 任务 | 完成日期 | 交付物 |
|---|---|---|
| 清理结构债务（空文件、占位 stub、重复文件） | 2026-06-28 | 56 个文件删除，`concept/SUMMARY.md` 更新 |
| 补全缺失 README | 2026-06-28 | 10 个 README.md |
| 实现 `unsafe_rust/` 练习主题 | 2026-06-28 | `exercises/src/unsafe_rust/mod.rs` + 17 个测试 |
| 补全 `crates/common` 示例/测试 | 2026-06-28 | 2 个 examples + 1 个 integration test |
| 清理 crates `src/lib.rs` 中英文混杂文档注释 | 2026-06-28 | 9 个 crate 顶层文档重写 |
| 复核 1.97 特性代码与 fallback | 2026-06-28 | `crates/c08_algorithms/src/rust_197_features.rs` |
| 增强发布日 API 探测脚本 | 2026-06-28 | `scripts/probe_rust_197_apis.rs` 覆盖 12 项 API |
| 生成 API 可用性探测报告 | 2026-06-28 | `reports/RUST_197_API_PROBE_2026_06_28.md` |
| 创建发布日执行脚本 | 2026-06-28 | `scripts/rust_197_release_day.sh` |

---

## 倒计时日程

### 2026-06-28（周日）— 发布前第 11 天

- [x] 完成剩余结构债务清理（BorrowSanitizer 重叠文件、crates `lib.rs` 混杂双语 docs）
- [x] 更新周进度报告 `.kimi/WEEKLY_PROGRESS_2026_06_28.md`
- [x] 生成本倒计时排期文件
- [x] 增强 `scripts/probe_rust_197_apis.rs`（12 项 API）并生成 `reports/RUST_197_API_PROBE_2026_06_28.md`
- [x] 全 workspace 回归：`cargo check` / `cargo test` / `cargo clippy`

### 2026-06-29（周一）— 发布前第 10 天

- [x] 复查 `crates/c08_algorithms/src/rust_197_features.rs` 注释准确性
- [x] 检查 Rust 1.97 beta 最新动态（releases.rs：beta 1.97.0 仍 Unreleased，2026-05-22 从 master 分支）
- [x] 更新 `concept/07_future/rust_1_97_preview.md` 头部探测快讯
- [x] 预建 `docs/06_toolchain/06_21_rust_1_97_features.md` 稳定特性迁移模板
- [x] 若 `retain_back` 状态明确，提前更新 fallback 注释（结论：当前 nightly 方法不存在，保留等效实现并标注推迟风险）

### 2026-06-30（周二）— 发布前第 9 天

- [x] 预检 `docs/06_toolchain/` 目录，确认 1.97 稳定特性文档迁移目标位置（已创建 `06_21_rust_1_97_features.md` 模板）
- [x] 准备 `CHANGELOG.md [3.1.0]` 1.97 特性条目草稿

### 2026-07-01（周三）— 发布前第 8 天

- [x] 复查 `concept/07_future/rust_1_97_preview.md` 头部状态与探测快讯
- [x] 确认并更新术语表 `concept/00_meta/terminology_glossary.md` 中 1.97 术语状态（17 项候选术语分组）

### 2026-07-02（周四）— 发布前第 7 天

- [x] 全 workspace 回归测试：`cargo test --workspace` 通过
- [x] 整理发布日人工决策清单：新增 `.kimi/RUST_197_RELEASE_DAY_DECISIONS.md`

### 2026-07-03（周五）— 发布前第 6 天

- [x] 周报更新 `.kimi/WEEKLY_PROGRESS_2026_07_05.md`
- [ ] 若 1.97.0 已提前发布，可提前开始发布日流程

### 2026-07-04 ~ 2026-07-07 — 观察与待命

- [ ] 每日检查 releases.rs / Rust 官方博客
- [ ] 记录任何影响发布日执行的变更（特性推迟、签名变化等）

### 2026-07-08（周三）— 发布日前一天

- [ ] 确认 `rust-toolchain.toml` 保持 `nightly`（workspace 依赖 nightly feature gates）
- [ ] 确认本地 rustup 可下载 1.97.0（用于单独运行探测脚本）
- [ ] 最终确认 `scripts/probe_rust_197_apis.rs` 在 1.97.0 下的输出
- [ ] 准备发布日工作分支：`git checkout -b rust-1.97-release-day`

### 2026-07-09（周四）— 发布日

- [ ] 执行 `.kimi/EXECUTION_RUST_1_97_RELEASE_2026_07_09.md`
- [ ] 运行 `scripts/rust_197_release_day.sh`
- [ ] 根据探测结果激活真实 API 调用
- [ ] 更新 `rust_1_97_preview.md` 并迁移到 `docs/06_toolchain/06_21_rust_1_97_features.md`
- [ ] 补充 1.97 特性测验
- [ ] 完善 `CHANGELOG.md [3.1.0]`
- [ ] 最终验证：`cargo check` / `cargo test` / `cargo clippy`
- [ ] 提交并创建 PR：`chore: stabilize Rust 1.97.0 support`

### 2026-07-10 ~ 2026-07-11 — 发布后稳定化

- [ ] 合并发布日 PR
- [ ] 归档发布日清单到 `archive/project_reports/`
- [ ] 全 workspace 最终回归
- [ ] 更新 `.kimi/EXECUTION_CHECKLIST_2026_06_26_CONFIRMED.md` 状态

---

## 阻塞项与 Fallback

| 风险 | 触发条件 | Fallback 动作 |
|---|---|---|
| Rust 1.97.0 延迟发布 | 07-09 仍无 1.97.0 | 顺延全部发布日任务；保持 nightly 工具链 |
| `VecDeque::truncate_front` 未稳定 | Release Notes 未包含 | 保留等效实现，标注 1.98 |
| `VecDeque::retain_back` 未稳定 | Release Notes 未包含 | 保留等效实现，标注 1.98 |
| 某 API 签名与预期不同 | 编译失败 | 按实际签名重写，不直接取消注释 |

---

*本排期基于 2026-06-28 状态生成，随上游发布动态调整。*
