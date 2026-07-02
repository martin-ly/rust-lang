# Rust 1.97.0 发布日人工决策清单

> **用途**: 2026-07-09 发布日当天，根据官方 Release Notes、探测脚本输出和本清单逐项判断后执行。
> **前置输入**:
> - 官方 Release Notes: <https://blog.rust-lang.org/2026/07/09/Rust-1.97.0.html>
> - 探测脚本: `scripts/probe_rust_197_apis.rs`
> - 激活指南: `.kimi/RUST_197_API_ACTIVATION_GUIDE.md`
> - 执行清单: `.kimi/EXECUTION_RUST_1_97_RELEASE_2026_07_09.md`

---

## 1. 工具链决策

| # | 决策项 | 默认选择 | 触发条件 | 备选方案 |
|---:|---|---|---|---|
| 1.1 | workspace 工具链 | 保持 `nightly` | 因 `gen_blocks`、`never_type`、`core_intrinsics` 等 nightly feature gates 在 crate 根使用 | 若未来所有 crate 移除 nightly gates，可整体切到 `1.97.0` stable |
| 1.2 | 单独验证 1.97.0 stable | 不执行 | 某个 crate 已移除 nightly gates 且希望验证 | 对该 crate 临时切到 `1.97.0` 运行 `cargo check` |

---

## 2. API 激活决策

**原则**: 仅当 Release Notes 明确列出某 API 已稳定，才取消注释真实调用并删除等效实现。

| # | API | 当前判断（2026-06-28） | 发布日动作 | 若未进入 1.97.0 |
|---:|---|---|---|---|
| 2.1 | `NonZero` bit ops (`highest_one` / `lowest_one` / `bit_width`) | 9 成概率进 1.97 | Release Notes 确认后激活 | 保留 fallback |
| 2.2 | `const char::is_control` | 9 成概率进 1.97 | Release Notes 确认后激活 | 保留 fallback |
| 2.3 | `NonZeroU32::midpoint` / `isqrt` | 9 成概率进 1.97 | Release Notes 确认后激活 | 保留 fallback |
| 2.4 | `ptr::fn_addr_eq` | 9 成概率进 1.97 | Release Notes 确认后激活 | 保留 fallback |
| 2.5 | `const size_of_val` / `align_of_val` | 9 成概率进 1.97 | Release Notes 确认后激活 | 保留 fallback |
| 2.6 | `BuildHasherDefault::new` const | 9 成概率进 1.97 | Release Notes 确认后激活 | 保留 fallback |
| 2.7 | `Box::as_ptr` / `Box::as_mut_ptr` | 不确定（beta cutoff 2026-05-22） | Release Notes 确认后激活 | 保留 fallback，标注 1.98 |
| 2.8 | `int::format_into` | 不确定（beta cutoff 2026-05-22） | Release Notes 确认后激活 | 保留 fallback，标注 1.98 |
| 2.9 | `VecDeque::truncate_front` | 低概率进 1.97 | 若 Release Notes 包含则激活 | 保留 fallback，标注 1.98 |
| 2.10 | `VecDeque::retain_back` | 极低概率（方法在 nightly 不存在） | 若 Release Notes 包含则激活 | 保留 fallback，标注 1.98+ |
| 2.11 | `Box::into_non_null` / `Vec::into_non_null` | 低概率 | 若 Release Notes 包含则激活 | 保留 fallback，标注 1.98+ |

---

## 3. 文档决策

| # | 决策项 | 默认选择 | 触发条件 | 备选方案 |
|---:|---|---|---|---|
| 3.1 | `concept/07_future/rust_1_97_preview.md` | 保留并顶部添加重定向 | 稳定特性已迁移到 `docs/06_toolchain/06_21_rust_1_97_features.md` | 若不迁移，仅更新状态标记 |
| 3.2 | 新建 `docs/06_toolchain/06_21_rust_1_97_features.md` | 执行 | 发布日有已稳定特性需要记录 | 若 1.97 无任何新稳定特性（极端情况），删除模板或改写为 "无新增" |
| 3.3 | 术语表更新 | 将已稳定术语状态改为 ✅ | 对应 API 已确认稳定 | 未稳定的保持候选或推迟状态 |
| 3.4 | `CHANGELOG.md [3.1.0]` | 根据实际稳定特性完善条目 | 任意 1.97 API 激活 | 若大量特性推迟，更新为 "1.97 仅少量 API 稳定" |

---

## 4. 练习与测试决策

| # | 决策项 | 默认选择 | 触发条件 | 备选方案 |
|---:|---|---|---|---|
| 4.1 | `exercises/tests/l3_rust_197_alignment.rs` | 已覆盖 13 个测验，真实 API 调用在 nightly 上通过 | 发布日激活真实 API 后，删除等效 helper | 若 API 未稳定，保留 helper |
| 4.2 | 新增 1.97 特性测验 | 不新增 | 若 Release Notes 出现未覆盖的新 API | 在 `l3_rust_197_alignment.rs` 中补充 |

---

## 5. 发布与归档决策

| # | 决策项 | 默认选择 | 触发条件 | 备选方案 |
|---:|---|---|---|---|
| 5.1 | 提交信息 | `chore: stabilize Rust 1.97.0 support` | 发布日执行完成 | 根据实际变更调整 scope |
| 5.2 | PR 还是直接合并 | 按仓库流程创建 PR | 需要 review | 若流程允许，直接合并 |
| 5.3 | 执行清单归档 | 移动到 `archive/project_reports/` | 发布日 PR 合并后 | 保留在 `.kimi/` 不移动 |

---

## 6. 风险快速检查表

| 现象 | 应对措施 |
|:---|:---|
| 某特性未进入 1.97（含 `retain_back`） | 保持等效实现；更新 `rust_197_features.rs`、术语表、`CHANGELOG.md` 状态为 "推迟至 1.98" |
| 稳定 API 签名与 nightly 不同 | 不要直接取消注释，按实际签名重写 |
| Windows 构建失败（`aws-lc-rs`/`ring`/`wpcap.lib`） | 检查是否需要 `--no-default-features` 或本地安装 Npcap SDK |
| 测试超时或不稳定 | 单独运行失败测试，排除网络/文件系统依赖 |

---

*本清单生成于 2026-06-28，随探测结果和执行清单同步更新。*
