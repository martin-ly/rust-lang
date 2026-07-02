# Rust 1.97.0 发布后稳定化清单

> **执行日期**: 2026-07-10 ~ 2026-07-11
> **目标**: 完成 1.97 发布日后的收尾、归档与回归验证
> **前置条件**: 2026-07-09 发布日 PR 已合并
> **对应清单**: `.kimi/EXECUTION_RUST_1_97_RELEASE_2026_07_09.md`

---

## 阶段 1：最终回归验证

> 所有验证均在 nightly 工具链上执行（workspace 依赖 nightly feature gates）。

- [ ] `cargo check --workspace`
- [ ] `cargo test --workspace`
- [ ] `cargo clippy --workspace --all-features -- -D warnings`
- [ ] `cargo audit --no-fetch`（检查是否有 1.97 相关安全通告）

## 阶段 2：文档收尾

- [ ] 确认 `concept/07_future/rust_1_97_preview.md` 已添加稳定化声明和重定向
- [ ] 确认 `docs/06_toolchain/06_21_rust_1_97_features.md` 已迁移完成
- [ ] 确认 `concept/00_meta/terminology_glossary.md` 中 1.97 术语状态已更新
- [ ] 搜索全仓库 `1.97` / `nightly` / `PFCP` 标记，统一刷新

## 阶段 3：CHANGELOG 与版本

- [ ] 最终回填 `CHANGELOG.md [3.1.0]` 实际条目
- [ ] 确认根 `Cargo.toml [workspace.package] version = "3.1.0"`
- [ ] 若 1.97 特性数量或影响超出预期，评估是否需要提升版本号

## 阶段 4：练习与测试

- [ ] 确认 `exercises/tests/l3_rust_197_alignment.rs` 已按实际稳定 API 更新
- [ ] 确认新增 1.97 特性测验已合并
- [ ] 运行 `cd exercises && cargo test`

## 阶段 5：归档与跟踪

- [ ] 将 `.kimi/EXECUTION_RUST_1_97_RELEASE_2026_07_09.md` 归档到 `archive/project_reports/`
- [ ] 将 `.kimi/RUST_197_RELEASE_COUNTDOWN_2026_06_28.md` 归档
- [ ] 将 `.kimi/RUST_197_RELEASE_PREFLIGHT_2026_07_08.md` 归档
- [ ] 将 `.kimi/RUST_197_API_ACTIVATION_GUIDE.md` 归档
- [ ] 更新 `.kimi/EXECUTION_CHECKLIST_2026_06_26_CONFIRMED.md` 中工作流 C 状态为完成

## 阶段 6：风险后验

| 假设 | 实际 | 处理 |
|---|---|---|
| `VecDeque::truncate_front` 进入 1.97 | 待确认 | 若未进，保留等效实现并更新注释为 1.98 |
| `VecDeque::retain_back` 进入 1.97 | 当前 nightly 方法不存在，大概率推迟 | 若未进，更新注释为 1.98+ |
| `Box::as_ptr` / `int::format_into` 进入 1.97 | nightly 可用，需核对 beta cutoff | 若未进，保留等效实现并标注 1.98 |
| 1.97.0 按时发布 | 待确认 | 若延迟，保持 nightly 工具链 |

---

*本清单应在 2026-07-09 发布日 PR 合并后立即执行。*
