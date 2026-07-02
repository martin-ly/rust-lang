# Rust 1.97.0 发布日清单预检报告

> **预检时间**: 2026-06-25
> **目标发布日**: 2026-07-09
> **工具链状态**: stable 1.96.0 / nightly 1.98.0

## 预检结论

- **Rust 1.97.0 stable 尚未发布**，当前 `rustup` 上 1.97 最新为 **beta.4**。
- 因此发布日清单中的工具链切换、代码激活、全 workspace 验证等阶段 **无法在 2026-06-25 完成**。
- 所有前置准备工作已就绪，可在 2026-07-09 发布日当天立即执行。

## 环境确认

| 检查项 | 命令/来源 | 结果 |
|:---|:---|:---|
| 当前默认 toolchain | `rustup toolchain list` | nightly 1.98.0（默认） |
| stable 版本 | `rustup check` | 1.96.0（up to date） |
| beta 版本 | `rustup check` | 1.97.0-beta.4 |
| 1.97.0 stable 可用性 | `rustup check` / releases.rs | **未发布** |
| 网络访问 | `rustup check` | 正常 |

## 已就绪的前置工作

- [x] `.kimi/EXECUTION_RUST_1_97_RELEASE_2026_07_09.md` 已存在并包含完整检查项。
- [x] `CHANGELOG.md` 顶部已预置 `[3.1.0]` 模板。
- [x] `concept/07_future/rust_1_97_preview.md` 已覆盖 1.97 候选特性。
- [x] `crates/c08_algorithms/src/rust_197_features.rs` 已包含等效实现与占位注释。
- [x] `concept/00_meta/terminology_glossary.md` 已包含 1.97 术语区。
- [x] `exercises/` 已具备 L3 生态对齐测验，待 1.97 发布后补充特性测验。

## 待 2026-07-09 执行的关键步骤

1. 确认 `Rust 1.97.0` 已发布：`rustup check` 或访问 <https://releases.rs>。
2. 更新 `rust-toolchain.toml`：`channel = "1.97.0"`。
3. 激活 `crates/c08_algorithms/src/rust_197_features.rs` 中真实 API。
4. 运行 `cargo check --workspace`、`cargo test --workspace`、`cargo clippy --workspace`。
5. 更新 `concept/07_future/rust_1_97_preview.md` 状态标记。
6. 完善 `CHANGELOG.md [3.1.0]` 条目并更新 workspace version。
7. 提交并更新 `.kimi/EXECUTION_CHECKLIST_2026_06_22.md`。

## 风险

- `VecDeque::retain_back`（PR #151973）虽已 FCP → `to-announce`，仍需发布日核对 Release Notes；若未进入 1.97.0，需推迟至 1.98 并保留等效实现。
- 若 1.97.0 发布延迟，本预检报告将按实际发布日更新。
