# Rust 1.97.0 发布日前一天预检清单

> **预检日期**: 2026-07-08
> **目标发布日**: 2026-07-09
> **目标版本**: Rust 1.97.0
> **对应总计划**: `.kimi/EXECUTION_RUST_1_97_RELEASE_2026_07_09.md`
> **倒计时排期**: `.kimi/RUST_197_RELEASE_COUNTDOWN_2026_06_28.md`

---

## 环境预检

- [ ] 确认 `rustup` 可正常访问官方源：`rustup check`
- [ ] 确认本机能下载 1.97.0（若已提前发布可提前安装）：`rustup toolchain install 1.97.0 --profile default`
- [ ] 确认当前工作树干净：`git status --short` 无未提交变更

## 代码预检

- [ ] `rust-toolchain.toml` 当前为 `channel = "nightly"`（发布日再切换）
- [ ] `crates/c08_algorithms/src/rust_197_features.rs` 中 fallback 实现完整
- [ ] 全 workspace 编译通过：`cargo check --workspace`
- [ ] 全 workspace 测试通过：`cargo test --workspace`
- [ ] Clippy 无警告：`cargo clippy --workspace --all-features -- -D warnings`

## 文档预检

- [ ] `concept/07_future/rust_1_97_preview.md` 已准备刷新
- [ ] `docs/06_toolchain/06_21_rust_1_97_features.md` 迁移目标目录已存在
- [ ] `CHANGELOG.md [3.1.0]` 已准备完善
- [ ] `concept/00_meta/terminology_glossary.md` 中 1.97 相关术语已定位

## 脚本预检

- [ ] `scripts/probe_rust_197_apis.rs` 可编译运行（当前 nightly 下会报告部分 API 未稳定，属正常）
- [ ] `scripts/rust_197_release_day.sh` 语法检查通过：`bash -n scripts/rust_197_release_day.sh`

## 发布日工作分支

- [ ] 已创建或准备创建分支：`git checkout -b rust-1.97-release-day`

## 风险快速确认

| 风险 | 检查命令/来源 | 当前状态 |
|---|---|---|
| 1.97.0 延迟发布 | `rustup check` / <https://releases.rs> | 待 07-09 确认 |
| `VecDeque::truncate_front` 未稳定 | Release Notes + 探测脚本 | 待 07-09 确认 |
| `VecDeque::retain_back` 未稳定 | Release Notes + 探测脚本 | 待 07-09 确认 |

---

*本清单应在 2026-07-08 完成，为 2026-07-09 发布日执行做准备。*
