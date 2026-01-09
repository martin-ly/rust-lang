# 工程基线与质量门禁（Rust 1.89）


## 📊 目录

- [工程基线与质量门禁（Rust 1.89）](#工程基线与质量门禁rust-189)
  - [📊 目录](#-目录)
  - [基线要求](#基线要求)
  - [CI 工作流](#ci-工作流)
  - [度量与阈值（首版）](#度量与阈值首版)
  - [本地开发约定](#本地开发约定)
  - [后续扩展](#后续扩展)


本文定义 workspace 统一工程基线：MSRV=1.89、格式与静态检查、测试与覆盖率、安全与合规、依赖整洁度、性能基准与并发正确性抽样验证。

## 基线要求

- MSRV 与 Edition：rust-version=1.89，edition=2024
- rustfmt：全仓 `cargo fmt --all -- --check`
- clippy：`cargo clippy --all-targets -- -D warnings`（可在仓库根定义豁免清单）
- 测试：`cargo nextest run --workspace`，失败即时输出
- 覆盖率：`cargo llvm-cov --workspace`，产出 lcov
- 安全：`cargo-audit`（RustSec）、`cargo-deny`（licenses/bans/sources）
- 依赖整洁：`cargo-udeps --workspace`

## CI 工作流

见 `.github/workflows/ci.yml`，覆盖 fmt/clippy/test/coverage/audit/deny/udeps。CI 使用稳定工具链 1.89 进行验证。

## 度量与阈值（首版）

- 覆盖率：行覆盖≥60%（首版建议值，可逐步提升）
- Clippy：零 warning（如需例外，建立最小例外白名单）
- Audit：禁止高危与关键告警
- Licenses：仅允许宽松许可证（见 `deny.toml`）

## 本地开发约定

- `rustup toolchain install 1.89.0`
- `cargo fmt --all`、`cargo clippy`、`cargo nextest run` 常规三件套
- 变更涉及公共 API 时补充文档与 doctest

## 后续扩展

- 性能回归：Criterion 基线与趋势跟踪
- 并发正确性：Miri/Loom 对关键 crate 抽样
- 覆盖率门槛与失败策略随阶段迭代
