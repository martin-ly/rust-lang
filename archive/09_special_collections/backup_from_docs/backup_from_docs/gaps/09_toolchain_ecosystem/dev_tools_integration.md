# 开发工具集成指南（IDE/CI/验证）

## IDE 集成

- rust-analyzer、Clippy、inlay hints、可视化 borrow 图（构想）

## CI 管道

- `cargo fmt --check`、`clippy -D warnings`、`audit`、`udeps`
- 单元/集成/属性/模糊/模型检查分层触发

## 验证集成

- Prusti/Creusot 合约；Kani 模型检查；Loom 并发探索
- 关键路径门禁：PR 必须通过最小验证集合

---

## 快速开始（IDE）

1. 安装 rust-analyzer，启用 inlay hints、proc-macro 支持
2. 启用 Clippy 严格规则：`workspace.lints = { rust = "deny(warnings)" }`
3. 自定义提示：显示生命周期省略推断、借用可视化（插件/脚本）

## GitHub Actions 最小门禁

```yaml
name: ci
on: [push, pull_request]
jobs:
  check:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@stable
      - name: fmt
        run: cargo fmt --all -- --check
      - name: clippy
        run: cargo clippy --all-targets --all-features -D warnings
      - name: audit
        run: cargo audit || true
      - name: test
        run: cargo test --all --all-features
```

## 验证/测试分层

- 单元/集成测试：`cargo test`（覆盖率基线）
- 属性测试：`proptest` 生成边界数据
- 模糊测试：`cargo fuzz` 针对解析/协议
- 并发探索：`loom` 针对关键互斥/顺序
- 模型检查：`kani` 针对状态空间小的核心算法

## VS Code/IDE 配置片段（示例）

```json
{
  "rust-analyzer.checkOnSave.command": "clippy",
  "rust-analyzer.cargo.features": "all",
  "editor.inlayHints.enabled": "on",
  "rust-analyzer.procMacro.enable": true
}
```

## Cargo 工作区 Lints（严苛模式）

```toml
[workspace.lints.rust]
unsafe_code = "forbid"
unused = "deny"
unused_imports = "deny"
dead_code = "deny"
```

## 预提交钩子（可选）

```bash
#!/usr/bin/env bash
set -euo pipefail
cargo fmt --all -- --check
cargo clippy --all-targets --all-features -D warnings
cargo test --all --all-features
cargo deny check || true
```

## Kani 最小样例

```rust
#[kani::proof]
fn sum_commutative(a: u32, b: u32) {
    let s1 = a.wrapping_add(b);
    let s2 = b.wrapping_add(a);
    assert!(s1 == s2);
}
```

## PR 模板建议

- 变更动机与范围
- 是否触达 `unsafe`/并发路径（需要 Loom/Kani）
- 回滚策略与兼容性说明

## 本地命令别名

```toml
[alias]
lint = "clippy --all-targets --all-features -D warnings"
check-sec = "audit && cargo geiger"
verify-core = "test -p core_crate && kani -p core_crate"
```

## JetBrains/CLion 最小配置（补充）

- 启用 Rust 插件与 `External Linters`（Clippy）
- 将 `Run on Save` 绑定到 `cargo clippy` 与 `cargo test -q`
- 在 `File Watchers` 中加入 `rustfmt` 自动格式化

## Windows/PowerShell 预提交（示例）

```powershell
#!/usr/bin/env pwsh
$ErrorActionPreference = 'Stop'
cargo fmt --all -- --check
cargo clippy --all-targets --all-features -D warnings
cargo test --all --all-features
cargo deny check 2>$null; if ($LASTEXITCODE -gt 1) { exit $LASTEXITCODE }
```

## 分层验证门禁（扩展说明）

- 必选：fmt/clippy/test
- 可选：`cargo audit`（允许临时豁免）、`cargo udeps`（定期运行）
- 并发/unsafe 变更：强制 Loom/Kani 作业并附带报告摘要

## PR 提交流程建议

- 必填：变更说明、影响面、回滚计划
- 勾选：是否修改不变量/并发路径；是否需要 loom/kani 运行
- 附件：性能基准对比（如有）
