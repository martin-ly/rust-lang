# 供应链安全审计报告

> **生成时间**: 2026-06-25
> **工具**: `cargo audit` 0.22.1（网络已恢复，可直接拉取 RustSec advisory-db）
> **Rust 版本**: 1.96.0 (Edition 2024)

## 执行结果

```bash
cargo audit
```

- **退出码**: 0
- **安全漏洞**: 0
- **允许警告**: 4（均为 `unmaintained` 提示，非安全漏洞）

## 允许警告详情

| Crate | 版本 | 类型 | ID | 影响路径 |
|:---|:---|:---|:---|:---|
| atomic-polyfill | 1.0.3 | unmaintained | RUSTSEC-2023-0089 | heapless → postcard → c10_networks |
| bare-metal | 0.2.5 | deprecated | RUSTSEC-2026-0110 | cortex-m → c13_embedded |
| instant | 0.1.13 | unmaintained | RUSTSEC-2024-0384 | fastrand → futures-lite → glommio → c06_async |
| paste | 1.0.15 | unmaintained | RUSTSEC-2024-0436 | tokenizers/pulp/netlink-packet-core/macro_rules_attribute/gemm-* → candle-core / libp2p / c08_algorithms |

> 这些警告均为上游 crate 维护状态变化，**不涉及已知可被利用的安全漏洞**。由于它们是 transitive dependencies，当前 workspace 无法直接移除，需等待上游更新。

## 与 2026-06-22 对比

- 2026-06-22：`cargo audit` 因网络/IO 错误无法运行，使用 `scripts/supply_chain_audit.py` 手动解析 RustSec advisory-db main.zip，结果 0 个安全公告。
- 2026-06-25：`cargo audit` 网络恢复，完整拉取 advisory-db 后扫描确认 0 个安全漏洞，4 个 unmaintained 警告。

## 后续建议

1. 继续每周运行 `cargo audit` 监控新公告。
2. 对 `atomic-polyfill`、`bare-metal`、`instant`、`paste` 等 transitive unmaintained crates，跟踪上游替代方案（如 `postcard` 升级 `heapless`、`glommio` 替换 `instant`、`candle`/`gemm` 替换 `paste`）。
3. Sea-ORM 2.0 stable 仍未发布，继续跟踪 `reports/SEA_ORM_2_0_RELEASE_TRACKING_2026_06_22.md`。
4. cargo-vet Windows 编译问题（LockFileEx）待上游修复，暂不启用。
