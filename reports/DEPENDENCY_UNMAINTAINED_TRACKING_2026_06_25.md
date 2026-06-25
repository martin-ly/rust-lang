# 上游 Unmaintained 依赖跟踪矩阵

> **生成时间**: 2026-06-25  
> **最后复核**: 2026-06-25  
> **工具**: `cargo audit` 0.22.1（本地 advisory-db）  
> **跟踪周期**: 每周 `cargo audit` 时复核

## 当前状态

| Crate | Advisory | 最新 crates.io 版本 | 来源路径 | 解除条件 | 状态 |
|:---|:---|:---|:---|:---|:---|
| `bare-metal` | RUSTSEC-2026-0110 | 0.2.5 | `cortex-m` 0.7.7 → `c13_embedded` | `cortex-m` 发布 0.8 并移除 `bare-metal` | ⏸️ 等待上游 |
| `instant` | RUSTSEC-2024-0384 | 0.1.13 | `glommio` 0.9.0 → `futures-lite` 1.13.0 → `c06_async` | `glommio` 升级至 `futures-lite` 2.x 或迁移到 `tokio-uring` | ⏸️ 等待上游 |
| `paste` | RUSTSEC-2024-0436 | 1.0.15 | `candle-core` 0.10.2 / `libp2p` 0.56.0 → `gemm-*` 等 | `candle-core` 或 `libp2p` 迁移出 `paste` | ⏸️ 等待上游 |

> `atomic-polyfill` (RUSTSEC-2023-0089) 已修复：2026-06-25 移除 `c10_networks` 的 `postcard` dev-dependency。

## 2026-06-25 复核结果

- 运行 `cargo update`：**0 个包可升级**（已锁定到最新兼容版本）。
- 运行 `cargo audit`：**0 安全漏洞**；3 个 `unmaintained` 警告仍通过 `.cargo/audit.toml` 忽略。
- `cargo search` 确认：
  - `cortex-m` 仍为 `0.7.7`
  - `glommio` 仍为 `0.9.0`
  - `candle-core` 仍为 `0.10.2`
  - `libp2p` 仍为 `0.56.0`

## 上游生态动态

| 项目 | 动态 | 影响 |
|:---|:---|:---|
| `cortex-m` | <https://github.com/rust-embedded/cortex-m>，截至复核日无 0.8 发布或 `bare-metal` 移除的公开 PR | 无变化 |
| `glommio` | `instant` 作者推荐迁移到 [`web-time`](https://crates.io/crates/web-time)；`glommio` 尚未发布依赖 `futures-lite` 2.x 的新版本 | 无变化 |
| `candle` | 社区讨论 `paste` 替代方案（如 [`pastey`](https://crates.io/crates/pastey)），但 `candle-core` 官方尚未移除 `paste` | 无变化 |
| `rust-libp2p` | 存在 `paste` 清理讨论（参考 Servo、uniffi-rs 等下游 issue），但 `libp2p` 0.56.0 仍依赖 `paste` | 无变化 |

## 检查命令

```bash
# 本地 advisory-db 兜底
cargo audit --db "D:\_program\cargo\advisory-db" --file Cargo.lock

# 查看最新版本
cargo search cortex-m --limit 1
cargo search glommio --limit 1
cargo search candle-core --limit 1
cargo search libp2p --limit 1
```

## 可行但暂不执行的缓解方案

| 方案 | 风险/代价 | 决策 |
|:---|:---|:---|
| 用 `[patch.crates-io]` 将 `paste` 替换为 `pastey` | `pastey` 与 `paste` 并非 100% API 一致，可能影响 `gemm`/`candle`/`libp2p` 深层宏；需大量测试 | 暂不执行，等待上游 |
| 从 `c06_async` 移除 `glommio`，改用 `tokio-uring` | 会损失 `glommio` 相关的 io_uring 教学内容 | 暂不执行，等待上游 |
| 升级 `cortex-m` 到 0.8（若发布） | 需验证嵌入式 target 兼容性 | 待发布后立即评估 |

## 解除流程

1. 当上游发布新版本并移除对应 unmaintained crate 后，运行 `cargo update -p <上游crate>`。
2. 重新运行 `cargo audit` 确认警告消失。
3. 从 `.cargo/audit.toml` 的 `ignore` 列表中移除对应 Advisory ID。
4. 更新本跟踪矩阵，标记状态为 ✅ 已解除。
