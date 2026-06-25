# 上游 Unmaintained 依赖跟踪矩阵

> **生成时间**: 2026-06-25  
> **工具**: `cargo audit` 0.22.1（本地 advisory-db）  
> **跟踪周期**: 每周 `cargo audit` 时复核

## 当前状态

| Crate | Advisory | 最新 crates.io 版本 | 来源路径 | 解除条件 | 状态 |
|:---|:---|:---|:---|:---|:---|
| `bare-metal` | RUSTSEC-2026-0110 | 0.2.5 | `cortex-m` 0.7.7 → `c13_embedded` | `cortex-m` 发布 0.8 并移除 `bare-metal` | ⏸️ 等待上游 |
| `instant` | RUSTSEC-2024-0384 | 0.1.13 | `glommio` 0.9.0 → `futures-lite` 1.13.0 → `c06_async` | `glommio` 升级至 `futures-lite` 2.x | ⏸️ 等待上游 |
| `paste` | RUSTSEC-2024-0436 | 1.0.15 | `candle-core` 0.10.2 / `libp2p` 0.56.0 → `gemm-*` 等 | `candle-core` 或 `libp2p` 迁移出 `paste` | ⏸️ 等待上游 |

> `atomic-polyfill` (RUSTSEC-2023-0089) 已修复：2026-06-25 移除 `c10_networks` 的 `postcard` dev-dependency。

## 上游跟踪链接

| 项目 | 相关 Issue / PR | 说明 |
|:---|:---|:---|
| `cortex-m` | <https://github.com/rust-embedded/cortex-m> | 关注 0.8 里程碑与 `bare-metal` 替换方案 |
| `glommio` | <https://github.com/DataDog/glommio> | 关注 `futures-lite` 升级或 `instant` 替代 |
| `candle` | <https://github.com/huggingface/candle> | 关注 `paste` 移除或替换为 `seq-macro` 等 |
| `rust-libp2p` | <https://github.com/libp2p/rust-libp2p> | 关注依赖树中 `paste` 的清理 |

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

## 解除流程

1. 当上游发布新版本并移除对应 unmaintained crate 后，运行 `cargo update -p <上游crate>`。
2. 重新运行 `cargo audit` 确认警告消失。
3. 从 `.cargo/audit.toml` 的 `ignore` 列表中移除对应 Advisory ID。
4. 更新本跟踪矩阵，标记状态为 ✅ 已解除。
