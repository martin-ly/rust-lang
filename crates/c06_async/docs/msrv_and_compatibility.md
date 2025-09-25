# MSRV 与兼容性指南（Rust 1.90）

## 0. 目录（严格编号）

1. 目标与范围
2. MSRV 定义与本仓说明
3. 依赖与特性开关
4. Tokio/Smol 兼容性要点
5. 构建/运行/测试矩阵建议
6. 已知问题与规避

## 1. 目标与范围

本指南明确本仓基线 Rust 版本（MSRV）与主要依赖的兼容性注意事项，帮助在 CI/CD 与多环境部署中稳定构建与运行。

## 2. MSRV 定义与本仓说明

- MSRV（Minimum Supported Rust Version）：本仓 `Cargo.toml` 指定 `rust-version = "1.90"`。
- 若需在 1.89 构建：部分示例可兼容，但不保证所有功能（建议使用 1.90）。

## 3. 依赖与特性开关

- Tokio：1.x；建议启用按需 feature，避免 `full` 导致二进制膨胀。
- tracing / tracing-subscriber：保持与 Tokio 生态兼容的稳定版本。
- sqlx：使用 `runtime-tokio-rustls` + 具体数据库（示例为 `sqlite`）。生产中建议外置数据库与迁移管理。
- Smol 生态：`async-io`、`async-channel`、`futures-lite`、`surf` 等，注意与 Tokio 类型隔离。

## 4. Tokio/Smol 兼容性要点

- 避免在同一进程混用不同运行时的 I/O 类型；如确需混合，采用进程边界/微服务分拆或明确适配层。
- 同步阻塞 I/O 使用 `spawn_blocking`（Tokio）或线程池封装，避免阻塞调度器线程。

## 5. 构建/运行/测试矩阵建议

- 最低版本：Rust 1.90，目标 `x86_64-pc-windows-msvc`/`x86_64-unknown-linux-gnu`。
- CI：`cargo check` + `cargo test` + `cargo bench --no-run`；对示例/基准分操作系统抽样运行。

## 6. 已知问题与规避

- 大量无界并发任务会导致内存抖动：使用信号量/有界通道与 `buffer_unordered(N)`。
- 取消与超时不等于回滚：针对副作用设计幂等与补偿逻辑。
