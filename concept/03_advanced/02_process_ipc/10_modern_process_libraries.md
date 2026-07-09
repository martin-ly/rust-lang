> **EN**: Modern Process Management Libraries in Rust
> **Summary**: Ecosystem survey of Rust process management libraries: std::process, tokio::process, duct, nix, sysinfo, procfs, daemonize, caps, users.

# Rust 现代进程管理库

> **权威页地位**：本页为 Rust 现代进程管理库生态的 canonical 解释来源。

## 1. 核心库对比

| 库 | 定位 | 关键特性 | 适用场景 |
| :--- | :--- | :--- | :--- |
| `std::process` | 标准库 | 同步、跨平台、零依赖 | 简单命令执行 |
| `tokio::process` | 异步运行时 | 与 Tokio 集成、异步 I/O、超时 | 高并发异步场景 |
| `duct` | 进程组合 | 链式管道、易读 API | shell-like 命令链 |
| `nix` | Unix 系统调用 | fork/exec、信号、rlimit、namespace | 需要 Unix 底层控制 |
| `sysinfo` | 系统信息 | 跨平台进程/系统监控 | 监控工具 |
| `procfs` | /proc 解析 | 详细 Linux 进程信息 | Linux 系统工具 |
| `daemonize` | 守护进程化 | 后台运行、PID 文件、权限降级 | Unix 守护进程 |
| `caps` | Linux Capabilities | 细粒度权限控制 | 安全沙箱 |
| `users` | 用户/组查询 | 解析 uid/gid、用户名 | 权限管理 |

> **注意**：`async-std` 已进入维护模式，新项目建议优先评估 Tokio 或 smol。

## 2. 选型决策树

```text
选择进程库
├── 需要异步与高并发 → tokio::process
├── 需要 shell 式管道 → duct
├── 需要 Unix 底层控制 → nix
├── 需要系统/进程监控 → sysinfo
├── 需要 Linux /proc 细节 → procfs
├── 需要守护进程化 → daemonize
└── 只需要跨平台基础 → std::process
```

## 3. 集成模式

- **Tokio + nix**：在异步框架中执行精细的 Unix 控制（信号、namespace）。
- **sysinfo + tokio**：异步轮询系统与进程指标。
- **duct + 流式处理**：利用 duct 简洁语法构建复杂管道，再用 `BufReader` 流式消费输出。

## 4. 最佳实践

- 优先使用标准库或成熟 crate，避免重复封装。
- 根据平台支持范围选择库：`nix` 仅 Unix，`sysinfo`/`duct`/`tokio` 跨平台。
- 锁定版本，避免使用通配符依赖。
- 将平台相关代码隔离在 `#[cfg]` 模块中。

## 5. 相关概念

- [进程模型与生命周期](01_process_model_and_lifecycle.md)
- [异步进程管理](03_async_process_management.md)
- [跨平台进程管理](04_cross_platform_process_management.md)
- [进程安全与沙箱](07_process_security_and_sandboxing.md)
- [核心开源库谱系](../../06_ecosystem/02_core_crates/03_core_crates.md)

---

> **权威来源**: [crates.io](https://crates.io/) · [Tokio Process](https://docs.rs/tokio/latest/tokio/process/) · [duct crate](https://docs.rs/duct/) · [nix crate](https://docs.rs/nix/) · [sysinfo crate](https://docs.rs/sysinfo/) · [procfs crate](https://docs.rs/procfs/) · [daemonize crate](https://docs.rs/daemonize/)
