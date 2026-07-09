> **EN**: Process Monitoring and Diagnostics in Rust
> **Summary**: Monitoring process status, resource usage, logging, and diagnostic techniques for Rust child processes.

# Rust 进程监控与诊断

> **权威页地位**：本页为 Rust 进程监控与诊断概念的 canonical 解释来源。

## 1. 概念定义

**进程监控与诊断 (Process Monitoring and Diagnostics)** 是跟踪子进程状态、资源使用、输出日志并据此定位问题的技术集合，服务于开发调试、生产运维和性能分析。

核心关注点：

- **状态监控**：进程是否存活，以及运行、停止、僵尸等状态。
- **资源监控**：CPU、内存、I/O 使用量。
- **日志与跟踪**：stdout/stderr 捕获、结构化日志。
- **诊断工具**：持久化记录、告警、自动化恢复。

## 2. 状态监控

### 2.1 存活检查

跨平台存活检查通常利用信号 0（Unix）或进程枚举（Windows）。

```rust
fn is_alive(pid: u32) -> bool {
    #[cfg(unix)]
    {
        use nix::sys::signal::{kill, Signal};
        use nix::unistd::Pid;
        kill(Pid::from_raw(pid as i32), Signal::from_c_int(0).unwrap()).is_ok()
    }
    #[cfg(windows)]
    {
        // 通过 OpenProcess 或 tasklist 等机制实现
        unimplemented!()
    }
}
```

### 2.2 状态机

| 状态 | 含义 | 检测方式 |
| :--- | :--- | :--- |
| Running | 正在运行 | `try_wait()` 返回 `Ok(None)` |
| Stopped | 被信号暂停 | Unix `/proc/[pid]/stat` |
| Zombie | 已退出但未被回收 | `/proc/[pid]/stat` 状态为 `Z` |
| Unknown | 不可识别 | 其他情况 |

### 2.3 批量监控

维护 `HashMap<u32, Child>` 的进程管理器，定期调用 `try_wait()` 更新状态并清理已退出进程，避免僵尸进程。

## 3. 资源监控

### 3.1 CPU 与内存

使用 `sysinfo` 等 crate 获取进程级 CPU 和内存使用，设置阈值后触发告警或终止。

### 3.2 跨平台资源监控

- **Linux**：`/proc/[pid]/stat`、`cgroups v2`。
- **Windows**：WMI、`windows` crate。
- **macOS**：`libproc` 或 `sysinfo`。

### 3.3 I/O 监控

对管道进行带计数的流式读取，统计字节数与事件次数。

## 4. 日志与调试

- **stdout/stderr 捕获**：通过 `Stdio::piped()` 与 `BufReader` 流式读取。
- **结构化日志**：使用 `tracing` 等框架将进程事件、PID、退出码、资源使用一并输出。
- **调试技巧**：为每个子进程分配唯一 ID，记录启动参数、环境变量、超时配置。

## 5. 最佳实践

- 定期检查 `Child::try_wait()`，及时回收子进程。
- 监控文件描述符数量，防止泄漏。
- 对监控数据设置采样间隔，避免高频轮询带来的开销。
- 将监控事件持久化到日志或时序数据库，便于回溯。

## 6. 相关概念

- [进程模型与生命周期](01_process_model_and_lifecycle.md)
- [高级进程管理](02_advanced_process_management.md)
- [异步进程管理](03_async_process_management.md)
- [IPC 机制](05_ipc_mechanisms.md)

---

> **权威来源**: [Rust Standard Library — std::process](https://doc.rust-lang.org/std/process/) · [sysinfo crate](https://docs.rs/sysinfo/) · [procfs crate](https://docs.rs/procfs/)
