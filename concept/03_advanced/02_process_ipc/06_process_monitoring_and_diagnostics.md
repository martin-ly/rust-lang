> **EN**: Process Monitoring and Diagnostics in Rust
> **Summary**: Monitoring process status, resource usage, logging, and diagnostic techniques for Rust child processes.
> **Rust Version**: 1.96.1+

# Rust 进程监控与诊断

> **权威页地位**：本页为 Rust 进程监控与诊断概念的 canonical 解释来源。
> **L2 向下引用**: 进程监控实现建立在 [Trait 系统](../../02_intermediate/00_traits/01_traits.md)、[L2 错误处理](../../02_intermediate/03_error_handling/04_error_handling.md) 与 [并发模型](../00_concurrency/01_concurrency.md) 之上。

## 1. 概念定义

**进程监控与诊断 (Process Monitoring and Diagnostics)** 是跟踪子进程状态、资源使用、输出日志并据此定位问题的技术集合，服务于开发调试、生产运维和性能分析。

核心关注点：

- **状态监控**：进程是否存活，以及运行、停止、僵尸等状态。
- **资源监控**：CPU、内存、I/O 使用量。
- **日志与跟踪**：stdout/stderr 捕获、结构化日志。
- **诊断工具**：持久化记录、告警、自动化恢复。

## 2. 状态监控

### 2.1 存活检查

跨平台存活检查通常利用信号 0（Unix）或进程枚举（Windows）。下面的 `nix` 示例仅在 Unix 平台生效：

```rust,ignore
#[cfg(unix)]
fn is_alive(pid: u32) -> bool {
    use nix::sys::signal::{kill, Signal};
    use nix::unistd::Pid;
    kill(Pid::from_raw(pid as i32), Signal::from_c_int(0).unwrap()).is_ok()
}
```

### 2.2 非阻塞轮询

使用 `std::process::Child::try_wait()` 可以在不阻塞当前线程的情况下更新进程状态，避免子进程变僵尸：

```rust,editable
use std::collections::HashMap;
use std::process::{Child, Command, Stdio};
use std::thread;
use std::time::{Duration, Instant};

struct MonitoredProcess {
    child: Child,
    started_at: Instant,
}

struct ProcessMonitor {
    processes: HashMap<u32, MonitoredProcess>,
}

impl ProcessMonitor {
    fn spawn(&mut self, program: &str, args: &[&str]) -> std::io::Result<u32> {
        let child = Command::new(program)
            .args(args)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()?;
        let pid = child.id();
        self.processes.insert(pid, MonitoredProcess {
            child,
            started_at: Instant::now(),
        });
        Ok(pid)
    }

    fn poll_all(&mut self) {
        let pids: Vec<u32> = self.processes.keys().copied().collect();
        for pid in pids {
            if let Some(mp) = self.processes.get_mut(&pid) {
                match mp.child.try_wait() {
                    Ok(Some(status)) => {
                        println!("[{}] exited with {}", pid, status);
                        self.processes.remove(&pid);
                    }
                    Ok(None) => {}
                    Err(e) => eprintln!("[{}] wait error: {}", pid, e),
                }
            }
        }
    }

    fn is_alive(&self, pid: u32) -> bool {
        self.processes.contains_key(&pid)
    }
}

fn main() -> std::io::Result<()> {
    let mut monitor = ProcessMonitor { processes: HashMap::new() };
    let pid = monitor.spawn("sleep", &["2"])?;
    println!("spawned {}", pid);
    for _ in 0..10 {
        monitor.poll_all();
        if !monitor.is_alive(pid) {
            break;
        }
        thread::sleep(Duration::from_millis(500));
    }
    Ok(())
}
```

### 2.3 状态机

| 状态 | 含义 | 检测方式 |
| :--- | :--- | :--- |
| Running | 正在运行 | `try_wait()` 返回 `Ok(None)` |
| Stopped | 被信号暂停 | Unix `/proc/[pid]/stat` |
| Zombie | 已退出但未被回收 | `/proc/[pid]/stat` 状态为 `Z` |
| Unknown | 不可识别 | 其他情况 |

### 2.4 批量监控

维护 `HashMap<u32, Child>` 的进程管理器，定期调用 `try_wait()` 更新状态并清理已退出进程，避免僵尸进程。

## 3. 资源监控

### 3.1 使用 `sysinfo`

`sysinfo` crate 提供跨平台进程与系统信息查询，是资源监控的常用选择：

```rust,ignore
use sysinfo::{System, SystemExt, ProcessExt};

fn print_top_memory_processes() {
    let mut sys = System::new_all();
    sys.refresh_all();
    let mut procs: Vec<_> = sys.processes().values().collect();
    procs.sort_by(|a, b| b.memory().cmp(&a.memory()));
    for p in procs.iter().take(5) {
        println!("{} pid={} mem={} KB", p.name(), p.pid(), p.memory() / 1024);
    }
}
```

### 3.2 Linux `/proc` 解析

在没有 `sysinfo` 的环境中，可以直接读取 `/proc/[pid]/stat` 获取 CPU 时间、RSS 等数据：

```rust,ignore
use std::fs;

fn read_proc_stat(pid: u32) -> Option<String> {
    fs::read_to_string(format!("/proc/{}/stat", pid)).ok()
}
```

### 3.3 I/O 监控

对管道进行带计数的流式读取，统计字节数与事件次数。结合 `BufReader` 与自定义 `Read` 包装器即可实现。

## 4. 日志与调试

- **stdout/stderr 捕获**：通过 `Stdio::piped()` 与 `BufReader` 流式读取。
- **结构化日志**：使用 `tracing` 等框架将进程事件、PID、退出码、资源使用一并输出。
- **调试技巧**：为每个子进程分配唯一 ID，记录启动参数、环境变量、超时配置。

```rust,ignore
use tracing::{info, warn};
use std::process::Stdio;
use tokio::process::Command;

async fn traced_command(program: &str, args: &[&str]) -> std::io::Result<()> {
    let output = Command::new(program)
        .args(args)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .await?;
    if output.status.success() {
        info!(target: "process", program, "stdout" = ?String::from_utf8_lossy(&output.stdout));
    } else {
        warn!(target: "process", program, "stderr" = ?String::from_utf8_lossy(&output.stderr));
    }
    Ok(())
}
```

## 5. 告警与自动恢复

当资源使用超过阈值时，监控系统可以自动发送告警或触发重启策略：

| 指标 | 阈值示例 | 动作 |
| :--- | :--- | :--- |
| CPU | 80% 持续 60s | 记录 + 告警 |
| 内存 | 500MB | 触发优雅终止 |
| 运行时长 | 超过最大允许时间 | 强制 kill |
| 退出码非 0 | 连续 3 次 | 指数退避重启 |

## 6. 诊断决策流程

```mermaid
flowchart TD
    A["发现进程异常"] --> B{"是否能获取 PID?"}
    B -->|是| C["读取 /proc/<pid> 或 sysinfo"]
    B -->|否| D["扫描进程列表匹配命令名"]
    C --> E{"资源是否超限?"}
    E -->|是| F["触发告警 / 终止"]
    E -->|否| G["记录时序并等待下次采样"]
    D --> H["日志关联分析"]
```

## 7. 最佳实践

- 定期检查 `Child::try_wait()`，及时回收子进程。
- 监控文件描述符数量，防止泄漏。
- 对监控数据设置采样间隔，避免高频轮询带来的开销。
- 将监控事件持久化到日志或时序数据库，便于回溯。
- 在异步运行时中优先使用 `tokio::process` + `tokio::time::interval` 做轮询。

## 8. 相关概念

- [进程模型与生命周期](01_process_model_and_lifecycle.md)
- [高级进程管理](02_advanced_process_management.md)
- [异步进程管理](03_async_process_management.md)
- [IPC 机制](05_ipc_mechanisms.md)
- [Rust 性能工程](08_process_performance_engineering.md)

---

> **权威来源**: [Rust Standard Library — std::process](https://doc.rust-lang.org/std/process/) · [sysinfo crate](https://docs.rs/sysinfo/) · [procfs crate](https://docs.rs/procfs/) · [tracing crate](https://docs.rs/tracing/)
