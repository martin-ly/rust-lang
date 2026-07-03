# Tier 1: C07 进程管理 - 常见问题

> **文档类型**: FAQ
> **适用版本**: Rust 1.96.1+
> **最后更新**: 2025-12-11

---

## 目录

- [Tier 1: C07 进程管理 - 常见问题](#tier-1-c07-进程管理---常见问题)
  - [目录](#目录)
  - [📋 问题索引](#-问题索引)
  - [基础问题](#基础问题)
    - [Q1: 如何创建和管理子进程？](#q1-如何创建和管理子进程)
    - [Q2: 如何获取子进程的输出？](#q2-如何获取子进程的输出)
    - [Q3: 如何向子进程传递输入？](#q3-如何向子进程传递输入)
  - [IPC 通信问题](#ipc-通信问题)
    - [Q4: 进程间如何通信？最好的方式是什么？](#q4-进程间如何通信最好的方式是什么)
    - [Q5: 管道和命名管道有什么区别？](#q5-管道和命名管道有什么区别)
    - [Q6: 如何实现双向通信？](#q6-如何实现双向通信)
  - [跨平台问题](#跨平台问题)
    - [Q7: 如何实现跨平台的进程管理？](#q7-如何实现跨平台的进程管理)
    - [Q8: Windows和Unix的进程模型有什么区别？](#q8-windows和unix的进程模型有什么区别)
  - [生命周期问题](#生命周期问题)
    - [Q9: 如何避免和处理僵尸进程？](#q9-如何避免和处理僵尸进程)
    - [Q10: 如何优雅地终止子进程？](#q10-如何优雅地终止子进程)
    - [Q11: 如何处理子进程超时？](#q11-如何处理子进程超时)
  - [异步与性能问题](#异步与性能问题)
    - [Q12: 什么时候应该使用异步进程管理？](#q12-什么时候应该使用异步进程管理)
    - [Q13: 如何提高进程通信性能？](#q13-如何提高进程通信性能)
    - [Q14: 如何监控进程资源使用？](#q14-如何监控进程资源使用)
  - [错误处理问题](#错误处理问题)
    - [Q15: 如何处理进程创建失败？](#q15-如何处理进程创建失败)
    - [Q16: 如何区分进程错误类型？](#q16-如何区分进程错误类型)
  - [🔗 相关资源](#-相关资源)
  - [**适用版本**: Rust 1.96.1+](#适用版本-rust-1920)

---

## 📋 问题索引

**按类别**: [基础](#基础问题) | [IPC](#ipc-通信问题) | [跨平台](#跨平台问题) | [生命周期](#生命周期问题) | [异步性能](#异步与性能问题) | [错误处理](#错误处理问题)

---

## 基础问题

### Q1: 如何创建和管理子进程？

**A**: Rust 的 `std::process::Command` 提供了创建和管理子进程的标准方式。

**基本用法**:

```rust
use std::process::Command;

// 方法1: 等待完成并获取输出
let output = Command::new("ls")
    .arg("-la")
    .output()
    .expect("failed to execute process");

println!("status: {}", output.status);
println!("stdout: {}", String::from_utf8_lossy(&output.stdout));
println!("stderr: {}", String::from_utf8_lossy(&output.stderr));

// 方法2: 只获取退出状态
let status = Command::new("ls")
    .status()
    .expect("failed to execute");

// 方法3: 启动后立即返回
let mut child = Command::new("long_running_task")
    .spawn()
    .expect("failed to spawn");

// 稍后等待
let status = child.wait()?;
```
**核心方法对比**:

| 方法       | 阻塞 | 返回值       | 用途           |
| :--- | :--- | :--- | :--- || `output()` | 是   | `Output`     | 需要捕获输出   |
| `status()` | 是   | `ExitStatus` | 只关心退出状态 |
| `spawn()`  | 否   | `Child`      | 需要后续操作   |

**参考**: [进程管理快速入门](../tier_02_guides/01_process_management_quick_start.md)

---

### Q2: 如何获取子进程的输出？

**A**: 配置 `stdout` 和 `stderr`，然后读取输出。

**方法1: 使用 `output()`**:

```rust
let output = Command::new("echo")
    .arg("Hello")
    .output()?;

let stdout = String::from_utf8_lossy(&output.stdout);
println!("Output: {}", stdout);
```
**方法2: 使用 `Stdio::piped()`**:

```rust
use std::process::{Command, Stdio};
use std::io::Read;

let mut child = Command::new("cat")
    .arg("file.txt")
    .stdout(Stdio::piped())
    .spawn()?;

// 读取stdout
if let Some(mut stdout) = child.stdout.take() {
    let mut output = String::new();
    stdout.read_to_string(&mut output)?;
    println!("{}", output);
}

child.wait()?;
```
**方法3: 实时读取**:

```rust
use std::io::BufRead;

let mut child = Command::new("tail")
    .arg("-f")
    .arg("log.txt")
    .stdout(Stdio::piped())
    .spawn()?;

if let Some(stdout) = child.stdout.take() {
    let reader = BufReader::new(stdout);
    for line in reader.lines() {
        println!("LOG: {}", line?);
    }
}
```
---

### Q3: 如何向子进程传递输入？

**A**: 配置 `stdin` 为 `Stdio::piped()`，然后写入数据。

```rust
use std::process::{Command, Stdio};
use std::io::Write;

let mut child = Command::new("cat")
    .stdin(Stdio::piped())
    .stdout(Stdio::piped())
    .spawn()?;

// 写入数据到子进程的stdin
if let Some(mut stdin) = child.stdin.take() {
    stdin.write_all(b"Hello from parent!\n")?;
    // drop(stdin); // 关闭stdin，让cat知道输入结束
}

// 读取输出
let output = child.wait_with_output()?;
println!("{}", String::from_utf8_lossy(&output.stdout));
```
---

## IPC 通信问题

### Q4: 进程间如何通信？最好的方式是什么？

**A**: Rust 支持多种 IPC 机制，选择取决于具体需求。

**IPC 方式对比**:

| IPC 类型        | 性能 | 复杂度 | 跨网络 | 适用场景         |
| :--- | :--- | :--- | :--- | :--- || **管道**        | 中   | 低     | 否     | 父子进程简单通信 |
| **命名管道**    | 中   | 低     | 否     | 本地无亲缘进程   |
| **Unix Socket** | 高   | 中     | 否     | 本地复杂通信     |
| **TCP Socket**  | 中   | 中     | 是     | 跨网络通信       |
| **共享内存**    | 最高 | 高     | 否     | 大数据量、高性能 |
| **消息队列**    | 中   | 中     | 否     | 异步消息传递     |

**选择建议**:

- **简单场景**: 管道
- **本地高性能**: Unix Socket 或共享内存
- **跨网络**: TCP Socket
- **异步消息**: 消息队列

**示例 - 管道**:

```rust
let mut child = Command::new("cat")
    .stdin(Stdio::piped())
    .stdout(Stdio::piped())
    .spawn()?;

// 写入
if let Some(mut stdin) = child.stdin.take() {
    stdin.write_all(b"data")?;
}

// 读取
let output = child.wait_with_output()?;
```
**参考**: [IPC通信实践](../tier_02_guides/02_ipc_communication_practice.md)

---

### Q5: 管道和命名管道有什么区别？

**A**: 主要区别在于使用范围和持久性。

**匿名管道 (Pipe)**:

- 只能用于有亲缘关系的进程（父子、兄弟）
- 生命周期随进程结束
- 通过文件描述符传递

**命名管道 (Named Pipe / FIFO)**:

- 在文件系统中有路径名
- 任何进程都可以访问（有权限）
- 持久化，可重复使用
- Unix: 使用 `mkfifo()`；Windows: 使用 `CreateNamedPipe()`

**Unix 命名管道示例**:

```rust
#[cfg(unix)]
use nix::unistd::mkfifo;
use nix::sys::stat::Mode;
use std::fs::File;
use std::io::{Read, Write};

// 创建命名管道
mkfifo(Path::new("/tmp/my_pipe"), Mode::S_IRWXU)?;

// 进程A写入
let mut file = File::create("/tmp/my_pipe")?;
file.write_all(b"Hello")?;

// 进程B读取
let mut file = File::open("/tmp/my_pipe")?;
let mut buf = String::new();
file.read_to_string(&mut buf)?;
```
---

### Q6: 如何实现双向通信？

**A**: 需要创建两个管道或使用支持双向的IPC机制。

**方法1: 两个管道**:

```rust
use std::process::{Command, Stdio};
use std::io::{Read, Write};

let mut child = Command::new("python")
    .arg("-u") // unbuffered
    .arg("script.py")
    .stdin(Stdio::piped())
    .stdout(Stdio::piped())
    .spawn()?;

// 向子进程写入
if let Some(mut stdin) = child.stdin.as_mut() {
    stdin.write_all(b"input\n")?;
}

// 从子进程读取
if let Some(mut stdout) = child.stdout.as_mut() {
    let mut buf = String::new();
    stdout.read_to_string(&mut buf)?;
    println!("Output: {}", buf);
}
```
**方法2: Unix Socket**:

```rust
#[cfg(unix)]
use std::os::unix::net::{UnixStream, UnixListener};

// 服务端
let listener = UnixListener::bind("/tmp/my.sock")?;
let (mut stream, _) = listener.accept()?;

// 双向通信
stream.write_all(b"request")?;
let mut buf = [0; 1024];
let n = stream.read(&mut buf)?;

// 客户端
let mut stream = UnixStream::connect("/tmp/my.sock")?;
stream.write_all(b"response")?;
let mut buf = [0; 1024];
let n = stream.read(&mut buf)?;
```
---

## 跨平台问题

### Q7: 如何实现跨平台的进程管理？

**A**: 使用条件编译和抽象层来处理平台差异。

**核心差异**:

| 特性       | Unix/Linux        | Windows             |
| :--- | :--- | :--- || 进程创建   | `fork()`+`exec()` | `CreateProcess()`   |
| 信号       | SIGTERM, SIGKILL  | 不支持              |
| 进程组     | 进程组ID          | 作业对象            |
| 路径分隔符 | `/`               | `\`                 |
| Shell      | `sh`, `bash`      | `cmd`, `powershell` |

**跨平台命令示例**:

```rust
let cmd = if cfg!(target_os = "windows") {
    Command::new("cmd")
        .args(["/C", "dir"])
        .spawn()?
} else {
    Command::new("sh")
        .args(["-c", "ls -la"])
        .spawn()?
};
```
**抽象化示例**:

```rust
fn run_shell_command(cmd: &str) -> Result<Output, std::io::Error> {
    if cfg!(windows) {
        Command::new("cmd")
            .args(["/C", cmd])
            .output()
    } else {
        Command::new("sh")
            .args(["-c", cmd])
            .output()
    }
}

let output = run_shell_command("echo Hello")?;
```
**推荐库**:

- `tokio` - 统一的异步进程API
- `nix` - Unix 系统调用封装
- `winapi` - Windows API 封装

**参考**: [跨平台实践](../tier_02_guides/04_cross_platform_practice.md)

---

### Q8: Windows和Unix的进程模型有什么区别？

**A**: 两者在进程创建和管理上有根本性差异。

**Unix/Linux**:

- `fork()`: 复制进程
- `exec()`: 替换程序
- 信号: SIGTERM, SIGKILL
- 进程组和会话
- `/proc` 文件系统

**Windows**:

- `CreateProcess()`: 直接创建进程
- 无 fork（无写时复制）
- 无 Unix 信号（有事件对象）
- 作业对象（Job Object）
- 注册表和服务管理

**Rust 处理**:

```rust
#[cfg(unix)]
use std::os::unix::process::CommandExt;

#[cfg(windows)]
use std::os::windows::process::CommandExt;

let mut cmd = Command::new("app");

#[cfg(unix)]
{
    cmd.process_group(0); // 创建新进程组
}

#[cfg(windows)]
{
    cmd.creation_flags(0x00000200); // CREATE_NEW_PROCESS_GROUP
}

cmd.spawn()?;
```
---

## 生命周期问题

### Q9: 如何避免和处理僵尸进程？

**A**: 僵尸进程是已终止但父进程未回收其退出状态的进程。

**产生原因**:

- 父进程创建子进程后未调用 `wait()`
- 父进程意外退出
- 错误处理不当

**避免方法**:

**方法1: 使用 `output()` 或 `status()` (自动等待)**:

```rust
// 自动等待并回收
let output = Command::new("child").output()?;
let status = Command::new("child").status()?;
```
**方法2: 手动 `wait()`**:

```rust
let mut child = Command::new("child").spawn()?;
// ... 做其他事情 ...
let status = child.wait()?; // 回收子进程
```
**方法3: 非阻塞 `try_wait()`**:

```rust
let mut child = Command::new("child").spawn()?;

loop {
    match child.try_wait() {
        Ok(Some(status)) => {
            println!("子进程退出: {}", status);
            break; // 已回收
        }
        Ok(None) => {
            // 仍在运行，做其他事情
            thread::sleep(Duration::from_millis(100));
        }
        Err(e) => return Err(e),
    }
}
```
**方法4: RAII 模式**:

```rust
struct ManagedChild(Child);

impl Drop for ManagedChild {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}
```
**Unix 信号处理**:

```rust
#[cfg(unix)]
{
    use nix::sys::signal::{signal, SigHandler, Signal};
    unsafe {
        // 忽略SIGCHLD，让内核自动回收
        signal(Signal::SIGCHLD, SigHandler::SigIgn)?;
    }
}
```
**参考**: [术语表 - 僵尸进程](03_glossary.md#僵尸进程-zombie-process)

---

### Q10: 如何优雅地终止子进程？

**A**: 优先使用信号（Unix）或请求终止（Windows），最后才强制kill。

**Unix优雅终止**:

```rust
#[cfg(unix)]
{
    use nix::sys::signal::{kill, Signal};
    use nix::unistd::Pid;

    let pid = Pid::from_raw(child.id() as i32);

    // 1. 发送SIGTERM（优雅终止）
    kill(pid, Signal::SIGTERM)?;

    // 2. 等待一段时间
    thread::sleep(Duration::from_secs(5));

    // 3. 检查是否还在运行
    match child.try_wait()? {
        Some(status) => println!("已终止: {}", status),
        None => {
            // 4. 强制SIGKILL
            println!("发送SIGKILL");
            kill(pid, Signal::SIGKILL)?;
            child.wait()?;
        }
    }
}
```
**跨平台通用**:

```rust
// 1. 尝试kill()
child.kill()?;

// 2. 等待并回收
let status = child.wait()?;
println!("进程已终止: {}", status);
```
---

### Q11: 如何处理子进程超时？

**A**: 使用定时器或异步超时机制。

**方法1: 定时器+try_wait()**:

```rust
use std::time::{Duration, Instant};

let mut child = Command::new("slow_task").spawn()?;
let timeout = Duration::from_secs(30);
let start = Instant::now();

loop {
    match child.try_wait()? {
        Some(status) => {
            println!("完成: {}", status);
            break;
        }
        None if start.elapsed() >= timeout => {
            println!("超时，终止进程");
            child.kill()?;
            child.wait()?;
            return Err("timeout".into());
        }
        None => {
            thread::sleep(Duration::from_millis(100));
        }
    }
}
```
**方法2: Tokio异步超时**:

```rust
use tokio::process::Command;
use tokio::time::{timeout, Duration};

let result = timeout(
    Duration::from_secs(30),
    Command::new("slow_task").output()
).await;

match result {
    Ok(Ok(output)) => println!("完成: {:?}", output.status),
    Ok(Err(e)) => eprintln!("进程错误: {}", e),
    Err(_) => eprintln!("超时"),
}
```
---

## 异步与性能问题

### Q12: 什么时候应该使用异步进程管理？

**A**: 异步适合需要同时管理多个进程或I/O密集型场景。

**适合异步**:

- ✅ 同时管理多个子进程
- ✅ 进程I/O密集型操作
- ✅ 需要超时控制
- ✅ 与其他异步操作协同
- ✅ Web服务器、爬虫等高并发场景

**不适合异步**:

- ❌ 单个进程简单执行
- ❌ CPU密集型任务
- ❌ 需要实时保证的场景

**Tokio示例**:

```rust
use tokio::process::Command;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 并发启动多个进程
    let tasks = vec![
        tokio::spawn(run_task("task1")),
        tokio::spawn(run_task("task2")),
        tokio::spawn(run_task("task3")),
    ];

    // 等待所有完成
    for task in tasks {
        task.await??;
    }

    Ok(())
}

async fn run_task(name: &str) -> Result<(), Box<dyn std::error::Error>> {
    let output = Command::new(name).output().await?;
    println!("{} 完成: {:?}", name, output.status);
    Ok(())
}
```
**参考**: [异步进程管理](../tier_02_guides/03_async_process_management.md)

---

### Q13: 如何提高进程通信性能？

**A**: 选择合适的IPC机制，减少数据拷贝，使用缓冲。

**性能优化建议**:

1. **选择高性能IPC**:
   - 共享内存 > Unix Socket > 管道 > TCP
2. **减少拷贝**:

   ```rust
   // 使用 BufReader/BufWriter
   use std::io::{BufReader, BufWriter};

   let stdout = BufReader::new(child.stdout.take().unwrap());
   let stdin = BufWriter::new(child.stdin.take().unwrap());
   ```
3. **批量传输**:

   ```rust
   // 批量而非逐个
   let data: Vec<u8> = (0..10000).map(|_| 42u8).collect();
   stdin.write_all(&data)?;
   ```
4. **零拷贝技术** (高级):

   ```rust
   // 使用 splice() (Linux)
   #[cfg(target_os = "linux")]
   use nix::fcntl::splice;
   ```
**参考**: [性能优化参考](../tier_03_references/05_performance_optimization_reference.md)

---

### Q14: 如何监控进程资源使用？

**A**: 使用系统工具或第三方库获取进程资源信息。

**方法1: 使用 sysinfo 库**:

```rust
use sysinfo::{System, SystemExt, ProcessExt};

let mut sys = System::new_all();
sys.refresh_all();

if let Some(process) = sys.process(pid.into()) {
    println!("CPU使用: {}%", process.cpu_usage());
    println!("内存: {} KB", process.memory());
}
```
**方法2: 读取 /proc (Linux)**:

```rust
#[cfg(target_os = "linux")]
fn get_process_stats(pid: u32) -> std::io::Result<String> {
    std::fs::read_to_string(format!("/proc/{}/stat", pid))
}
```
**参考**: [进程监控与诊断](../tier_02_guides/05_process_monitoring_and_diagnostics.md)

---

## 错误处理问题

### Q15: 如何处理进程创建失败？

**A**: 使用 `Result` 和模式匹配处理各种错误。

```rust
use std::io::ErrorKind;

match Command::new("nonexistent").spawn() {
    Ok(child) => println!("成功: PID {}", child.id()),
    Err(e) => match e.kind() {
        ErrorKind::NotFound => {
            eprintln!("程序不存在");
        }
        ErrorKind::PermissionDenied => {
            eprintln!("权限不足");
        }
        _ => {
            eprintln!("其他错误: {}", e);
        }
    }
}
```
---

### Q16: 如何区分进程错误类型？

**A**: 检查 `ExitStatus` 和错误码。

```rust
let output = Command::new("app").output()?;

if output.status.success() {
    println!("成功");
} else if let Some(code) = output.status.code() {
    println!("失败，退出码: {}", code);
} else {
    #[cfg(unix)]
    {
        use std::os::unix::process::ExitStatusExt;
        if let Some(signal) = output.status.signal() {
            println!("被信号终止: {}", signal);
        }
    }
}
```
---

## 🔗 相关资源

- [项目概览](01_project_overview.md)
- [主索引导航](02_navigation.md)
- [术语表](03_glossary.md)
- [进程管理快速入门](../tier_02_guides/01_process_management_quick_start.md)
- [IPC通信实践](../tier_02_guides/02_ipc_communication_practice.md)

---

**文档维护**: Documentation Team
**创建日期**: 2025-10-22
**适用版本**: Rust 1.96.1+
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.1+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
