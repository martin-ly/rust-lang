# C07-01. 进程模型与生命周期

本章系统梳理 Rust 进程的理论基础、生命周期管理、资源属性控制及其安全抽象。

## 1. 进程定义与模型

- **进程**：操作系统分配资源和调度的基本单位，拥有独立的地址空间、代码、数据、堆栈和系统资源。
- **Rust 抽象**：通过 `std::process` 提供跨平台进程管理，封装平台细节，保证内存与资源安全。

```rust
pub struct Process {
    // 实际实现封装了平台特定细节
    inner: imp::Process,
}
```

- **内存隔离**：Rust 进程模型依赖操作系统的虚拟内存机制，确保进程间内存安全隔离。
- **所有权模型**：Rust 类型系统和所有权机制防止跨进程悬垂指针和未定义行为。

## 2. 生命周期管理

- **状态流转**：Created → Running → (Waiting →)* → Terminated
- **核心类型**：`std::process::Command`（进程构建器）、`Child`（子进程句柄）

```rust
let mut command = Command::new("program");
let child = command.spawn()?;  // Created → Running
let status = child.wait()?;    // 等待进程终止
```

- **资源释放**：`Child` 实现 `Drop` trait，析构时自动释放系统资源（文件描述符、内存等）。
- **安全保证**：即使子进程崩溃，父进程不会受内存安全威胁，所有错误通过 `Result` 类型显式处理。

## 3. 进程属性与资源控制

- **属性配置**：环境变量、工作目录、I/O 重定向、资源限制等

```rust
Command::new("program")
    .stdin(Stdio::piped())
    .stdout(Stdio::null())
    .stderr(Stdio::inherit())
    .env_clear()
    .env("PATH", "/usr/bin");
```

- **资源限制**：可通过平台 API（如 Linux 的 `setrlimit`）设置内存、文件数等限制

```rust
use nix::sys::resource::{setrlimit, Resource};
setrlimit(Resource::RLIMIT_AS, 1024 * 1024 * 100, 1024 * 1024 * 200)?;
```

- **继承与隔离**：子进程默认继承父进程资源限制，可显式修改。

## 4. Rust 的进程安全抽象

- **Drop 语义**：Rust 保证进程相关资源在作用域结束时自动释放，防止资源泄漏。
- **错误处理**：所有进程操作均返回 `Result`，强制开发者处理失败分支。
- **平台兼容性**：`std::process` 屏蔽平台差异，提供统一 API。

## 5. 小结

Rust 进程模型以类型系统和所有权为基础，结合操作系统原语，提供了安全、可移植、易用的进程管理能力。生命周期管理、资源控制和错误处理机制共同确保了系统级编程的健壮性和安全性。
