> **EN**: Process Model and Lifecycle in Rust
> **Summary**: A canonical guide to Rust's process abstraction, lifecycle management, resource control, and IPC safety guarantees, grounded in `std::process` and modern async runtimes.

# Rust 进程模型与生命周期

> **权威页地位**：本页为 Rust 进程与 IPC 概念的 canonical 解释来源。
> **对应 crate 示例**：`crates/c07_process/docs/01_process_model_and_lifecycle.md` 现为摘要页，指向此处。

---

## 1. 进程定义与模型

### 1.1 进程理论基础

- **进程**：操作系统分配资源和调度的基本单位，拥有独立的地址空间、代码、数据、堆栈和系统资源。
- **Rust 抽象**：通过 `std::process` 提供跨平台进程管理，封装平台细节，保证内存与资源安全。
- **内存隔离**：Rust 进程模型依赖操作系统的虚拟内存机制，确保进程间内存安全隔离。
- **所有权模型**：Rust 类型系统和所有权机制防止跨进程悬垂指针和未定义行为。

### 1.2 Rust 进程抽象

Rust 采用 1:1 进程模型映射到操作系统进程，核心类型包括：

- `std::process::Command`：进程构建器，用于配置命令、参数、环境变量、I/O 重定向等。
- `std::process::Child`：子进程句柄，代表已启动的进程。
- `std::process::ExitStatus`：进程退出状态，包含退出码或信号信息。
- `std::process::Stdio`：标准输入输出配置。

### 1.3 内存安全与所有权

- **Drop 语义**：进程相关资源在作用域结束时自动释放，防止资源泄漏。
- **错误处理**：所有进程操作均返回 `Result`，强制开发者处理失败分支。
- **平台兼容性**：`std::process` 屏蔽平台差异，提供统一 API。

---

## 2. 生命周期管理

### 2.1 进程状态机

典型进程生命周期：

```text
Created → Running → (Waiting →)* → Terminated
```

- `Command::spawn()`：创建并启动进程（Created → Running）。
- `Child::wait()` / `Child::wait_with_output()`：等待进程终止。
- `Child::try_wait()`：非阻塞检查进程状态。
- `Child::kill()`：终止进程。

### 2.2 异步生命周期管理

现代 Rust 异步运行时（如 Tokio）提供 `tokio::process::Command`，支持：

- 异步等待子进程完成。
- 超时控制与自动清理。
- 并发管理多个子进程。

### 2.3 资源自动释放

- `Child` 实现 `Drop` trait，析构时自动释放系统资源（文件描述符、内存等）。
- 即使子进程崩溃，父进程不会受内存安全威胁，所有错误通过 `Result` 类型显式处理。

---

## 3. 进程属性与资源控制

### 3.1 基础属性配置

- **环境变量**：通过 `Command::env`、`Command::env_clear` 等管理。
- **工作目录**：通过 `Command::current_dir` 设置。
- **I/O 重定向**：通过 `Command::stdin`、`Command::stdout`、`Command::stderr` 配置。

### 3.2 高级资源限制

在 Unix 平台上，可通过 `nix::sys::resource::setrlimit` 等系统调用设置：

- 内存限制（`RLIMIT_AS`）
- 文件描述符限制（`RLIMIT_NOFILE`）
- CPU 时间限制（`RLIMIT_CPU`）

Windows 平台需使用对应的 Windows API 进行资源限制配置。

### 3.3 跨平台资源管理

- 子进程默认继承父进程资源限制，可显式修改。
- 使用条件编译（`#[cfg(unix)]`、`#[cfg(windows)]`）处理平台特定逻辑。

---

## 4. Rust 的进程安全抽象

> **L2 向下引用**: 进程安全抽象建立在 [Trait 系统](../../02_intermediate/00_traits/01_traits.md) 与 [L2 错误处理](../../02_intermediate/03_error_handling/04_error_handling.md) 之上。

### 4.1 类型安全保证

- 进程 I/O 管道通过 `Option<ChildStdin>`、`Option<ChildStdout>`、`Option<ChildStderr>` 暴露，所有权确保每个管道只被消费一次。
- 所有系统调用错误通过 `Result` 传播。

### 4.2 错误处理机制

建议为进程操作定义专门的错误类型，区分：

- 进程启动失败
- 进程等待失败
- 进程输出失败
- 进程终止失败
- 超时
- 异常退出

### 4.3 平台兼容性

- `std::process` 提供跨平台统一 API。
- 平台特定扩展通过 `std::os::unix::process::CommandExt` 和 `std::os::windows::process::CommandExt` 提供。

---

## 5. 现代库集成

### 5.1 Tokio 异步进程

`tokio::process::Command` 提供与 Tokio 运行时集成的异步进程管理能力，支持异步读写和超时。

### 5.2 Duct 进程组合

`duct` crate 提供简洁的进程管道组合 API，适合 shell-like 的进程链式调用。

### 5.3 Nix 系统调用封装

`nix` crate 封装 Unix 系统调用，提供更细粒度的进程控制（如资源限制、信号处理等）。

---

## 6. 最佳实践

### 6.1 资源管理

- 总是为进程执行设置超时。
- 使用 RAII 模式，依赖 `Drop` 自动释放资源。
- 异步等待时优先使用 `tokio::time::timeout`。

### 6.2 错误处理

- 根据退出码、stderr 输出、错误类型进行分类处理。
- 区分权限不足、资源不足、命令执行失败等场景。
- 避免在错误路径中忽略子进程句柄，防止僵尸进程。

### 6.3 避免僵尸进程

- 确保对 `Child` 调用 `wait` 或 `wait_with_output`。
- 在异步场景中，使用结构化并发模式管理子进程生命周期。

---

## 7. 关键特性总结

1. **内存安全**：所有权模型确保进程间内存隔离。
2. **资源管理**：自动资源释放，防止泄漏。
3. **错误处理**：强制错误处理，提高健壮性。
4. **跨平台兼容**：统一的 API 接口。
5. **异步支持**：与 Tokio 等现代运行时集成。

---

## 8. 相关概念

- [并发模型](../00_concurrency/01_concurrency.md)
- [异步编程](../01_async/02_async.md)
- [错误处理基础](../../01_foundation/08_error_handling/32_error_handling_basics.md)
- [L2 错误处理](../../02_intermediate/03_error_handling/04_error_handling.md)

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
