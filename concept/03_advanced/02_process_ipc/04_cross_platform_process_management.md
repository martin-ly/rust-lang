> **EN**: Cross-Platform Process Management in Rust
> **Summary**: Writing portable process-management code across Windows, Linux, and macOS using std::process, platform extensions, and conditional compilation.

# Rust 跨平台进程管理

> **权威页地位**：本页为 Rust 跨平台进程管理概念的 canonical 解释来源。
> **对应 crate 示例**：`crates/c07_process/docs/06_cross_platform_process_management.md` 现为摘要页，指向此处。

---

## 1. 平台差异概述

Rust 的 `std::process` 已经封装了大部分跨平台差异，但某些功能仍依赖平台特定扩展：

| 平台 | 进程创建 | 服务管理 | 路径分隔符 | 信号处理 |
| :--- | :--- | :--- | :--- | :--- |
| Windows | `CreateProcess` | Windows Service | `\` | Windows 信号/事件 |
| Linux | `fork/exec` | systemd | `/` | Unix 信号 |
| macOS | `fork/exec` | launchd | `/` | Unix 信号 |

## 2. 统一抽象层

通过条件编译和 trait 抽象，可以编写跨平台的进程管理代码：

```rust
use std::process::{Command, Stdio};
use std::path::PathBuf;

#[derive(Debug, Clone)]
pub enum Platform {
    Windows,
    Linux,
    MacOS,
    Unix,
    Unknown,
}

#[derive(Debug, Clone)]
pub struct CrossPlatformConfig {
    pub default_shell: String,
    pub path_separator: char,
    pub executable_extension: String,
    pub temp_dir: PathBuf,
    pub supports_process_groups: bool,
    pub supports_signals: bool,
    pub supports_job_control: bool,
}

impl CrossPlatformConfig {
    pub fn for_current_platform() -> (Platform, Self) {
        if cfg!(target_os = "windows") {
            (Platform::Windows, Self {
                default_shell: "cmd.exe".into(),
                path_separator: '\\',
                executable_extension: ".exe".into(),
                temp_dir: std::env::var("TEMP").map(PathBuf::from).unwrap_or_else(|_| PathBuf::from("C:\\Temp")),
                supports_process_groups: false,
                supports_signals: false,
                supports_job_control: true,
            })
        } else if cfg!(target_os = "linux") {
            (Platform::Linux, Self {
                default_shell: "/bin/bash".into(),
                path_separator: '/',
                executable_extension: "".into(),
                temp_dir: PathBuf::from("/tmp"),
                supports_process_groups: true,
                supports_signals: true,
                supports_job_control: true,
            })
        } else if cfg!(target_os = "macos") {
            (Platform::MacOS, Self {
                default_shell: "/bin/zsh".into(),
                path_separator: '/',
                executable_extension: "".into(),
                temp_dir: PathBuf::from("/tmp"),
                supports_process_groups: true,
                supports_signals: true,
                supports_job_control: true,
            })
        } else {
            (Platform::Unknown, Self {
                default_shell: "/bin/sh".into(),
                path_separator: '/',
                executable_extension: "".into(),
                temp_dir: PathBuf::from("/tmp"),
                supports_process_groups: cfg!(unix),
                supports_signals: cfg!(unix),
                supports_job_control: cfg!(unix),
            })
        }
    }
}
```

## 3. 平台特定扩展

Rust 通过 `std::os` 模块提供平台扩展 trait：

- `std::os::unix::process::CommandExt`
- `std::os::windows::process::CommandExt`

```rust
use std::process::Command;

#[cfg(unix)]
fn configure_unix(cmd: &mut Command) {
    use std::os::unix::process::CommandExt;
    cmd.process_group(0); // 创建新进程组
}

#[cfg(windows)]
fn configure_windows(cmd: &mut Command) {
    use std::os::windows::process::CommandExt;
    const CREATE_NO_WINDOW: u32 = 0x08000000;
    cmd.creation_flags(CREATE_NO_WINDOW);
}
```

## 4. 路径与环境变量

跨平台路径处理应使用 `std::path` 而非硬编码分隔符：

```rust
use std::path::PathBuf;

fn config_path() -> PathBuf {
    let mut path = PathBuf::from("config");
    path.push("app.toml");
    path
}
```

## 5. 服务集成

| 平台 | 服务管理器 | Rust 集成方式 |
| :--- | :--- | :--- |
| Linux | systemd | D-Bus / systemd notify crate |
| Windows | Windows Service | `windows-service` crate |
| macOS | launchd | plist 配置 + `launchctl` |

## 6. 决策树

```text
处理跨平台差异
│
├── 是否需要平台特定功能？
│   ├── 是 → 使用条件编译
│   │   ├── Windows → Windows API
│   │   ├── Linux → systemd / nix
│   │   └── macOS → launchd / nix
│   └── 否 → 使用 std::process 统一抽象层
```

## 7. 最佳实践

- 默认使用 `std::process` 保持可移植性。
- 将平台特定逻辑隔离在 `#[cfg(...)]` 模块中。
- 路径操作始终使用 `std::path::Path` 和 `PathBuf`。
- 在 CI 中针对目标平台进行交叉编译与测试。

## 补充视角：平台特定 API 与资源控制

> 本节选编自 `crates/c07_process/docs/10_cross_platform_guide.md`，
> 作为 canonical 跨平台进程管理概念页的工程实践补充。

### Windows 特定能力

- **作业对象（Job Objects）**：将一组进程绑定到统一资源限制与生命周期管理单元。
- **服务管理**：通过 `sc` 命令或 `windows-service` crate 注册/管理 Windows Service。
- **进程优先级**：`SetPriorityClass` 设置 `IDLE` 到 `REALTIME` 优先级。

### Unix/Linux 特定能力

- **进程组与会话**：`setpgid`、`setsid` 控制进程组与终端会话。
- **资源限制**：`nix::sys::resource::setrlimit` 设置内存、文件描述符、CPU 时间上限。
- **用户/组切换**：`setuid` / `setgid` 实现特权降级。

### 命令解析差异

- Windows 默认由 `cmd.exe /C` 解析复杂命令，需注意引号与空格转义。
- Unix 通常直接 `exec` 目标程序，参数按数组传递。

---

## 相关概念

- [进程模型与生命周期](01_process_model_and_lifecycle.md)
- [高级进程管理](02_advanced_process_management.md)
- [异步进程管理](03_async_process_management.md)
- [条件编译](../03_proc_macros/28_conditional_compilation.md)

---

> **权威来源**: [Rust Standard Library — std::process](https://doc.rust-lang.org/std/process/) · [Rust Reference — Conditional Compilation](https://doc.rust-lang.org/reference/conditional-compilation.html)
