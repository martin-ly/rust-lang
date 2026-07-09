> **EN**: Process Security and Sandboxing in Rust
> **Summary**: Process isolation, privilege dropping, resource limits, namespaces, seccomp, and sandbox design for Rust child processes.

# Rust 进程安全与沙箱

> **权威页地位**：本页为 Rust 进程安全与沙箱概念的 canonical 解释来源。

## 1. 概念定义

**进程安全与沙箱 (Process Security and Sandboxing)** 通过最小权限、资源限制、隔离机制等手段，降低不可信或高敏感子进程对主机的影响。

## 2. 权限最小化

### 2.1 用户/组降级

在 Unix 上通过 `std::os::unix::process::CommandExt::uid` / `gid` 以低权限用户启动子进程。

### 2.2 Linux Capabilities

使用 `caps` crate 仅保留必要 capability，其余全部清除，实现比完整 root 更细粒度的权限控制。

## 3. 资源限制

### 3.1 rlimit

通过 `nix::sys::resource::setrlimit` 限制 CPU 时间、虚拟内存、文件描述符、进程数等。

### 3.2 cgroups

Linux cgroups v2 可限制内存、CPU 权重、I/O 带宽，并将子进程加入指定 cgroup。

## 4. 隔离机制

### 4.1 Linux Namespaces

使用 `nix::sched::unshare` 创建新的 PID、网络、挂载、UTS、IPC、用户命名空间，实现类容器隔离。

### 4.2 文件系统隔离

- **chroot**：切换根目录，限制文件访问范围。
- **pivot_root**：配合 bind mount 实现更完整的根切换。

### 4.3 网络隔离

通过网络命名空间与 veth 对，将子进程置于独立网络栈。

## 5. 系统调用过滤

### 5.1 Seccomp

使用 `seccompiler` 定义允许/禁止的系统调用白名单，阻断危险调用如 `execve`、`ptrace`。

### 5.2 强制访问控制

- **AppArmor**：基于路径的配置文件控制资源访问。
- **SELinux**：基于安全标签的强制访问控制。

## 6. 沙箱设计模式

| 级别 | 机制 | 复杂度 | 安全性 |
| :--- | :--- | :--- | :--- |
| 基础 | 权限降级 + rlimit | 低 | 中 |
| 进阶 | + namespaces + chroot | 中 | 高 |
| 高安全 | + seccomp + AppArmor/SELinux | 高 | 最高 |

## 7. 威胁模型

常见攻击向量包括：提权、资源耗尽、信息泄露、恶意系统调用、网络横向移动。沙箱设计应结合具体威胁模型选择机制。

## 8. 相关概念

- [进程模型与生命周期](01_process_model_and_lifecycle.md)
- [跨平台进程管理](04_cross_platform_process_management.md)
- [IPC 机制](05_ipc_mechanisms.md)
- [Rust 安全实践](../../06_ecosystem/07_security_and_cryptography/19_security_practices.md)

---

> **权威来源**: [Rust Standard Library — std::process](https://doc.rust-lang.org/std/process/) · [nix crate](https://docs.rs/nix/) · [seccompiler crate](https://docs.rs/seccompiler/) · [Linux kernel — namespaces/cgroups/seccomp](https://www.kernel.org/doc/html/latest/)
