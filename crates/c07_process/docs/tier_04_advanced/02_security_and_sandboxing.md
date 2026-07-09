> **EN**: Process Security and Sandboxing
> **Summary**: Advanced guide to process isolation, privilege dropping, resource limits, namespaces, seccomp, and sandbox design in Rust. The canonical concept explanation has been migrated to the concept authority page.

# Tier 4: 安全与沙箱

> **权威来源**: [concept/03_advanced/02_process_ipc/07_process_security_and_sandboxing.md](../../../../concept/03_advanced/02_process_ipc/07_process_security_and_sandboxing.md)

本文件为 `crates/c07_process` 的专题实践材料。通用 Rust 进程安全与沙箱概念请参见上方权威页；完整代码示例、练习与案例仍保留在本书。

## 主题列表

- 进程隔离技术（权限降级、用户与组管理、Capabilities）
- 资源限制（rlimit、cgroups、内存与 CPU 限制）
- 容器化技术（Linux Namespaces、网络隔离、文件系统隔离）
- 安全机制（Seccomp 过滤、AppArmor/SELinux、审计日志）
- 沙箱实现
- 容器安全与威胁模型
- 安全配置模板与安全测试
