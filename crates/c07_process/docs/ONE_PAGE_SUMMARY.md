# C07 进程管理 - 一页纸总结

> **用途**: 快速回顾核心概念、常见坑、学习路径
> **完整文档**: [00_MASTER_INDEX](./00_MASTER_INDEX.md)

---

## 核心概念（4 条）

| 概念 | 说明 |
|------|------|
| **进程创建** | `Command::new()`、`spawn()`、`output()`；环境变量、工作目录 |
| **标准 IO** | `stdin`/`stdout`/`stderr`；管道 `Stdio::piped()` |
| **信号处理** | `signal_hook`；SIGINT、SIGTERM 等 |
| **IPC** | 管道、Unix domain socket；跨进程通信 |

---

## 常见坑与解决

| 坑 | 解决 |
|----|------|
| 子进程僵尸 | `wait()` 或 `try_wait()` 回收；或 `kill_on_drop` |
| 管道死锁 | 避免父子同时读写；用 `spawn` + 异步读取 |
| 跨平台差异 | 用 `std::process` 抽象；信号仅 Unix |
| 权限与沙箱 | 注意 `setuid`、chroot；生产用专用运行时 |

---

## 进程速选

| 场景 | 选型 |
|------|------|
| 执行命令取输出 | `Command::output()` |
| 流式输出 | `Command::spawn()` + `stdout` 读取 |
| 管道链 | `Command` 链式 `stdin(prev.stdout)` |
| 超时控制 | `wait_timeout` 或 `tokio::process` |

---

## 学习路径

1. **入门** (1 周): `Command` 基础 → 标准 IO 重定向 → 错误处理
2. **进阶** (2 周): 信号、IPC、与 C10 网络结合
3. **高级** (持续): 异步进程、生产部署

---

## 速查与练习

- **速查卡**: [process_management_cheatsheet](../../../docs/02_reference/quick_reference/process_management_cheatsheet.md)
- **RBE 练习**: [Process](https://doc.rust-lang.org/rust-by-example/std_misc/process.html)
- **Rustlings**: 无进程专题；参考 RBE 与 C07 模块
