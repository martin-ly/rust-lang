# 概览：进程与系统交互（c07_process）

本模块聚焦进程创建与管理、IO/管道、环境变量、退出码、子进程与进程间通信等，涵盖实战与最佳实践。

---

## 目录导航

- 视图与专题
  - [view01.md](./view01.md)
  - [view02.md](./view02.md)
  - [view03.md](./view03.md)
  - [view04.md](./view04.md)
  - [view05.md](./view05.md)

- 关联文档
  - 顶层说明：`README.md`
  - 项目总结：`FINAL_PROJECT_COMPLETION_SUMMARY.md`、`PROJECT_COMPLETION_REPORT_2025.md`

---

## 快速开始

1) 从 `view01.md`/`view02.md` 理解进程基础与命令执行
2) 阅读 `view03.md`/`view04.md` 掌握管道与环境
3) 在 `src/` 中运行子进程示例并观察错误处理

---

## 待完善

- 增补跨平台差异（Windows/Unix）注意事项与案例
- 增补与 `c10_networks` 的管道/子进程网络工具链联动

### 跨平台差异与案例（补全）

- 路径与 Shell 差异
  - Windows 默认 `cmd.exe`/PowerShell，不支持 Unix 管道语法的某些细节；建议使用 `Command` + 显式参数数组
  - 可执行文件后缀（`.exe`）与 PATH 解析差异；使用绝对路径更稳妥

- I/O 与编码
  - Windows 控制台编码可能为 CP936/GBK；将输出视作字节并按需转换为 UTF-8
  - 行结束符差异（CRLF vs LF）；对文本处理使用平台无关库

- 权限与进程模型
  - 进程组/信号：Unix `SIGTERM/SIGKILL`，Windows 需通过 Job 对组进行终止
  - 临时文件与重定向：Windows 对独占/共享访问更敏感，打开文件时显式共享策略

- 最小示例（跨平台 Command）

```rust
use std::process::{Command, Stdio};

fn run_echo() -> anyhow::Result<String> {
    let mut cmd = if cfg!(windows) {
        let mut c = Command::new("cmd");
        c.args(["/C", "echo hello"]);
        c
    } else {
        let mut c = Command::new("sh");
        c.args(["-c", "echo hello"]);
        c
    };
    let out = cmd.stdout(Stdio::piped()).output()?;
    Ok(String::from_utf8_lossy(&out.stdout).to_string())
}
```

### 与网络工具链联动（补全）

- 典型场景：通过子进程调用 `curl`/`iperf`/`tcpdump` 收集网络指标；以管道将数据输送给统计程序
- 建议：
  - 为长时任务使用超时/心跳监控；对输出使用有界缓冲避免阻塞
  - 将网络工具与 `c10_networks` 的异步客户端组合，统一指标上报到 `obs`/tracing
