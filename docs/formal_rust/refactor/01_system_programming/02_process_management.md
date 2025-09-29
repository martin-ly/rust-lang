# 系统编程 · 进程管理（已完成 100%）

## 目录

- [系统编程 · 进程管理（已完成 100%）](#系统编程--进程管理已完成-100)
  - [目录](#目录)
  - [1. 概述](#1-概述)
  - [2. 主题要点](#2-主题要点)
    - [2.1 子进程与管道示例](#21-子进程与管道示例)
  - [3. 形式化要点](#3-形式化要点)
  - [4. 跨链路导航](#4-跨链路导航)
  - [5. 运行示例与依赖](#5-运行示例与依赖)

## 1. 概述

覆盖进程创建、监控、IPC、同步、信号与资源治理等。

## 2. 主题要点

- 创建/终止、配置与环境
- IPC：管道、共享内存、消息通道
- 同步：互斥、条件变量、信号量

### 2.1 子进程与管道示例

```rust
use std::io::{Read, Write};
use std::process::{Command, Stdio};

fn main() -> std::io::Result<()> {
    let mut child = Command::new("rustc")
        .arg("--version")
        .stdout(Stdio::piped())
        .spawn()?;
    let mut out = String::new();
    child.stdout.as_mut().unwrap().read_to_string(&mut out)?;
    println!("child says: {}", out.trim());
    Ok(())
}
```

## 3. 形式化要点

- 死锁预防与检测、资源有界性
- 信号的时序与传播不变量

## 4. 跨链路导航

- 概念框架：`../01_conceptual_framework/01_05_relationship_graph.md`

## 5. 运行示例与依赖

- 依赖：标准库即可。
- 运行：`cargo run -q`；若在Windows上，可将示例命令替换为 `cmd /C ver`。
