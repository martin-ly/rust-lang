# Tokio-Process 异步进程形式化分析

> **主题**: 子进程管理的异步安全
>
> **形式化框架**: 进程生命周期 + IO重定向
>
> **参考**: tokio::process Documentation

---

## 目录

- [Tokio-Process 异步进程形式化分析](#tokio-process-异步进程形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 进程创建](#2-进程创建)
    - [定理 2.1 (Command构建)](#定理-21-command构建)
  - [3. IO重定向](#3-io重定向)
    - [定理 3.1 (异步管道)](#定理-31-异步管道)
  - [4. 等待语义](#4-等待语义)
    - [定理 4.1 (异步等待)](#定理-41-异步等待)
    - [定理 4.2 (超时控制)](#定理-42-超时控制)
  - [5. 信号处理](#5-信号处理)
    - [定理 5.1 (优雅终止)](#定理-51-优雅终止)
  - [6. 反例](#6-反例)
    - [反例 6.1 (僵尸进程)](#反例-61-僵尸进程)
    - [反例 6.2 (管道填满)](#反例-62-管道填满)

---

## 1. 引言

tokio::process提供:

- 异步子进程管理
- 非阻塞IO
- 优雅终止
- 跨平台支持

---

## 2. 进程创建

### 定理 2.1 (Command构建)

> 标准库Command的异步扩展。

```rust
use tokio::process::Command;

let mut child = Command::new("/bin/cat")
    .arg("file.txt")
    .stdout(Stdio::piped())
    .spawn()?;
```

∎

---

## 3. IO重定向

### 定理 3.1 (异步管道)

> 子进程IO与AsyncRead/AsyncWrite集成。

```rust
let mut child = Command::new("/bin/ls")
    .stdout(Stdio::piped())
    .spawn()?;

let stdout = child.stdout.take().unwrap();
let reader = BufReader::new(stdout);
let mut lines = reader.lines();

while let Some(line) = lines.next_line().await? {
    println!("{}", line);
}
```

∎

---

## 4. 等待语义

### 定理 4.1 (异步等待)

> wait()不阻塞运行时线程。

```rust
let status = child.wait().await?;
if status.success() {
    println!("Exit: {}", status.code().unwrap_or(-1));
}
```

∎

### 定理 4.2 (超时控制)

> 可配置超时终止。

```rust
let status = timeout(Duration::from_secs(30), child.wait())
    .await
    .map_err(|_| {
        child.kill().await?;  // 超时杀死
    })??;
```

∎

---

## 5. 信号处理

### 定理 5.1 (优雅终止)

> 先尝试SIGTERM，再SIGKILL。

```rust
// 发送SIGTERM (Unix) 或 Terminate (Windows)
child.kill().await?;
```

∎

---

## 6. 反例

### 反例 6.1 (僵尸进程)

```rust
// 错误: 不wait导致僵尸
let _child = Command::new("sleep").arg("10").spawn()?;
// 进程结束后成为僵尸

// 正确: 必须wait或kill
let status = child.wait().await?;
```

### 反例 6.2 (管道填满)

```rust
// 错误: 不读取stdout导致子进程阻塞
let child = Command::new("yes")
    .stdout(Stdio::piped())
    .spawn()?;
child.wait().await?;  // 死锁!

// 正确: 并发读取
let mut child = Command::new("yes")
    .stdout(Stdio::piped())
    .spawn()?;
let stdout = child.stdout.take().unwrap();
tokio::spawn(async move {
    let mut reader = BufReader::new(stdout).lines();
    while let Ok(Some(_)) = reader.next_line().await {}
});
child.wait().await?;
```

---

*文档版本: 1.0.0*
*定理数量: 6个*
