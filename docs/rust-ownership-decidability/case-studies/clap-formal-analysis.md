# Clap命令行解析形式化分析

> **主题**: 声明式命令行解析
> **形式化框架**: 派生宏 + 类型安全参数 + 验证
> **参考**: Clap Documentation (<https://docs.rs/clap>)

---

## 目录

- [Clap命令行解析形式化分析](#clap命令行解析形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 派生宏系统](#2-派生宏系统)
    - [定义 DERIVE-1 ( 结构体派生 )](#定义-derive-1--结构体派生-)
    - [定义 DERIVE-2 ( 属性映射 )](#定义-derive-2--属性映射-)
    - [定理 DERIVE-T1 ( 完备解析 )](#定理-derive-t1--完备解析-)
  - [3. 参数类型](#3-参数类型)
    - [定义 ARG-1 ( 位置参数 )](#定义-arg-1--位置参数-)
    - [定义 ARG-2 ( 可选参数 )](#定义-arg-2--可选参数-)
    - [定理 ARG-T1 ( 类型转换安全 )](#定理-arg-t1--类型转换安全-)
  - [4. 验证与约束](#4-验证与约束)
    - [定义 VALIDATE-1 ( 值验证 )](#定义-validate-1--值验证-)
    - [定义 VALIDATE-2 ( 组合约束 )](#定义-validate-2--组合约束-)
  - [5. 子命令](#5-子命令)
    - [定义 SUBCMD-1 ( 子命令枚举 )](#定义-subcmd-1--子命令枚举-)
    - [定理 SUBCMD-T1 ( 互斥性 )](#定理-subcmd-t1--互斥性-)
  - [6. 定理与证明](#6-定理与证明)
    - [定理 CLAP-T1 ( 零运行时开销 )](#定理-clap-t1--零运行时开销-)
    - [定理 CLAP-T2 ( 类型安全保证 )](#定理-clap-t2--类型安全保证-)
  - [7. 代码示例](#7-代码示例)
    - [示例1: 完整CLI](#示例1-完整cli)
    - [示例2: 高级验证](#示例2-高级验证)

---

## 1. 引言

Clap是Rust标准命令行解析库：

- 派生宏驱动（derive）
- Builder API
- 类型安全参数解析
- 自动帮助生成
- shell补全

---

## 2. 派生宏系统

### 定义 DERIVE-1 ( 结构体派生 )

```rust
#[derive(Parser)]
#[command(name = "myapp", version = "1.0")]
struct Cli {
    #[arg(short, long)]
    verbose: bool,
    #[arg(short, long, default_value = "config.toml")]
    config: PathBuf,
}
```

**形式化**:

$$
\text{Cli} = \{ (f_i : T_i, \text{attrs}_i) \mid \text{Parser}(\text{Cli}) \}
$$

### 定义 DERIVE-2 ( 属性映射 )

| 属性 | 类型约束 | 含义 |
| :--- | :--- | :--- |
| `short` | - | 短选项 |
| `long` | - | 长选项 |
| `default_value` | `T: FromStr` | 默认值 |
| `required` | `bool` | 是否必需 |

### 定理 DERIVE-T1 ( 完备解析 )

派生宏生成完整解析代码。

$$
\text{derive(Parser)} \to \text{impl Parser for Cli}
$$

---

## 3. 参数类型

### 定义 ARG-1 ( 位置参数 )

```rust
#[derive(Parser)]
struct Args {
    input: PathBuf,        // 必需位置参数
    output: Option<PathBuf>, // 可选位置参数
}
```

$$
\text{Positional}(T) = \text{Required}(T) \mid \text{Optional}(T)
$$

### 定义 ARG-2 ( 可选参数 )

```rust
#[derive(Parser)]
struct Args {
    #[arg(short, long)]
    level: u32,
    #[arg(short, long, action = ArgAction::Count)]
    verbose: u8,
}
```

$$
\text{Option}(name, short, T) \text{ where } T: \text{FromStr}
$$

### 定理 ARG-T1 ( 类型转换安全 )

无效输入导致优雅错误。

$$
\text{parse}(s, T) = \text{Ok}(v) \mid \text{Err}(e) \text{ with context}
$$

---

## 4. 验证与约束

### 定义 VALIDATE-1 ( 值验证 )

```rust
#[derive(Parser)]
struct Args {
    #[arg(short, long, value_parser = clap::value_parser!(u32).range(1..=100))]
    port: u32,
}
```

$$
\text{Validator} : T \to \text{bool}
$$

### 定义 VALIDATE-2 ( 组合约束 )

```rust
#[derive(Args)]
struct Config {
    #[arg(group = "input", required = true)]
    file: Option<PathBuf>,
    #[arg(group = "input")]
    url: Option<String>,
}
```

$$
\text{Group} = \{ a_1, a_2, \ldots \} \text{ with constraint } \text{exactly\_one}(g)
$$

---

## 5. 子命令

### 定义 SUBCMD-1 ( 子命令枚举 )

```rust
#[derive(Subcommand)]
enum Commands {
    Add { files: Vec<PathBuf> },
    Remove { pattern: String },
    List { all: bool },
}
```

$$
\text{Subcommand} = \{ C_i(\text{args}_i) \mid i = 1..n \}
$$

### 定理 SUBCMD-T1 ( 互斥性 )

子命令相互排斥。

$$
\forall c_1, c_2 : \text{Commands}.\ c_1 \neq c_2 \to \neg(c_1 \land c_2)
$$

---

## 6. 定理与证明

### 定理 CLAP-T1 ( 零运行时开销 )

解析在编译期生成代码。

$$
\text{parse\_time}(n) = O(n) \text{ where } n = \text{arg\_count}
$$

### 定理 CLAP-T2 ( 类型安全保证 )

无效参数类型导致编译错误。

$$
\text{field} : T \text{ where } T \not: \text{FromStr} \to \text{compile\_error}
$$

---

## 7. 代码示例

### 示例1: 完整CLI

```rust
use clap::{Parser, Subcommand, Args};
use std::path::PathBuf;

#[derive(Parser)]
#[command(name = "todo")]
#[command(about = "A simple todo CLI")]
#[command(version = "1.0")]
struct Cli {
    #[command(subcommand)]
    command: Commands,
    #[arg(short, long, global = true)]
    verbose: bool,
}

#[derive(Subcommand)]
enum Commands {
    Add(AddArgs),
    List(ListArgs),
    Done { id: u32 },
}

#[derive(Args)]
struct AddArgs {
    #[arg(required = true)]
    tasks: Vec<String>,
    #[arg(short, long)]
    priority: Option<u8>,
}

#[derive(Args)]
struct ListArgs {
    #[arg(short, long)]
    all: bool,
    #[arg(short, long, default_value = "10")]
    limit: usize,
}

fn main() {
    let cli = Cli::parse();

    match cli.command {
        Commands::Add(args) => add_tasks(args),
        Commands::List(args) => list_tasks(args),
        Commands::Done { id } => mark_done(id),
    }
}
```

### 示例2: 高级验证

```rust
use clap::{Parser, error::ErrorKind};

#[derive(Parser)]
struct ServerArgs {
    #[arg(short, long, default_value = "8080")]
    #[arg(value_parser = port_in_range)]
    port: u16,

    #[arg(short, long)]
    #[arg(value_parser = validate_host)]
    host: String,
}

fn port_in_range(s: &str) -> Result<u16, String> {
    let port: u16 = s.parse().map_err(|_| format!("`{}` isn't a valid port", s))?;
    if port >= 1024 {
        Ok(port)
    } else {
        Err(format!("Port {} is reserved (must be >= 1024)", port))
    }
}

fn validate_host(s: &str) -> Result<String, String> {
    if s.is_empty() {
        Err("Host cannot be empty".to_string())
    } else {
        Ok(s.to_string())
    }
}
```

---

**维护者**: Rust CLI Formal Methods Team
**创建日期**: 2026-03-05
**Clap版本**: 4.x
**状态**: ✅ 已对齐
