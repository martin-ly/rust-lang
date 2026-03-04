# Clap 命令行解析形式化分析

> **主题**: 声明式命令行解析
>
> **形式化框架**: 类型推导 + 验证
>
> **参考**: Clap v4 Documentation

---

## 目录

- [Clap 命令行解析形式化分析](#clap-命令行解析形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 派生宏语义](#2-派生宏语义)
    - [定义 2.1 (派生展开)](#定义-21-派生展开)
    - [定理 2.1 (零运行时开销)](#定理-21-零运行时开销)
  - [3. 类型安全](#3-类型安全)
    - [3.1 值解析器](#31-值解析器)
    - [定理 3.1 (类型驱动解析)](#定理-31-类型驱动解析)
    - [3.2 验证器](#32-验证器)
    - [定理 3.2 (自定义验证)](#定理-32-自定义验证)
  - [4. 冲突检测](#4-冲突检测)
    - [定理 4.1 (编译时冲突检查)](#定理-41-编译时冲突检查)
  - [5. 生命周期管理](#5-生命周期管理)
    - [定理 5.1 (自包含参数)](#定理-51-自包含参数)
  - [6. 反例](#6-反例)
    - [反例 6.1 (生命周期陷阱)](#反例-61-生命周期陷阱)
    - [反例 6.2 (默认值类型)](#反例-62-默认值类型)

---

## 1. 引言

Clap提供:

- 派生宏(derive)和构建器(builder)两种API
- 编译时验证
- 自动生成帮助
- Shell补全

---

## 2. 派生宏语义

### 定义 2.1 (派生展开)

```rust
#[derive(Parser)]
struct Args {
    #[arg(short, long)]
    name: String,

    #[arg(default_value = "1")]
    count: u32,
}
```

展开后等价于:

```rust
impl Parser for Args {
    fn parse() -> Self {
        // 构建Command
        // 解析参数
        // 填充结构体
    }
}
```

### 定理 2.1 (零运行时开销)

> derive宏在编译时展开，无运行时开销。

∎

---

## 3. 类型安全

### 3.1 值解析器

### 定理 3.1 (类型驱动解析)

> 字段类型决定解析行为。

| 类型 | 解析行为 |
|------|----------|
| `String` | 原样存储 |
| `u32` | 解析整数，失败报错 |
| `PathBuf` | 转换为路径 |
| `bool` | 标志存在性 |
| `Option<T>` | 可选参数 |
| `Vec<T>` | 多值参数 |

```rust
#[derive(Parser)]
struct Args {
    port: u16,           // 自动验证范围
    config: PathBuf,     // 接受任何路径
    verbose: bool,       // --verbose 标志
    name: Option<String>, // 可选
    files: Vec<PathBuf>,  // 多个文件
}
```

∎

### 3.2 验证器

### 定理 3.2 (自定义验证)

> 自定义验证在解析时执行。

```rust
#[derive(Parser)]
struct Args {
    #[arg(value_parser = validate_port)]
    port: u16,
}

fn validate_port(s: &str) -> Result<u16, String> {
    let port: u16 = s.parse().map_err(|_| "invalid port")?;
    if port < 1024 {
        return Err("port must be >= 1024".to_string());
    }
    Ok(port)
}
```

∎

---

## 4. 冲突检测

### 定理 4.1 (编译时冲突检查)

> 某些冲突在编译时检测。

**检测内容**:

- 重复的short/long名称
- 无效的标识符

**运行时检测**:

- 互斥组冲突
- 缺少必需参数
- 未知参数

∎

---

## 5. 生命周期管理

### 定理 5.1 (自包含参数)

> 解析后的Args拥有所有数据。

```rust
let args = Args::parse();  // 所有权转移
// args包含所有解析后的值
// 不涉及外部引用
```

∎

---

## 6. 反例

### 反例 6.1 (生命周期陷阱)

```rust
// 错误: 引用外部数据
#[derive(Parser)]
struct Args<'a> {
    name: &'a str,  // 不支持!
}

// 正确: 使用Owned类型
#[derive(Parser)]
struct Args {
    name: String,
}
```

### 反例 6.2 (默认值类型)

```rust
// 错误: 默认值类型不匹配
#[arg(default_value = "not_a_number")]
count: u32,  // 编译错误!

// 正确
#[arg(default_value = "0")]
count: u32,
```

---

*文档版本: 1.0.0*
*定理数量: 7个*
