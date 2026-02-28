# 错误处理概念思维导图

> **创建日期**: 2026-02-24
> **最后更新**: 2026-02-28
> **状态**: ✅ 已扩展
> **版本**: Rust 1.93.1+ (Edition 2024)

---

## 错误处理全景

```mermaid
mindmap
  root((错误处理<br/>Error Handling))
    错误类型
      可恢复错误
        Result<T, E>
          Ok(T)
          Err(E)
        Option<T>
          Some(T)
          None
        自定义错误
          thiserror
          anyhow
      不可恢复错误
        panic!
        assert!
        unimplemented!
        todo!
    传播机制
      ? 运算符
        自动转换
        传播控制
      match
        穷尽检查
        模式匹配
      组合方法
        and_then
        map_err
        unwrap_or
    错误设计
      错误类型
        枚举区分
        错误链
        上下文
      错误消息
        清晰描述
        行动建议
        调试信息
      错误转换
        From trait
        Try trait
        自动转换
    处理策略
      立即处理
        局部恢复
        默认值
        重试
      传播向上
        分层处理
        边界转换
        最终处理
      终止程序
        致命错误
        不变式违反
        资源耗尽
    最佳实践
      类型安全
        禁止异常
        显式处理
        穷尽检查
      性能考虑
        错误路径优化
        栈展开成本
        panic=abort
      用户体验
        友好消息
        日志记录
        遥测上报
    工具支持
      anyhow
        应用开发
        错误链
        上下文
      thiserror
        库开发
        自定义类型
        派生宏
      eyre
        可定制报告
        Hook系统
```

---

## Result<T, E> 详解

### 基本使用

```rust
// 定义可能失败的操作
fn divide(a: f64, b: f64) -> Result<f64, MathError> {
    if b == 0.0 {
        return Err(MathError::DivideByZero);
    }
    Ok(a / b)
}

// 使用?传播
fn calculate(x: f64, y: f64) -> Result<f64, MathError> {
    let a = divide(x, y)?;
    let b = divide(y, x)?;
    Ok(a + b)
}
```

### 组合方法

| 方法 | 签名 | 用途 |
| :--- | :--- | :--- |
| `map` | `Result<T,E> -> Result<U,E>` | 转换成功值 |
| `map_err` | `Result<T,E> -> Result<T,F>` | 转换错误类型 |
| `and_then` | `Result<T,E> -> Result<U,E>` | 链式操作 |
| `or_else` | `Result<T,E> -> Result<T,F>` | 错误恢复 |
| `unwrap_or` | `Result<T,E> -> T` | 提供默认值 |
| `unwrap_or_else` | `Result<T,E> -> T` | 惰性默认值 |

---

## 错误类型设计

### 使用 thiserror (库开发)

```rust
use thiserror::Error;

#[derive(Error, Debug)]
pub enum ConfigError {
    #[error("IO错误: {0}")]
    Io(#[from] io::Error),

    #[error("解析错误: {message} (行 {line})")]
    Parse { message: String, line: usize },

    #[error("无效配置项: {0}")]
    InvalidItem(String),

    #[error("缺失必要字段: {0}")]
    MissingField(&'static str),
}
```

### 使用 anyhow (应用开发)

```rust
use anyhow::{Context, Result};

fn main() -> Result<()> {
    let config = std::fs::read_to_string("config.toml")
        .context("读取配置文件失败")?;

    let settings: Settings = toml::from_str(&config)
        .context("解析配置失败，请检查格式")?;

    run_app(settings)
        .context("应用运行失败")?;

    Ok(())
}
```

---

## panic! 使用指南

### 适用场景

| 场景 | 示例 | 原因 |
| :--- | :--- | :--- |
| 内部不变式违反 | `vec[idx]`越界 | bug，不应发生 |
| 外部假设失败 | FFI返回无效值 | 契约违反 |
| 内存分配失败 | 极端情况 | 无法恢复 |
| 快速失败开发 | `todo!()` | 占位实现 |

### 与 Result 对比

```rust
// ✅ 使用Result - 调用者决定如何处理
fn parse_port(s: &str) -> Result<u16, ParseError>;

// ✅ 使用panic - 程序有bug
fn internal_get(&self, idx: usize) -> &T {
    assert!(idx < self.len(), "索引越界");
    &self.data[idx]
}

// ❌ 错误使用 - 用户输入不应panic
fn parse_user_input(s: &str) -> i32 {
    s.parse().unwrap()  // 危险!
}
```

---

## 错误转换

### From trait

```rust
impl From<io::Error> for MyError {
    fn from(err: io::Error) -> Self {
        MyError::Io(err)
    }
}

// 自动转换
fn read_file() -> Result<String, MyError> {
    let content = std::fs::read_to_string("file.txt")?; // io::Error -> MyError
    Ok(content)
}
```

### Try trait (实验性)

```rust
// 统一处理Option和Result
fn get_or_default<T: Default>(opt: Option<T>) -> T {
    opt? // 如果是None，返回默认值
}
```

---

## 错误处理模式

### 模式1: 立即处理

```rust
match result {
    Ok(value) => value,
    Err(e) => {
        log::error!("操作失败: {}", e);
        default_value
    }
}
```

### 模式2: 传播并添加上下文

```rust
let data = operation()
    .map_err(|e| Error::with_context(e, "在初始化阶段"))?;
```

### 模式3: 错误恢复

```rust
let result = primary_op()
    .or_else(|_| fallback_op())
    .or_else(|_| default_op())?;
```

### 模式4: 聚合错误

```rust
let errors: Vec<Error> = operations
    .iter()
    .filter_map(|op| op.execute().err())
    .collect();

if !errors.is_empty() {
    return Err(Error::Multiple(errors));
}
```

---

## 性能考虑

| 机制 | 成功路径开销 | 错误路径开销 | 使用建议 |
| :--- | :--- | :--- | :--- |
| Result | 零(优化后) | 正常 | 可恢复错误 |
| panic | 零 | 极高(栈展开) | 不可恢复 |
| abort | 零 | 进程终止 | 嵌入式 |

---

## 错误处理层次

```
                            错误处理系统
                                 │
            ┌────────────────────┼────────────────────┐
            │                    │                    │
       【不可恢复】          【可恢复】            【传播机制】
            │                    │                    │
    ┌───────┴───────┐    ┌───────┴───────┐    ┌───────┴───────┐
    │               │    │               │    │               │
   panic!        abort   Result<T, E>    Option  ?操作符       try!
    │               │      │               │      │               │
  栈展开        立即终止  Ok/Err          Some/None  自动传播     早期宏
```

---

## Result类型详解

```
Result<T, E>
│
├── 变体
│   ├── Ok(T) - 成功
│   └── Err(E) - 错误
│
├── 组合子
│   ├── map - 转换Ok值
│   ├── map_err - 转换Err值
│   ├── and_then - 链式操作
│   └── unwrap_or - 默认值
│
└── 转换
    ├── unwrap() - 解包(危险)
    ├── expect() - 带消息解包
    └── unwrap_or_default()
```

| 方法 | 用途 | 安全 |
| :--- | :--- | :--- |
| `is_ok()` | 检查成功 | ✅ |
| `is_err()` | 检查错误 | ✅ |
| `unwrap()` | 强制解包 | ❌ |
| `?` | 传播错误 | ✅ |

---

## Option类型

```
Option<T>
│
├── Some(T) - 有值
├── None - 无值
│
└── 与Result转换
    ├── ok_or()
    ├── ok_or_else()
    └── transpose()
```

---

## 错误类型设计

```
错误类型
│
├── 标准库
│   ├── std::io::Error
│   └── std::fmt::Error
│
├── 自定义错误
│   └── thiserror
│
└── 动态错误
    └── anyhow
```

---

## ?操作符机制

```
?展开
│
├── Result
│   └── Ok(v) → v
│   └── Err(e) → return Err(e.into())
│
└── Option
    └── Some(v) → v
    └── None → return None
```

---

## 最佳实践

```
实践指南
│
├── 使用Result进行错误传播
├── 避免unwrap()生产代码
├── 自定义错误提供上下文
└── 使用?简化错误处理
```

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-28
**状态**: ✅ 已扩展 - 错误处理概念思维导图完整版
