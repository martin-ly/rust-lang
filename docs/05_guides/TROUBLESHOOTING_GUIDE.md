# 故障排查指南

**创建日期**: 2025-12-11
**最后更新**: 2026-02-15
**Rust 版本**: 1.93.0+ (Edition 2024)
**状态**: ✅ 已完成

---

## 📋 目录

- [故障排查指南](#故障排查指南)
  - [📋 目录](#-目录)
  - [📋 概述](#-概述)
  - [🔧 编译错误](#-编译错误)
    - [1. 所有权错误](#1-所有权错误)
    - [2. 生命周期错误](#2-生命周期错误)
    - [3. 类型不匹配](#3-类型不匹配)
  - [🐛 运行时错误](#-运行时错误)
    - [1. Panic 错误](#1-panic-错误)
    - [2. 死锁](#2-死锁)
    - [3. 内存泄漏](#3-内存泄漏)
  - [⚡ 性能问题](#-性能问题)
    - [1. 编译时间过长](#1-编译时间过长)
    - [2. 运行时性能问题](#2-运行时性能问题)
  - [🔌 网络问题](#-网络问题)
    - [1. 连接超时](#1-连接超时)
    - [2. DNS 解析失败](#2-dns-解析失败)
  - [🧪 测试问题](#-测试问题)
    - [1. 测试失败](#1-测试失败)
    - [2. 异步测试问题](#2-异步测试问题)
  - [📚 调试技巧](#-调试技巧)
    - [1. 使用 println](#1-使用-println)
    - [2. 使用 dbg! 宏](#2-使用-dbg-宏)
    - [3. 使用调试器](#3-使用调试器)
    - [4. 使用日志](#4-使用日志)
  - [🔍 常见问题 FAQ](#-常见问题-faq)
    - [Q: 如何查看详细的编译错误？](#q-如何查看详细的编译错误)
    - [Q: 如何清理编译缓存？](#q-如何清理编译缓存)
    - [Q: 如何更新依赖？](#q-如何更新依赖)
    - [Q: 如何查看依赖树？](#q-如何查看依赖树)
  - [错误码快速查找](#错误码快速查找)
  - [使用场景](#使用场景)
    - [场景1: 编译错误排查](#场景1-编译错误排查)
    - [场景2: 运行时问题诊断](#场景2-运行时问题诊断)
    - [场景3: 性能问题优化](#场景3-性能问题优化)
    - [场景4: 生产环境问题](#场景4-生产环境问题)
  - [形式化链接](#形式化链接)
  - [📚 相关资源](#-相关资源)

---

## 📋 概述

本文档提供常见问题的排查和解决方案，帮助开发者快速定位和解决问题。

---

## 🔧 编译错误

### 1. 所有权错误

**错误信息**:

```text
error[E0382]: borrow of moved value: `x`
```

**原因**: 值被移动后再次使用

**解决方案**:

```rust
// ❌ 错误
let x = String::from("hello");
let y = x;  // x 被移动
println!("{}", x);  // 错误！

// ✅ 正确
let x = String::from("hello");
let y = x.clone();  // 克隆而非移动
println!("{}", x);

// 或使用引用
let x = String::from("hello");
let y = &x;  // 借用而非移动
println!("{}", x);
```

### 2. 生命周期错误

**错误信息**:

```text
error[E0597]: `x` does not live long enough
```

**原因**: 引用的生命周期不够长

**解决方案**:

```rust
// ❌ 错误
fn get_ref() -> &str {
    let s = String::from("hello");
    &s  // s 在函数结束时被丢弃
}

// ✅ 正确
fn get_ref() -> String {
    let s = String::from("hello");
    s  // 返回所有权
}

// 或使用生命周期参数
fn get_ref<'a>(s: &'a str) -> &'a str {
    s
}
```

### 3. 类型不匹配

**错误信息**:

```
error[E0308]: mismatched types
```

**原因**: 类型不匹配

**解决方案**:

```rust
// ❌ 错误
let x: i32 = "42".parse().unwrap();  // 需要指定类型

// ✅ 正确
let x: i32 = "42".parse().unwrap();
// 或
let x = "42".parse::<i32>().unwrap();
```

---

## 🐛 运行时错误

### 1. Panic 错误

**错误信息**:

```
thread 'main' panicked at 'index out of bounds'
```

**原因**: 数组越界访问

**解决方案**:

```rust
// ❌ 错误
let arr = [1, 2, 3];
let value = arr[10];  // panic!

// ✅ 正确
let arr = [1, 2, 3];
if let Some(value) = arr.get(10) {
    // 安全访问
} else {
    // 处理越界情况
}
```

### 2. 死锁

**症状**: 程序挂起，无响应

**原因**: 多个锁的获取顺序不一致

**解决方案**:

```rust
// ❌ 可能导致死锁
let mutex1 = Arc::new(Mutex::new(0));
let mutex2 = Arc::new(Mutex::new(0));

// 线程1: 先锁 mutex1，再锁 mutex2
// 线程2: 先锁 mutex2，再锁 mutex1

// ✅ 解决方案：统一锁的顺序
// 所有线程都按相同顺序获取锁
```

### 3. 内存泄漏

**症状**: 内存使用持续增长

**原因**: 循环引用（Rc）或未释放资源

**解决方案**:

```rust
// ❌ 循环引用
use std::rc::Rc;
use std::cell::RefCell;

struct Node {
    next: Option<Rc<RefCell<Node>>>,
}

// ✅ 使用 Weak 打破循环
use std::rc::{Rc, Weak};

struct Node {
    next: Option<Weak<RefCell<Node>>>,
}
```

---

## ⚡ 性能问题

### 1. 编译时间过长

**原因**: 依赖过多或代码结构问题

**解决方案**:

```toml
# Cargo.toml
[profile.dev]
incremental = true  # 启用增量编译

# 使用 workspace 依赖
[dependencies]
serde = { workspace = true }
```

### 2. 运行时性能问题

**诊断工具**:

```bash
# 使用 perf (Linux)
perf record --call-graph=dwarf ./target/release/my_app
perf report

# 使用 cargo-flamegraph
cargo flamegraph --bin my_app
```

**优化技巧**:

- 使用 `release` 模式编译
- 启用 LTO（Link Time Optimization）
- 使用 `Vec::with_capacity` 预分配
- 避免不必要的克隆

---

## 🔌 网络问题

### 1. 连接超时

**错误信息**:

```
error: timeout while waiting for connection
```

**解决方案**:

```rust
use tokio::time::{timeout, Duration};

// 设置超时
match timeout(Duration::from_secs(5), connect()).await {
    Ok(result) => result?,
    Err(_) => {
        eprintln!("连接超时");
        // 处理超时
    }
}
```

### 2. DNS 解析失败

**错误信息**:

```
error: failed to resolve hostname
```

**Rust 1.93 改进**：Rust 1.93 更新了 musl 到 1.2.5，显著改进了 DNS 解析器的可靠性，特别是对于大型 DNS 记录和递归名称服务器。如果使用 musl 目标，升级到 Rust 1.93 可以解决许多 DNS 解析问题。

**解决方案**:

```rust
use std::net::TcpStream;

// Rust 1.93+ (musl 1.2.5) 改进了 DNS 解析
// 对于静态链接的 musl 二进制文件，DNS 解析更可靠
let stream = TcpStream::connect("example.com:80")?;

// 或者使用异步 DNS 解析
use tokio::net::TcpStream;

let stream = TcpStream::connect("example.com:80").await?;
```

**如果仍遇到问题，可以添加重试机制**:

```rust
use std::net::TcpStream;
use std::time::Duration;

// 添加重试机制
let mut retries = 3;
while retries > 0 {
    match TcpStream::connect_timeout(
        &"example.com:80".parse()?,
        Duration::from_secs(5)
    ) {
        Ok(stream) => {
            println!("连接成功");
            break;
        }
        Err(e) => {
            retries -= 1;
            if retries == 0 {
                return Err(e);
            }
            std::thread::sleep(Duration::from_secs(1));
        }
    }
}
```

**musl 1.2.5 改进说明**（Rust 1.93+）：

- 改进了 DNS 解析器，特别是对于大型 DNS 记录
- 更好地处理递归名称服务器
- 提高了静态链接 musl 二进制文件的网络可靠性

**兼容性检查**：

- 确保使用 libc >= 0.2.146（如果使用 musl 目标）

**升级建议**：

- 如果使用 musl 目标且遇到 DNS 解析问题，强烈建议升级到 Rust 1.93.0+

---

## 🧪 测试问题

### 1. 测试失败

**诊断步骤**:

1. 检查测试输出
2. 运行单个测试: `cargo test test_name`
3. 启用详细输出: `cargo test -- --nocapture`
4. 检查测试环境

### 2. 异步测试问题

**错误信息**:

```
error: future cannot be sent between threads safely
```

**解决方案**:

```rust
// ✅ 确保 Future 是 Send
#[tokio::test]
async fn test_async() {
    // 使用 Arc 而非 Rc
    let data = Arc::new(Mutex::new(0));
    // ...
}
```

---

## 📚 调试技巧

### 1. 使用 println

```rust
println!("调试信息: {:?}", value);
```

### 2. 使用 dbg! 宏

```rust
let value = dbg!(calculate_value());
```

### 3. 使用调试器

```bash
# 使用 gdb
gdb ./target/debug/my_app

# 使用 lldb (macOS)
lldb ./target/debug/my_app
```

### 4. 使用日志

```rust
use tracing::{info, error, warn};

info!("信息: {}", value);
warn!("警告: {}", value);
error!("错误: {}", value);
```

---

## 🔍 常见问题 FAQ

### Q: 如何查看详细的编译错误？

A: 使用 `cargo build --verbose` 或 `RUST_BACKTRACE=1 cargo run`

### Q: 如何清理编译缓存？

A: 使用 `cargo clean` 清理所有编译产物

### Q: 如何更新依赖？

A: 使用 `cargo update` 更新依赖版本

### Q: 如何查看依赖树？

A: 使用 `cargo tree` 查看依赖关系

---

## 错误码快速查找

常见错误码 → 本项目文档映射见 [ERROR_CODE_MAPPING.md](../02_reference/ERROR_CODE_MAPPING.md)。

---

## 使用场景

### 场景1: 编译错误排查

遇到编译错误时快速定位解决：

1. 查看错误码，参考 [错误码快速查找](#错误码快速查找)
2. 根据错误类型查阅 [编译错误](#-编译错误) 章节
3. 使用 [调试技巧](#-调试技巧) 辅助定位

### 场景2: 运行时问题诊断

程序运行异常时的排查流程：

- 使用 `RUST_BACKTRACE=1` 获取堆栈信息
- 查阅 [运行时错误](#-运行时错误) 常见场景
- 应用 [调试技巧](#-调试技巧) 逐步定位

### 场景3: 性能问题优化

程序性能不达标的排查：

1. 使用 [perf 或 flamegraph](#2-运行时性能问题) 定位热点
2. 参考 [PERFORMANCE_TUNING_GUIDE.md](./PERFORMANCE_TUNING_GUIDE.md) 优化
3. 检查是否存在 [编译时间过长](#1-编译时间过长) 问题

### 场景4: 生产环境问题

生产环境故障应急处理：

- 使用日志系统（[使用日志](#4-使用日志)）收集信息
- 检查 [网络问题](#-网络问题) 连接状态
- 应用 [常见问题 FAQ](#-常见问题-faq) 快速解决方案

---

## 形式化链接

| 链接类型 | 目标文档 |
| :--- | :--- |
| **核心模块** | [C01 所有权](../../crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md) |
| | [C05 线程](../../crates/c05_threads/docs/00_MASTER_INDEX.md) |
| | [C06 异步](../../crates/c06_async/docs/00_MASTER_INDEX.md) |
| | [C10 网络](../../crates/c10_networks/docs/00_MASTER_INDEX.md) |
| **错误参考** | [ERROR_CODE_MAPPING.md](../02_reference/ERROR_CODE_MAPPING.md) |
| **相关指南** | [PERFORMANCE_TUNING_GUIDE.md](./PERFORMANCE_TUNING_GUIDE.md) |
| | [TESTING_COVERAGE_GUIDE.md](./TESTING_COVERAGE_GUIDE.md) |
| | [BEST_PRACTICES.md](./BEST_PRACTICES.md) |
| **外部资源** | [Rust错误索引](https://doc.rust-lang.org/error-index.html) |

---

## 📚 相关资源

- [Rust 错误索引](https://doc.rust-lang.org/error-index.html)
- [Rust 常见问题](https://doc.rust-lang.org/book/appendix-06-translation.html)
- [Rust 性能书](https://nnethercote.github.io/perf-book/)

---

**维护者**: Rust 学习项目团队
**状态**: ✅ 持续更新
**最后更新**: 2026-01-26
