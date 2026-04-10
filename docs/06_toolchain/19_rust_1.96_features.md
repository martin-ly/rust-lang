# Rust 1.95 & 1.96 新特性详解

## 目录

- [Rust 1.95 & 1.96 新特性详解](#rust-195-新特性)

---

## Rust 1.95 新特性

### 1. if let 守卫 (if let guards)

Rust 1.95 在 match 表达式中引入了 `if let` 守卫，允许在模式匹配守卫中进行嵌套模式匹配。

#### 基本语法

```rust
match value {
    pattern if let Some(x) = option => { /* use x */ }
    _ => {}
}
```

#### 使用示例

```rust
fn process_message(msg: Message, user: Option<User>) {
    match msg {
        Message::Text(text) if let Some(u) = user => {
            println!("{} says: {}", u.name, text);
        }
        Message::Text(text) => {
            println!("Anonymous says: {}", text);
        }
        _ => {}
    }
}
```

#### 对比传统写法

**传统方式 (Rust < 1.95):**

```rust
match msg {
    Message::Text(text) => {
        if let Some(u) = user {
            println!("{} says: {}", u.name, text);
        } else {
            println!("Anonymous says: {}", text);
        }
    }
    _ => {}
}
```

**新方式 (Rust 1.95+):**

```rust
match msg {
    Message::Text(text) if let Some(u) = user => {
        println!("{} says: {}", u.name, text);
    }
    Message::Text(text) => {
        println!("Anonymous says: {}", text);
    }
    _ => {}
}
```

### 2. RangeInclusive 改进

Rust 1.95 对 `RangeInclusive` 类型进行了优化，提高了迭代性能和内存使用效率。

```rust
// 更高效的 inclusive range 迭代
for i in 1..=100 {
    // 在 1.95+ 中，编译器可以更好地优化这个循环
}
```

---

## Rust 1.96 新特性

### 1. Range 类型系统重构

Rust 1.96 引入了更严格的 Range 类型系统，明确区分不同类型的范围。

#### 新的 Range 类型

| 类型 | 语法 | 包含起始 | 包含结束 |
|------|------|----------|----------|
| `Range` | `a..b` | 是 | 否 |
| `RangeFrom` | `a..` | 是 | 无 |
| `RangeTo` | `..b` | 无 | 否 |
| `RangeFull` | `..` | 无 | 无 |
| `RangeInclusive` | `a..=b` | 是 | 是 |
| `RangeToInclusive` | `..=b` | 无 | 是 |

#### 示例代码

```rust
use std::ops::{Range, RangeInclusive, RangeFrom};

fn analyze_ranges() {
    // 标准范围 (半开区间)
    let r1: Range<i32> = 0..10;      // 包含 0-9

    // 包含范围 (闭区间)
    let r2: RangeInclusive<i32> = 0..=10;  // 包含 0-10

    // 无限范围
    let r3: RangeFrom<i32> = 5..;    // 5, 6, 7, ...

    // 使用新的类型推断
    let numbers: Vec<_> = (0..=5).collect();
    assert_eq!(numbers, vec![0, 1, 2, 3, 4, 5]);
}
```

### 2. PinCoerceUnsized trait

Rust 1.96 引入了 `PinCoerceUnsized` trait，允许对 `Pin<P>` 进行安全的强制类型转换。

#### 基本概念

```rust
use std::pin::Pin;
use std::marker::Unpin;

// 新的 trait 允许将 Pin<Box<T>> 转换为 Pin<Box<dyn Trait>>
trait PinCoerceUnsized<Target> {
    fn pin_coerce_unsized(self) -> Target;
}
```

#### 实际应用

```rust
use std::pin::Pin;
use std::future::Future;

async fn run_tasks() {
    // 现在可以更方便地转换 Pin<Box<_>> 类型
    let fut: Pin<Box<dyn Future<Output = i32>>> =
        Box::pin(async { 42 });

    // 调用异步函数
    let result = fut.await;
    assert_eq!(result, 42);
}
```

#### 与 async/await 的集成

```rust
use std::pin::Pin;

// 定义一个 trait 对象安全的异步 trait
trait AsyncProcessor {
    fn process(&self) -> Pin<Box<dyn Future<Output = Result<(), Error>> + '_>>;
}

// 实现可以被轻松地转换为 trait 对象
struct MyProcessor;

impl AsyncProcessor for MyProcessor {
    fn process(&self) -> Pin<Box<dyn Future<Output = Result<(), Error>> + '_>> {
        Box::pin(async {
            // 处理逻辑
            Ok(())
        })
    }
}
```

### 3. 元组 Coercion

Rust 1.96 允许元组类型之间的自动强制转换（coercion），简化了某些泛型代码。

#### 基本规则

```rust
// 元组 coercion 允许类型自动转换
fn process_tuple(t: (i32, i32)) {
    // 处理逻辑
}

// 现在支持更多灵活的转换
let pair: (i8, i8) = (1, 2);
// 在适当情况下可以自动转换为 (i32, i32)
```

#### 实际示例

```rust
// 使用元组 coercion 简化泛型代码
fn sum_tuple<T, U>((a, b): (T, U)) -> T
where
    T: std::ops::Add<Output = T> + From<U>,
{
    a + T::from(b)
}

fn main() {
    // 自动类型转换
    let result: i32 = sum_tuple((10i32, 20i8));
    assert_eq!(result, 30);
}
```

### 4. 新的 Lint 规则

Rust 1.96 引入了多个新的编译器警告和 lint 规则。

#### 新增的 Lints

| Lint 名称 | 级别 | 描述 |
|-----------|------|------|
| `unused_tuple_struct_fields` | Warn | 检测未使用的元组结构体字段 |
| `redundant_guards` | Warn | 检测冗余的 match 守卫 |
| `opaque_hidden_inferred_bound` | Warn | 检测不透明类型中的隐藏推断边界 |

#### 配置示例

```rust
// 在代码中控制 lint
#![allow(unused_tuple_struct_fields)]
#![warn(redundant_guards)]

// 或者使用命令行
// rustc -W unused_tuple_struct_fields main.rs
```

#### Cargo.toml 配置

```toml
[lints.rust]
unused_tuple_struct_fields = "warn"
redundant_guards = "deny"
```

---

## 迁移指南

### 从 Rust 1.94 迁移到 1.96

#### 步骤 1: 更新工具链

```bash
# 安装新版本
rustup update stable

# 切换到 1.96
rustup default 1.96.0
```

#### 步骤 2: 检查兼容性

```bash
# 运行 cargo check 检查问题
cargo check

# 检查所有 targets
cargo check --all-targets

# 检查所有 features
cargo check --all-features
```

#### 步骤 3: 修复新 Lint 警告

```bash
# 自动修复一些问题
cargo fix --edition 2021

# 允许自动应用建议的修复
cargo fix --edition 2021 --allow-dirty
```

#### 步骤 4: 测试

```bash
# 运行测试套件
cargo test

# 运行 Miri 检查 (如果适用)
cargo miri test

# 检查文档构建
cargo doc --no-deps
```

### 已知问题与解决方案

| 问题 | 解决方案 |
|------|----------|
| Range 类型推断失败 | 明确指定类型注解 |
| Pin 转换错误 | 使用新的 `PinCoerceUnsized` trait |
| 新的 lint 警告 | 根据情况修复或允许 |
| 元组 coercion 冲突 | 添加显式类型转换 |

---

## 代码示例

### 完整示例: 使用新特性重构代码

```rust
// 示例：使用 if let guards 重构错误处理

use std::collections::HashMap;

struct Config {
    values: HashMap<String, String>,
}

impl Config {
    fn get_int(&self, key: &str) -> Option<i32> {
        self.values.get(key).and_then(|v| v.parse().ok())
    }
}

// 旧写法 (Rust < 1.95)
fn process_event_old(event: Event, config: &Config) -> Result<(), Error> {
    match event {
        Event::ConfigUpdate(key) => {
            if let Some(value) = config.values.get(&key) {
                if let Ok(num) = value.parse::<i32>() {
                    if num > 0 {
                        println!("Valid config: {}", num);
                        return Ok(());
                    }
                }
            }
            Err(Error::InvalidConfig)
        }
        _ => Ok(()
    }
}

// 新写法 (Rust 1.95+)
fn process_event_new(event: Event, config: &Config) -> Result<(), Error> {
    match event {
        Event::ConfigUpdate(key)
            if let Some(value) = config.values.get(&key)
            && let Ok(num) = value.parse::<i32>()
            && num > 0 =>
        {
            println!("Valid config: {}", num);
            Ok(())
        }
        Event::ConfigUpdate(_) => Err(Error::InvalidConfig),
        _ => Ok(()),
    }
}
```

### 示例: Range 类型使用模式

```rust
use std::ops::RangeInclusive;

// 定义清晰的范围类型
fn process_range_data(data: &[i32], valid_range: RangeInclusive<i32>) -> Vec<i32> {
    data.iter()
        .filter(|&&x| valid_range.contains(&x))
        .copied()
        .collect()
}

fn main() {
    let data = vec![1, 5, 10, 15, 20, 25];

    // 使用闭区间范围
    let filtered = process_range_data(&data, 5..=20);
    assert_eq!(filtered, vec![5, 10, 15, 20]);

    // 组合多个范围
    let combined: Vec<_> = data
        .iter()
        .filter(|&&x| (1..=10).contains(&x) || (20..=30).contains(&x))
        .copied()
        .collect();
    assert_eq!(combined, vec![1, 5, 10, 20, 25]);
}
```

### 示例: Pin 与异步代码

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

// 定义自定义 Future
struct DelayedValue<T> {
    value: Option<T>,
}

impl<T> Future for DelayedValue<T> {
    type Output = T;

    fn poll(mut self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<T> {
        match self.value.take() {
            Some(v) => Poll::Ready(v),
            None => panic!("polled after completion"),
        }
    }
}

// 使用 PinCoerceUnsized 特性
fn boxed_future<T>(value: T) -> Pin<Box<dyn Future<Output = T>>> {
    Box::pin(DelayedValue { value: Some(value) })
}

async fn demo() {
    let fut = boxed_future(42);
    let result = fut.await;
    assert_eq!(result, 42);
}
```

---

## 参考链接

- [Rust 1.95 Release Notes](https://blog.rust-lang.org/2024/XX/XX/Rust-1.95.0.html)
- [Rust 1.96 Release Notes](https://blog.rust-lang.org/2025/XX/XX/Rust-1.96.0.html)
- [RFC: if let guards](https://rust-lang.github.io/rfcs/2294-if-let-guard.html)
- [PinCoerceUnsized Documentation](https://doc.rust-lang.org/std/pin/struct.Pin.html)
