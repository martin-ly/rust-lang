# 🔧 故障排查指南 (Troubleshooting Guide)

> **文档定位**: Rust 学习和开发中常见问题的诊断和解决方案  
> **使用方式**: 遇到问题时快速查找解决方案  
> **相关文档**: [FAQ](./crates/) | [快速参考](./QUICK_REFERENCE.md) | [贡献指南](./CONTRIBUTING.md)

**最后更新**: 2025-10-19  
**适用版本**: Rust 1.90+

---

## 📋 目录

- [🔧 故障排查指南 (Troubleshooting Guide)](#-故障排查指南-troubleshooting-guide)
  - [📋 目录](#-目录)
  - [编译错误](#编译错误)
    - [所有权和借用错误](#所有权和借用错误)
      - [错误: "value moved here"](#错误-value-moved-here)
      - [错误: "cannot borrow as mutable more than once"](#错误-cannot-borrow-as-mutable-more-than-once)
      - [错误: "cannot borrow as mutable because it is also borrowed as immutable"](#错误-cannot-borrow-as-mutable-because-it-is-also-borrowed-as-immutable)
    - [生命周期错误](#生命周期错误)
      - [错误: "lifetime may not live long enough"](#错误-lifetime-may-not-live-long-enough)
    - [类型错误](#类型错误)
      - [错误: "mismatched types"](#错误-mismatched-types)
      - [错误: "trait bound not satisfied"](#错误-trait-bound-not-satisfied)
  - [运行时错误](#运行时错误)
    - [panic! 错误](#panic-错误)
      - [错误: "index out of bounds"](#错误-index-out-of-bounds)
      - [错误: "unwrap on None"](#错误-unwrap-on-none)
    - [并发错误](#并发错误)
      - [错误: "deadlock detected"](#错误-deadlock-detected)
      - [错误: "data race"](#错误-data-race)
  - [性能问题](#性能问题)
    - [慢速编译](#慢速编译)
    - [运行时性能低](#运行时性能低)
  - [依赖问题](#依赖问题)
    - [依赖版本冲突](#依赖版本冲突)
    - [依赖下载失败](#依赖下载失败)
  - [工具链问题](#工具链问题)
    - [rustup 问题](#rustup-问题)
      - [错误: "toolchain not installed"](#错误-toolchain-not-installed)
    - [cargo 问题](#cargo-问题)
      - [错误: "could not find Cargo.toml"](#错误-could-not-find-cargotoml)
  - [IDE 问题](#ide-问题)
    - [rust-analyzer 问题](#rust-analyzer-问题)
      - [问题: rust-analyzer 无法工作](#问题-rust-analyzer-无法工作)
  - [测试问题](#测试问题)
    - [测试失败](#测试失败)
      - [错误: "test result: FAILED"](#错误-test-result-failed)
  - [🔗 更多帮助](#-更多帮助)
    - [社区资源](#社区资源)
    - [文档资源](#文档资源)
    - [项目文档](#项目文档)
  - [📝 贡献故障排查案例](#-贡献故障排查案例)

---

## 编译错误

### 所有权和借用错误

#### 错误: "value moved here"

**症状**:

```rust
error[E0382]: use of moved value: `s1`
let s1 = String::from("hello");
let s2 = s1;
println!("{}", s1);  // 错误
```

**原因**: 值的所有权已经转移给了 `s2`。

**解决方案**:

```rust
// 方案1: 使用克隆
let s1 = String::from("hello");
let s2 = s1.clone();
println!("{}, {}", s1, s2);  // OK

// 方案2: 使用引用
let s1 = String::from("hello");
let s2 = &s1;
println!("{}, {}", s1, s2);  // OK

// 方案3: 重新安排代码顺序
let s1 = String::from("hello");
println!("{}", s1);
let s2 = s1;  // 之后再移动
```

#### 错误: "cannot borrow as mutable more than once"

**症状**:

```rust
error[E0499]: cannot borrow `s` as mutable more than once at a time
let mut s = String::from("hello");
let r1 = &mut s;
let r2 = &mut s;  // 错误
```

**原因**: 同一时间只能有一个可变引用。

**解决方案**:

```rust
// 方案1: 分开作用域
let mut s = String::from("hello");
{
    let r1 = &mut s;
    // 使用 r1
}  // r1 在这里离开作用域
let r2 = &mut s;  // OK

// 方案2: 使用 RefCell (内部可变性)
use std::cell::RefCell;
let s = RefCell::new(String::from("hello"));
let mut r1 = s.borrow_mut();
drop(r1);  // 显式释放
let mut r2 = s.borrow_mut();  // OK
```

#### 错误: "cannot borrow as mutable because it is also borrowed as immutable"

**症状**:

```rust
error[E0502]: cannot borrow `s` as mutable because it is also borrowed as immutable
let mut s = String::from("hello");
let r1 = &s;
let r2 = &mut s;  // 错误
```

**原因**: 不可变引用存在时，不能创建可变引用。

**解决方案**:

```rust
// 方案1: 先使用完不可变引用
let mut s = String::from("hello");
let r1 = &s;
println!("{}", r1);  // 最后一次使用 r1
let r2 = &mut s;  // OK（NLL - Non-Lexical Lifetimes）

// 方案2: 重新组织代码
let mut s = String::from("hello");
{
    let r1 = &s;
    println!("{}", r1);
}  // r1 离开作用域
let r2 = &mut s;  // OK
```

### 生命周期错误

#### 错误: "lifetime may not live long enough"

**症状**:

```rust
error: lifetime may not live long enough
fn longest(x: &str, y: &str) -> &str {
    if x.len() > y.len() { x } else { y }
}
```

**原因**: 编译器无法确定返回值的生命周期。

**解决方案**:

```rust
// 显式标注生命周期
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}

// 或者返回拥有所有权的类型
fn longest_owned(x: &str, y: &str) -> String {
    if x.len() > y.len() { 
        x.to_string() 
    } else { 
        y.to_string() 
    }
}
```

### 类型错误

#### 错误: "mismatched types"

**症状**:

```rust
error[E0308]: mismatched types
expected `i32`, found `&i32`
let x: i32 = 5;
let y: i32 = &x;  // 错误
```

**原因**: 类型不匹配。

**解决方案**:

```rust
// 方案1: 解引用
let x: i32 = 5;
let y: i32 = *&x;  // OK

// 方案2: 使用正确的类型
let x: i32 = 5;
let y: &i32 = &x;  // OK

// 方案3: 使用类型转换
let x: i32 = 5;
let y: i64 = x as i64;  // OK
```

#### 错误: "trait bound not satisfied"

**症状**:

```rust
error[E0277]: the trait bound `T: std::fmt::Display` is not satisfied
fn print<T>(val: T) {
    println!("{}", val);  // 错误
}
```

**原因**: 泛型类型没有实现所需的 trait。

**解决方案**:

```rust
// 添加 trait 约束
fn print<T: std::fmt::Display>(val: T) {
    println!("{}", val);  // OK
}

// 或使用 where 子句
fn print<T>(val: T) 
where 
    T: std::fmt::Display 
{
    println!("{}", val);  // OK
}

// 使用 Debug trait（更通用）
fn print<T: std::fmt::Debug>(val: T) {
    println!("{:?}", val);  // OK
}
```

---

## 运行时错误

### panic! 错误

#### 错误: "index out of bounds"

**症状**:

```rust
thread 'main' panicked at 'index out of bounds: the len is 3 but the index is 5'
let v = vec![1, 2, 3];
let x = v[5];  // panic!
```

**原因**: 访问数组越界。

**解决方案**:

```rust
// 方案1: 使用 get 方法
let v = vec![1, 2, 3];
match v.get(5) {
    Some(x) => println!("{}", x),
    None => println!("Index out of bounds"),
}

// 方案2: 先检查长度
let v = vec![1, 2, 3];
let index = 5;
if index < v.len() {
    println!("{}", v[index]);
} else {
    println!("Index out of bounds");
}

// 方案3: 使用迭代器
let v = vec![1, 2, 3];
for item in &v {
    println!("{}", item);
}
```

#### 错误: "unwrap on None"

**症状**:

```rust
thread 'main' panicked at 'called `Option::unwrap()` on a `None` value'
let x: Option<i32> = None;
let y = x.unwrap();  // panic!
```

**原因**: 对 `None` 值调用 `unwrap()`。

**解决方案**:

```rust
// 方案1: 使用 match
let x: Option<i32> = None;
let y = match x {
    Some(val) => val,
    None => 0,  // 默认值
};

// 方案2: 使用 unwrap_or
let x: Option<i32> = None;
let y = x.unwrap_or(0);

// 方案3: 使用 unwrap_or_else
let x: Option<i32> = None;
let y = x.unwrap_or_else(|| {
    println!("Using default value");
    0
});

// 方案4: 使用 if let
let x: Option<i32> = None;
if let Some(y) = x {
    println!("{}", y);
} else {
    println!("No value");
}

// 方案5: 使用 ? 运算符（在返回 Result/Option 的函数中）
fn process(x: Option<i32>) -> Option<i32> {
    let y = x?;  // 如果是 None，提前返回
    Some(y * 2)
}
```

### 并发错误

#### 错误: "deadlock detected"

**症状**:

```rust
// 程序挂起，不继续执行
use std::sync::Mutex;
let m1 = Mutex::new(0);
let m2 = Mutex::new(0);
let _g1 = m1.lock().unwrap();
let _g2 = m2.lock().unwrap();
// 另一个线程以相反顺序获取锁
```

**原因**: 两个或多个线程互相等待对方释放锁。

**解决方案**:

```rust
// 方案1: 统一锁的获取顺序
use std::sync::Mutex;
use std::thread;

let m1 = Arc::new(Mutex::new(0));
let m2 = Arc::new(Mutex::new(0));

// 所有线程都按相同顺序获取锁
let m1_clone = Arc::clone(&m1);
let m2_clone = Arc::clone(&m2);
thread::spawn(move || {
    let _g1 = m1_clone.lock().unwrap();
    let _g2 = m2_clone.lock().unwrap();
    // ...
});

// 方案2: 使用 try_lock
let m1 = Mutex::new(0);
let m2 = Mutex::new(0);
if let Ok(_g1) = m1.try_lock() {
    if let Ok(_g2) = m2.try_lock() {
        // 两个锁都获取成功
    }
}

// 方案3: 使用更高层的抽象（如 Channel）
use std::sync::mpsc;
let (tx, rx) = mpsc::channel();
// 通过消息传递避免共享状态
```

#### 错误: "data race"

**症状**:

```rust
// 编译错误（Rust 防止数据竞争）
error[E0277]: `Rc<Mutex<i32>>` cannot be sent between threads safely
```

**原因**: 尝试在多线程间共享非线程安全的类型。

**解决方案**:

```rust
// 方案1: 使用 Arc 代替 Rc
use std::sync::{Arc, Mutex};
use std::thread;

let counter = Arc::new(Mutex::new(0));
let counter2 = Arc::clone(&counter);

thread::spawn(move || {
    let mut num = counter2.lock().unwrap();
    *num += 1;
});

// 方案2: 使用原子类型
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

let counter = Arc::new(AtomicUsize::new(0));
let counter2 = Arc::clone(&counter);

thread::spawn(move || {
    counter2.fetch_add(1, Ordering::SeqCst);
});
```

---

## 性能问题

### 慢速编译

**症状**: 编译时间过长。

**诊断**:

```bash
# 查看编译时间分析
cargo build --timings

# 使用增量编译（默认启用）
CARGO_INCREMENTAL=1 cargo build

# 查看依赖树
cargo tree
```

**解决方案**:

```rust
// 1. 减少泛型单态化
// 不好: 每个类型都生成一份代码
fn process<T: Display>(val: T) { /* ... */ }

// 好: 使用 trait 对象
fn process(val: &dyn Display) { /* ... */ }

// 2. 使用工作空间分割项目
// Cargo.toml
[workspace]
members = ["module1", "module2"]

// 3. 启用并行编译
// .cargo/config.toml
[build]
jobs = 8  # 根据 CPU 核心数调整

// 4. 使用 sccache 缓存编译结果
# 安装 sccache
cargo install sccache
# 设置环境变量
export RUSTC_WRAPPER=sccache
```

### 运行时性能低

**症状**: 程序运行缓慢。

**诊断**:

```bash
# 使用 release 模式编译
cargo build --release

# 使用性能分析工具
cargo install flamegraph
cargo flamegraph

# 使用 criterion 进行基准测试
cargo bench
```

**解决方案**:

```rust
// 1. 避免不必要的克隆
// 不好
fn process(data: Vec<i32>) -> Vec<i32> {
    data.clone()  // 不必要的克隆
}

// 好
fn process(data: &[i32]) -> Vec<i32> {
    data.to_vec()  // 只在需要时克隆
}

// 2. 使用迭代器（零成本抽象）
// 不好
let mut result = Vec::new();
for i in 0..1000 {
    result.push(i * 2);
}

// 好
let result: Vec<_> = (0..1000).map(|i| i * 2).collect();

// 3. 使用 Vec::with_capacity 预分配
// 不好
let mut v = Vec::new();
for i in 0..1000 {
    v.push(i);
}

// 好
let mut v = Vec::with_capacity(1000);
for i in 0..1000 {
    v.push(i);
}

// 4. 避免频繁的字符串拼接
// 不好
let mut s = String::new();
for i in 0..1000 {
    s = s + &i.to_string();  // 每次都重新分配
}

// 好
let mut s = String::with_capacity(4000);
for i in 0..1000 {
    s.push_str(&i.to_string());
}

// 5. 使用引用避免移动
// 不好
fn process(large_data: Vec<u8>) {
    // 数据被移动
}

// 好
fn process(large_data: &[u8]) {
    // 只传递引用
}
```

---

## 依赖问题

### 依赖版本冲突

**症状**:

```text
error: failed to select a version for `serde`
```

**诊断**:

```bash
# 查看依赖树
cargo tree

# 更新依赖
cargo update
```

**解决方案**:

```toml
# Cargo.toml

# 1. 使用具体版本
[dependencies]
serde = "=1.0.195"  # 精确版本

# 2. 使用补丁
[patch.crates-io]
serde = { git = "https://github.com/serde-rs/serde", branch = "master" }

# 3. 使用兼容版本范围
[dependencies]
serde = "^1.0"  # 兼容 1.x 版本
```

### 依赖下载失败

**症状**:

```text
error: failed to download from `https://crates.io/...`
```

**解决方案**:

```bash
# 1. 更换国内镜像（.cargo/config.toml）
[source.crates-io]
replace-with = 'tuna'

[source.tuna]
registry = "https://mirrors.tuna.tsinghua.edu.cn/git/crates.io-index.git"

# 2. 使用代理
export HTTP_PROXY=http://proxy.example.com:8080
export HTTPS_PROXY=http://proxy.example.com:8080

# 3. 清理缓存重试
cargo clean
rm -rf ~/.cargo/registry
cargo build
```

---

## 工具链问题

### rustup 问题

#### 错误: "toolchain not installed"

**症状**:

```bash
error: toolchain 'stable-x86_64-unknown-linux-gnu' is not installed
```

**解决方案**:

```bash
# 安装工具链
rustup install stable

# 更新工具链
rustup update

# 设置默认工具链
rustup default stable

# 查看已安装的工具链
rustup show
```

### cargo 问题

#### 错误: "could not find Cargo.toml"

**症状**:

```bash
error: could not find `Cargo.toml` in `/path/to/dir` or any parent directory
```

**解决方案**:

```bash
# 确保在项目根目录
cd /path/to/project

# 或创建新项目
cargo new my_project
cd my_project

# 或初始化现有目录
cargo init
```

---

## IDE 问题

### rust-analyzer 问题

#### 问题: rust-analyzer 无法工作

**症状**: IDE 中没有代码补全、类型提示等。

**诊断**:

```bash
# 检查 rust-analyzer 是否安装
rust-analyzer --version

# 检查项目是否能编译
cargo check
```

**解决方案**:

```bash
# 1. 安装/更新 rust-analyzer
rustup component add rust-analyzer

# 2. 重启 VS Code 的语言服务器
# VS Code: Ctrl+Shift+P -> "Restart Language Server"

# 3. 清理并重建项目
cargo clean
cargo build

# 4. 检查 VS Code 设置
# settings.json
{
    "rust-analyzer.checkOnSave.command": "clippy",
    "rust-analyzer.cargo.loadOutDirsFromCheck": true
}
```

---

## 测试问题

### 测试失败

#### 错误: "test result: FAILED"

**症状**:

```bash
running 1 test
test tests::it_works ... FAILED

failures:
    tests::it_works
```

**诊断**:

```bash
# 运行单个测试
cargo test it_works

# 显示测试输出
cargo test -- --nocapture

# 显示详细信息
cargo test -- --show-output
```

**解决方案**:

```rust
// 1. 使用 assert_eq! 显示差异
#[test]
fn test_addition() {
    assert_eq!(2 + 2, 4);  // 清晰的错误消息
}

// 2. 使用自定义错误消息
#[test]
fn test_with_message() {
    assert!(2 + 2 == 4, "Math is broken! 2 + 2 = {}", 2 + 2);
}

// 3. 测试 panic
#[test]
#[should_panic(expected = "divide by zero")]
fn test_panic() {
    divide(10, 0);
}

// 4. 测试 Result
#[test]
fn test_result() -> Result<(), String> {
    if 2 + 2 == 4 {
        Ok(())
    } else {
        Err(String::from("Math is broken"))
    }
}
```

---

## 🔗 更多帮助

### 社区资源

- **Rust 官方论坛**: [users.rust-lang.org](https://users.rust-lang.org/)
- **Stack Overflow**: [rust 标签](https://stackoverflow.com/questions/tagged/rust)
- **Rust Discord**: [discord.gg/rust-lang](https://discord.gg/rust-lang)
- **Reddit**: [r/rust](https://www.reddit.com/r/rust/)

### 文档资源

- **Rust 错误索引**: [doc.rust-lang.org/error-index.html](https://doc.rust-lang.org/error-index.html)
- **The Rust Book**: [doc.rust-lang.org/book/](https://doc.rust-lang.org/book/)
- **Rust By Example**: [doc.rust-lang.org/rust-by-example/](https://doc.rust-lang.org/rust-by-example/)

### 项目文档

- **FAQ**: 查看各模块的 FAQ.md
- **快速参考**: [QUICK_REFERENCE.md](./QUICK_REFERENCE.md)
- **学习路径**: [README.md](./README.md)

---

## 📝 贡献故障排查案例

如果你遇到了新的问题并找到了解决方案，欢迎贡献到本文档：

1. Fork 本项目
2. 添加你的案例到相应分类
3. 提交 Pull Request

查看 [贡献指南](./CONTRIBUTING.md) 了解更多。

---

**遇到问题？不要慌！** 🚀

大多数 Rust 错误都有清晰的错误消息和解决方案。仔细阅读错误信息，通常就能找到解决办法！

**最后更新**: 2025-10-19  
**维护团队**: Rust 学习社区  
**版本**: v1.0
