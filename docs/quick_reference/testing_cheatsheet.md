# 🧪 Rust 测试速查卡

> **快速参考** | [完整文档](../../docs/rust-formal-engineering-system/05_software_engineering/07_testing/) | [代码示例](../../crates/)
> **最后更新**: 2025-11-15 | **Rust 版本**: 1.91.1+ | **Edition**: 2024

---

## 📋 目录

- [🧪 Rust 测试速查卡](#-rust-测试速查卡)
  - [📋 目录](#-目录)
  - [📋 测试类型概览](#-测试类型概览)
  - [🔬 单元测试（Unit Tests）](#-单元测试unit-tests)
    - [基本结构](#基本结构)
    - [断言宏](#断言宏)
    - [测试失败和 panic](#测试失败和-panic)
    - [使用 Result 类型](#使用-result-类型)
    - [忽略测试](#忽略测试)
    - [测试组织](#测试组织)
  - [🔗 集成测试（Integration Tests）](#-集成测试integration-tests)
    - [目录结构](#目录结构)
    - [基本集成测试](#基本集成测试)
    - [公共测试模块](#公共测试模块)
    - [测试子模块](#测试子模块)
  - [📚 文档测试（Doc Tests）](#-文档测试doc-tests)
    - [基本文档测试](#基本文档测试)
    - [隐藏辅助代码](#隐藏辅助代码)
    - [忽略文档测试](#忽略文档测试)
    - [编译但不运行](#编译但不运行)
  - [⚡ 性能测试（Benchmark Tests）](#-性能测试benchmark-tests)
    - [Cargo.toml 配置](#cargotoml-配置)
    - [Criterion 基准测试](#criterion-基准测试)
    - [比较基准测试](#比较基准测试)
    - [异步基准测试](#异步基准测试)
    - [运行基准测试](#运行基准测试)
  - [🛠️ 测试工具和库](#️-测试工具和库)
    - [常用测试库](#常用测试库)
    - [异步测试](#异步测试)
    - [属性测试（Proptest）](#属性测试proptest)
    - [Mock 测试（Mockall）](#mock-测试mockall)
    - [参数化测试（Rstest）](#参数化测试rstest)
    - [模糊测试（Cargo-fuzz）](#模糊测试cargo-fuzz)
  - [🎯 测试最佳实践](#-测试最佳实践)
    - [测试金字塔](#测试金字塔)
    - [测试驱动开发（TDD）](#测试驱动开发tdd)
    - [测试命名](#测试命名)
    - [测试组织](#测试组织-1)
    - [测试私有函数](#测试私有函数)
    - [测试并发代码](#测试并发代码)
    - [测试文件 I/O](#测试文件-io)
  - [📊 测试覆盖率](#-测试覆盖率)
    - [使用 cargo-tarpaulin](#使用-cargo-tarpaulin)
    - [tarpaulin.toml 配置](#tarpaulintoml-配置)
  - [🚀 运行测试](#-运行测试)
    - [基本命令](#基本命令)
    - [测试输出](#测试输出)
    - [并行控制](#并行控制)
  - [🔍 测试调试](#-测试调试)
    - [打印调试信息](#打印调试信息)
    - [使用断言消息](#使用断言消息)
    - [测试超时](#测试超时)
  - [📝 测试模式速查](#-测试模式速查)
    - [测试 Result 类型](#测试-result-类型)
    - [测试 Option 类型](#测试-option-类型)
    - [测试浮点数（近似相等）](#测试浮点数近似相等)
    - [测试集合](#测试集合)
  - [🎓 常见测试场景](#-常见测试场景)
    - [测试错误处理](#测试错误处理)
    - [测试生命周期](#测试生命周期)
    - [测试泛型函数](#测试泛型函数)
    - [测试 trait 实现](#测试-trait-实现)
  - [🔄 CI/CD 集成](#-cicd-集成)
    - [GitHub Actions 测试](#github-actions-测试)
    - [测试覆盖率 CI](#测试覆盖率-ci)
    - [性能测试 CI](#性能测试-ci)
  - [🎓 高级测试模式](#-高级测试模式)
    - [快照测试](#快照测试)
    - [金标准测试（Golden Tests）](#金标准测试golden-tests)
    - [测试夹具（Fixtures）](#测试夹具fixtures)
    - [参数化测试（高级）](#参数化测试高级)
    - [测试并发安全性](#测试并发安全性)
    - [使用 Loom 测试并发](#使用-loom-测试并发)
  - [🔧 测试工具速查](#-测试工具速查)
    - [常用测试命令](#常用测试命令)
    - [测试覆盖率工具](#测试覆盖率工具)
    - [性能分析工具](#性能分析工具)
  - [📚 相关资源](#-相关资源)
    - [官方文档](#官方文档)
    - [测试框架和工具](#测试框架和工具)
    - [测试覆盖率](#测试覆盖率)
    - [模糊测试](#模糊测试)
    - [并发测试](#并发测试)
    - [相关文档](#相关文档)

---

## 📋 测试类型概览

```text
单元测试    → src/ 文件中的 #[cfg(test)] mod tests
集成测试    → tests/ 目录下的独立文件
文档测试    → 文档注释中的代码块
性能测试    → benches/ 目录下的基准测试
```

---

## 🔬 单元测试（Unit Tests）

### 基本结构

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
```

### 断言宏

```rust
#[test]
fn test_assertions() {
    // 基本断言
    assert!(true);
    assert_eq!(2 + 2, 4);
    assert_ne!(2 + 2, 5);

    // 带消息的断言
    assert!(value > 0, "值必须大于 0，得到 {}", value);
    assert_eq!(a, b, "a ({}) 应该等于 b ({})", a, b);

    // Option/Result 断言
    assert!(result.is_ok());
    assert!(option.is_some());
    assert_eq!(result.unwrap(), expected);
}
```

### 测试失败和 panic

```rust
#[test]
#[should_panic]
fn test_panics() {
    panic!("这个测试应该 panic");
}

#[test]
#[should_panic(expected = "值超出范围")]
fn test_expected_panic() {
    if true {
        panic!("值超出范围");
    }
}
```

### 使用 Result 类型

```rust
#[test]
fn test_with_result() -> Result<(), String> {
    if 2 + 2 == 4 {
        Ok(())
    } else {
        Err(String::from("数学出错了"))
    }
}
```

### 忽略测试

```rust
#[test]
#[ignore]
fn expensive_test() {
    // 只在 cargo test -- --ignored 时运行
}

#[test]
#[ignore = "需要网络连接"]
fn network_test() {
    // 被忽略的测试
}
```

### 测试组织

```rust
#[cfg(test)]
mod tests {
    use super::*;

    mod add_tests {
        use super::*;

        #[test]
        fn test_add_positive() {
            assert_eq!(add(2, 3), 5);
        }

        #[test]
        fn test_add_negative() {
            assert_eq!(add(-2, -3), -5);
        }
    }

    mod multiply_tests {
        use super::*;

        #[test]
        fn test_multiply() {
            assert_eq!(multiply(2, 3), 6);
        }
    }
}
```

---

## 🔗 集成测试（Integration Tests）

### 目录结构

```text
my_project/
├── Cargo.toml
├── src/
│   └── lib.rs
└── tests/
    ├── integration_test.rs
    └── common/
        └── mod.rs
```

### 基本集成测试

```rust
// tests/integration_test.rs
use my_project;

#[test]
fn test_integration() {
    let result = my_project::add(2, 3);
    assert_eq!(result, 5);
}
```

### 公共测试模块

```rust
// tests/common/mod.rs
pub fn setup() {
    println!("设置测试环境");
}

pub fn teardown() {
    println!("清理测试环境");
}

// tests/integration_test.rs
mod common;

#[test]
fn test_with_setup() {
    common::setup();
    // 测试代码
    common::teardown();
}
```

### 测试子模块

```rust
// tests/integration/
//   ├── mod.rs
//   ├── api_tests.rs
//   └── database_tests.rs

// tests/integration/mod.rs
mod api_tests;
mod database_tests;

// tests/integration/api_tests.rs
#[test]
fn test_api_endpoint() {
    // API 测试
}
```

---

## 📚 文档测试（Doc Tests）

### 基本文档测试

```rust
/// 将两个数字相加
///
/// # 示例
///
/// ```
/// let result = add(2, 3);
/// assert_eq!(result, 5);
/// ```
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}
```

### 隐藏辅助代码

```rust
/// 计算阶乘
///
/// # 示例
///
/// ```
/// # use my_project::factorial;
/// assert_eq!(factorial(5), 120);
/// ```
pub fn factorial(n: u32) -> u32 {
    if n <= 1 {
        1
    } else {
        n * factorial(n - 1)
    }
}
```

### 忽略文档测试

```rust
/// 这个示例不会运行
///
/// ```rust,no_run
/// let result = expensive_operation();
/// ```
pub fn expensive_operation() -> i32 {
    // 实现
    42
}
```

### 编译但不运行

```rust
/// 只编译不运行
///
/// ```rust,compile_fail
/// let x: i32 = "hello"; // 这应该编译失败
/// ```
```

---

## ⚡ 性能测试（Benchmark Tests）

### Cargo.toml 配置

```toml
[dev-dependencies]
criterion = { version = "0.5", features = ["html_reports"] }

[[bench]]
name = "my_benchmark"
harness = false
```

### Criterion 基准测试

```rust
// benches/my_benchmark.rs
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn fibonacci(n: u64) -> u64 {
    match n {
        0 => 1,
        1 => 1,
        n => fibonacci(n - 1) + fibonacci(n - 2),
    }
}

fn bench_fibonacci(c: &mut Criterion) {
    c.bench_function("fib 20", |b| b.iter(|| fibonacci(black_box(20))));
}

criterion_group!(benches, bench_fibonacci);
criterion_main!(benches);
```

### 比较基准测试

```rust
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};

fn bench_comparison(c: &mut Criterion) {
    let mut group = c.benchmark_group("comparison");

    for size in [100, 1000, 10000].iter() {
        group.bench_with_input(
            BenchmarkId::new("algorithm_a", size),
            size,
            |b, &size| {
                b.iter(|| algorithm_a(black_box(size)));
            },
        );

        group.bench_with_input(
            BenchmarkId::new("algorithm_b", size),
            size,
            |b, &size| {
                b.iter(|| algorithm_b(black_box(size)));
            },
        );
    }

    group.finish();
}

criterion_group!(benches, bench_comparison);
criterion_main!(benches);
```

### 异步基准测试

```rust
use criterion::{criterion_group, criterion_main, Criterion};
use tokio::runtime::Runtime;

async fn async_operation() -> i32 {
    tokio::time::sleep(tokio::time::Duration::from_millis(1)).await;
    42
}

fn bench_async(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();

    c.bench_function("async_op", |b| {
        b.to_async(&rt).iter(|| async_operation());
    });
}

criterion_group!(benches, bench_async);
criterion_main!(benches);
```

### 运行基准测试

```bash
# 运行所有基准测试
cargo bench

# 运行特定基准测试
cargo bench --bench my_benchmark

# 运行特定测试
cargo bench --bench my_benchmark fib_20
```

---

## 🛠️ 测试工具和库

### 常用测试库

```toml
[dev-dependencies]
# 异步测试
tokio-test = "0.4"

# 属性测试
proptest = "1.0"

# Mock 测试
mockall = "0.12"

# 参数化测试
rstest = "0.18"

# 临时文件
tempfile = "3.0"

# 测试覆盖率
cargo-tarpaulin = "0.25"
```

### 异步测试

```rust
use tokio::test;

#[tokio::test]
async fn test_async_function() {
    let result = async_function().await;
    assert_eq!(result, 42);
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn test_multi_thread() {
    // 多线程异步测试
}
```

### 属性测试（Proptest）

```rust
use proptest::prelude::*;

proptest! {
    #[test]
    fn test_addition_commutative(a in 0..1000i32, b in 0..1000i32) {
        assert_eq!(add(a, b), add(b, a));
    }

    #[test]
    fn test_string_operations(s in ".*") {
        let reversed = s.chars().rev().collect::<String>();
        assert_eq!(reversed.chars().rev().collect::<String>(), s);
    }
}

// 高级属性测试
proptest! {
    #[test]
    fn test_vector_operations(
        mut vec in prop::collection::vec(0..100i32, 0..100)
    ) {
        let original_len = vec.len();
        vec.sort();
        assert_eq!(vec.len(), original_len);
        for i in 1..vec.len() {
            assert!(vec[i-1] <= vec[i]);
        }
    }
}
```

### Mock 测试（Mockall）

```rust
use mockall::predicate::*;
use mockall::*;

#[automock]
trait MyTrait {
    fn foo(&self, x: i32) -> i32;
}

#[test]
fn test_mock() {
    let mut mock = MockMyTrait::new();
    mock.expect_foo()
        .with(eq(4))
        .times(1)
        .returning(|x| x + 1);

    assert_eq!(5, mock.foo(4));
}
```

### 参数化测试（Rstest）

```rust
use rstest::rstest;

#[rstest]
#[case(0, 0)]
#[case(1, 1)]
#[case(2, 4)]
#[case(3, 9)]
fn test_square(#[case] input: i32, #[case] expected: i32) {
    assert_eq!(square(input), expected);
}

#[rstest]
fn test_with_fixture(#[from(fixture)] value: i32) {
    assert_eq!(value, 42);
}

fn fixture() -> i32 {
    42
}
```

### 模糊测试（Cargo-fuzz）

```toml
# Cargo.toml
[package]
name = "my_project"

[dependencies]
# ...

[dev-dependencies]
# ...

[dependencies.libfuzzer-sys]
version = "0.4"
```

```rust
// fuzz/fuzz_targets/parser_fuzz.rs
#![no_main]

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    // 测试解析器是否能处理任意输入而不崩溃
    if let Ok(s) = std::str::from_utf8(data) {
        let _ = parse_input(s);
    }
});

fn parse_input(input: &str) -> Result<(), String> {
    // 解析逻辑
    Ok(())
}
```

```bash
# 安装 cargo-fuzz
cargo install cargo-fuzz

# 运行模糊测试
cargo fuzz run parser_fuzz

# 运行特定时间
cargo fuzz run parser_fuzz -- -max_total_time=300
```

---

## 🎯 测试最佳实践

### 测试金字塔

```text
        /\
       /E2E\         10% - 端到端测试
      /------\
     /Integration\   20% - 集成测试
    /------------\
   /   Unit Tests \  70% - 单元测试
  /----------------\
```

**比例分配**:

| 测试类型 | 比例 | 特点 | 运行时间 |
|---------|------|------|---------|
| 单元测试 | 70% | 快速、隔离、可重复 | 秒级 |
| 集成测试 | 20% | 测试模块交互 | 分钟级 |
| E2E 测试 | 10% | 完整用户流程 | 小时级 |

### 测试驱动开发（TDD）

```rust
// 步骤 1: Red - 写失败的测试
#[test]
fn test_fibonacci() {
    assert_eq!(fibonacci(0), 0);
    assert_eq!(fibonacci(1), 1);
    assert_eq!(fibonacci(10), 55);
}

// 步骤 2: Green - 最小实现
fn fibonacci(n: u32) -> u32 {
    match n {
        0 => 0,
        1 => 1,
        _ => fibonacci(n - 1) + fibonacci(n - 2),
    }
}

// 步骤 3: Refactor - 优化实现
fn fibonacci(n: u32) -> u32 {
    let mut a = 0;
    let mut b = 1;
    for _ in 0..n {
        let temp = a;
        a = b;
        b = temp + b;
    }
    a
}
```

### 测试命名

```rust
// ✅ 好的命名
#[test]
fn test_add_two_positive_numbers() { }

#[test]
fn test_divide_by_zero_panics() { }

// ❌ 不好的命名
#[test]
fn test1() { }

#[test]
fn test_thing() { }
```

### 测试组织

```rust
#[cfg(test)]
mod tests {
    use super::*;

    // 测试夹具
    fn create_test_data() -> Vec<i32> {
        vec![1, 2, 3, 4, 5]
    }

    mod happy_path {
        use super::*;

        #[test]
        fn test_normal_case() {
            let data = create_test_data();
            // 测试正常情况
        }
    }

    mod edge_cases {
        use super::*;

        #[test]
        fn test_empty_input() {
            // 测试边界情况
        }

        #[test]
        fn test_overflow() {
            // 测试溢出情况
        }
    }

    mod error_cases {
        use super::*;

        #[test]
        #[should_panic]
        fn test_invalid_input() {
            // 测试错误情况
        }
    }
}
```

### 测试私有函数

```rust
pub fn public_function() -> i32 {
    private_helper(42)
}

fn private_helper(x: i32) -> i32 {
    x * 2
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_private_helper() {
        // 可以测试私有函数
        assert_eq!(private_helper(21), 42);
    }
}
```

### 测试并发代码

```rust
use std::sync::{Arc, Mutex};
use std::thread;

#[test]
fn test_concurrent_access() {
    let data = Arc::new(Mutex::new(0));
    let mut handles = vec![];

    for _ in 0..10 {
        let data = Arc::clone(&data);
        let handle = thread::spawn(move || {
            let mut num = data.lock().unwrap();
            *num += 1;
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    assert_eq!(*data.lock().unwrap(), 10);
}
```

### 测试文件 I/O

```rust
use std::fs;
use tempfile::TempDir;

#[test]
fn test_file_operations() {
    let temp_dir = TempDir::new().unwrap();
    let file_path = temp_dir.path().join("test.txt");

    fs::write(&file_path, "test content").unwrap();
    let content = fs::read_to_string(&file_path).unwrap();

    assert_eq!(content, "test content");
}
```

---

## 📊 测试覆盖率

### 使用 cargo-tarpaulin

```bash
# 安装
cargo install cargo-tarpaulin

# 运行覆盖率测试
cargo tarpaulin --out Html

# 输出到终端
cargo tarpaulin --out Stdout

# 设置覆盖率阈值
cargo tarpaulin --out Html --fail-under 80
```

### tarpaulin.toml 配置

```toml
[tool.tarpaulin]
# 覆盖率阈值
fail_under = 80

# 排除文件
exclude_files = [
    "*/tests/*",
    "*/benches/*",
    "*/examples/*",
]

# 排除行
exclude_lines = [
    "panic!",
    "unreachable!",
]
```

---

## 🚀 运行测试

### 基本命令

```bash
# 运行所有测试
cargo test

# 运行特定测试
cargo test test_name

# 运行匹配模式的测试
cargo test add

# 运行被忽略的测试
cargo test -- --ignored

# 运行所有测试（包括被忽略的）
cargo test -- --include-ignored

# 显示输出
cargo test -- --nocapture

# 单线程运行（用于调试）
cargo test -- --test-threads=1

# 运行特定测试文件
cargo test --test integration_test
```

### 测试输出

```bash
# 显示测试输出
cargo test -- --show-output

# 显示所有输出（包括通过的测试）
cargo test -- --nocapture

# 只显示失败的测试
cargo test --quiet
```

### 并行控制

```bash
# 使用 4 个线程
cargo test -- --test-threads=4

# 单线程（用于调试）
cargo test -- --test-threads=1
```

---

## 🔍 测试调试

### 打印调试信息

```rust
#[test]
fn test_with_debug() {
    let value = 42;
    println!("调试值: {}", value);
    dbg!(value);  // 使用 dbg! 宏
    assert_eq!(value, 42);
}
```

### 使用断言消息

```rust
#[test]
fn test_with_message() {
    let result = calculate();
    assert!(
        result > 0,
        "计算结果应该大于 0，得到 {}",
        result
    );
}
```

### 测试超时

```rust
use std::time::{Duration, Instant};

#[test]
fn test_with_timeout() {
    let start = Instant::now();
    // 执行操作
    let duration = start.elapsed();

    assert!(
        duration < Duration::from_secs(5),
        "操作超时: {:?}",
        duration
    );
}
```

---

## 📝 测试模式速查

### 测试 Result 类型

```rust
#[test]
fn test_result() {
    let result: Result<i32, String> = Ok(42);

    assert!(result.is_ok());
    assert_eq!(result.unwrap(), 42);
    assert_eq!(result.unwrap_or(0), 42);

    let err: Result<i32, String> = Err("error".to_string());
    assert!(err.is_err());
    assert_eq!(err.unwrap_err(), "error");
}
```

### 测试 Option 类型

```rust
#[test]
fn test_option() {
    let some: Option<i32> = Some(42);
    let none: Option<i32> = None;

    assert!(some.is_some());
    assert_eq!(some.unwrap(), 42);
    assert_eq!(some.unwrap_or(0), 42);

    assert!(none.is_none());
    assert_eq!(none.unwrap_or(0), 0);
}
```

### 测试浮点数（近似相等）

```rust
#[test]
fn test_float_approx() {
    let a = 0.1 + 0.2;
    let b = 0.3;

    // 使用近似比较
    assert!((a - b).abs() < f64::EPSILON);

    // 或使用 approx crate
    // use approx::assert_relative_eq;
    // assert_relative_eq!(a, b);
}
```

### 测试集合

```rust
#[test]
fn test_collections() {
    let vec = vec![1, 2, 3];

    assert_eq!(vec.len(), 3);
    assert!(vec.contains(&2));
    assert_eq!(vec[0], 1);

    let map = std::collections::HashMap::from([
        ("key1", "value1"),
        ("key2", "value2"),
    ]);

    assert_eq!(map.get("key1"), Some(&"value1"));
    assert!(map.contains_key("key2"));
}
```

---

## 🎓 常见测试场景

### 测试错误处理

```rust
#[test]
fn test_error_handling() {
    let result = risky_operation();

    match result {
        Ok(value) => assert_eq!(value, expected),
        Err(e) => {
            assert!(e.to_string().contains("expected error"));
        }
    }
}
```

### 测试生命周期

```rust
#[test]
fn test_lifetimes() {
    let data = String::from("test");
    let result = process_data(&data);
    assert_eq!(result, "processed: test");
    // data 仍然有效
}
```

### 测试泛型函数

```rust
#[test]
fn test_generic() {
    assert_eq!(identity(42), 42);
    assert_eq!(identity("hello"), "hello");
}

fn identity<T>(x: T) -> T {
    x
}
```

### 测试 trait 实现

```rust
#[test]
fn test_trait_impl() {
    let obj = MyStruct;
    assert_eq!(obj.method(), expected);
}
```

---

## 🔄 CI/CD 集成

### GitHub Actions 测试

```yaml
# .github/workflows/test.yml
name: Tests

on: [push, pull_request]

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3

      - name: Install Rust
        uses: actions-rs/toolchain@v1
        with:
          toolchain: stable
          override: true

      - name: Run tests
        run: cargo test --all-features

      - name: Run tests with output
        run: cargo test -- --nocapture

      - name: Run ignored tests
        run: cargo test -- --ignored

      - name: Check formatting
        run: cargo fmt -- --check

      - name: Clippy
        run: cargo clippy -- -D warnings
```

### 测试覆盖率 CI

```yaml
- name: Install tarpaulin
  run: cargo install cargo-tarpaulin

- name: Generate coverage
  run: cargo tarpaulin --out Xml

- name: Upload coverage
  uses: codecov/codecov-action@v3
  with:
    files: ./cobertura.xml
```

### 性能测试 CI

```yaml
- name: Run benchmarks
  run: cargo bench -- --test

- name: Check for performance regressions
  run: |
    cargo bench --bench my_benchmark > current.txt
    # 与基准比较
```

---

## 🎓 高级测试模式

### 快照测试

```rust
use insta::assert_snapshot;

#[test]
fn test_output() {
    let output = generate_output();
    assert_snapshot!(output, @"expected output");
}
```

### 金标准测试（Golden Tests）

```rust
use std::fs;

#[test]
fn test_golden_file() {
    let result = process_data();
    let expected = fs::read_to_string("tests/golden/expected.txt")
        .expect("无法读取金标准文件");
    assert_eq!(result, expected);
}
```

### 测试夹具（Fixtures）

```rust
struct TestFixture {
    data: Vec<i32>,
}

impl TestFixture {
    fn new() -> Self {
        Self {
            data: vec![1, 2, 3, 4, 5],
        }
    }

    fn with_data(data: Vec<i32>) -> Self {
        Self { data }
    }
}

#[test]
fn test_with_fixture() {
    let fixture = TestFixture::new();
    assert_eq!(fixture.data.len(), 5);
}
```

### 参数化测试（高级）

```rust
use rstest::rstest;

#[rstest]
#[case(0, 0, 0)]
#[case(1, 2, 3)]
#[case(2, 3, 5)]
#[case(100, 200, 300)]
fn test_addition(#[case] a: i32, #[case] b: i32, #[case] expected: i32) {
    assert_eq!(add(a, b), expected);
}

#[rstest]
fn test_with_multiple_fixtures(
    #[from(fixture1)] value1: i32,
    #[from(fixture2)] value2: String,
) {
    assert_eq!(value1, 42);
    assert_eq!(value2, "test");
}
```

### 测试并发安全性

```rust
use std::sync::Arc;
use std::thread;

#[test]
fn test_thread_safety() {
    let data = Arc::new(Mutex::new(0));
    let mut handles = vec![];

    for _ in 0..10 {
        let data = Arc::clone(&data);
        let handle = thread::spawn(move || {
            for _ in 0..1000 {
                let mut num = data.lock().unwrap();
                *num += 1;
            }
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    assert_eq!(*data.lock().unwrap(), 10000);
}
```

### 使用 Loom 测试并发

```rust
use loom::thread;

#[test]
fn test_loom_concurrent() {
    loom::model(|| {
        let data = Arc::new(Mutex::new(0));
        let data_clone = Arc::clone(&data);

        let t1 = thread::spawn(move || {
            let mut num = data_clone.lock().unwrap();
            *num += 1;
        });

        let t2 = thread::spawn(move || {
            let mut num = data.lock().unwrap();
            *num += 1;
        });

        t1.join().unwrap();
        t2.join().unwrap();
    });
}
```

---

## 🔧 测试工具速查

### 常用测试命令

```bash
# 基本测试
cargo test                    # 运行所有测试
cargo test --lib              # 只运行库测试
cargo test --tests            # 只运行集成测试
cargo test --benches          # 运行基准测试
cargo test --doc              # 运行文档测试

# 过滤和选择
cargo test test_name          # 运行匹配的测试
cargo test --test test_file   # 运行特定测试文件
cargo test -- --exact         # 精确匹配测试名

# 输出控制
cargo test -- --nocapture     # 显示所有输出
cargo test -- --show-output   # 显示测试输出
cargo test -- --quiet         # 安静模式

# 并行控制
cargo test -- --test-threads=1    # 单线程运行
cargo test -- --test-threads=4    # 4线程运行

# 其他选项
cargo test -- --ignored           # 只运行被忽略的测试
cargo test -- --include-ignored   # 运行所有测试（包括被忽略的）
cargo test -- --list              # 列出所有测试
cargo test -- --skip test_name    # 跳过特定测试
```

### 测试覆盖率工具

```bash
# cargo-tarpaulin
cargo install cargo-tarpaulin
cargo tarpaulin --out Html
cargo tarpaulin --out Stdout
cargo tarpaulin --fail-under 80

# grcov (需要 nightly)
cargo install grcov
RUSTFLAGS="-C instrument-coverage" cargo test
grcov . --binary-path ./target/debug/ -s . -t html --branch --ignore-not-existing -o coverage/
```

### 性能分析工具

```bash
# perf (Linux)
perf record --call-graph dwarf cargo test --bench
perf report

# valgrind (内存检查)
valgrind --leak-check=full cargo test

# heaptrack (内存分析)
heaptrack cargo test
```

---

## 📚 相关资源

### 官方文档

- [Rust 测试文档](https://doc.rust-lang.org/book/ch11-00-testing.html)
- [Rust 测试 API 文档](https://doc.rust-lang.org/std/#testing)

### 测试框架和工具

- [Criterion.rs](https://docs.rs/criterion/) - 基准测试框架
- [Proptest](https://docs.rs/proptest/) - 属性测试
- [Mockall](https://docs.rs/mockall/) - Mock 框架
- [Rstest](https://docs.rs/rstest/) - 参数化测试
- [Tokio Test](https://docs.rs/tokio-test/) - 异步测试工具
- [Insta](https://docs.rs/insta/) - 快照测试

### 测试覆盖率

- [cargo-tarpaulin](https://github.com/xd009642/tarpaulin) - 代码覆盖率工具
- [grcov](https://github.com/mozilla/grcov) - 覆盖率工具

### 模糊测试

- [cargo-fuzz](https://github.com/rust-fuzz/cargo-fuzz) - 模糊测试工具
- [libfuzzer-sys](https://docs.rs/libfuzzer-sys/) - LibFuzzer 绑定

### 并发测试

- [Loom](https://docs.rs/loom/) - 并发模型检查器
- [Shuttle](https://docs.rs/shuttle/) - 并发测试框架

### 相关文档

- [完整测试文档](../../docs/rust-formal-engineering-system/05_software_engineering/07_testing/)
- [WASM 测试策略](../../crates/c12_wasm/docs/wasm_engineering/Testing_Strategies.md)

---

**最后更新**: 2025-11-15
**维护者**: 文档团队
**状态**: 持续更新中 📝

🎯 **全面测试，确保质量！**
