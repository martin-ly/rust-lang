# 测试工具

> **核心库**: criterion, proptest, mockall, wiremock, rstest, insta  
> **适用场景**: 单元测试、集成测试、基准测试、属性测试、Mock、快照测试

---

## 📋 目录

- [测试工具](#测试工具)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [测试金字塔](#测试金字塔)
    - [Rust 测试生态](#rust-测试生态)
  - [核心库对比](#核心库对比)
    - [功能矩阵](#功能矩阵)
    - [选择指南](#选择指南)
  - [单元测试](#单元测试)
    - [内置测试框架](#内置测试框架)
      - [基础用法](#基础用法)
      - [集成测试](#集成测试)
    - [rstest - 参数化测试](#rstest---参数化测试)
      - [基础用法：参数化测试](#基础用法参数化测试)
      - [高级用法：Fixture](#高级用法fixture)
    - [mockall - Mock 框架](#mockall---mock-框架)
      - [基础用法：Trait Mock](#基础用法trait-mock)
      - [高级用法：返回值序列](#高级用法返回值序列)
      - [实战：测试依赖注入](#实战测试依赖注入)
  - [属性测试](#属性测试)
    - [proptest - 基于属性的测试](#proptest---基于属性的测试)
      - [基础用法：字符串反转](#基础用法字符串反转)
      - [高级用法：自定义策略](#高级用法自定义策略)
      - [实战：测试排序算法](#实战测试排序算法)
    - [quickcheck 对比](#quickcheck-对比)
  - [集成测试1](#集成测试1)
    - [wiremock - HTTP Mock](#wiremock---http-mock)
      - [基础用法：Mock HTTP 响应](#基础用法mock-http-响应)
      - [高级用法：请求验证](#高级用法请求验证)
      - [实战：测试外部 API 调用](#实战测试外部-api-调用)
    - [testcontainers - 容器测试](#testcontainers---容器测试)
      - [基础用法：PostgreSQL 测试](#基础用法postgresql-测试)
  - [基准测试](#基准测试)
    - [criterion - 性能基准](#criterion---性能基准)
      - [基础用法：简单基准](#基础用法简单基准)
      - [高级用法：参数化基准](#高级用法参数化基准)
      - [实战：对比算法](#实战对比算法)
    - [divan 对比](#divan-对比)
  - [快照测试](#快照测试)
    - [insta - 快照测试](#insta---快照测试)
      - [基础用法：断言快照](#基础用法断言快照)
      - [高级用法：JSON 快照](#高级用法json-快照)
  - [实战场景](#实战场景)
    - [场景1: Web API 测试](#场景1-web-api-测试)
    - [场景2: 数据库层测试](#场景2-数据库层测试)
    - [场景3: 性能回归测试](#场景3-性能回归测试)
  - [最佳实践](#最佳实践)
    - [1. 测试命名规范](#1-测试命名规范)
    - [2. 使用 Arrange-Act-Assert 模式](#2-使用-arrange-act-assert-模式)
    - [3. 测试隔离](#3-测试隔离)
    - [4. 参数化测试减少重复](#4-参数化测试减少重复)
    - [5. 基准测试的 black\_box](#5-基准测试的-black_box)
  - [常见陷阱](#常见陷阱)
    - [⚠️ 陷阱1: 测试中的 unwrap()](#️-陷阱1-测试中的-unwrap)
    - [⚠️ 陷阱2: 忘记设置 Mock 期望](#️-陷阱2-忘记设置-mock-期望)
    - [⚠️ 陷阱3: 异步测试中的 block\_on](#️-陷阱3-异步测试中的-block_on)
    - [⚠️ 陷阱4: 基准测试中的副作用](#️-陷阱4-基准测试中的副作用)
  - [参考资源](#参考资源)
    - [官方文档](#官方文档)
    - [教程与文章](#教程与文章)
    - [示例项目](#示例项目)
    - [相关文档](#相关文档)

---

## 概述

### 测试金字塔

```text
        /\
       /  \
      /集成\         少量：端到端测试
     /------\
    / 单元   \       大量：单元测试
   /----------\
  /  基础设施  \     支持：Mock、基准测试、属性测试
 /--------------\
```

**测试类型**:

1. **单元测试**: 测试单个函数、模块
2. **集成测试**: 测试组件交互
3. **端到端测试**: 测试完整流程
4. **属性测试**: 基于属性的随机测试
5. **基准测试**: 性能回归检测
6. **快照测试**: UI 或数据结构对比

### Rust 测试生态

**内置工具**:

- `cargo test`: 运行测试
- `#[test]`: 测试标注
- `assert!`, `assert_eq!`: 断言宏
- `#[cfg(test)]`: 测试模块

**第三方工具**:

- **mockall**: Mock 框架（类似 Mockito）
- **proptest**: 属性测试（类似 QuickCheck）
- **criterion**: 基准测试（类似 JMH）
- **wiremock**: HTTP Mock（类似 WireMock）
- **insta**: 快照测试（类似 Jest Snapshot）

---

## 核心库对比

### 功能矩阵

| 库 | 类型 | 用途 | 学习曲线 | 性能 | 推荐度 |
|-----|------|------|---------|------|--------|
| **mockall** | Mock | 单元测试依赖隔离 | 中等 | 高 | ⭐⭐⭐⭐⭐ |
| **proptest** | 属性测试 | 随机输入测试 | 高 | 中等 | ⭐⭐⭐⭐ |
| **criterion** | 基准测试 | 性能回归检测 | 低 | 高 | ⭐⭐⭐⭐⭐ |
| **wiremock** | HTTP Mock | API 集成测试 | 低 | 高 | ⭐⭐⭐⭐⭐ |
| **rstest** | 参数化测试 | 减少重复代码 | 低 | 高 | ⭐⭐⭐⭐ |
| **insta** | 快照测试 | 数据结构对比 | 低 | 高 | ⭐⭐⭐⭐ |
| **testcontainers** | 容器测试 | 真实环境测试 | 中等 | 中等 | ⭐⭐⭐⭐ |

### 选择指南

| 场景 | 推荐工具 | 理由 |
|------|---------|------|
| **单元测试** | 内置 + rstest + mockall | 覆盖大部分场景 |
| **API 测试** | wiremock + reqwest | HTTP Mock + 真实请求 |
| **数据库测试** | testcontainers | 真实数据库环境 |
| **性能测试** | criterion | 统计分析 + 回归检测 |
| **随机测试** | proptest | 发现边界情况 |
| **快照测试** | insta | 数据结构对比 |
| **CLI 测试** | assert_cmd + predicates | 命令行测试 |

---

## 单元测试

### 内置测试框架

#### 基础用法

```rust
// src/lib.rs
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}

pub fn divide(a: i32, b: i32) -> Result<i32, String> {
    if b == 0 {
        Err("除数不能为0".to_string())
    } else {
        Ok(a / b)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_add() {
        assert_eq!(add(2, 3), 5);
    }

    #[test]
    fn test_divide_success() {
        assert_eq!(divide(10, 2), Ok(5));
    }

    #[test]
    fn test_divide_by_zero() {
        assert_eq!(divide(10, 0), Err("除数不能为0".to_string()));
    }

    #[test]
    #[should_panic(expected = "index out of bounds")]
    fn test_panic() {
        let v = vec![1, 2, 3];
        let _ = v[10]; // 应该 panic
    }

    #[test]
    #[ignore] // 忽略此测试（用于慢测试）
    fn expensive_test() {
        // 耗时操作
    }
}
```

**运行测试**:

```bash
cargo test                    # 运行所有测试
cargo test test_add           # 运行特定测试
cargo test -- --ignored       # 运行被忽略的测试
cargo test -- --test-threads=1  # 单线程运行
cargo test -- --nocapture     # 显示 println! 输出
```

#### 集成测试

**目录结构**:

```text
project/
├── src/
│   └── lib.rs
├── tests/
│   ├── integration_test.rs
│   └── common/
│       └── mod.rs  # 共享代码
└── Cargo.toml
```

**集成测试示例**:

```rust
// tests/integration_test.rs
use my_crate::*;

#[test]
fn test_integration() {
    let result = add(2, 3);
    assert_eq!(result, 5);
}
```

### rstest - 参数化测试

**安装**:

```toml
[dev-dependencies]
rstest = "0.18"
```

#### 基础用法：参数化测试

```rust
use rstest::rstest;

#[rstest]
#[case(2, 3, 5)]
#[case(10, 20, 30)]
#[case(-5, 5, 0)]
#[case(0, 0, 0)]
fn test_add_parameterized(#[case] a: i32, #[case] b: i32, #[case] expected: i32) {
    assert_eq!(add(a, b), expected);
}
```

**要点**:

- `#[rstest]`: 标注参数化测试
- `#[case(...)]`: 定义测试用例
- 自动生成多个测试函数

#### 高级用法：Fixture

```rust
use rstest::*;

struct TestDb {
    connection: String,
}

impl TestDb {
    fn new() -> Self {
        println!("设置测试数据库");
        TestDb {
            connection: "test_db".to_string(),
        }
    }

    fn insert(&self, key: &str, value: &str) {
        println!("插入: {} = {}", key, value);
    }

    fn get(&self, key: &str) -> Option<String> {
        Some(format!("value_{}", key))
    }
}

impl Drop for TestDb {
    fn drop(&mut self) {
        println!("清理测试数据库");
    }
}

#[fixture]
fn test_db() -> TestDb {
    TestDb::new()
}

#[rstest]
fn test_insert(test_db: TestDb) {
    test_db.insert("key1", "value1");
    // 测试结束自动调用 drop
}

#[rstest]
fn test_get(test_db: TestDb) {
    let value = test_db.get("key1");
    assert!(value.is_some());
}
```

**Fixture 优势**:

- 自动设置和清理
- 可复用测试资源
- 支持依赖注入

### mockall - Mock 框架

**安装**:

```toml
[dev-dependencies]
mockall = "0.12"
```

#### 基础用法：Trait Mock

```rust
use mockall::*;
use mockall::predicate::*;

#[automock]
trait Database {
    fn get_user(&self, id: u32) -> Option<String>;
    fn save_user(&mut self, id: u32, name: String) -> Result<(), String>;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_get_user() {
        let mut mock = MockDatabase::new();
        
        // 设置期望
        mock.expect_get_user()
            .with(eq(1))           // 参数匹配
            .times(1)               // 调用次数
            .returning(|_| Some("Alice".to_string()));
        
        // 调用
        assert_eq!(mock.get_user(1), Some("Alice".to_string()));
    }

    #[test]
    fn test_save_user() {
        let mut mock = MockDatabase::new();
        
        mock.expect_save_user()
            .with(eq(1), eq("Bob".to_string()))
            .times(1)
            .returning(|_, _| Ok(()));
        
        assert!(mock.save_user(1, "Bob".to_string()).is_ok());
    }

    #[test]
    #[should_panic(expected = "MockDatabase::get_user: No matching expectation found")]
    fn test_unexpected_call() {
        let mock = MockDatabase::new();
        // 没有设置期望，调用会 panic
        let _ = mock.get_user(1);
    }
}
```

#### 高级用法：返回值序列

```rust
#[test]
fn test_retry_logic() {
    let mut mock = MockDatabase::new();
    
    // 第一次失败，第二次成功
    mock.expect_get_user()
        .with(eq(1))
        .times(2)
        .returning(|_| None)
        .returning(|_| Some("Alice".to_string()));
    
    // 模拟重试逻辑
    let result1 = mock.get_user(1);
    assert_eq!(result1, None);
    
    let result2 = mock.get_user(1);
    assert_eq!(result2, Some("Alice".to_string()));
}
```

#### 实战：测试依赖注入

```rust
struct UserService<D: Database> {
    db: D,
}

impl<D: Database> UserService<D> {
    fn new(db: D) -> Self {
        UserService { db }
    }

    fn get_user_name(&self, id: u32) -> String {
        self.db.get_user(id).unwrap_or_else(|| "Unknown".to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_user_service() {
        let mut mock_db = MockDatabase::new();
        
        mock_db.expect_get_user()
            .with(eq(1))
            .times(1)
            .returning(|_| Some("Alice".to_string()));
        
        let service = UserService::new(mock_db);
        assert_eq!(service.get_user_name(1), "Alice");
    }

    #[test]
    fn test_user_not_found() {
        let mut mock_db = MockDatabase::new();
        
        mock_db.expect_get_user()
            .with(eq(999))
            .times(1)
            .returning(|_| None);
        
        let service = UserService::new(mock_db);
        assert_eq!(service.get_user_name(999), "Unknown");
    }
}
```

---

## 属性测试

### proptest - 基于属性的测试

**概念**: 不编写具体测试用例，而是定义属性（property），让工具生成大量随机输入验证属性。

**安装**:

```toml
[dev-dependencies]
proptest = "1.4"
```

#### 基础用法：字符串反转

```rust
use proptest::prelude::*;

proptest! {
    #[test]
    fn test_reverse_reverse(s in ".*") {
        // 属性：反转两次应该等于原字符串
        let reversed: String = s.chars().rev().collect();
        let double_reversed: String = reversed.chars().rev().collect();
        prop_assert_eq!(s, double_reversed);
    }

    #[test]
    fn test_string_length_preserved(s in ".*") {
        // 属性：反转不改变长度
        let reversed: String = s.chars().rev().collect();
        prop_assert_eq!(s.len(), reversed.len());
    }
}
```

**运行结果**:

```text
running 2 tests
test test_reverse_reverse ... ok (100 cases)
test test_string_length_preserved ... ok (100 cases)
```

#### 高级用法：自定义策略

```rust
use proptest::prelude::*;

// 自定义生成器
fn valid_email() -> impl Strategy<Value = String> {
    "[a-z]{1,10}@[a-z]{1,10}\\.(com|org|net)"
}

proptest! {
    #[test]
    fn test_email_validation(email in valid_email()) {
        // 验证邮箱格式
        assert!(email.contains('@'));
        assert!(email.contains('.'));
    }

    #[test]
    fn test_age_range(age in 0u8..=120) {
        // 年龄范围测试
        assert!(age <= 120);
    }

    #[test]
    fn test_positive_sum(a in 0i32..=100, b in 0i32..=100) {
        // 两个非负数之和应该非负
        prop_assert!(a + b >= 0);
    }
}
```

#### 实战：测试排序算法

```rust
use proptest::prelude::*;

fn my_sort(v: &mut Vec<i32>) {
    v.sort();
}

proptest! {
    #[test]
    fn test_sort_preserves_length(mut v in prop::collection::vec(any::<i32>(), 0..100)) {
        let original_len = v.len();
        my_sort(&mut v);
        prop_assert_eq!(v.len(), original_len);
    }

    #[test]
    fn test_sort_is_sorted(mut v in prop::collection::vec(any::<i32>(), 0..100)) {
        my_sort(&mut v);
        
        // 验证有序性
        for i in 1..v.len() {
            prop_assert!(v[i - 1] <= v[i]);
        }
    }

    #[test]
    fn test_sort_idempotent(mut v in prop::collection::vec(any::<i32>(), 0..100)) {
        my_sort(&mut v);
        let sorted = v.clone();
        my_sort(&mut v);
        
        // 排序两次结果相同
        prop_assert_eq!(v, sorted);
    }
}
```

### quickcheck 对比

| 特性 | proptest | quickcheck |
|------|---------|-----------|
| **策略灵活性** | 高（自定义策略） | 中等 |
| **错误缩小** | 自动（shrinking） | 自动 |
| **性能** | 更快 | 较慢 |
| **宏支持** | `proptest!` | `quickcheck!` |
| **推荐度** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ |

---

## 集成测试1

### wiremock - HTTP Mock

**安装**:

```toml
[dev-dependencies]
wiremock = "0.6"
tokio = { version = "1", features = ["full"] }
reqwest = "0.11"
```

#### 基础用法：Mock HTTP 响应

```rust
use wiremock::{MockServer, Mock, ResponseTemplate};
use wiremock::matchers::{method, path};

#[tokio::test]
async fn test_http_get() {
    // 启动 Mock 服务器
    let mock_server = MockServer::start().await;

    // 注册 Mock
    Mock::given(method("GET"))
        .and(path("/users/1"))
        .respond_with(ResponseTemplate::new(200).set_body_json(serde_json::json!({
            "id": 1,
            "name": "Alice"
        })))
        .mount(&mock_server)
        .await;

    // 发送请求
    let url = format!("{}/users/1", mock_server.uri());
    let response = reqwest::get(&url).await.unwrap();

    assert_eq!(response.status(), 200);
    let body: serde_json::Value = response.json().await.unwrap();
    assert_eq!(body["name"], "Alice");
}
```

#### 高级用法：请求验证

```rust
use wiremock::matchers::{header, query_param};

#[tokio::test]
async fn test_request_headers() {
    let mock_server = MockServer::start().await;

    Mock::given(method("POST"))
        .and(path("/api/data"))
        .and(header("Content-Type", "application/json"))
        .and(header("Authorization", "Bearer token123"))
        .and(query_param("filter", "active"))
        .respond_with(ResponseTemplate::new(201))
        .expect(1)  // 期望调用1次
        .mount(&mock_server)
        .await;

    // 发送请求
    let client = reqwest::Client::new();
    let url = format!("{}/api/data?filter=active", mock_server.uri());
    let response = client
        .post(&url)
        .header("Content-Type", "application/json")
        .header("Authorization", "Bearer token123")
        .body(r#"{"key": "value"}"#)
        .send()
        .await
        .unwrap();

    assert_eq!(response.status(), 201);
}
```

#### 实战：测试外部 API 调用

```rust
async fn fetch_user(base_url: &str, user_id: u32) -> Result<User, reqwest::Error> {
    let url = format!("{}/users/{}", base_url, user_id);
    let response = reqwest::get(&url).await?;
    response.json().await
}

#[derive(Debug, serde::Deserialize, PartialEq)]
struct User {
    id: u32,
    name: String,
}

#[tokio::test]
async fn test_fetch_user_success() {
    let mock_server = MockServer::start().await;

    Mock::given(method("GET"))
        .and(path("/users/1"))
        .respond_with(ResponseTemplate::new(200).set_body_json(serde_json::json!({
            "id": 1,
            "name": "Alice"
        })))
        .mount(&mock_server)
        .await;

    let result = fetch_user(&mock_server.uri(), 1).await;
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), User { id: 1, name: "Alice".to_string() });
}

#[tokio::test]
async fn test_fetch_user_not_found() {
    let mock_server = MockServer::start().await;

    Mock::given(method("GET"))
        .and(path("/users/999"))
        .respond_with(ResponseTemplate::new(404))
        .mount(&mock_server)
        .await;

    let result = fetch_user(&mock_server.uri(), 999).await;
    assert!(result.is_err());
}
```

### testcontainers - 容器测试

**安装**:

```toml
[dev-dependencies]
testcontainers = "0.15"
```

#### 基础用法：PostgreSQL 测试

```rust
use testcontainers::{clients, images::postgres::Postgres};

#[tokio::test]
async fn test_with_postgres() {
    let docker = clients::Cli::default();
    let postgres = docker.run(Postgres::default());

    let port = postgres.get_host_port_ipv4(5432);
    let connection_string = format!("postgres://postgres:postgres@localhost:{}/postgres", port);

    // 使用真实的 PostgreSQL 进行测试
    // ...

    // 容器在测试结束后自动删除
}
```

---

## 基准测试

### criterion - 性能基准

**安装**:

```toml
[dev-dependencies]
criterion = { version = "0.5", features = ["html_reports"] }

[[bench]]
name = "my_benchmark"
harness = false
```

#### 基础用法：简单基准

```rust
// benches/my_benchmark.rs
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn fibonacci(n: u64) -> u64 {
    match n {
        0 | 1 => 1,
        n => fibonacci(n - 1) + fibonacci(n - 2),
    }
}

fn fibonacci_benchmark(c: &mut Criterion) {
    c.bench_function("fib 20", |b| {
        b.iter(|| fibonacci(black_box(20)))
    });
}

criterion_group!(benches, fibonacci_benchmark);
criterion_main!(benches);
```

**运行**:

```bash
cargo bench
```

**输出**:

```text
fib 20                  time:   [2.5731 ms 2.5783 ms 2.5836 ms]
```

#### 高级用法：参数化基准

```rust
use criterion::{BenchmarkId, Criterion};

fn bench_fibonacci(c: &mut Criterion) {
    let mut group = c.benchmark_group("fibonacci");
    
    for i in [10, 15, 20, 25].iter() {
        group.bench_with_input(BenchmarkId::from_parameter(i), i, |b, &n| {
            b.iter(|| fibonacci(black_box(n)));
        });
    }
    
    group.finish();
}
```

#### 实战：对比算法

```rust
fn merge_sort(v: &mut [i32]) {
    // 归并排序实现
}

fn quick_sort(v: &mut [i32]) {
    // 快速排序实现
}

fn bench_sorting(c: &mut Criterion) {
    let mut group = c.benchmark_group("sorting");
    
    for size in [100, 1000, 10000].iter() {
        let data: Vec<i32> = (0..*size).collect();
        
        group.bench_with_input(BenchmarkId::new("merge_sort", size), &data, |b, data| {
            b.iter(|| {
                let mut v = data.clone();
                merge_sort(&mut v);
            });
        });
        
        group.bench_with_input(BenchmarkId::new("quick_sort", size), &data, |b, data| {
            b.iter(|| {
                let mut v = data.clone();
                quick_sort(&mut v);
            });
        });
    }
    
    group.finish();
}
```

### divan 对比

| 特性 | criterion | divan |
|------|-----------|-------|
| **统计分析** | 详细（置信区间） | 简化 |
| **HTML 报告** | ✅ | ❌ |
| **编译速度** | 较慢 | 快 |
| **宏支持** | `criterion_group!` | `#[divan::bench]` |
| **推荐度** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ |

---

## 快照测试

### insta - 快照测试

**安装**:

```toml
[dev-dependencies]
insta = "1.34"
```

#### 基础用法：断言快照

```rust
use insta::assert_snapshot;

#[test]
fn test_output() {
    let output = generate_report();
    assert_snapshot!(output);
}
```

**首次运行**:

```bash
cargo test
cargo insta review  # 审查快照
cargo insta accept  # 接受快照
```

**生成的快照文件** (`snapshots/my_test__output.snap`):

```text
---
source: src/lib.rs
expression: output
---
Generated Report
================
Date: 2025-10-20
Status: OK
```

#### 高级用法：JSON 快照

```rust
use insta::assert_json_snapshot;

#[test]
fn test_user_json() {
    let user = User {
        id: 1,
        name: "Alice".to_string(),
        email: "alice@example.com".to_string(),
    };
    
    assert_json_snapshot!(user);
}
```

---

## 实战场景

### 场景1: Web API 测试

**需求描述**: 测试 REST API 的 CRUD 操作，使用 wiremock 模拟外部依赖。

**完整实现**:

```rust
use axum::{Router, Json, extract::Path};
use serde::{Serialize, Deserialize};

#[derive(Debug, Serialize, Deserialize, Clone, PartialEq)]
struct User {
    id: u32,
    name: String,
    email: String,
}

// API 实现（简化）
async fn create_user(Json(user): Json<User>) -> Json<User> {
    Json(user)
}

async fn get_user(Path(id): Path<u32>) -> Json<Option<User>> {
    if id == 1 {
        Json(Some(User {
            id: 1,
            name: "Alice".to_string(),
            email: "alice@example.com".to_string(),
        }))
    } else {
        Json(None)
    }
}

// 测试
#[cfg(test)]
mod tests {
    use super::*;
    use axum::body::Body;
    use axum::http::{Request, StatusCode};
    use tower::ServiceExt;

    #[tokio::test]
    async fn test_create_user() {
        let app = Router::new().route("/users", axum::routing::post(create_user));

        let user = User {
            id: 1,
            name: "Alice".to_string(),
            email: "alice@example.com".to_string(),
        };

        let request = Request::builder()
            .uri("/users")
            .method("POST")
            .header("Content-Type", "application/json")
            .body(Body::from(serde_json::to_string(&user).unwrap()))
            .unwrap();

        let response = app.oneshot(request).await.unwrap();
        assert_eq!(response.status(), StatusCode::OK);
    }

    #[tokio::test]
    async fn test_get_user() {
        let app = Router::new().route("/users/:id", axum::routing::get(get_user));

        let request = Request::builder()
            .uri("/users/1")
            .body(Body::empty())
            .unwrap();

        let response = app.oneshot(request).await.unwrap();
        assert_eq!(response.status(), StatusCode::OK);
    }
}
```

### 场景2: 数据库层测试

**需求描述**: 测试数据库访问层，使用 mockall 隔离依赖。

**完整实现**:

```rust
use mockall::*;

#[automock]
trait UserRepository {
    fn find_by_id(&self, id: u32) -> Option<User>;
    fn save(&mut self, user: User) -> Result<(), String>;
}

struct UserService<R: UserRepository> {
    repo: R,
}

impl<R: UserRepository> UserService<R> {
    fn new(repo: R) -> Self {
        UserService { repo }
    }

    fn get_user(&self, id: u32) -> Result<User, String> {
        self.repo.find_by_id(id).ok_or_else(|| "用户不存在".to_string())
    }

    fn create_user(&mut self, user: User) -> Result<(), String> {
        self.repo.save(user)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_get_user_success() {
        let mut mock_repo = MockUserRepository::new();
        
        mock_repo.expect_find_by_id()
            .with(eq(1))
            .times(1)
            .returning(|_| Some(User {
                id: 1,
                name: "Alice".to_string(),
                email: "alice@example.com".to_string(),
            }));

        let service = UserService::new(mock_repo);
        let result = service.get_user(1);
        
        assert!(result.is_ok());
        assert_eq!(result.unwrap().name, "Alice");
    }

    #[test]
    fn test_get_user_not_found() {
        let mut mock_repo = MockUserRepository::new();
        
        mock_repo.expect_find_by_id()
            .with(eq(999))
            .times(1)
            .returning(|_| None);

        let service = UserService::new(mock_repo);
        let result = service.get_user(999);
        
        assert!(result.is_err());
        assert_eq!(result.unwrap_err(), "用户不存在");
    }
}
```

### 场景3: 性能回归测试

**需求描述**: 使用 criterion 检测性能回归。

**完整实现**:

```rust
// benches/performance.rs
use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};

fn hash_string_builtin(s: &str) -> u64 {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    
    let mut hasher = DefaultHasher::new();
    s.hash(&mut hasher);
    hasher.finish()
}

fn hash_string_custom(s: &str) -> u64 {
    let mut hash = 5381u64;
    for byte in s.bytes() {
        hash = hash.wrapping_mul(33).wrapping_add(byte as u64);
    }
    hash
}

fn benchmark_hash(c: &mut Criterion) {
    let mut group = c.benchmark_group("string_hash");
    
    for size in [10, 100, 1000].iter() {
        let s = "a".repeat(*size);
        
        group.bench_with_input(BenchmarkId::new("builtin", size), &s, |b, s| {
            b.iter(|| hash_string_builtin(black_box(s)));
        });
        
        group.bench_with_input(BenchmarkId::new("custom", size), &s, |b, s| {
            b.iter(|| hash_string_custom(black_box(s)));
        });
    }
    
    group.finish();
}

criterion_group!(benches, benchmark_hash);
criterion_main!(benches);
```

**运行**:

```bash
cargo bench
```

**输出**:

```text
string_hash/builtin/10  time:   [12.345 ns 12.456 ns 12.567 ns]
string_hash/custom/10   time:   [8.123 ns 8.234 ns 8.345 ns]
                        change: [-35.2% -34.8% -34.4%] (p = 0.00 < 0.05)
                        Performance has improved.
```

---

## 最佳实践

### 1. 测试命名规范

**描述**: 清晰的命名提高可读性。

```rust
// ✅ 好的命名
#[test]
fn test_divide_by_zero_returns_error() { }

#[test]
fn test_user_login_with_invalid_password_fails() { }

// ❌ 不好的命名
#[test]
fn test1() { }

#[test]
fn test_user() { }
```

### 2. 使用 Arrange-Act-Assert 模式

**描述**: 三段式测试结构。

```rust
#[test]
fn test_user_creation() {
    // Arrange（准备）
    let name = "Alice";
    let email = "alice@example.com";
    
    // Act（执行）
    let user = User::new(name, email);
    
    // Assert（断言）
    assert_eq!(user.name, name);
    assert_eq!(user.email, email);
}
```

### 3. 测试隔离

**描述**: 每个测试独立，不依赖其他测试。

```rust
// ✅ 好的做法：每个测试独立
#[test]
fn test_1() {
    let db = setup_test_db();
    // ...
    teardown_test_db(db);
}

#[test]
fn test_2() {
    let db = setup_test_db();
    // ...
    teardown_test_db(db);
}

// ❌ 不好的做法：测试间共享状态
static mut COUNTER: i32 = 0;

#[test]
fn test_a() {
    unsafe { COUNTER += 1; }
}

#[test]
fn test_b() {
    unsafe { assert_eq!(COUNTER, 1); } // 依赖 test_a
}
```

### 4. 参数化测试减少重复

**描述**: 使用 rstest 避免重复代码。

```rust
// ❌ 重复代码
#[test]
fn test_add_1() {
    assert_eq!(add(2, 3), 5);
}

#[test]
fn test_add_2() {
    assert_eq!(add(10, 20), 30);
}

// ✅ 参数化测试
#[rstest]
#[case(2, 3, 5)]
#[case(10, 20, 30)]
#[case(-5, 5, 0)]
fn test_add(#[case] a: i32, #[case] b: i32, #[case] expected: i32) {
    assert_eq!(add(a, b), expected);
}
```

### 5. 基准测试的 black_box

**描述**: 防止编译器优化掉测试代码。

```rust
use criterion::black_box;

// ✅ 正确使用 black_box
fn benchmark(c: &mut Criterion) {
    c.bench_function("compute", |b| {
        b.iter(|| expensive_function(black_box(42)))
    });
}

// ❌ 不使用 black_box（可能被优化）
fn benchmark_wrong(c: &mut Criterion) {
    c.bench_function("compute", |b| {
        b.iter(|| expensive_function(42)) // 结果可能被缓存
    });
}
```

---

## 常见陷阱

### ⚠️ 陷阱1: 测试中的 unwrap()

**问题描述**: 测试失败信息不明确。

❌ **错误示例**:

```rust
#[test]
fn test_parse() {
    let result = parse("invalid").unwrap(); // panic: called `Result::unwrap()` on an `Err` value
}
```

✅ **正确做法**:

```rust
#[test]
fn test_parse() {
    let result = parse("invalid");
    assert!(result.is_err(), "应该返回错误，但得到: {:?}", result);
}
```

### ⚠️ 陷阱2: 忘记设置 Mock 期望

**问题描述**: Mock 未设置期望导致 panic。

❌ **错误示例**:

```rust
#[test]
fn test_with_mock() {
    let mock = MockDatabase::new();
    let _ = mock.get_user(1); // panic: No matching expectation found
}
```

✅ **正确做法**:

```rust
#[test]
fn test_with_mock() {
    let mut mock = MockDatabase::new();
    mock.expect_get_user()
        .with(eq(1))
        .times(1)
        .returning(|_| Some("Alice".to_string()));
    
    let result = mock.get_user(1);
    assert_eq!(result, Some("Alice".to_string()));
}
```

### ⚠️ 陷阱3: 异步测试中的 block_on

**问题描述**: 在异步测试中使用同步代码。

❌ **错误示例**:

```rust
#[test]
fn test_async_function() {
    let result = tokio::runtime::Runtime::new()
        .unwrap()
        .block_on(async_function());
    // 复杂且容易出错
}
```

✅ **正确做法**:

```rust
#[tokio::test]
async fn test_async_function() {
    let result = async_function().await;
    assert!(result.is_ok());
}
```

### ⚠️ 陷阱4: 基准测试中的副作用

**问题描述**: 测试代码有副作用影响结果。

❌ **错误示例**:

```rust
static mut CACHE: Option<Vec<i32>> = None;

fn benchmark(c: &mut Criterion) {
    c.bench_function("compute", |b| {
        b.iter(|| {
            unsafe {
                if CACHE.is_none() {
                    CACHE = Some(expensive_compute());
                }
                CACHE.as_ref().unwrap()
            }
        });
    });
}
```

✅ **正确做法**:

```rust
fn benchmark(c: &mut Criterion) {
    c.bench_function("compute", |b| {
        b.iter(|| {
            black_box(expensive_compute())
        });
    });
}
```

---

## 参考资源

### 官方文档

- 📚 [Rust 测试文档](https://doc.rust-lang.org/book/ch11-00-testing.html)
- 📚 [criterion 文档](https://bheisler.github.io/criterion.rs/book/)
- 📚 [proptest 文档](https://docs.rs/proptest/latest/proptest/)
- 📚 [mockall 文档](https://docs.rs/mockall/latest/mockall/)
- 📚 [wiremock 文档](https://docs.rs/wiremock/latest/wiremock/)

### 教程与文章

- 📖 [Rust 测试最佳实践](https://matklad.github.io/2021/05/31/how-to-test.html)
- 📖 [属性测试入门](https://hypothesis.works/articles/what-is-property-based-testing/)
- 📖 [基准测试指南](https://easyperf.net/blog/2018/09/05/Performance-Analysis-Vocabulary)

### 示例项目

- 💻 [Rust 测试示例](https://github.com/rust-lang/rustlings)
- 💻 [mockall 示例](https://github.com/asomers/mockall/tree/master/mockall/examples)
- 💻 [criterion 示例](https://github.com/bheisler/criterion.rs/tree/master/benches)

### 相关文档

- 🔗 [CLI 工具开发](../cli_tools/README.md)
- 🔗 [异步运行时](../../02_system_programming/async_runtime/README.md)
- 🔗 [日志系统](../../05_toolchain/logging/README.md)

---

**文档版本**: 2.0.0  
**最后更新**: 2025-10-20  
**维护者**: Rust 学习社区
