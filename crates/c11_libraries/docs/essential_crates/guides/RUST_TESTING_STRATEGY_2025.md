# Rust 测试策略完全指南 (2025版)

> 从单元测试到生产监控：构建高质量 Rust 应用的完整测试体系

## 📋 目录

- [Rust 测试策略完全指南 (2025版)](#rust-测试策略完全指南-2025版)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [测试的价值](#测试的价值)
    - [核心依赖](#核心依赖)
  - [测试金字塔](#测试金字塔)
    - [理想的测试分布](#理想的测试分布)
  - [单元测试](#单元测试)
    - [1. 基础单元测试](#1-基础单元测试)
    - [2. 参数化测试 (rstest)](#2-参数化测试-rstest)
    - [3. 异步测试](#3-异步测试)
  - [集成测试](#集成测试)
    - [1. API 集成测试](#1-api-集成测试)
    - [2. 数据库测试 (Testcontainers)](#2-数据库测试-testcontainers)
  - [性能测试](#性能测试)
    - [使用 Criterion](#使用-criterion)
  - [属性测试](#属性测试)
    - [使用 Proptest](#使用-proptest)
  - [模拟与存根](#模拟与存根)
    - [使用 Mockall](#使用-mockall)
    - [HTTP Mock (wiremock)](#http-mock-wiremock)
  - [快照测试](#快照测试)
    - [使用 Insta](#使用-insta)
  - [端到端测试](#端到端测试)
    - [CLI 应用测试 (assert\_cmd)](#cli-应用测试-assert_cmd)
    - [Web 应用测试 (Playwright/Selenium)](#web-应用测试-playwrightselenium)
  - [测试覆盖率](#测试覆盖率)
    - [使用 cargo-llvm-cov](#使用-cargo-llvm-cov)
  - [CI/CD 集成](#cicd-集成)
    - [GitHub Actions 完整配置](#github-actions-完整配置)
  - [生产监控](#生产监控)
    - [集成测试作为监控](#集成测试作为监控)
  - [最佳实践](#最佳实践)
    - [✅ 推荐做法](#-推荐做法)
  - [常见陷阱](#常见陷阱)
    - [❌ 避免的错误](#-避免的错误)
  - [参考资源](#参考资源)
    - [官方文档](#官方文档)
    - [测试库](#测试库)
    - [工具](#工具)
    - [学习资源](#学习资源)
  - [总结](#总结)

---

## 概述

### 测试的价值

**为什么要写测试？**

- ✅ **验证正确性**：确保代码按预期工作
- ✅ **回归防护**：防止修改破坏现有功能
- ✅ **文档作用**：测试即示例代码
- ✅ **重构信心**：安全地改进代码结构
- ✅ **早期发现 Bug**：开发阶段而非生产环境

### 核心依赖

```toml
[dev-dependencies]
# 基准测试
criterion = { version = "0.5", features = ["html_reports"] }

# 属性测试
proptest = "1.4"
quickcheck = "1.0"

# 模拟
mockall = "0.12"
wiremock = "0.6"

# 快照测试
insta = { version = "1.34", features = ["yaml"] }

# 测试工具
rstest = "0.18"
assert_cmd = "2.0"
predicates = "3.0"
testcontainers = "0.15"

# 异步测试
tokio-test = "0.4"
```

---

## 测试金字塔

### 理想的测试分布

```text
          ▲
         ╱ ╲
        ╱   ╲           E2E Tests (5%)
       ╱     ╲          - Playwright
      ╱───────╲         - Selenium
     ╱         ╲
    ╱           ╲       Integration Tests (15%)
   ╱             ╲      - API Tests
  ╱───────────────╲     - Database Tests
 ╱                 ╲
╱___________________╲   Unit Tests (80%)
                        - Pure Functions
                        - Business Logic
```

**原则：**

1. **单元测试占多数** (80%)：快速、隔离、易维护
2. **集成测试适中** (15%)：验证组件交互
3. **端到端测试最少** (5%)：覆盖关键用户流程

---

## 单元测试

### 1. 基础单元测试

```rust
// src/lib.rs

/// 计算两个数的和
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}

/// 检查字符串是否为回文
pub fn is_palindrome(s: &str) -> bool {
    let s = s.chars().filter(|c| c.is_alphanumeric()).collect::<String>().to_lowercase();
    s == s.chars().rev().collect::<String>()
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_add() {
        assert_eq!(add(2, 3), 5);
        assert_eq!(add(-1, 1), 0);
        assert_eq!(add(0, 0), 0);
    }
    
    #[test]
    fn test_palindrome() {
        assert!(is_palindrome("radar"));
        assert!(is_palindrome("A man a plan a canal Panama"));
        assert!(!is_palindrome("hello"));
    }
    
    #[test]
    #[should_panic(expected = "divide by zero")]
    fn test_divide_by_zero() {
        let _ = 1 / 0;
    }
    
    #[test]
    #[ignore]  // 使用 `cargo test -- --ignored` 运行
    fn expensive_test() {
        // 耗时的测试...
    }
}
```

### 2. 参数化测试 (rstest)

```rust
use rstest::rstest;

#[rstest]
#[case(2, 3, 5)]
#[case(-1, 1, 0)]
#[case(0, 0, 0)]
#[case(100, -50, 50)]
fn test_add_parametrized(#[case] a: i32, #[case] b: i32, #[case] expected: i32) {
    assert_eq!(add(a, b), expected);
}

#[rstest]
#[case("radar")]
#[case("A man a plan a canal Panama")]
#[case("Was it a car or a cat I saw?")]
fn test_palindrome_positive(#[case] input: &str) {
    assert!(is_palindrome(input));
}

#[rstest]
#[case("hello")]
#[case("world")]
#[case("Rust")]
fn test_palindrome_negative(#[case] input: &str) {
    assert!(!is_palindrome(input));
}
```

### 3. 异步测试

```rust
use tokio::time::{sleep, Duration};

async fn fetch_data() -> Result<String, reqwest::Error> {
    sleep(Duration::from_millis(100)).await;
    Ok("data".to_string())
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[tokio::test]
    async fn test_fetch_data() {
        let result = fetch_data().await;
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), "data");
    }
    
    #[tokio::test]
    async fn test_timeout() {
        let result = tokio::time::timeout(
            Duration::from_millis(50),
            fetch_data()
        ).await;
        
        assert!(result.is_err());  // 超时
    }
}
```

---

## 集成测试

### 1. API 集成测试

**项目结构：**

```text
my_app/
├── src/
│   ├── main.rs
│   └── routes.rs
├── tests/
│   ├── common/
│   │   └── mod.rs     # 测试辅助函数
│   └── api_tests.rs   # API 集成测试
└── Cargo.toml
```

**tests/common/mod.rs:**

```rust
use axum::Router;
use sqlx::{PgPool, postgres::PgPoolOptions};
use tokio::net::TcpListener;

pub struct TestApp {
    pub address: String,
    pub db_pool: PgPool,
}

impl TestApp {
    pub async fn spawn() -> Self {
        // 1. 创建测试数据库
        let db_pool = PgPoolOptions::new()
            .max_connections(5)
            .connect("postgres://test:test@localhost/test_db")
            .await
            .expect("Failed to connect to database");
        
        // 2. 运行迁移
        sqlx::migrate!("./migrations")
            .run(&db_pool)
            .await
            .expect("Failed to run migrations");
        
        // 3. 创建应用
        let app = create_app(db_pool.clone());
        
        // 4. 绑定到随机端口
        let listener = TcpListener::bind("127.0.0.1:0")
            .await
            .expect("Failed to bind");
        let address = format!("http://{}", listener.local_addr().unwrap());
        
        // 5. 启动服务器
        tokio::spawn(async move {
            axum::serve(listener, app).await.unwrap();
        });
        
        Self { address, db_pool }
    }
    
    pub async fn cleanup(&self) {
        sqlx::query!("TRUNCATE TABLE users CASCADE")
            .execute(&self.db_pool)
            .await
            .expect("Failed to clean database");
    }
}
```

**tests/api_tests.rs:**

```rust
use reqwest::StatusCode;
use serde_json::json;

mod common;

#[tokio::test]
async fn test_health_check() {
    // Arrange
    let app = common::TestApp::spawn().await;
    let client = reqwest::Client::new();
    
    // Act
    let response = client
        .get(&format!("{}/health", app.address))
        .send()
        .await
        .expect("Failed to execute request");
    
    // Assert
    assert_eq!(response.status(), StatusCode::OK);
    assert_eq!(response.text().await.unwrap(), "OK");
}

#[tokio::test]
async fn test_create_user() {
    // Arrange
    let app = common::TestApp::spawn().await;
    let client = reqwest::Client::new();
    
    // Act
    let response = client
        .post(&format!("{}/api/users", app.address))
        .json(&json!({
            "username": "testuser",
            "email": "test@example.com",
            "password": "SecurePass123!"
        }))
        .send()
        .await
        .expect("Failed to execute request");
    
    // Assert
    assert_eq!(response.status(), StatusCode::CREATED);
    
    let user: serde_json::Value = response.json().await.unwrap();
    assert_eq!(user["username"], "testuser");
    assert_eq!(user["email"], "test@example.com");
    
    // Cleanup
    app.cleanup().await;
}

#[tokio::test]
async fn test_create_user_duplicate_email() {
    let app = common::TestApp::spawn().await;
    let client = reqwest::Client::new();
    
    // 第一次创建成功
    let response1 = client
        .post(&format!("{}/api/users", app.address))
        .json(&json!({
            "username": "user1",
            "email": "duplicate@example.com",
            "password": "Pass123!"
        }))
        .send()
        .await
        .unwrap();
    assert_eq!(response1.status(), StatusCode::CREATED);
    
    // 第二次创建失败 (邮箱重复)
    let response2 = client
        .post(&format!("{}/api/users", app.address))
        .json(&json!({
            "username": "user2",
            "email": "duplicate@example.com",  // 相同邮箱
            "password": "Pass123!"
        }))
        .send()
        .await
        .unwrap();
    assert_eq!(response2.status(), StatusCode::CONFLICT);
    
    app.cleanup().await;
}
```

### 2. 数据库测试 (Testcontainers)

```rust
use testcontainers::{clients, images::postgres::Postgres, Container};
use sqlx::{PgPool, postgres::PgPoolOptions};

async fn setup_test_db() -> (Container<'_, Postgres>, PgPool) {
    let docker = clients::Cli::default();
    let postgres = docker.run(Postgres::default());
    
    let connection_string = format!(
        "postgres://postgres:postgres@127.0.0.1:{}/postgres",
        postgres.get_host_port_ipv4(5432)
    );
    
    let pool = PgPoolOptions::new()
        .max_connections(5)
        .connect(&connection_string)
        .await
        .expect("Failed to connect to Postgres");
    
    sqlx::migrate!("./migrations")
        .run(&pool)
        .await
        .expect("Failed to run migrations");
    
    (postgres, pool)
}

#[tokio::test]
async fn test_user_crud() {
    let (_container, pool) = setup_test_db().await;
    
    // Create
    let user_id = sqlx::query_scalar!(
        "INSERT INTO users (username, email) VALUES ($1, $2) RETURNING id",
        "testuser",
        "test@example.com"
    )
    .fetch_one(&pool)
    .await
    .unwrap();
    
    // Read
    let user = sqlx::query!("SELECT * FROM users WHERE id = $1", user_id)
        .fetch_one(&pool)
        .await
        .unwrap();
    assert_eq!(user.username, "testuser");
    
    // Update
    sqlx::query!("UPDATE users SET email = $1 WHERE id = $2", "new@example.com", user_id)
        .execute(&pool)
        .await
        .unwrap();
    
    // Delete
    sqlx::query!("DELETE FROM users WHERE id = $1", user_id)
        .execute(&pool)
        .await
        .unwrap();
    
    let count = sqlx::query_scalar!("SELECT COUNT(*) FROM users")
        .fetch_one(&pool)
        .await
        .unwrap();
    assert_eq!(count, Some(0));
}
```

---

## 性能测试

### 使用 Criterion

**benches/my_benchmark.rs:**

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};

fn fibonacci(n: u64) -> u64 {
    match n {
        0 => 0,
        1 => 1,
        n => fibonacci(n - 1) + fibonacci(n - 2),
    }
}

fn fibonacci_iterative(n: u64) -> u64 {
    if n == 0 {
        return 0;
    }
    let (mut a, mut b) = (0, 1);
    for _ in 1..n {
        let temp = a + b;
        a = b;
        b = temp;
    }
    b
}

fn bench_fibonacci(c: &mut Criterion) {
    let mut group = c.benchmark_group("fibonacci");
    
    for i in [10u64, 15, 20].iter() {
        group.bench_with_input(BenchmarkId::new("Recursive", i), i, |b, i| {
            b.iter(|| fibonacci(black_box(*i)));
        });
        
        group.bench_with_input(BenchmarkId::new("Iterative", i), i, |b, i| {
            b.iter(|| fibonacci_iterative(black_box(*i)));
        });
    }
    
    group.finish();
}

criterion_group!(benches, bench_fibonacci);
criterion_main!(benches);
```

**运行基准测试：**

```bash
cargo bench

# 输出示例:
# fibonacci/Recursive/10  time:   [1.2 µs 1.3 µs 1.4 µs]
# fibonacci/Iterative/10  time:   [15 ns 16 ns 17 ns]
#                         change: [-5.2% -3.1% -1.0%] (p = 0.01 < 0.05)
#                         Performance has improved.
```

**生成的 HTML 报告**：`target/criterion/report/index.html`

---

## 属性测试

### 使用 Proptest

```rust
use proptest::prelude::*;

fn reverse_twice<T: Clone>(v: Vec<T>) -> Vec<T> {
    let mut reversed = v.clone();
    reversed.reverse();
    reversed.reverse();
    reversed
}

proptest! {
    // 属性: reverse_twice 应该返回原始向量
    #[test]
    fn test_reverse_twice_property(v in prop::collection::vec(any::<i32>(), 0..100)) {
        prop_assert_eq!(reverse_twice(v.clone()), v);
    }
    
    // 属性: 字符串解析后再序列化应该相等
    #[test]
    fn test_parse_display_roundtrip(n in any::<i32>()) {
        let s = n.to_string();
        let parsed: i32 = s.parse().unwrap();
        prop_assert_eq!(parsed, n);
    }
    
    // 属性: 排序后的数组应该是有序的
    #[test]
    fn test_sort_is_sorted(mut v in prop::collection::vec(any::<i32>(), 0..100)) {
        v.sort();
        prop_assert!(v.windows(2).all(|w| w[0] <= w[1]));
    }
}
```

**自定义策略：**

```rust
use proptest::prelude::*;

// 生成有效的邮箱地址
fn email_strategy() -> impl Strategy<Value = String> {
    r"[a-z]{3,10}@[a-z]{3,10}\.(com|org|net)"
        .prop_map(|s| s.to_string())
}

proptest! {
    #[test]
    fn test_email_validation(email in email_strategy()) {
        prop_assert!(validate_email(&email));
    }
}
```

---

## 模拟与存根

### 使用 Mockall

```rust
use mockall::automock;
use mockall::predicate::*;

// 定义 trait
#[automock]
pub trait UserRepository {
    fn get_user(&self, id: i64) -> Result<User, Error>;
    fn create_user(&mut self, user: User) -> Result<i64, Error>;
}

// 测试使用 mock
#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_user_service() {
        // 创建 mock
        let mut mock_repo = MockUserRepository::new();
        
        // 设置期望
        mock_repo
            .expect_get_user()
            .with(eq(1))
            .times(1)
            .returning(|_| Ok(User {
                id: 1,
                username: "testuser".to_string(),
                email: "test@example.com".to_string(),
            }));
        
        // 调用被测试的代码
        let user = mock_repo.get_user(1).unwrap();
        assert_eq!(user.username, "testuser");
    }
}
```

### HTTP Mock (wiremock)

```rust
use wiremock::{MockServer, Mock, ResponseTemplate};
use wiremock::matchers::{method, path};

#[tokio::test]
async fn test_external_api() {
    // 启动 mock 服务器
    let mock_server = MockServer::start().await;
    
    // 配置 mock 响应
    Mock::given(method("GET"))
        .and(path("/api/users/1"))
        .respond_with(ResponseTemplate::new(200).set_body_json(serde_json::json!({
            "id": 1,
            "name": "Test User"
        })))
        .mount(&mock_server)
        .await;
    
    // 调用客户端代码
    let client = reqwest::Client::new();
    let response = client
        .get(&format!("{}/api/users/1", mock_server.uri()))
        .send()
        .await
        .unwrap();
    
    assert_eq!(response.status(), 200);
    
    let user: serde_json::Value = response.json().await.unwrap();
    assert_eq!(user["name"], "Test User");
}
```

---

## 快照测试

### 使用 Insta

```rust
use insta::assert_yaml_snapshot;

#[derive(serde::Serialize)]
struct User {
    id: i64,
    username: String,
    email: String,
    created_at: String,
}

#[test]
fn test_user_serialization() {
    let user = User {
        id: 1,
        username: "testuser".to_string(),
        email: "test@example.com".to_string(),
        created_at: "2025-10-20T12:00:00Z".to_string(),
    };
    
    // 第一次运行时，会生成快照文件
    // 后续运行会比较当前输出与快照
    assert_yaml_snapshot!(user, @r###"
    ---
    id: 1
    username: testuser
    email: test@example.com
    created_at: "2025-10-20T12:00:00Z"
    "###);
}

#[test]
fn test_api_response() {
    let response = create_user_response();
    
    // 使用动态字段 (忽略每次不同的值)
    insta::with_settings!({
        filters => vec![
            (r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z", "[TIMESTAMP]"),
            (r#""id":\s*\d+"#, r#""id": "[ID]""#),
        ]
    }, {
        assert_yaml_snapshot!(response);
    });
}
```

**快照审查：**

```bash
# 运行测试
cargo test

# 审查快照变更
cargo insta review

# 接受所有快照
cargo insta accept
```

---

## 端到端测试

### CLI 应用测试 (assert_cmd)

```rust
use assert_cmd::Command;
use predicates::prelude::*;

#[test]
fn test_cli_help() {
    let mut cmd = Command::cargo_bin("myapp").unwrap();
    
    cmd.arg("--help")
        .assert()
        .success()
        .stdout(predicate::str::contains("Usage:"));
}

#[test]
fn test_cli_invalid_input() {
    let mut cmd = Command::cargo_bin("myapp").unwrap();
    
    cmd.arg("--invalid")
        .assert()
        .failure()
        .stderr(predicate::str::contains("error:"));
}

#[test]
fn test_cli_file_processing() {
    let mut cmd = Command::cargo_bin("myapp").unwrap();
    
    cmd.arg("process")
        .arg("tests/fixtures/input.txt")
        .assert()
        .success()
        .stdout(predicate::str::contains("Processed 100 lines"));
}
```

### Web 应用测试 (Playwright/Selenium)

```rust
// 注意: 这需要额外的 JavaScript/TypeScript 测试代码
// 这里展示测试结构

// tests/e2e/login.spec.ts
import { test, expect } from '@playwright/test';

test('user can login', async ({ page }) => {
  await page.goto('http://localhost:8080/login');
  
  await page.fill('input[name="username"]', 'testuser');
  await page.fill('input[name="password"]', 'password123');
  await page.click('button[type="submit"]');
  
  await expect(page).toHaveURL('http://localhost:8080/dashboard');
  await expect(page.locator('h1')).toContainText('Welcome, testuser');
});
```

---

## 测试覆盖率

### 使用 cargo-llvm-cov

```bash
# 安装
cargo install cargo-llvm-cov

# 生成覆盖率报告
cargo llvm-cov --html

# 输出:
# Filename                      Regions    Missed Regions     Cover
# ────────────────────────────────────────────────────────────────
# src/lib.rs                         50                 5    90.00%
# src/utils.rs                       30                 0   100.00%
# ────────────────────────────────────────────────────────────────
# TOTAL                              80                 5    93.75%

# 打开 HTML 报告
open target/llvm-cov/html/index.html
```

**CI 集成 (GitHub Actions):**

```yaml
- name: Code Coverage
  run: |
    cargo install cargo-llvm-cov
    cargo llvm-cov --all-features --workspace --lcov --output-path lcov.info

- name: Upload to Codecov
  uses: codecov/codecov-action@v3
  with:
    files: lcov.info
    fail_ci_if_error: true
```

---

## CI/CD 集成

### GitHub Actions 完整配置

```yaml
name: Test Suite

on: [push, pull_request]

env:
  CARGO_TERM_COLOR: always

jobs:
  test:
    name: Test Suite
    runs-on: ubuntu-latest
    
    services:
      postgres:
        image: postgres:16-alpine
        env:
          POSTGRES_USER: test
          POSTGRES_PASSWORD: test
          POSTGRES_DB: testdb
        options: >-
          --health-cmd pg_isready
          --health-interval 10s
          --health-timeout 5s
          --health-retries 5
        ports:
          - 5432:5432
    
    steps:
      - uses: actions/checkout@v4
      
      - name: Install Rust
        uses: dtolnay/rust-toolchain@stable
      
      - name: Cache
        uses: actions/cache@v3
        with:
          path: |
            ~/.cargo/bin/
            ~/.cargo/registry/index/
            ~/.cargo/registry/cache/
            ~/.cargo/git/db/
            target/
          key: ${{ runner.os }}-cargo-${{ hashFiles('**/Cargo.lock') }}
      
      - name: Run Tests
        run: cargo test --all-features --workspace
        env:
          DATABASE_URL: postgres://test:test@localhost:5432/testdb
      
      - name: Run Doc Tests
        run: cargo test --doc
      
      - name: Code Coverage
        run: |
          cargo install cargo-llvm-cov
          cargo llvm-cov --all-features --workspace --lcov --output-path lcov.info
      
      - name: Upload Coverage
        uses: codecov/codecov-action@v3
        with:
          files: lcov.info
          fail_ci_if_error: true
```

---

## 生产监控

### 集成测试作为监控

```rust
// 定时运行的健康检查测试
#[tokio::test]
#[ignore]  // 标记为 "smoke test"
async fn production_health_check() {
    let client = reqwest::Client::new();
    
    let response = client
        .get("https://api.myapp.com/health")
        .send()
        .await
        .expect("Failed to connect to production");
    
    assert_eq!(response.status(), 200);
    
    let health: serde_json::Value = response.json().await.unwrap();
    assert_eq!(health["status"], "healthy");
    assert_eq!(health["database"], "connected");
}
```

**Cron 配置 (每5分钟运行一次):**

```yaml
# .github/workflows/smoke-tests.yml
name: Production Smoke Tests
on:
  schedule:
    - cron: '*/5 * * * *'  # 每5分钟

jobs:
  smoke-tests:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@stable
      - run: cargo test --test smoke_tests -- --ignored
```

---

## 最佳实践

### ✅ 推荐做法

1. **遵循测试金字塔**

   ```text
   单元测试 (80%) > 集成测试 (15%) > E2E测试 (5%)
   ```

2. **使用 AAA 模式**

   ```rust
   #[test]
   fn test_example() {
       // Arrange (准备)
       let input = 5;
       
       // Act (执行)
       let result = add(input, 3);
       
       // Assert (断言)
       assert_eq!(result, 8);
   }
   ```

3. **测试应该独立**

   ```rust
   // ✅ 每个测试都清理自己的数据
   #[tokio::test]
   async fn test_user_creation() {
       let app = TestApp::spawn().await;
       // ... 测试逻辑 ...
       app.cleanup().await;  // 清理
   }
   ```

4. **使用有意义的测试名称**

   ```rust
   // ❌ 不清晰
   #[test]
   fn test1() { ... }
   
   // ✅ 清晰描述测试内容
   #[test]
   fn should_return_error_when_email_is_invalid() { ... }
   ```

5. **测试边界条件**

   ```rust
   #[test]
   fn test_division() {
       assert_eq!(divide(10, 2), 5);     // 正常情况
       assert_eq!(divide(0, 5), 0);      // 零除数
       assert_eq!(divide(i32::MAX, 1), i32::MAX);  // 最大值
   }
   ```

6. **使用属性测试验证不变式**

   ```rust
   proptest! {
       #[test]
       fn test_sort_invariants(v in prop::collection::vec(any::<i32>(), 0..100)) {
           let mut sorted = v.clone();
           sorted.sort();
           
           // 不变式: 排序后长度不变
           prop_assert_eq!(sorted.len(), v.len());
           
           // 不变式: 排序后是有序的
           prop_assert!(sorted.windows(2).all(|w| w[0] <= w[1]));
       }
   }
   ```

7. **Mock 外部依赖**

   ```rust
   // ✅ 不依赖真实的数据库/API
   let mut mock_repo = MockUserRepository::new();
   mock_repo.expect_get_user().returning(|_| Ok(mock_user()));
   ```

8. **使用快照测试处理复杂输出**

   ```rust
   // ✅ 自动验证复杂的 JSON/YAML 结构
   assert_yaml_snapshot!(complex_response);
   ```

9. **测试覆盖率 > 80%**

   ```bash
   cargo llvm-cov --all-features --workspace --html
   # 目标: 80%+ 覆盖率
   ```

10. **CI 中运行所有测试**

    ```yaml
    - run: cargo test --all-features --workspace
    - run: cargo test --doc
    ```

---

## 常见陷阱

### ❌ 避免的错误

1. **测试依赖共享状态**

   ```rust
   // ❌ 测试相互影响
   static mut COUNTER: i32 = 0;
   
   #[test]
   fn test1() {
       unsafe { COUNTER += 1; }
       assert_eq!(unsafe { COUNTER }, 1);  // 可能失败
   }
   
   // ✅ 每个测试独立
   #[test]
   fn test2() {
       let counter = 0;
       assert_eq!(counter + 1, 1);
   }
   ```

2. **忽略错误路径**

   ```rust
   // ❌ 只测试成功场景
   #[test]
   fn test_divide() {
       assert_eq!(divide(10, 2), 5);
   }
   
   // ✅ 也测试错误场景
   #[test]
   fn test_divide_by_zero() {
       assert!(divide(10, 0).is_err());
   }
   ```

3. **过度使用 Mock**

   ```rust
   // ❌ Mock 了所有东西，测试变成了 "测试 Mock"
   mock_a.expect_foo().returning(|| mock_b);
   mock_b.expect_bar().returning(|| mock_c);
   // ...
   
   // ✅ 只 Mock 外部依赖
   mock_http_client.expect_get().returning(|| Ok(response));
   ```

4. **测试实现细节而非行为**

   ```rust
   // ❌ 测试内部实现
   #[test]
   fn test_internal_state() {
       let obj = MyStruct::new();
       assert_eq!(obj.internal_counter, 0);  // 依赖内部状态
   }
   
   // ✅ 测试公共接口
   #[test]
   fn test_public_behavior() {
       let obj = MyStruct::new();
       assert_eq!(obj.get_count(), 0);  // 测试行为
   }
   ```

5. **慢速测试**

   ```rust
   // ❌ 每个测试都启动真实数据库
   #[tokio::test]
   async fn test_slow() {
       let db = setup_real_database().await;  // 耗时 5 秒
       // ...
   }
   
   // ✅ 使用 Testcontainers 或 Mock
   #[tokio::test]
   async fn test_fast() {
       let mock_db = MockDatabase::new();  // 瞬间完成
       // ...
   }
   ```

6. **不清理测试数据**

   ```rust
   // ❌ 测试数据残留
   #[tokio::test]
   async fn test_user() {
       create_user(&db, "testuser").await;
       // 没有清理
   }
   
   // ✅ 每次测试后清理
   #[tokio::test]
   async fn test_user() {
       let app = TestApp::spawn().await;
       create_user(&app.db, "testuser").await;
       app.cleanup().await;  // 清理
   }
   ```

7. **忽略测试失败**

   ```rust
   // ❌ 盲目使用 #[ignore]
   #[test]
   #[ignore]
   fn test_sometimes_fails() { ... }
   
   // ✅ 修复测试或删除它
   ```

8. **没有 CI 集成**

   ```bash
   # ❌ 只在本地运行测试
   cargo test
   
   # ✅ 在 CI 中自动运行
   # .github/workflows/test.yml
   ```

9. **测试覆盖率不足**

   ```bash
   # ❌ 只有 30% 覆盖率
   cargo llvm-cov
   # Coverage: 30%
   
   # ✅ 目标 80%+ 覆盖率
   ```

10. **不使用属性测试**

    ```rust
    // ❌ 手动列举测试用例
    #[test]
    fn test_cases() {
        assert_eq!(add(1, 2), 3);
        assert_eq!(add(5, 5), 10);
        // ...100 行 ...
    }
    
    // ✅ 使用属性测试
    proptest! {
        #[test]
        fn test_add_commutative(a in any::<i32>(), b in any::<i32>()) {
            prop_assert_eq!(add(a, b), add(b, a));
        }
    }
    ```

---

## 参考资源

### 官方文档

- [The Rust Book - Testing](https://doc.rust-lang.org/book/ch11-00-testing.html)
- [cargo test 文档](https://doc.rust-lang.org/cargo/commands/cargo-test.html)

### 测试库

- [Criterion](https://github.com/bheisler/criterion.rs) - 基准测试
- [Proptest](https://github.com/proptest-rs/proptest) - 属性测试
- [Mockall](https://github.com/asomers/mockall) - Mock 框架
- [Insta](https://github.com/mitsuhiko/insta) - 快照测试
- [Wiremock](https://github.com/LukeMathWalker/wiremock-rs) - HTTP Mock

### 工具

- [cargo-llvm-cov](https://github.com/taiki-e/cargo-llvm-cov) - 覆盖率
- [cargo-nextest](https://nexte.st/) - 更快的测试运行器
- [cargo-watch](https://github.com/watchexec/cargo-watch) - 文件监视

### 学习资源

- [Test-Driven Development in Rust](https://www.lurklurk.org/effective-rust/testing.html)
- [Property-Based Testing in Rust](https://proptest-rs.github.io/proptest/intro.html)

---

## 总结

Rust 测试体系的**核心要素**：

1. ✅ **单元测试**：80% 覆盖率
2. ✅ **集成测试**：API + 数据库测试
3. ✅ **性能测试**：Criterion 基准测试
4. ✅ **属性测试**：Proptest 验证不变式
5. ✅ **Mock & Stub**：隔离外部依赖
6. ✅ **快照测试**：复杂输出验证
7. ✅ **E2E 测试**：关键用户流程
8. ✅ **代码覆盖率**：> 80%
9. ✅ **CI/CD 集成**：自动化测试
10. ✅ **生产监控**：Smoke Tests

🧪 **记住**：测试不是负担，而是重构和演进代码的信心来源！高质量的测试让你能够安全地改进系统。
