# Rust 测试策略决策树

本文档提供了一个系统化的 Rust 测试策略决策框架，帮助开发团队根据项目特点选择合适的测试类型、工具和最佳实践。

---

## 快速决策索引

```text
┌─────────────────────────────────────────────────────────────────────────────┐
│                          Rust 测试策略决策入口                                │
└─────────────────────────────────────────────────────────────────────────────┘
                                      │
        ┌─────────────────────────────┼─────────────────────────────┐
        ▼                             ▼                             ▼
   ┌─────────┐                  ┌─────────┐                   ┌─────────┐
   │  项目阶段 │                  │  测试目标 │                   │  代码特征 │
   │ (Stage) │                  │  (Goal) │                   │(Feature)│
   └────┬────┘                  └────┬────┘                   └────┬────┘
        │                            │                             │
   ┌────┴────┐                  ┌────┴────┐                   ┌────┴────┐
   │• 原型开发 │                  │• 功能验证 │                   │• 纯函数   │
   │• 迭代开发 │                  │• 性能基准 │                   │• 异步代码 │
   │• 维护阶段 │                  │• 回归防护 │                   │• I/O操作 │
   │• 重构阶段 │                  │• 文档示例 │                   │• 并发逻辑 │
   └─────────┘                  └─────────┘                   └─────────┘
```

---

## 一、测试类型选择决策树

### 1.1 单元测试 (Unit Tests)

```text
何时选择单元测试?
│
├─► 测试单个函数或方法的独立行为
│   └─► 使用 #[test] 属性标记
│
├─► 验证边界条件和错误处理
│   └─► 结合 should_panic 测试异常情况
│
├─► 需要快速反馈（毫秒级执行）
│   └─► 每个测试聚焦单一职责
│
└─► 模块内部实现细节验证
    └─► 使用 #[cfg(test)] 模块组织

📁 文件位置: src/*.rs 内的 #[cfg(test)] 模块
🎯 覆盖率目标: >80%
⏱️ 执行时间: <10ms / 测试
```

**代码示例：**

```rust
// src/calculator.rs
pub struct Calculator;

impl Calculator {
    pub fn add(a: i32, b: i32) -> i32 {
        a.saturating_add(b)
    }

    pub fn divide(a: f64, b: f64) -> Result<f64, String> {
        if b == 0.0 {
            Err("除数不能为零".to_string())
        } else {
            Ok(a / b)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // 基础功能测试
    #[test]
    fn test_add_positive_numbers() {
        let calc = Calculator;
        assert_eq!(calc.add(2, 3), 5);
    }

    // 边界条件测试
    #[test]
    fn test_add_overflow() {
        let calc = Calculator;
        assert_eq!(calc.add(i32::MAX, 1), i32::MAX); // saturating_add 行为
    }

    // 错误处理测试
    #[test]
    fn test_divide_by_zero() {
        let calc = Calculator;
        let result = calc.divide(10.0, 0.0);
        assert!(result.is_err());
        assert_eq!(result.unwrap_err(), "除数不能为零");
    }

    // 参数化测试模式
    #[test]
    fn test_add_various_cases() {
        let test_cases = vec![
            (0, 0, 0),
            (-1, 1, 0),
            (i32::MAX, 0, i32::MAX),
            (i32::MIN, 0, i32::MIN),
        ];

        let calc = Calculator;
        for (a, b, expected) in test_cases {
            assert_eq!(calc.add(a, b), expected, "测试失败: {} + {}", a, b);
        }
    }
}
```

---

### 1.2 集成测试 (Integration Tests)

```text
何时选择集成测试?
│
├─► 验证多个模块的协作行为
│   └─► 测试 crate 的公共 API
│
├─► 数据库、文件系统、网络交互
│   └─► 使用 testcontainers 或临时目录
│
├─► 端到端工作流验证
│   └─► 模拟真实使用场景
│
└─► 外部依赖集成
    └─► HTTP 客户端、消息队列等

📁 文件位置: tests/*.rs
🎯 覆盖率目标: 关键路径 100%
⏱️ 执行时间: <1s / 测试套件
```

**代码示例：**

```rust
// tests/user_api_integration.rs
use my_app::{AppConfig, Database, UserService};
use std::sync::Arc;

// 共享测试基础设施
mod common;
use common::setup_test_db;

#[tokio::test]
async fn test_user_registration_flow() {
    // Arrange: 设置测试环境
    let db = setup_test_db().await;
    let user_service = UserService::new(Arc::new(db));

    // Act: 执行被测操作
    let result = user_service
        .register_user("alice@example.com", "password123")
        .await;

    // Assert: 验证结果
    assert!(result.is_ok());
    let user = result.unwrap();
    assert_eq!(user.email, "alice@example.com");
    assert!(user.id > 0);

    // 验证数据库状态
    let stored_user = user_service.find_by_email("alice@example.com").await;
    assert!(stored_user.is_some());
}

#[tokio::test]
async fn test_duplicate_email_registration() {
    let db = setup_test_db().await;
    let user_service = UserService::new(Arc::new(db));

    // 第一次注册
    let _ = user_service
        .register_user("bob@example.com", "password123")
        .await;

    // 重复注册应失败
    let result = user_service
        .register_user("bob@example.com", "different_password")
        .await;

    assert!(result.is_err());
    assert!(result.unwrap_err().to_string().contains("已存在"));
}

// tests/common/mod.rs
pub async fn setup_test_db() -> Database {
    use std::env;
    use uuid::Uuid;

    // 使用唯一的测试数据库名称
    let test_db_name = format!("test_db_{}", Uuid::new_v4());
    let database_url = env::var("DATABASE_URL")
        .unwrap_or_else(|_| "postgres://localhost/test".to_string());

    let config = AppConfig {
        database_url: format!("{}/{}", database_url, test_db_name),
        ..Default::default()
    };

    let db = Database::connect(&config.database_url).await.unwrap();
    db.run_migrations().await.unwrap();

    db
}
```

---

### 1.3 文档测试 (Doc Tests)

```text
何时选择文档测试?
│
├─► 公共 API 的代码示例
│   └─► 确保文档与代码同步
│
├─► 展示函数用法和预期输出
│   └─► 使用 ``` 代码块
│
├─► 隐藏初始化代码
│   └─► 使用 # 前缀隐藏行
│
└─► 防止文档过时
    └─► CI 中自动运行

📁 文件位置: src/lib.rs 或模块文件的文档注释中
🎯 覆盖率目标: 所有公共 API
⏱️ 执行时间: 随 cargo test 自动执行
```

**代码示例：**

```rust
//! # 数据处理库
//!
//! 提供高效的数据转换和验证功能。
//!
//! ## 快速开始
//!
//! ```
//! use data_utils::{Validator, DataTransformer};
//!
//! let validator = Validator::new();
//! assert!(validator.is_valid_email("user@example.com"));
//! ```

/// 验证器结构体，用于数据格式验证。
///
/// # 示例
///
/// 基本用法：
///
/// ```
/// use data_utils::Validator;
///
/// let validator = Validator::new();
///
/// // 验证邮箱格式
/// assert!(validator.is_valid_email("test@example.com"));
/// assert!(!validator.is_valid_email("invalid-email"));
/// ```
///
/// 验证 URL：
///
/// ```
/// # use data_utils::Validator;
/// # let validator = Validator::new();
/// assert!(validator.is_valid_url("https://example.com"));
/// assert!(!validator.is_valid_url("not-a-url"));
/// ```
pub struct Validator;

impl Validator {
    /// 创建新的验证器实例。
    ///
    /// # 示例
    ///
    /// ```
    /// use data_utils::Validator;
    ///
    /// let validator = Validator::new();
    /// ```
    pub fn new() -> Self {
        Self
    }

    /// 验证邮箱地址格式。
    ///
    /// # 参数
    ///
    /// * `email` - 待验证的邮箱字符串
    ///
    /// # 返回
    ///
    /// 如果格式有效返回 `true`，否则返回 `false`
    ///
    /// # 示例
    ///
    /// ```
    /// use data_utils::Validator;
    ///
    /// let v = Validator::new();
    ///
    /// // 有效邮箱
    /// assert!(v.is_valid_email("simple@example.com"));
    /// assert!(v.is_valid_email("very.common@example.com"));
    ///
    /// // 无效邮箱
    /// assert!(!v.is_valid_email(""));
    /// assert!(!v.is_valid_email("@example.com"));
    /// assert!(!v.is_valid_email("spaces in@example.com"));
    /// ```
    pub fn is_valid_email(&self, email: &str) -> bool {
        email.contains('@') && !email.contains(' ')
    }
}

// Cargo.toml 配置以启用文档测试
// [lib]
// doctest = true
```

---

### 1.4 基准测试 (Benchmarks)

```text
何时选择基准测试?
│
├─► 识别性能瓶颈
│   └─► 使用 Criterion 或内置 bench
│
├─► 防止性能回归
│   └─► CI 中对比基线
│
├─► 算法优化验证
│   └─► A/B 测试不同实现
│
└─► 内存使用分析
    └─► 结合 valgrind 或 dhat

📁 文件位置: benches/*.rs
🎯 目标: 关键路径性能可量化
⏱️ 执行时间: 数秒到数分钟
```

**代码示例：**

```rust
// benches/sorting_benchmark.rs
use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use my_algorithm::{bubble_sort, quick_sort, merge_sort};

fn sorting_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("sorting_algorithms");

    // 不同数据规模的测试
    for size in [100, 1_000, 10_000].iter() {
        // 生成随机数据
        let data: Vec<i32> = (0..*size).rev().collect();

        group.bench_with_input(
            BenchmarkId::new("bubble_sort", size),
            size,
            |b, _| {
                b.iter(|| bubble_sort(black_box(&data)));
            }
        );

        group.bench_with_input(
            BenchmarkId::new("quick_sort", size),
            size,
            |b, _| {
                b.iter(|| quick_sort(black_box(&data)));
            }
        );

        group.bench_with_input(
            BenchmarkId::new("merge_sort", size),
            size,
            |b, _| {
                b.iter(|| merge_sort(black_box(&data)));
            }
        );
    }

    group.finish();
}

// 异步基准测试
fn async_benchmark(c: &mut Criterion) {
    let rt = tokio::runtime::Runtime::new().unwrap();

    c.bench_function("async_database_query", |b| {
        b.to_async(&rt).iter(|| async {
            let db = setup_db().await;
            db.query("SELECT * FROM users").await.unwrap()
        });
    });
}

criterion_group!(benches, sorting_benchmark, async_benchmark);
criterion_main!(benches);
```

**Cargo.toml 配置：**

```toml
[[bench]]
name = "sorting_benchmark"
harness = false

[dev-dependencies]
criterion = { version = "0.5", features = ["async_tokio"] }
```

---

### 1.5 模糊测试 (Fuzz Testing)

```text
何时选择模糊测试?
│
├─► 解析器和安全关键代码
│   └─► 文件格式解析器
│
├─► 发现边界情况漏洞
│   └─► 使用 cargo-fuzz
│
├─► C FFI 边界检查
│   └─► 防止内存安全问题
│
└─► 输入验证逻辑
    └─► 随机数据注入

📁 文件位置: fuzz/fuzz_targets/*.rs
🎯 目标: 发现 panic 或崩溃
⏱️ 执行时间: 持续运行（CI 或夜间）
```

**代码示例：**

```rust
// fuzz/fuzz_targets/parser.rs
#![no_main]

use libfuzzer_sys::fuzz_target;
use my_parser::JsonParser;

fuzz_target!(|data: &[u8]| {
    // 将随机字节作为输入
    if let Ok(input) = std::str::from_utf8(data) {
        // 解析器不应 panic
        let _ = JsonParser::parse(input);
    }
});

// fuzz/fuzz_targets/http_parser.rs
#![no_main]

use libfuzzer_sys::fuzz_target;
use my_http::RequestParser;

fuzz_target!(|data: &[u8]| {
    // 模糊测试 HTTP 请求解析
    let _ = RequestParser::parse(data);
});
```

**设置和运行：**

```bash
# 安装 cargo-fuzz
cargo install cargo-fuzz

# 初始化模糊测试项目
cargo fuzz init

# 运行模糊测试（默认无限运行）
cargo fuzz run parser

# 带超时运行
cargo fuzz run parser -- -max_total_time=300

# 复现特定崩溃
cargo fuzz run parser crash-abc123
```

---

### 1.6 属性测试 (Property Testing)

```text
何时选择属性测试?
│
├─► 数学性质验证
│   └─► 交换律、结合律等
│
├─► 逆操作验证
│   └─► 序列化/反序列化对
│
├─► 复杂输入空间
│   └─► 使用 proptest
│
└─► 状态机测试
    └─► 模型驱动验证

📁 文件位置: 集成在单元测试或独立测试文件
🎯 目标: 发现边缘案例
⏱️ 执行时间: 秒级（默认 100-10000 次迭代）
```

**代码示例：**

```rust
// 使用 proptest 进行属性测试
use proptest::prelude::*;

// 测试加法交换律
proptest! {
    #[test]
    fn test_addition_is_commutative(a in -1000i32..=1000, b in -1000i32..=1000) {
        prop_assert_eq!(a + b, b + a);
    }

    #[test]
    fn test_serialization_roundtrip(
        user in user_strategy()
    ) {
        let serialized = serde_json::to_string(&user)?;
        let deserialized: User = serde_json::from_str(&serialized)?;
        prop_assert_eq!(user, deserialized);
    }
}

// 自定义策略
fn user_strategy() -> impl Strategy<Value = User> {
    ("[a-zA-Z0-9]{1,20}", 1u64..10000)
        .prop_map(|(name, id)| User { name, id })
}

// 状态机属性测试
use proptest::state_machine::{ReferenceStateMachine, StateMachineTest};

#[derive(Clone, Debug)]
struct MyStateMachine {
    items: Vec<u32>,
}

enum Transition {
    Push(u32),
    Pop,
    Clear,
}

impl ReferenceStateMachine for MyStateMachine {
    type State = Self;
    type Transition = Transition;

    fn init_state() -> BoxedStrategy<Self::State> {
        Just(Self { items: vec![] }).boxed()
    }

    fn transitions(_state: &Self::State) -> BoxedStrategy<Self::Transition> {
        prop_oneof![
            any::<u32>().prop_map(Transition::Push),
            Just(Transition::Pop),
            Just(Transition::Clear),
        ]
        .boxed()
    }

    fn apply(state: &Self::State, transition: &Self::Transition) -> Self::State {
        let mut new_state = state.clone();
        match transition {
            Transition::Push(x) => new_state.items.push(*x),
            Transition::Pop => { new_state.items.pop(); },
            Transition::Clear => new_state.items.clear(),
        }
        new_state
    }
}
```

---

## 二、测试工具选择矩阵

### 2.1 工具对比表

| 工具/库 | 用途 | 适用场景 | 学习曲线 | 维护状态 |
| :--- | :--- | :--- | :--- | :--- |
| **内置 test** | 基础单元/集成测试 | 所有项目 | ⭐ 低 | Rust 内置 |
| **tokio-test** | 异步运行时测试 | async/await 代码 | ⭐⭐ 中 | 活跃 |
| **mockall** | 模拟对象生成 | 依赖隔离 | ⭐⭐ 中 | 活跃 |
| **insta** | 快照测试 | 复杂输出验证 | ⭐⭐ 中 | 活跃 |
| **criterion** | 性能基准测试 | 算法优化 | ⭐⭐⭐ 高 | 活跃 |
| **proptest** | 属性测试 | 不变量验证 | ⭐⭐⭐ 高 | 活跃 |
| **cargo-fuzz** | 模糊测试 | 安全关键代码 | ⭐⭐⭐ 高 | 活跃 |
| **fake** | 测试数据生成 | 需要模拟数据 | ⭐ 低 | 活跃 |
| **assert_cmd** | CLI 测试 | 命令行工具 | ⭐ 低 | 活跃 |
| **predicates** | 断言增强 | 复杂条件验证 | ⭐ 低 | 活跃 |

### 2.2 异步测试：tokio-test

```rust
// 基础异步测试
#[tokio::test]
async fn test_async_function() {
    let result = async_function().await;
    assert_eq!(result, expected);
}

// 使用 tokio::test 宏配置
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn test_concurrent_operations() {
    let handles: Vec<_> = (0..10)
        .map(|i| tokio::spawn(async move { process(i).await }))
        .collect();

    for handle in handles {
        assert!(handle.await.is_ok());
    }
}

// 超时控制
#[tokio::test]
async fn test_with_timeout() {
    let result = tokio::time::timeout(
        Duration::from_secs(1),
        slow_operation()
    ).await;

    assert!(result.is_ok(), "操作超时");
}

// 模拟时间推进
#[tokio::test]
async fn test_timer_behavior() {
    tokio::time::pause();

    let start = tokio::time::Instant::now();
    let timeout = tokio::time::timeout(
        Duration::from_secs(60),
        tokio::time::sleep(Duration::from_secs(30))
    );

    // 手动推进时间
    tokio::time::advance(Duration::from_secs(30)).await;

    assert!(timeout.await.is_ok());
    assert_eq!(start.elapsed(), Duration::from_secs(30));
}
```

### 2.3 模拟对象：mockall

```rust
use mockall::{mock, predicate::*};
use mockall_double::double;

// 定义 trait
#[cfg_attr(test, mockall::automock)]
pub trait Database {
    fn get_user(&self, id: u64) -> Option<User>;
    fn save_user(&mut self, user: &User) -> Result<(), Error>;
    async fn async_query(&self, sql: &str) -> Vec<Row>;
}

// 使用模拟的测试
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_user_service_with_mock() {
        let mut mock_db = MockDatabase::new();

        // 设置预期行为
        mock_db
            .expect_get_user()
            .with(eq(42))
            .times(1)
            .returning(|_| Some(User { id: 42, name: "Alice".to_string() }));

        mock_db
            .expect_save_user()
            .withf(|user| user.name.len() > 0)
            .times(1)
            .returning(|_| Ok(()));

        let service = UserService::new(mock_db);
        let user = service.find_user(42).unwrap();
        assert_eq!(user.name, "Alice");
    }

    // 异步模拟
    #[tokio::test]
    async fn test_async_mock() {
        let mut mock_db = MockDatabase::new();

        mock_db
            .expect_async_query()
            .with(eq("SELECT * FROM users"))
            .returning(|_| vec![]);

        let result = mock_db.async_query("SELECT * FROM users").await;
        assert!(result.is_empty());
    }

    // 序列模拟
    #[test]
    fn test_sequential_calls() {
        let mut mock_db = MockDatabase::new();

        mock_db
            .expect_get_user()
            .times(3)
            .returning(|id| Some(User { id, name: format!("User{}", id) }));

        // 连续调用返回不同值
        assert_eq!(mock_db.get_user(1).unwrap().name, "User1");
        assert_eq!(mock_db.get_user(2).unwrap().name, "User2");
        assert_eq!(mock_db.get_user(3).unwrap().name, "User3");
    }
}

// 条件编译使用模拟
#[double]
use crate::db::Database;

pub struct UserService {
    db: Database,
}
```

### 2.4 快照测试：insta

```rust
use insta::{assert_snapshot, with_settings};
use serde::Serialize;

#[derive(Serialize)]
struct ApiResponse {
    users: Vec<User>,
    total: usize,
    page: usize,
}

#[test]
fn test_api_response_format() {
    let response = ApiResponse {
        users: vec![
            User { id: 1, name: "Alice".to_string() },
            User { id: 2, name: "Bob".to_string() },
        ],
        total: 2,
        page: 1,
    };

    // 自动创建和管理快照文件
    assert_snapshot!(serde_json::to_string_pretty(&response).unwrap());
}

// 带设置值的快照
#[test]
fn test_with_filters() {
    with_settings!({
        filters => vec![
            (r"\d{4}-\d{2}-\d{2}", "[DATE]"),
            (r"user_\d+", "user_[ID]"),
        ],
    }, {
        let output = generate_report();
        assert_snapshot!(output);
    });
}

// 内联快照
#[test]
fn test_inline_snapshot() {
    let result = format_output();
    insta::assert_snapshot!(result, @"预期输出内容");
}

//  glob 快照测试
#[test]
fn test_all_fixtures() {
    insta::glob!("fixtures/*.input", |path| {
        let input = std::fs::read_to_string(path).unwrap();
        let output = process_input(&input);
        assert_snapshot!(output);
    });
}
```

**工作流程：**

```bash
# 首次运行创建快照
cargo test

# 审查和接受快照变更
cargo insta review

# 接受所有快照
cargo insta accept

# 拒绝变更
cargo insta reject
```

### 2.5 基准测试：Criterion

```rust
use criterion::{Criterion, BenchmarkGroup, measurement::WallTime};
use criterion::async_executor::FuturesExecutor;

fn configure_benchmark(group: &mut BenchmarkGroup<WallTime>) {
    group
        .warm_up_time(Duration::from_secs(3))
        .measurement_time(Duration::from_secs(5))
        .sample_size(200);
}

fn bench_database_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("db_operations");
    configure_benchmark(&mut group);

    group.bench_function("insert", |b| {
        let db = setup_test_database();
        b.iter(|| db.insert(generate_random_user()));
    });

    group.bench_function("query_by_id", |b| {
        let db = setup_test_database_with_data(1000);
        let mut i = 0;
        b.iter(|| {
            i = (i + 1) % 1000;
            db.query_by_id(i)
        });
    });

    group.finish();
}

// 自定义测量器
use criterion::measurement::Measurement;

fn bench_with_custom_measurement(c: &mut Criterion) {
    c.bench_function_with_input(
        "allocations",
        &data,
        |b, data| {
            b.iter(|| {
                let _ = process_data(data);
            });
        }
    );
}

criterion_group!(benches, bench_database_operations);
criterion_main!(benches);
```

---

## 三、测试策略维度

### 3.1 测试金字塔

```text
                    ▲
                   /│\
                  / │ \         E2E 测试 (5%)
                 /  │  \        - 完整用户场景
                /   │   \       - 慢，但覆盖关键路径
               /────┼────\
              /     │     \     集成测试 (15%)
             /      │      \    - 模块间协作
            /       │       \   - 数据库/外部服务
           /────────┼────────\
          /         │         \ 单元测试 (80%)
         /          │          \- 快速反馈
        /           │           \- 高覆盖率
       ──────────────────────────
```

**Rust 项目金字塔实现：**

```text
my_project/
├── src/
│   └── *.rs          # 单元测试 (#[cfg(test)])
├── tests/
│   └── *.rs          # 集成测试
├── benches/
│   └── *.rs          # 性能测试
├── examples/
│   └── *.rs          # 示例 (可兼作简单 E2E)
└── tests/e2e/
    └── *.rs          # 端到端测试 (可选)
```

### 3.2 覆盖率目标

| 层级 | 目标 | 工具 | 备注 |
| :--- | :--- | :--- | :--- |
| **行覆盖率** | ≥80% | cargo-tarpaulin | 核心业务逻辑 ≥90% |
| **分支覆盖率** | ≥70% | cargo-tarpaulin | 关键决策路径 |
| **函数覆盖率** | ≥90% | llvm-cov | 公共 API 100% |
| **文档覆盖率** | 100% | rustdoc --test | 所有公共项 |

**配置示例：**

```toml
# tarpaulin.toml
[engine]
impl = "Llvm"

[report]
output = ["Html", "Xml", "Stdout"]

[run]
exclude-files = ["tests/*", "benches/*", "examples/*"]
exclude = ["integration_tests"]

[target]
timeout = "300s"
```

```yaml
# .github/workflows/coverage.yml
name: Coverage

on: [push, pull_request]

jobs:
  coverage:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Install tarpaulin
        run: cargo install cargo-tarpaulin

      - name: Generate coverage
        run: cargo tarpaulin --out Xml --out Html

      - name: Upload to Codecov
        uses: codecov/codecov-action@v3
        with:
          files: ./cobertura.xml
          fail_ci_if_error: true
```

### 3.3 CI 集成策略

```yaml
# .github/workflows/test.yml
name: Test Suite

on:
  push:
    branches: [main, develop]
  pull_request:
    branches: [main]

env:
  CARGO_TERM_COLOR: always
  RUST_BACKTRACE: 1

jobs:
  # 快速检查 - 每次提交运行
  quick-check:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@stable
      - uses: Swatinem/rust-cache@v2

      - name: Format check
        run: cargo fmt --check

      - name: Clippy lint
        run: cargo clippy --all-targets --all-features -- -D warnings

      - name: Unit tests
        run: cargo test --lib -- --test-threads=$(nproc)

  # 完整测试套件 - PR 时运行
  full-test:
    runs-on: ${{ matrix.os }}
    strategy:
      matrix:
        os: [ubuntu-latest, windows-latest, macos-latest]
        rust: [stable, beta]
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@master
        with:
          toolchain: ${{ matrix.rust }}
      - uses: Swatinem/rust-cache@v2

      - name: Run all tests
        run: cargo test --all-features

      - name: Documentation tests
        run: cargo test --doc

      - name: Build documentation
        run: cargo doc --no-deps

  # 性能回归测试 - 定期运行
  perf-regression:
    runs-on: ubuntu-latest
    if: github.event_name == 'pull_request'
    steps:
      - uses: actions/checkout@v4
      - uses: boa-dev/criterion-compare-action@v3
        with:
          branchName: ${{ github.base_ref }}
          token: ${{ secrets.GITHUB_TOKEN }}

  # 安全审计
  security-audit:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: rustsec/audit-check@v1
        with:
          token: ${{ secrets.GITHUB_TOKEN }}
```

### 3.4 性能回归防护

```rust
// benches/regression_tests.rs
use criterion::{criterion_group, criterion_main, Criterion};

fn critical_path_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("critical_path");

    // 设置严格的性能阈值
    group.significance_level(0.05)
         .sample_size(500);

    group.bench_function("parse_large_file", |b| {
        let data = generate_test_data(10_000);
        b.iter(|| parser::parse(&data));
    });

    // 对比基线性能
    group.bench_function("current_impl", |b| {
        b.iter_batched(
            setup_data,
            |data| current_implementation(data),
            criterion::BatchSize::SmallInput
        );
    });

    group.finish();
}

criterion_group! {
    name = benches;
    config = Criterion::default()
        .with_plots()
        .save_baseline("main".to_owned());
    targets = critical_path_benchmark
}
criterion_main!(benches);
```

---

## 四、最佳实践

### 4.1 测试组织结构

```text
crates/
├── core/
│   ├── src/
│   │   ├── lib.rs
│   │   ├── parser.rs
│   │   └── parser/
│   │       ├── mod.rs
│   │       └── tests.rs      # 内联单元测试
│   └── tests/
│       ├── common/
│       │   ├── mod.rs        # 共享测试工具
│       │   └── fixtures.rs   # 测试数据
│       └── integration/      # 集成测试分类
│           ├── api_tests.rs
│           └── db_tests.rs
├── api/
│   └── tests/
│       └── e2e/              # 端到端测试
└── shared/
    └── src/
        └── test_helpers/     # 跨 crate 测试工具
```

**命名约定：**

```rust
// 测试函数命名
#[test]
fn test_<被测功能>_<场景>_<预期结果>() {
    // test_user_login_with_valid_credentials_succeeds
    // test_user_login_with_invalid_password_fails
}

// 模块组织
#[cfg(test)]
mod tests {
    mod unit;
    mod property;
    mod fuzz;
}
```

### 4.2 测试数据管理

```rust
// tests/common/fixtures.rs
use once_cell::sync::Lazy;
use std::collections::HashMap;

// 静态测试数据
pub static VALID_USERS: Lazy<Vec<User>> = Lazy::new(|| {
    vec![
        User {
            id: 1,
            email: "alice@example.com".into(),
            role: Role::Admin,
        },
        User {
            id: 2,
            email: "bob@example.com".into(),
            role: Role::User,
        },
    ]
});

// 工厂函数
pub struct UserFactory;

impl UserFactory {
    pub fn admin() -> User {
        User {
            id: rand::random(),
            email: format!("admin{}@test.com", rand::random::<u32>()),
            role: Role::Admin,
        }
    }

    pub fn user() -> User {
        User {
            id: rand::random(),
            email: format!("user{}@test.com", rand::random::<u32>()),
            role: Role::User,
        }
    }

    pub fn with_email(email: &str) -> User {
        User {
            id: rand::random(),
            email: email.into(),
            role: Role::User,
        }
    }
}

// 使用 fake crate 生成数据
use fake::{Fake, Faker};
use fake::faker::internet::en::SafeEmail;
use fake::faker::name::en::Name;

pub fn generate_test_users(count: usize) -> Vec<User> {
    (0..count)
        .map(|_| User {
            id: Faker.fake(),
            name: Name().fake(),
            email: SafeEmail().fake(),
        })
        .collect()
}
```

### 4.3 异步测试模式

```rust
// 模式 1: 基本异步测试
#[tokio::test]
async fn basic_async_test() {
    let result = async_operation().await;
    assert!(result.is_ok());
}

// 模式 2: 并发测试
#[tokio::test]
async fn concurrent_test() {
    let handles: Vec<_> = (0..10)
        .map(|i| tokio::spawn(async move { process(i).await }))
        .collect();

    let results = futures::future::join_all(handles).await;
    assert!(results.iter().all(|r| r.is_ok()));
}

// 模式 3: 超时控制
#[tokio::test]
async fn test_with_timeout() {
    let result = tokio::time::timeout(
        Duration::from_secs(5),
        potentially_slow_operation()
    ).await;

    assert!(result.is_ok(), "操作超时");
}

// 模式 4: 模拟时间
#[tokio::test]
async fn test_time_based_logic() {
    tokio::time::pause();

    let start = Instant::now();
    let handle = tokio::spawn(async {
        tokio::time::sleep(Duration::from_secs(60)).await;
    });

    tokio::time::advance(Duration::from_secs(30)).await;
    assert!(!handle.is_finished());

    tokio::time::advance(Duration::from_secs(30)).await;
    assert!(handle.is_finished());

    assert_eq!(start.elapsed(), Duration::from_secs(60));
}

// 模式 5: 共享状态管理
use std::sync::Arc;
use tokio::sync::RwLock;

#[tokio::test]
async fn test_shared_state() {
    let state = Arc::new(RwLock::new(Vec::new()));

    let mut handles = vec![];
    for i in 0..100 {
        let state = Arc::clone(&state);
        handles.push(tokio::spawn(async move {
            let mut guard = state.write().await;
            guard.push(i);
        }));
    }

    for handle in handles {
        handle.await.unwrap();
    }

    let final_state = state.read().await;
    assert_eq!(final_state.len(), 100);
}
```

### 4.4 测试文档化

```rust
/// # 测试说明
///
/// ## 正常场景
/// ```
/// use my_crate::Parser;
///
/// let parser = Parser::new();
/// let result = parser.parse("valid input");
/// assert!(result.is_ok());
/// ```
///
/// ## 边界条件
/// ```
/// use my_crate::Parser;
///
/// let parser = Parser::new();
///
/// // 空输入
/// assert!(parser.parse("").is_err());
///
/// // 超长输入
/// let long_input = "x".repeat(10000);
/// assert!(parser.parse(&long_input).is_err());
/// ```
///
/// ## 错误处理
/// ```
/// use my_crate::Parser;
///
/// let parser = Parser::new();
/// let err = parser.parse("invalid").unwrap_err();
///
/// assert!(matches!(err, ParseError::InvalidFormat));
/// ```
pub struct Parser;

// 测试文档模块
#[cfg(test)]
mod test_documentation {
    //! ## 测试覆盖矩阵
    //!
    //! | 功能 | 单元测试 | 集成测试 | 文档测试 |
    //! | :--- | :--- | :--- | :--- |
    //! | 解析 | ✅ | ✅ | ✅ |
    //! | 验证 | ✅ | ✅ | ❌ |
    //! | 序列化 | ✅ | ❌ | ✅ |
    //!
    //! ## 已知限制
    //! - 不支持超过 1MB 的输入
    //! - 多线程环境下需要外部同步
}
```

---

## 五、决策流程图

```text
开始测试规划
      │
      ▼
┌─────────────────┐
│ 需要测试什么？  │
└─────────────────┘
      │
      ├─► 单个函数/方法 ──► 单元测试 ──► #[test] + mockall
      │
      ├─► 模块间交互 ─────► 集成测试 ──► tests/ 目录
      │
      ├─► 公共 API ───────► 文档测试 ──► rustdoc --test
      │
      ├─► 性能指标 ───────► 基准测试 ──► Criterion
      │
      ├─► 安全关键代码 ───► 模糊测试 ──► cargo-fuzz
      │
      └─► 不变量验证 ─────► 属性测试 ──► proptest

继续深入：异步代码？
      │
      ├─► 是 ──► tokio-test + #[tokio::test]
      │
      └─► 否 ──► 标准测试

继续深入：外部依赖？
      │
      ├─► 是 ──► 使用 mockall 模拟
      │
      └─► 否 ──► 直接测试

继续深入：复杂输出？
      │
      ├─► 是 ──► insta 快照测试
      │
      └─► 否 ──► 常规断言
```

---

## 六、快速参考卡片

### 6.1 常用命令

```bash
# 运行所有测试
cargo test

# 仅运行单元测试
cargo test --lib

# 仅运行集成测试
cargo test --test integration_test_name

# 运行特定测试
cargo test test_name_pattern

# 文档测试
cargo test --doc

# 基准测试
cargo bench

# 覆盖率
cargo tarpaulin

# 模糊测试
cargo fuzz run target_name

# 性能分析
cargo flamegraph
```

### 6.2 常用属性

| 属性 | 用途 |
| :--- | :--- |
| `#[test]` | 标记测试函数 |
| `#[ignore]` | 跳过测试 |
| `#[should_panic]` | 预期 panic |
| `#[tokio::test]` | 异步测试 |
| `#[tokio::test(flavor = "multi_thread")]` | 多线程异步 |
| `#[serial]` | 串行执行（serial_test crate） |
| `#[cfg(test)]` | 测试专用代码 |

---

## 七、推荐配置模板

### 7.1 Cargo.toml 测试配置

```toml
[dev-dependencies]
# 基础测试
tokio-test = "0.4"
assert_matches = "1.5"

# 模拟
mockall = "0.12"

# 快照测试
insta = { version = "1.34", features = ["yaml", "json"] }

# 属性测试
proptest = "1.4"

# 测试数据
fake = { version = "2.9", features = ["derive"] }

# CLI 测试
assert_cmd = "2.0"
predicates = "3.0"

# 基准测试
criterion = { version = "0.5", features = ["async_tokio", "html_reports"] }

# 并发测试控制
serial_test = "3.0"

[profile.test]
opt-level = 1          # 测试时轻度优化
debug = true
lto = false

[profile.bench]
opt-level = 3
debug = false
lto = true

[[bench]]
name = "my_benchmark"
harness = false
```

### 7.2 测试环境配置

```rust
// .cargo/config.toml 或 tests/config.rs

#[cfg(test)]
pub mod test_config {
    use std::sync::Once;

    static INIT: Once = Once::new();

    pub fn setup() {
        INIT.call_once(|| {
            // 初始化日志
            let _ = env_logger::builder()
                .is_test(true)
                .filter_level(log::LevelFilter::Debug)
                .try_init();

            // 设置测试环境变量
            std::env::set_var("TEST_MODE", "true");

            // 初始化资源
        });
    }
}
```

---

## 八、参考资源

- [Rust Testing Guide](https://doc.rust-lang.org/rustc/tests/index.html)
- [Mockall Documentation](https://docs.rs/mockall)
- [Criterion.rs Book](https://bheisler.github.io/criterion.rs/book/)
- [Proptest Book](https://altsysrq.github.io/proptest-book/)
- [Insta Documentation](https://insta.rs/docs/)
- [Tokio Testing](https://tokio.rs/tokio/topics/testing)

---

*文档版本: 1.0*
*最后更新: 2026-02-21*
