# 🦀 Rust API测试规范


## 📊 目录

- [📋 目录](#目录)
- [🎯 测试概述](#测试概述)
  - [测试目标](#测试目标)
  - [测试类型](#测试类型)
- [🧪 单元测试](#单元测试)
  - [基本测试结构](#基本测试结构)
  - [测试数据生成](#测试数据生成)
  - [模拟对象测试](#模拟对象测试)
- [🔗 集成测试](#集成测试)
  - [基本集成测试](#基本集成测试)
  - [异步集成测试](#异步集成测试)
  - [测试容器集成](#测试容器集成)
- [📊 性能测试](#性能测试)
  - [基准测试](#基准测试)
  - [压力测试](#压力测试)
- [🔒 安全测试](#安全测试)
  - [输入验证测试](#输入验证测试)
  - [权限测试](#权限测试)
- [📝 文档测试](#文档测试)
  - [基本文档测试](#基本文档测试)
  - [复杂文档测试](#复杂文档测试)
- [🔄 测试自动化](#测试自动化)
  - [测试脚本](#测试脚本)
  - [CI/CD集成](#cicd集成)
- [📈 测试质量](#测试质量)
  - [测试覆盖率](#测试覆盖率)
  - [测试质量指标](#测试质量指标)
  - [测试审查清单](#测试审查清单)
- [📝 最佳实践](#最佳实践)
  - [测试设计原则](#测试设计原则)
  - [测试组织](#测试组织)
  - [测试数据管理](#测试数据管理)


**创建时间**: 2025年9月25日
**版本**: 1.0.0
**适用对象**: 所有Rust API测试者

---

## 📋 目录

- [🦀 Rust API测试规范](#-rust-api测试规范)
  - [📋 目录](#-目录)
  - [🎯 测试概述](#-测试概述)
  - [🧪 单元测试](#-单元测试)
  - [🔗 集成测试](#-集成测试)
  - [📊 性能测试](#-性能测试)
  - [🔒 安全测试](#-安全测试)
  - [📝 文档测试](#-文档测试)
  - [🔄 测试自动化](#-测试自动化)
  - [📈 测试质量](#-测试质量)
  - [📝 最佳实践](#-最佳实践)

---

## 🎯 测试概述

### 测试目标

1. **功能正确性**: 确保API功能正确
2. **性能保证**: 确保API性能满足要求
3. **安全性**: 确保API安全可靠
4. **稳定性**: 确保API稳定运行
5. **兼容性**: 确保API向后兼容

### 测试类型

- **单元测试**: 测试单个函数或模块
- **集成测试**: 测试模块间交互
- **性能测试**: 测试API性能
- **安全测试**: 测试API安全性
- **文档测试**: 测试文档示例

---

## 🧪 单元测试

### 基本测试结构

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_functionality() {
        // 测试基本功能
        let result = add(2, 3);
        assert_eq!(result, 5);
    }

    #[test]
    fn test_edge_cases() {
        // 测试边界情况
        assert_eq!(add(0, 0), 0);
        assert_eq!(add(-1, 1), 0);
        assert_eq!(add(i32::MAX, 0), i32::MAX);
    }

    #[test]
    #[should_panic]
    fn test_panic_condition() {
        // 测试panic情况
        divide(10, 0);
    }

    #[test]
    fn test_error_handling() {
        // 测试错误处理
        let result = safe_divide(10, 0);
        assert!(result.is_err());

        match result.unwrap_err() {
            ApiError::DivisionByZero => assert!(true),
            _ => assert!(false, "Expected DivisionByZero error"),
        }
    }
}
```

### 测试数据生成

```rust
use proptest::prelude::*;

proptest! {
    #[test]
    fn test_addition_properties(a in any::<i32>(), b in any::<i32>()) {
        let result = add(a, b);

        // 测试交换律
        assert_eq!(result, add(b, a));

        // 测试结合律
        assert_eq!(add(add(a, b), 0), result);
    }

    #[test]
    fn test_string_processing(s in "\\PC*") {
        let result = process_string(&s);

        // 结果长度应该小于等于输入长度
        assert!(result.len() <= s.len());

        // 结果不应该包含空字符
        assert!(!result.contains('\0'));
    }
}
```

### 模拟对象测试

```rust
use mockall::*;

#[automock]
trait Database {
    fn get_user(&self, id: u32) -> Result<User, Error>;
    fn save_user(&mut self, user: &User) -> Result<(), Error>;
}

#[test]
fn test_user_service() {
    let mut mock_db = MockDatabase::new();

    // 设置期望
    mock_db.expect_get_user()
        .with(eq(1))
        .times(1)
        .returning(|_| Ok(User::new("John".to_string())));

    mock_db.expect_save_user()
        .with(eq(User::new("John".to_string())))
        .times(1)
        .returning(|_| Ok(()));

    // 测试服务
    let mut service = UserService::new(mock_db);

    let user = service.get_user(1).unwrap();
    assert_eq!(user.name, "John");

    let result = service.save_user(&user);
    assert!(result.is_ok());
}
```

---

## 🔗 集成测试

### 基本集成测试

```rust
// tests/integration_tests.rs
use my_crate::*;
use tempfile::TempDir;

#[test]
fn test_user_crud_operations() {
    // 设置测试环境
    let temp_dir = TempDir::new().unwrap();
    let db_path = temp_dir.path().join("test.db");

    let mut service = UserService::new(&db_path).unwrap();

    // 创建用户
    let user = User::new("John Doe".to_string(), "john@example.com".to_string());
    let created_user = service.create_user(user).unwrap();
    assert_eq!(created_user.name, "John Doe");

    // 读取用户
    let retrieved_user = service.get_user(created_user.id).unwrap();
    assert_eq!(retrieved_user.unwrap().name, "John Doe");

    // 更新用户
    let mut updated_user = created_user;
    updated_user.name = "Jane Doe".to_string();
    let saved_user = service.update_user(updated_user).unwrap();
    assert_eq!(saved_user.name, "Jane Doe");

    // 删除用户
    let result = service.delete_user(saved_user.id);
    assert!(result.is_ok());

    // 验证删除
    let deleted_user = service.get_user(saved_user.id).unwrap();
    assert!(deleted_user.is_none());
}
```

### 异步集成测试

```rust
use tokio_test;

#[tokio::test]
async fn test_async_user_operations() {
    let mut service = UserService::new().await.unwrap();

    // 创建用户
    let user = User::new("John Doe".to_string(), "john@example.com".to_string());
    let created_user = service.create_user(user).await.unwrap();

    // 并发读取用户
    let futures: Vec<_> = (0..10)
        .map(|_| service.get_user(created_user.id))
        .collect();

    let results = futures::future::join_all(futures).await;

    for result in results {
        assert!(result.is_ok());
        let user = result.unwrap();
        assert_eq!(user.unwrap().name, "John Doe");
    }
}
```

### 测试容器集成

```rust
use testcontainers::*;
use testcontainers::images::postgres::Postgres;

#[tokio::test]
async fn test_with_postgres_container() {
    let docker = clients::Cli::default();
    let postgres_image = Postgres::default();

    let container = docker.run(postgres_image);
    let connection_string = format!(
        "postgresql://postgres:postgres@localhost:{}/postgres",
        container.get_host_port_ipv4(5432)
    );

    let mut service = UserService::new(&connection_string).await.unwrap();

    // 测试数据库操作
    let user = User::new("John Doe".to_string(), "john@example.com".to_string());
    let created_user = service.create_user(user).await.unwrap();

    assert_eq!(created_user.name, "John Doe");
}
```

---

## 📊 性能测试

### 基准测试

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use std::time::Duration;

fn benchmark_user_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("user_operations");

    group.measurement_time(Duration::from_secs(10));
    group.sample_size(100);
    group.confidence_level(0.95);
    group.significance_level(0.05);

    // 基准测试用户创建
    group.bench_function("create_user", |b| {
        let mut service = UserService::new().unwrap();
        b.iter(|| {
            let user = User::new("John Doe".to_string(), "john@example.com".to_string());
            black_box(service.create_user(user).unwrap())
        })
    });

    // 基准测试用户查询
    group.bench_function("get_user", |b| {
        let mut service = UserService::new().unwrap();
        let user = User::new("John Doe".to_string(), "john@example.com".to_string());
        let created_user = service.create_user(user).unwrap();

        b.iter(|| {
            black_box(service.get_user(created_user.id).unwrap())
        })
    });

    // 基准测试用户更新
    group.bench_function("update_user", |b| {
        let mut service = UserService::new().unwrap();
        let user = User::new("John Doe".to_string(), "john@example.com".to_string());
        let created_user = service.create_user(user).unwrap();

        b.iter(|| {
            let mut updated_user = created_user.clone();
            updated_user.name = "Jane Doe".to_string();
            black_box(service.update_user(updated_user).unwrap())
        })
    });

    group.finish();
}

criterion_group!(benches, benchmark_user_operations);
criterion_main!(benches);
```

### 压力测试

```rust
use tokio_test;

#[tokio::test]
async fn test_concurrent_user_creation() {
    let mut service = UserService::new().await.unwrap();

    // 并发创建100个用户
    let futures: Vec<_> = (0..100)
        .map(|i| {
            let user = User::new(
                format!("User {}", i),
                format!("user{}@example.com", i),
            );
            service.create_user(user)
        })
        .collect();

    let start = std::time::Instant::now();
    let results = futures::future::join_all(futures).await;
    let duration = start.elapsed();

    // 验证所有用户都创建成功
    for result in results {
        assert!(result.is_ok());
    }

    // 验证性能要求（100个用户创建应该在1秒内完成）
    assert!(duration.as_secs() < 1);
}
```

---

## 🔒 安全测试

### 输入验证测试

```rust
#[test]
fn test_input_validation() {
    let service = UserService::new().unwrap();

    // 测试空用户名
    let user = User::new("".to_string(), "john@example.com".to_string());
    let result = service.create_user(user);
    assert!(result.is_err());

    // 测试无效邮箱
    let user = User::new("John Doe".to_string(), "invalid-email".to_string());
    let result = service.create_user(user);
    assert!(result.is_err());

    // 测试SQL注入
    let user = User::new("'; DROP TABLE users; --".to_string(), "john@example.com".to_string());
    let result = service.create_user(user);
    assert!(result.is_err());

    // 测试XSS攻击
    let user = User::new("<script>alert('xss')</script>".to_string(), "john@example.com".to_string());
    let result = service.create_user(user);
    assert!(result.is_err());
}
```

### 权限测试

```rust
#[test]
fn test_permission_checks() {
    let service = UserService::new().unwrap();

    // 测试未授权访问
    let result = service.get_user(1);
    assert!(result.is_err());

    // 测试权限提升
    let user = User::new("John Doe".to_string(), "john@example.com".to_string());
    let result = service.create_user(user);
    assert!(result.is_err()); // 应该失败，因为没有创建权限
}
```

---

## 📝 文档测试

### 基本文档测试

```rust
/// 计算两个数的和
///
/// # 参数
///
/// * `a` - 第一个数
/// * `b` - 第二个数
///
/// # 返回值
///
/// 返回两个数的和
///
/// # 示例
///
/// ```rust
/// use my_crate::add;
///
/// assert_eq!(add(2, 3), 5);
/// assert_eq!(add(0, 0), 0);
/// assert_eq!(add(-1, 1), 0);
/// ```
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}
```

### 复杂文档测试

```rust
/// 用户服务
///
/// 提供用户的CRUD操作
///
/// # 示例
///
/// ```rust
/// use my_crate::{UserService, User};
///
/// # async fn example() -> Result<(), Box<dyn std::error::Error>> {
/// let mut service = UserService::new().await?;
///
/// // 创建用户
/// let user = User::new("John Doe".to_string(), "john@example.com".to_string());
/// let created_user = service.create_user(user).await?;
///
/// // 获取用户
/// let retrieved_user = service.get_user(created_user.id).await?;
/// assert_eq!(retrieved_user.unwrap().name, "John Doe");
///
/// // 更新用户
/// let mut updated_user = created_user;
/// updated_user.name = "Jane Doe".to_string();
/// let saved_user = service.update_user(updated_user).await?;
/// assert_eq!(saved_user.name, "Jane Doe");
///
/// // 删除用户
/// service.delete_user(saved_user.id).await?;
/// # Ok(())
/// # }
/// ```
pub struct UserService {
    // 实现细节
}
```

---

## 🔄 测试自动化

### 测试脚本

```bash
#!/bin/bash
# scripts/run-tests.sh

set -e

echo "Running all tests..."

# 运行单元测试
echo "Running unit tests..."
cargo test --lib

# 运行集成测试
echo "Running integration tests..."
cargo test --test '*'

# 运行文档测试
echo "Running documentation tests..."
cargo test --doc

# 运行基准测试
echo "Running benchmark tests..."
cargo bench

# 运行代码覆盖率测试
echo "Running coverage tests..."
cargo tarpaulin --out Html

echo "All tests completed successfully!"
```

### CI/CD集成

```yaml
# .github/workflows/test.yml
name: Test

on:
  push:
    branches: [ main ]
  pull_request:
    branches: [ main ]

env:
  CARGO_TERM_COLOR: always

jobs:
  test:
    name: Test
    runs-on: ubuntu-latest

    steps:
    - uses: actions/checkout@v3

    - name: Install Rust
      uses: actions-rs/toolchain@v1
      with:
        toolchain: stable
        components: rustfmt, clippy
        override: true

    - name: Run unit tests
      run: cargo test --lib

    - name: Run integration tests
      run: cargo test --test '*'

    - name: Run documentation tests
      run: cargo test --doc

    - name: Run benchmark tests
      run: cargo bench

    - name: Run coverage tests
      run: |
        cargo install cargo-tarpaulin
        cargo tarpaulin --out Html

    - name: Upload coverage report
      uses: actions/upload-artifact@v3
      with:
        name: coverage-report
        path: tarpaulin-report.html
```

---

## 📈 测试质量

### 测试覆盖率

```bash
# 安装覆盖率工具
cargo install cargo-tarpaulin

# 运行覆盖率测试
cargo tarpaulin --out Html

# 检查覆盖率阈值
cargo tarpaulin --fail-under 80
```

### 测试质量指标

- **代码覆盖率**: 目标 > 80%
- **分支覆盖率**: 目标 > 70%
- **函数覆盖率**: 目标 > 90%
- **行覆盖率**: 目标 > 80%

### 测试审查清单

- [ ] 单元测试覆盖所有公共函数
- [ ] 集成测试覆盖主要工作流
- [ ] 性能测试验证性能要求
- [ ] 安全测试验证安全性
- [ ] 文档测试验证示例代码
- [ ] 测试覆盖率满足要求
- [ ] 测试运行稳定可靠
- [ ] 测试维护成本合理

---

## 📝 最佳实践

### 测试设计原则

1. **独立性**: 测试之间相互独立
2. **可重复性**: 测试结果可重复
3. **快速性**: 测试运行快速
4. **清晰性**: 测试意图清晰
5. **维护性**: 测试易于维护

### 测试组织

```rust
// 按功能组织测试
#[cfg(test)]
mod tests {
    mod user_tests {
        use super::super::*;

        #[test]
        fn test_user_creation() {
            // 测试用户创建
        }

        #[test]
        fn test_user_validation() {
            // 测试用户验证
        }
    }

    mod api_tests {
        use super::super::*;

        #[test]
        fn test_api_endpoints() {
            // 测试API端点
        }
    }
}
```

### 测试数据管理

```rust
// 测试数据工厂
struct TestDataFactory;

impl TestDataFactory {
    fn create_user() -> User {
        User::new("Test User".to_string(), "test@example.com".to_string())
    }

    fn create_user_with_name(name: String) -> User {
        User::new(name, "test@example.com".to_string())
    }

    fn create_multiple_users(count: usize) -> Vec<User> {
        (0..count)
            .map(|i| User::new(format!("User {}", i), format!("user{}@example.com", i)))
            .collect()
    }
}
```

---

-**遵循这些API测试规范，您将能够建立高质量、可靠的Rust API测试体系！🦀**-
