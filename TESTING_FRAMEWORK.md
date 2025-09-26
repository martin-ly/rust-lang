# 🧪 Rust测试框架指南

**创建时间**: 2025年9月25日 13:48  
**版本**: v1.0  
**适用对象**: Rust开发者  

---

## 📋 框架概述

本指南介绍了Rust的测试框架，包括单元测试、集成测试、文档测试和基准测试。通过系统性的测试，可以确保代码质量和可靠性。

---

## 🎯 测试类型

### 单元测试 (Unit Tests)

- **位置**: 与源代码在同一文件中
- **作用域**: 测试单个模块或函数
- **特点**: 快速、独立、可重复

### 集成测试 (Integration Tests)

- **位置**: `tests/`目录下的独立文件
- **作用域**: 测试整个crate的公共API
- **特点**: 测试模块间的交互

### 文档测试 (Doc Tests)

- **位置**: 文档注释中的代码块
- **作用域**: 验证文档示例的正确性
- **特点**: 确保文档和代码同步

### 基准测试 (Benchmark Tests)

- **位置**: `benches/`目录下的独立文件
- **作用域**: 测试代码性能
- **特点**: 测量执行时间和资源使用

---

## 🛠️ 测试工具

### 内置测试框架

#### 基本测试宏

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_functionality() {
        assert!(true);
    }

    #[test]
    fn test_with_result() -> Result<(), String> {
        // 返回Result的测试
        Ok(())
    }

    #[test]
    #[ignore]
    fn test_expensive_operation() {
        // 被忽略的测试，只在--ignored时运行
    }

    #[test]
    #[should_panic]
    fn test_panics() {
        panic!("This test should panic");
    }
}
```

#### 断言宏

```rust
#[cfg(test)]
mod assertion_tests {
    use super::*;

    #[test]
    fn test_assertions() {
        // 基本断言
        assert!(true);
        assert!(false, "Custom panic message");
        
        // 相等断言
        assert_eq!(2 + 2, 4);
        assert_ne!(3, 4);
        
        // 浮点数断言（考虑精度）
        assert!((0.1 + 0.2 - 0.3).abs() < 1e-10);
        
        // 字符串断言
        assert_eq!("hello", "hello");
        assert_ne!("hello", "world");
    }
}
```

### 第三方测试库

#### 使用proptest进行属性测试

```rust
use proptest::prelude::*;

proptest! {
    #[test]
    fn test_addition_properties(a: i32, b: i32) {
        let result = a + b;
        
        // 测试加法交换律
        prop_assert_eq!(result, b + a);
        
        // 测试加法结合律
        prop_assert_eq!((a + b) + 1, a + (b + 1));
    }
}
```

#### 使用mockall进行模拟测试

```rust
use mockall::predicate::*;
use mockall::mock;

mock! {
    Database {}
    
    impl Database {
        fn get_user(&self, id: u32) -> Option<String>;
        fn save_user(&self, id: u32, name: String) -> bool;
    }
}

#[cfg(test)]
mod mock_tests {
    use super::*;

    #[test]
    fn test_database_mock() {
        let mut mock_db = MockDatabase::new();
        
        mock_db
            .expect_get_user()
            .with(eq(1))
            .times(1)
            .returning(|_| Some("Alice".to_string()));
        
        let result = mock_db.get_user(1);
        assert_eq!(result, Some("Alice".to_string()));
    }
}
```

---

## 📝 测试最佳实践

### 测试组织结构

#### 模块化测试

```rust
// 主模块
pub mod calculator {
    pub fn add(a: i32, b: i32) -> i32 {
        a + b
    }
    
    pub fn divide(a: i32, b: i32) -> Result<i32, String> {
        if b == 0 {
            Err("Division by zero".to_string())
        } else {
            Ok(a / b)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::calculator::*;

    mod add_tests {
        use super::*;

        #[test]
        fn test_add_positive_numbers() {
            assert_eq!(add(2, 3), 5);
        }

        #[test]
        fn test_add_negative_numbers() {
            assert_eq!(add(-2, -3), -5);
        }

        #[test]
        fn test_add_mixed_numbers() {
            assert_eq!(add(-2, 3), 1);
        }
    }

    mod divide_tests {
        use super::*;

        #[test]
        fn test_divide_success() {
            assert_eq!(divide(10, 2), Ok(5));
        }

        #[test]
        fn test_divide_by_zero() {
            assert_eq!(divide(10, 0), Err("Division by zero".to_string()));
        }

        #[test]
        fn test_divide_result() -> Result<(), String> {
            let result = divide(15, 3)?;
            assert_eq!(result, 5);
            Ok(())
        }
    }
}
```

### 测试数据管理

#### 测试夹具

```rust
#[cfg(test)]
mod test_fixtures {
    use super::*;

    struct TestData {
        input: Vec<i32>,
        expected: i32,
    }

    impl TestData {
        fn new(input: Vec<i32>, expected: i32) -> Self {
            TestData { input, expected }
        }
    }

    fn get_test_cases() -> Vec<TestData> {
        vec![
            TestData::new(vec![1, 2, 3], 6),
            TestData::new(vec![-1, -2, -3], -6),
            TestData::new(vec![0, 0, 0], 0),
            TestData::new(vec![], 0),
        ]
    }

    #[test]
    fn test_sum_with_fixtures() {
        for test_case in get_test_cases() {
            let result: i32 = test_case.input.iter().sum();
            assert_eq!(result, test_case.expected);
        }
    }
}
```

#### 临时文件测试

```rust
#[cfg(test)]
mod file_tests {
    use super::*;
    use std::fs;
    use tempfile::tempdir;

    #[test]
    fn test_file_operations() {
        let temp_dir = tempdir().unwrap();
        let file_path = temp_dir.path().join("test.txt");
        
        // 写入测试数据
        fs::write(&file_path, "Hello, World!").unwrap();
        
        // 读取并验证
        let content = fs::read_to_string(&file_path).unwrap();
        assert_eq!(content, "Hello, World!");
        
        // 临时目录会自动清理
    }
}
```

---

## 🔄 集成测试

### 测试组织

#### tests目录结构

```text
tests/
├── common/
│   └── mod.rs          # 公共测试工具
├── integration_test.rs # 主要集成测试
├── api_test.rs        # API测试
└── lib.rs             # 测试库配置
```

#### 公共测试工具

```rust
// tests/common/mod.rs
pub mod utils {
    use std::process::Command;
    use std::time::Duration;

    pub fn setup_test_environment() {
        // 设置测试环境
        std::env::set_var("TEST_MODE", "true");
    }

    pub fn cleanup_test_environment() {
        // 清理测试环境
        std::env::remove_var("TEST_MODE");
    }

    pub fn wait_for_service(port: u16, timeout: Duration) -> bool {
        // 等待服务启动
        let start = std::time::Instant::now();
        while start.elapsed() < timeout {
            if std::net::TcpStream::connect(format!("127.0.0.1:{}", port)).is_ok() {
                return true;
            }
            std::thread::sleep(Duration::from_millis(100));
        }
        false
    }
}
```

#### 集成测试示例

```rust
// tests/integration_test.rs
use my_crate::{Calculator, Database};
use tests::common::utils;

#[test]
fn test_calculator_integration() {
    utils::setup_test_environment();
    
    let calc = Calculator::new();
    let result = calc.evaluate("2 + 3 * 4");
    
    assert_eq!(result, Ok(14));
    
    utils::cleanup_test_environment();
}

#[test]
fn test_database_integration() {
    let db = Database::new(":memory:").unwrap();
    
    db.create_user("Alice", "alice@example.com").unwrap();
    let user = db.get_user_by_email("alice@example.com").unwrap();
    
    assert_eq!(user.name, "Alice");
}
```

---

## 📚 文档测试

### 基本文档测试

```rust
/// 计算两个数的和
/// 
/// # 参数
/// * `a` - 第一个数字
/// * `b` - 第二个数字
/// 
/// # 返回值
/// 返回两个数字的和
/// 
/// # 示例
/// ```
/// use my_crate::add;
/// 
/// let result = add(2, 3);
/// assert_eq!(result, 5);
/// ```
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}

/// 计算阶乘
/// 
/// # 示例
/// ```
/// use my_crate::factorial;
/// 
/// assert_eq!(factorial(5), 120);
/// assert_eq!(factorial(0), 1);
/// ```
pub fn factorial(n: u32) -> u32 {
    match n {
        0 | 1 => 1,
        _ => n * factorial(n - 1),
    }
}
```

### 隐藏文档测试

```rust
/// 内部辅助函数
/// 
/// # 示例
/// ```rust
/// # use my_crate::internal_helper;
/// # let secret = "hidden";
/// internal_helper(secret);
/// ```
fn internal_helper(secret: &str) {
    // 实现细节
}
```

---

## ⚡ 基准测试

### 基本基准测试

```rust
// benches/benchmark.rs
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use my_crate::{fast_function, slow_function};

fn bench_fast_function(c: &mut Criterion) {
    c.bench_function("fast_function", |b| {
        b.iter(|| fast_function(black_box(1000)))
    });
}

fn bench_slow_function(c: &mut Criterion) {
    c.bench_function("slow_function", |b| {
        b.iter(|| slow_function(black_box(1000)))
    });
}

fn bench_comparison(c: &mut Criterion) {
    let mut group = c.benchmark_group("comparison");
    
    group.bench_function("fast", |b| {
        b.iter(|| fast_function(black_box(1000)))
    });
    
    group.bench_function("slow", |b| {
        b.iter(|| slow_function(black_box(1000)))
    });
    
    group.finish();
}

criterion_group!(benches, bench_fast_function, bench_slow_function, bench_comparison);
criterion_main!(benches);
```

### 基准测试配置

```toml
# Cargo.toml
[dev-dependencies]
criterion = "0.5"

[[bench]]
name = "benchmark"
harness = false
```

---

## 🚀 测试运行

### Cargo测试命令

```bash
# 运行所有测试
cargo test

# 运行特定测试
cargo test test_name

# 运行集成测试
cargo test --test integration_test

# 运行被忽略的测试
cargo test --ignored

# 运行基准测试
cargo bench

# 生成测试覆盖率报告
cargo tarpaulin

# 并行运行测试
cargo test --jobs 4
```

### 测试配置

```toml
# Cargo.toml
[profile.test]
debug = true
opt-level = 0

[profile.bench]
debug = false
opt-level = 3
lto = true
```

---

## 📊 测试覆盖率

### 使用tarpaulin

```bash
# 安装tarpaulin
cargo install cargo-tarpaulin

# 生成覆盖率报告
cargo tarpaulin --out Html

# 生成XML报告
cargo tarpaulin --out Xml

# 设置覆盖率阈值
cargo tarpaulin --fail-under 80
```

### 覆盖率配置

```toml
# tarpaulin.toml
[tool.tarpaulin]
fail_under = 80
out = ["Html", "Xml"]
timeout = 300
```

---

## 🔍 测试调试

### 调试技巧

```rust
#[cfg(test)]
mod debug_tests {
    use super::*;

    #[test]
    fn test_with_debug_output() {
        let result = complex_calculation();
        
        // 使用println!进行调试
        println!("Calculation result: {:?}", result);
        
        // 使用dbg!宏
        let value = dbg!(result);
        
        assert!(value > 0);
    }

    #[test]
    fn test_with_assertions() {
        let data = generate_test_data();
        
        // 详细的断言信息
        assert!(
            data.len() > 0,
            "Expected non-empty data, got length: {}",
            data.len()
        );
    }
}
```

---

## 📞 测试最佳实践

### 测试原则

1. **独立性**: 每个测试应该独立运行
2. **可重复性**: 测试结果应该一致
3. **快速性**: 测试应该快速执行
4. **清晰性**: 测试意图应该清晰

### 测试命名

```rust
#[cfg(test)]
mod naming_tests {
    use super::*;

    // ✅ 好的测试命名
    #[test]
    fn test_add_positive_numbers_returns_correct_sum() {
        assert_eq!(add(2, 3), 5);
    }

    #[test]
    fn test_divide_by_zero_returns_error() {
        assert!(divide(10, 0).is_err());
    }

    // ❌ 避免的测试命名
    #[test]
    fn test1() {
        // 名称不清晰
    }

    #[test]
    fn test_add() {
        // 不够具体
    }
}
```

---

**框架状态**: 🔄 持续更新中  
**最后更新**: 2025年9月25日 13:48  
**适用版本**: Rust 1.70+  

---

*本测试框架指南提供了Rust测试的全面指导，帮助您建立可靠的测试体系。如有任何问题或建议，欢迎反馈。*
