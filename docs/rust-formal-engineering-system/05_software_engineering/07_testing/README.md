# 测试

> **创建日期**: 2026-02-20
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成

> 内容已整合至： [testing_cheatsheet.md](../../../quick_reference/testing_cheatsheet.md)

[返回主索引](../../00_master_index.md)

---

## Rust 测试生态系统

### 单元测试

```rust
// 模块内的测试
#[cfg(test)]
mod tests {
    use super::*;

    // 基本测试
    #[test]
    fn test_add() {
        assert_eq!(add(2, 3), 5);
    }

    // 自定义错误信息
    #[test]
    fn test_add_with_message() {
        let result = add(2, 3);
        assert!(result > 0, "Result should be positive, got {}", result);
    }

    // 应该 panic 的测试
    #[test]
    #[should_panic(expected = "division by zero")]
    fn test_divide_by_zero() {
        divide(10, 0);
    }

    // 忽略测试
    #[test]
    #[ignore = "slow test"]
    fn slow_test() {
        // 长时间运行的测试
    }

    // 返回 Result 的测试
    #[test]
    fn test_with_result() -> Result<(), String> {
        let result = some_operation()?;
        assert_eq!(result, 42);
        Ok(())
    }
}

fn add(a: i32, b: i32) -> i32 {
    a + b
}

fn divide(a: i32, b: i32) -> i32 {
    if b == 0 {
        panic!("division by zero");
    }
    a / b
}

fn some_operation() -> Result<i32, String> {
    Ok(42)
}
```

### 集成测试

```rust
// tests/integration_test.rs
use my_crate::add;

#[test]
fn test_add_integration() {
    assert_eq!(add(2, 3), 5);
}
```

### 文档测试

```rust
/// 加法函数
///
/// # Examples
///
/// ```
/// use my_crate::add;
/// let result = add(2, 3);
/// assert_eq!(result, 5);
/// ```
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}
```

### 属性测试

```rust
// 使用 proptest 进行属性测试
#[cfg(test)]
mod property_tests {
    use proptest::prelude::*;

    proptest! {
        // 测试加法交换律
        #[test]
        fn test_add_commutative(a: i32, b: i32) {
            prop_assert_eq!(add(a, b), add(b, a));
        }

        // 测试加法结合律
        #[test]
        fn test_add_associative(a: i32, b: i32, c: i32) {
            prop_assert_eq!(
                add(add(a, b), c),
                add(a, add(b, c))
            );
        }
    }
}

fn add(a: i32, b: i32) -> i32 {
    a + b
}
```

### 模拟与 Mock

```rust
// 使用 mockall 创建 mock
#[cfg(test)]
mod mock_tests {
    use mockall::automock;

    #[automock]
    trait Database {
        fn get_user(&self, id: u64) -> Option<String>;
        fn save_user(&mut self, id: u64, name: &str) -> Result<(), String>;
    }

    #[test]
    fn test_with_mock() {
        let mut mock = MockDatabase::new();
        mock.expect_get_user()
            .with(mockall::predicate::eq(1))
            .returning(|_| Some("Alice".to_string()));

        assert_eq!(mock.get_user(1), Some("Alice".to_string()));
    }
}
```

## 相关文档

| 文档 | 描述 | 路径 |
| :--- | :--- | :--- |
| 测试速查表 | 完整测试指南 | [../../../quick_reference/testing_cheatsheet.md](../../../quick_reference/testing_cheatsheet.md) |
| 测试覆盖指南 | 测试覆盖率文档 | [../../../TESTING_COVERAGE_GUIDE.md](../../../TESTING_COVERAGE_GUIDE.md) |
| 性能测试报告 | 性能测试指南 | [../../../05_guides/PERFORMANCE_TESTING_REPORT.md](../../../05_guides/PERFORMANCE_TESTING_REPORT.md) |
