# 测试

> **创建日期**: 2026-02-20
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成

> **概念说明**: 测试是软件质量保障的核心环节，Rust 提供内建的测试框架支持单元测试、集成测试和文档测试。形式化测试通过属性测试（Property-based Testing）和模型检查验证代码正确性。

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

### 形式化验证测试

```rust
// 使用 Kani 进行形式化验证
#[cfg(kani)]
mod verification_tests {
    // 验证溢出安全
    #[kani::proof]
    fn test_add_no_overflow() {
        let a: u32 = kani::any();
        let b: u32 = kani::any();
        kani::assume(a < 1000 && b < 1000);
        let result = a + b;
        assert!(result < 2000);
    }

    // 验证内存安全
    #[kani::proof]
    fn test_vec_access() {
        let v = vec![1, 2, 3];
        let idx: usize = kani::any();
        kani::assume(idx < v.len());
        assert!(v[idx] > 0);
    }
}

// 使用 Prusti 进行契约验证
#[cfg(prusti)]
mod contract_tests {
    #[requires(x > 0)]
    #[ensures(result > x)]
    fn double(x: i32) -> i32 {
        x * 2
    }
}
```

### 并发测试

```rust
#[cfg(test)]
mod concurrency_tests {
    use std::sync::Arc;
    use std::thread;

    #[test]
    fn test_concurrent_counter() {
        let counter = Arc::new(std::sync::Mutex::new(0));
        let mut handles = vec![];

        for _ in 0..10 {
            let c = Arc::clone(&counter);
            let handle = thread::spawn(move || {
                let mut num = c.lock().unwrap();
                *num += 1;
            });
            handles.push(handle);
        }

        for handle in handles {
            handle.join().unwrap();
        }

        assert_eq!(*counter.lock().unwrap(), 10);
    }
}
```

---

## 形式化方法

| 文档 | 描述 | 路径 |
| :--- | :--- | :--- |
| 形式化方法概述 | 形式化验证基础理论 | [../../../../research_notes/formal_methods/README.md](../../../../research_notes/formal_methods/README.md) |
| 类型系统形式化 | 类型理论数学定义 | [../../../../research_notes/formal_methods/type_system_formalization.md](../../../../research_notes/formal_methods/type_system_formalization.md) |
| 所有权模型形式化 | 所有权系统数学定义 | [../../../../research_notes/formal_methods/ownership_model.md](../../../../research_notes/formal_methods/ownership_model.md) |
| 证明索引 | 形式化证明集合 | [../../../../research_notes/PROOF_INDEX.md](../../../../research_notes/PROOF_INDEX.md) |

## 相关文档

| 文档 | 描述 | 路径 |
| :--- | :--- | :--- |
| 测试速查表 | 完整测试指南 | [../../../quick_reference/testing_cheatsheet.md](../../../quick_reference/testing_cheatsheet.md) |
| 测试覆盖指南 | 测试覆盖率文档 | [../../../TESTING_COVERAGE_GUIDE.md](../../../TESTING_COVERAGE_GUIDE.md) |
| 性能测试报告 | 性能测试指南 | [../../../05_guides/PERFORMANCE_TESTING_REPORT.md](../../../05_guides/PERFORMANCE_TESTING_REPORT.md) |
| 质量保障指南 | 质量保障体系 | [../../../../research_notes/QUALITY_CHECKLIST.md](../../../../research_notes/QUALITY_CHECKLIST.md) |
| 工具指南 | 验证工具使用 | [../../../../research_notes/TOOLS_GUIDE.md](../../../../research_notes/TOOLS_GUIDE.md) |
| 安全分析 | 安全边界分析 | [../../../../research_notes/SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS.md](../../../../research_notes/SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS.md) |

---

[返回主索引](../../00_master_index.md) | [返回软件工程索引](../README.md)
