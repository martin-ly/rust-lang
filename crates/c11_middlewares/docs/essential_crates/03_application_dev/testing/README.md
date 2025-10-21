# 测试工具

> **核心库**: criterion, proptest, mockall, wiremock  
> **适用场景**: 单元测试、基准测试、属性测试、Mock

---

## 📋 测试工具

| 库 | 类型 | 用途 | 推荐度 |
|-----|------|------|--------|
| **criterion** | 基准测试 | 性能测试 | ⭐⭐⭐⭐⭐ |
| **proptest** | 属性测试 | 随机测试 | ⭐⭐⭐⭐ |
| **mockall** | Mock | 单元测试 | ⭐⭐⭐⭐⭐ |
| **wiremock** | HTTP Mock | 集成测试 | ⭐⭐⭐⭐ |

---

## ⚡ criterion - 基准测试

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn fibonacci(n: u64) -> u64 {
    match n {
        0 => 1,
        1 => 1,
        n => fibonacci(n-1) + fibonacci(n-2),
    }
}

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("fib 20", |b| b.iter(|| fibonacci(black_box(20))));
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
```

---

## 🎲 proptest - 属性测试

```rust
use proptest::prelude::*;

proptest! {
    #[test]
    fn test_reverse_reverse(s in ".*") {
        let reversed: String = s.chars().rev().collect();
        let double_reversed: String = reversed.chars().rev().collect();
        prop_assert_eq!(s, double_reversed);
    }
}
```

---

## 🎭 mockall - Mock

```rust
use mockall::*;
use mockall::predicate::*;

#[automock]
trait Database {
    fn get_user(&self, id: u32) -> Option<String>;
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_get_user() {
        let mut mock = MockDatabase::new();
        mock.expect_get_user()
            .with(eq(1))
            .times(1)
            .returning(|_| Some("Alice".to_string()));
        
        assert_eq!(mock.get_user(1), Some("Alice".to_string()));
    }
}
```

---

**文档版本**: 1.0.0  
**最后更新**: 2025-10-20
