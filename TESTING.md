# 测试指南

> **最后更新**: 2026-04-10

---

## 测试策略

本项目采用多层次测试策略:

- 单元测试: 测试单个函数和模块
- 集成测试: 测试多个模块协作
- 基准测试: 性能测试
- 文档测试: 代码示例验证
- Miri 测试: 内存安全验证

---

## 运行测试

### 所有测试

```bash
cargo test --workspace
```

### 特定 Crate 测试

```bash
cargo test -p c01_ownership_borrow_scope
cargo test -p c06_async
```

### 特定测试

```bash
cargo test test_name -p c01_ownership_borrow_scope
```

### 忽略慢的测试

```bash
cargo test --workspace -- --skip slow
```

---

## 单元测试

### 测试位置

单元测试位于:

- src/ 文件中的 #[cfg(test)] 模块
- tests/ 目录下的测试文件

### 基本示例

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_add() {
        assert_eq!(add(2, 3), 5);
    }

    #[test]
    #[should_panic]
    fn test_divide_by_zero() {
        divide(10, 0);
    }
}
```

---

## 集成测试

### 运行集成测试

```bash
cargo test -p integration_tests
```

### 测试结构

```rust
// tests/integration_test.rs
use c01_ownership_borrow_scope::*;
use c02_type_system::*;

#[test]
fn test_cross_crate() {
    // 测试多个 crate 协作
}
```

---

## 基准测试

### 运行基准测试

```bash
# 所有基准测试
cargo bench --workspace

# 特定 crate
cargo bench -p c08_algorithms
```

### 基准测试示例

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn fibonacci(n: u64) -> u64 {
    match n {
        0 => 1,
        1 => 1,
        n => fibonacci(n - 1) + fibonacci(n - 2),
    }
}

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("fib 20", |b| b.iter(|| fibonacci(black_box(20))));
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
```

---

## 异步测试

### Tokio 测试

```rust
#[tokio::test]
async fn test_async_function() {
    let result = async_function().await;
    assert_eq!(result, 42);
}

#[tokio::test]
async fn test_timeout() {
    let result = tokio::time::timeout(
        Duration::from_secs(1),
        slow_operation()
    ).await;

    assert!(result.is_ok());
}
```

---

## 文档测试

### 代码块测试

```rust
/// 示例函数
/// ```
/// let result = my_crate::add(2, 3);
/// assert_eq!(result, 5);
/// ```
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}
```

### 运行文档测试

```bash
cargo test --doc
cargo test --doc -p c01_ownership_borrow_scope
```

---

## Miri 测试

Miri 用于检测未定义行为和内存安全问题。

### 安装 Miri

```bash
rustup component add miri
```

### 运行 Miri

```bash
# 测试所有
cargo miri test

# 测试特定 crate
cargo miri test -p c01_ownership_borrow_scope

# 运行程序
cargo miri run -p c01_ownership_borrow_scope
```

---

## 测试覆盖率

### 使用 cargo-tarpaulin

```bash
# 安装
cargo install cargo-tarpaulin

# 生成覆盖率报告
cargo tarpaulin --workspace

# HTML 报告
cargo tarpaulin --workspace --out Html
```

### 查看报告

打开 `tarpaulin-report.html` 查看详细覆盖率。

---

## 持续集成

### GitHub Actions

测试在以下情况运行:

- 每次 push
- 每次 pull request
- 每日定时构建

### 测试矩阵

- Rust 版本: 1.96.0
- 平台: Ubuntu, macOS, Windows
- 测试类型: 单元、集成、文档、Miri

---

## 最佳实践

1. 每个测试一个断言
2. 使用有意义的测试名称
3. 使用 before_each 设置测试环境
4. 清理测试数据
5. 测试边界条件
6. 测试错误情况

---

## 调试失败的测试

### 输出详细信息

```bash
cargo test -- --nocapture
```

### 只运行失败的测试

```bash
cargo test -- --failed
```

### 输出到文件

```bash
cargo test 2>&1 | tee test-output.log
```
