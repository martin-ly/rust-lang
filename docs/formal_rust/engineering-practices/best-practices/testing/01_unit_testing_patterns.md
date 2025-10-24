# 🧪 Rust单元测试模式最佳实践


## 📊 目录

- [概述](#概述)
- [1. 基础测试模式](#1-基础测试模式)
  - [1.1 测试结构模式 (Test Structure Pattern)](#11-测试结构模式-test-structure-pattern)
  - [1.2 参数化测试模式 (Parameterized Test Pattern)](#12-参数化测试模式-parameterized-test-pattern)
- [2. 高级测试模式](#2-高级测试模式)
  - [2.1 属性测试模式 (Property-Based Testing)](#21-属性测试模式-property-based-testing)
  - [2.2 模拟测试模式 (Mock Testing Pattern)](#22-模拟测试模式-mock-testing-pattern)
- [3. 集成测试模式](#3-集成测试模式)
  - [3.1 模块集成测试 (Module Integration Testing)](#31-模块集成测试-module-integration-testing)
  - [3.2 异步集成测试 (Async Integration Testing)](#32-异步集成测试-async-integration-testing)
- [4. 性能测试模式](#4-性能测试模式)
  - [4.1 基准测试 (Benchmark Testing)](#41-基准测试-benchmark-testing)
  - [4.2 压力测试 (Stress Testing)](#42-压力测试-stress-testing)
- [5. 测试工具和框架](#5-测试工具和框架)
  - [5.1 自定义测试宏 (Custom Test Macros)](#51-自定义测试宏-custom-test-macros)
  - [5.2 测试数据生成器 (Test Data Generators)](#52-测试数据生成器-test-data-generators)
- [6. 测试最佳实践](#6-测试最佳实践)
  - [6.1 测试组织原则](#61-测试组织原则)
  - [6.2 测试覆盖率](#62-测试覆盖率)
  - [6.3 持续集成测试](#63-持续集成测试)


## 概述

本文档基于MIT 6.172、Stanford CS110、CMU 15-410、UC Berkeley CS61C等著名大学Rust课程的标准，详细分析Rust单元测试的各种模式和实践技巧。

## 1. 基础测试模式

### 1.1 测试结构模式 (Test Structure Pattern)

```rust
// MIT 6.172风格：清晰的测试结构
#[cfg(test)]
mod tests {
    use super::*;
    
    // 测试夹具 (Test Fixtures)
    struct TestFixture {
        data: Vec<i32>,
        expected_sum: i32,
    }
    
    impl TestFixture {
        fn new() -> Self {
            TestFixture {
                data: vec![1, 2, 3, 4, 5],
                expected_sum: 15,
            }
        }
        
        fn empty() -> Self {
            TestFixture {
                data: vec![],
                expected_sum: 0,
            }
        }
        
        fn with_negative() -> Self {
            TestFixture {
                data: vec![-1, -2, 3, 4],
                expected_sum: 4,
            }
        }
    }
    
    // 基础功能测试
    #[test]
    fn test_sum_basic() {
        let fixture = TestFixture::new();
        let result = sum(&fixture.data);
        assert_eq!(result, fixture.expected_sum);
    }
    
    #[test]
    fn test_sum_empty() {
        let fixture = TestFixture::empty();
        let result = sum(&fixture.data);
        assert_eq!(result, fixture.expected_sum);
    }
    
    #[test]
    fn test_sum_with_negative() {
        let fixture = TestFixture::with_negative();
        let result = sum(&fixture.data);
        assert_eq!(result, fixture.expected_sum);
    }
}

// 被测试的函数
pub fn sum(numbers: &[i32]) -> i32 {
    numbers.iter().sum()
}
```

### 1.2 参数化测试模式 (Parameterized Test Pattern)

```rust
// Stanford CS110风格：参数化测试
#[cfg(test)]
mod parameterized_tests {
    use super::*;
    
    // 使用宏进行参数化测试
    macro_rules! test_cases {
        ($($name:ident: $value:expr,)*) => {
            $(
                #[test]
                fn $name() {
                    let (input, expected) = $value;
                    let result = process_data(input);
                    assert_eq!(result, expected);
                }
            )*
        }
    }
    
    test_cases! {
        test_empty_string: ("", 0),
        test_single_char: ("a", 1),
        test_multiple_chars: ("abc", 3),
        test_with_spaces: ("a b c", 3),
        test_with_numbers: ("a1b2c3", 3),
    }
    
    // 使用属性宏进行参数化测试
    #[test_case("" => 0)]
    #[test_case("a" => 1)]
    #[test_case("abc" => 3)]
    #[test_case("a b c" => 3)]
    fn test_process_data_parametrized(input: &str) -> usize {
        process_data(input)
    }
}

// 被测试的函数
pub fn process_data(input: &str) -> usize {
    input.chars().filter(|c| c.is_alphabetic()).count()
}
```

## 2. 高级测试模式

### 2.1 属性测试模式 (Property-Based Testing)

```rust
// CMU 15-410风格：属性测试
#[cfg(test)]
mod property_tests {
    use super::*;
    use proptest::prelude::*;
    
    // 属性：加法交换律
    proptest! {
        #[test]
        fn test_addition_commutative(a: i32, b: i32) {
            prop_assert_eq!(add(a, b), add(b, a));
        }
    }
    
    // 属性：加法结合律
    proptest! {
        #[test]
        fn test_addition_associative(a: i32, b: i32, c: i32) {
            prop_assert_eq!(add(add(a, b), c), add(a, add(b, c)));
        }
    }
    
    // 属性：加法单位元
    proptest! {
        #[test]
        fn test_addition_identity(a: i32) {
            prop_assert_eq!(add(a, 0), a);
            prop_assert_eq!(add(0, a), a);
        }
    }
    
    // 属性：列表操作
    proptest! {
        #[test]
        fn test_list_operations(mut list: Vec<i32>) {
            let original_len = list.len();
            
            // 添加元素后长度增加
            list.push(42);
            prop_assert_eq!(list.len(), original_len + 1);
            
            // 移除元素后长度减少
            if !list.is_empty() {
                list.pop();
                prop_assert_eq!(list.len(), original_len);
            }
        }
    }
    
    // 自定义策略
    proptest! {
        #[test]
        fn test_with_custom_strategy(
            list in prop::collection::vec(0..100i32, 0..100)
        ) {
            let sorted = sort_list(&list);
            prop_assert!(is_sorted(&sorted));
            prop_assert_eq!(sorted.len(), list.len());
        }
    }
}

// 被测试的函数
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}

pub fn sort_list(list: &[i32]) -> Vec<i32> {
    let mut sorted = list.to_vec();
    sorted.sort();
    sorted
}

pub fn is_sorted(list: &[i32]) -> bool {
    list.windows(2).all(|window| window[0] <= window[1])
}
```

### 2.2 模拟测试模式 (Mock Testing Pattern)

```rust
// UC Berkeley CS61C风格：模拟测试
#[cfg(test)]
mod mock_tests {
    use super::*;
    use mockall::predicate::*;
    use mockall::*;
    
    // 定义模拟特征
    #[automock]
    trait Database {
        fn query(&self, id: u32) -> Result<String, String>;
        fn insert(&mut self, id: u32, data: &str) -> Result<(), String>;
        fn update(&mut self, id: u32, data: &str) -> Result<(), String>;
        fn delete(&mut self, id: u32) -> Result<(), String>;
    }
    
    // 使用模拟的测试
    #[test]
    fn test_successful_query() {
        let mut mock_db = MockDatabase::new();
        
        // 设置期望
        mock_db
            .expect_query()
            .with(eq(1))
            .times(1)
            .returning(|_| Ok("test data".to_string()));
        
        // 执行测试
        let result = query_user_data(&mock_db, 1);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), "test data");
    }
    
    #[test]
    fn test_failed_query() {
        let mut mock_db = MockDatabase::new();
        
        // 设置期望
        mock_db
            .expect_query()
            .with(eq(999))
            .times(1)
            .returning(|_| Err("User not found".to_string()));
        
        // 执行测试
        let result = query_user_data(&mock_db, 999);
        assert!(result.is_err());
        assert_eq!(result.unwrap_err(), "User not found");
    }
    
    #[test]
    fn test_complex_operation() {
        let mut mock_db = MockDatabase::new();
        
        // 设置多个期望
        mock_db
            .expect_query()
            .with(eq(1))
            .times(1)
            .returning(|_| Ok("old data".to_string()));
        
        mock_db
            .expect_update()
            .with(eq(1), eq("new data"))
            .times(1)
            .returning(|_, _| Ok(()));
        
        // 执行测试
        let result = update_user_data(&mut mock_db, 1, "new data");
        assert!(result.is_ok());
    }
}

// 被测试的函数
pub fn query_user_data(db: &dyn Database, id: u32) -> Result<String, String> {
    db.query(id)
}

pub fn update_user_data(db: &mut dyn Database, id: u32, new_data: &str) -> Result<(), String> {
    // 先查询现有数据
    let _existing_data = db.query(id)?;
    
    // 更新数据
    db.update(id, new_data)
}
```

## 3. 集成测试模式

### 3.1 模块集成测试 (Module Integration Testing)

```rust
// MIT 6.172风格：模块集成测试
#[cfg(test)]
mod integration_tests {
    use super::*;
    
    // 测试整个模块的功能
    #[test]
    fn test_data_processing_pipeline() {
        let input_data = vec![1, 2, 3, 4, 5];
        
        // 测试完整的数据处理流水线
        let filtered = filter_even_numbers(&input_data);
        let doubled = double_numbers(&filtered);
        let summed = sum_numbers(&doubled);
        
        // 验证结果
        assert_eq!(filtered, vec![2, 4]);
        assert_eq!(doubled, vec![4, 8]);
        assert_eq!(summed, 12);
    }
    
    #[test]
    fn test_error_propagation() {
        let invalid_data = vec![1, -1, 2, -2];
        
        // 测试错误传播
        let result = process_with_validation(&invalid_data);
        assert!(result.is_err());
        
        if let Err(ProcessingError::ValidationError(msg)) = result {
            assert!(msg.contains("negative"));
        }
    }
    
    // 测试边界条件
    #[test]
    fn test_edge_cases() {
        // 空数据
        assert_eq!(process_data(&[]), 0);
        
        // 单个元素
        assert_eq!(process_data(&[42]), 42);
        
        // 大数值
        assert_eq!(process_data(&[i32::MAX, 1]), i32::MAX.wrapping_add(1));
    }
}

// 被测试的模块函数
pub fn filter_even_numbers(numbers: &[i32]) -> Vec<i32> {
    numbers.iter().filter(|&&x| x % 2 == 0).cloned().collect()
}

pub fn double_numbers(numbers: &[i32]) -> Vec<i32> {
    numbers.iter().map(|&x| x * 2).collect()
}

pub fn sum_numbers(numbers: &[i32]) -> i32 {
    numbers.iter().sum()
}

pub fn process_data(numbers: &[i32]) -> i32 {
    numbers.iter().sum()
}

pub fn process_with_validation(numbers: &[i32]) -> Result<i32, ProcessingError> {
    for &num in numbers {
        if num < 0 {
            return Err(ProcessingError::ValidationError(
                "Found negative number".to_string()
            ));
        }
    }
    Ok(numbers.iter().sum())
}
```

### 3.2 异步集成测试 (Async Integration Testing)

```rust
// Stanford CS110风格：异步集成测试
#[cfg(test)]
mod async_integration_tests {
    use super::*;
    use tokio::test;
    
    #[tokio::test]
    async fn test_async_data_processing() {
        let input_data = vec![1, 2, 3, 4, 5];
        
        // 测试异步数据处理
        let result = async_process_data(&input_data).await;
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), 15);
    }
    
    #[tokio::test]
    async fn test_concurrent_processing() {
        let data_sets = vec![
            vec![1, 2, 3],
            vec![4, 5, 6],
            vec![7, 8, 9],
        ];
        
        // 并发处理多个数据集
        let futures: Vec<_> = data_sets
            .iter()
            .map(|data| async_process_data(data))
            .collect();
        
        let results = futures::future::join_all(futures).await;
        
        // 验证所有结果
        for result in results {
            assert!(result.is_ok());
        }
        
        let sums: Vec<i32> = results.into_iter().map(|r| r.unwrap()).collect();
        assert_eq!(sums, vec![6, 15, 24]);
    }
    
    #[tokio::test]
    async fn test_error_handling_in_async() {
        let invalid_data = vec![1, -1, 2];
        
        let result = async_process_with_validation(&invalid_data).await;
        assert!(result.is_err());
    }
}

// 异步被测试函数
pub async fn async_process_data(numbers: &[i32]) -> Result<i32, ProcessingError> {
    // 模拟异步处理
    tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
    Ok(numbers.iter().sum())
}

pub async fn async_process_with_validation(numbers: &[i32]) -> Result<i32, ProcessingError> {
    tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
    
    for &num in numbers {
        if num < 0 {
            return Err(ProcessingError::ValidationError(
                "Found negative number".to_string()
            ));
        }
    }
    Ok(numbers.iter().sum())
}
```

## 4. 性能测试模式

### 4.1 基准测试 (Benchmark Testing)

```rust
// CMU 15-410风格：基准测试
#[cfg(test)]
mod benchmark_tests {
    use super::*;
    use criterion::{black_box, criterion_group, criterion_main, Criterion};
    
    pub fn benchmark_sum(c: &mut Criterion) {
        let data: Vec<i32> = (0..1000).collect();
        
        c.bench_function("sum_1000_elements", |b| {
            b.iter(|| sum(black_box(&data)))
        });
    }
    
    pub fn benchmark_sort(c: &mut Criterion) {
        let mut data: Vec<i32> = (0..1000).rev().collect();
        
        c.bench_function("sort_1000_elements", |b| {
            b.iter(|| {
                let mut test_data = data.clone();
                test_data.sort();
                black_box(test_data)
            })
        });
    }
    
    pub fn benchmark_string_processing(c: &mut Criterion) {
        let test_string = "a".repeat(1000);
        
        c.bench_function("process_1000_char_string", |b| {
            b.iter(|| process_data(black_box(&test_string)))
        });
    }
    
    criterion_group!(benches, benchmark_sum, benchmark_sort, benchmark_string_processing);
    criterion_main!(benches);
}
```

### 4.2 压力测试 (Stress Testing)

```rust
// UC Berkeley CS61C风格：压力测试
#[cfg(test)]
mod stress_tests {
    use super::*;
    use std::sync::Arc;
    use tokio::sync::Semaphore;
    
    #[tokio::test]
    async fn test_concurrent_access() {
        let semaphore = Arc::new(Semaphore::new(10));
        let counter = Arc::new(std::sync::Mutex::new(0));
        
        let mut handles = vec![];
        
        // 创建100个并发任务
        for _ in 0..100 {
            let sem = semaphore.clone();
            let counter = counter.clone();
            
            let handle = tokio::spawn(async move {
                let _permit = sem.acquire().await.unwrap();
                
                // 模拟工作
                tokio::time::sleep(tokio::time::Duration::from_millis(1)).await;
                
                let mut count = counter.lock().unwrap();
                *count += 1;
            });
            
            handles.push(handle);
        }
        
        // 等待所有任务完成
        for handle in handles {
            handle.await.unwrap();
        }
        
        assert_eq!(*counter.lock().unwrap(), 100);
    }
    
    #[tokio::test]
    async fn test_memory_pressure() {
        let mut data = Vec::new();
        
        // 分配大量内存
        for i in 0..1_000_000 {
            data.push(i);
        }
        
        // 验证数据完整性
        for (i, &value) in data.iter().enumerate() {
            assert_eq!(value, i);
        }
        
        // 测试内存释放
        drop(data);
    }
}
```

## 5. 测试工具和框架

### 5.1 自定义测试宏 (Custom Test Macros)

```rust
// MIT 6.172风格：自定义测试宏
#[cfg(test)]
mod custom_test_macros {
    use super::*;
    
    // 自定义测试宏
    macro_rules! test_matrix {
        ($func:ident, $($name:ident: $input:expr => $expected:expr),*) => {
            $(
                #[test]
                fn $name() {
                    let result = $func($input);
                    assert_eq!(result, $expected);
                }
            )*
        };
    }
    
    // 使用自定义宏
    test_matrix! {
        factorial,
        test_factorial_0: 0 => 1,
        test_factorial_1: 1 => 1,
        test_factorial_5: 5 => 120,
        test_factorial_10: 10 => 3628800
    }
    
    // 自定义属性宏
    macro_rules! test_with_timeout {
        ($timeout:expr, $test_fn:expr) => {
            #[test]
            fn test_with_timeout() {
                use std::time::Duration;
                use std::panic::catch_unwind;
                
                let result = std::thread::spawn(|| {
                    catch_unwind($test_fn)
                });
                
                match result.join() {
                    Ok(Ok(())) => (),
                    Ok(Err(e)) => std::panic::resume_unwind(e),
                    Err(_) => panic!("Test timed out after {:?}", Duration::from_secs($timeout)),
                }
            }
        };
    }
}

// 被测试的函数
pub fn factorial(n: u64) -> u64 {
    if n <= 1 {
        1
    } else {
        n * factorial(n - 1)
    }
}
```

### 5.2 测试数据生成器 (Test Data Generators)

```rust
// Stanford CS110风格：测试数据生成器
#[cfg(test)]
mod test_data_generators {
    use super::*;
    use rand::Rng;
    
    // 测试数据生成器特征
    trait TestDataGenerator<T> {
        fn generate(&self) -> T;
        fn generate_multiple(&self, count: usize) -> Vec<T>;
    }
    
    // 整数数据生成器
    struct IntegerGenerator {
        min: i32,
        max: i32,
    }
    
    impl IntegerGenerator {
        fn new(min: i32, max: i32) -> Self {
            IntegerGenerator { min, max }
        }
    }
    
    impl TestDataGenerator<i32> for IntegerGenerator {
        fn generate(&self) -> i32 {
            let mut rng = rand::thread_rng();
            rng.gen_range(self.min..=self.max)
        }
        
        fn generate_multiple(&self, count: usize) -> Vec<i32> {
            (0..count).map(|_| self.generate()).collect()
        }
    }
    
    // 字符串数据生成器
    struct StringGenerator {
        min_len: usize,
        max_len: usize,
    }
    
    impl StringGenerator {
        fn new(min_len: usize, max_len: usize) -> Self {
            StringGenerator { min_len, max_len }
        }
    }
    
    impl TestDataGenerator<String> for StringGenerator {
        fn generate(&self) -> String {
            let mut rng = rand::thread_rng();
            let len = rng.gen_range(self.min_len..=self.max_len);
            
            (0..len)
                .map(|_| rng.gen_range(b'a'..=b'z') as char)
                .collect()
        }
        
        fn generate_multiple(&self, count: usize) -> Vec<String> {
            (0..count).map(|_| self.generate()).collect()
        }
    }
    
    // 使用数据生成器的测试
    #[test]
    fn test_with_generated_data() {
        let int_gen = IntegerGenerator::new(-100, 100);
        let string_gen = StringGenerator::new(5, 20);
        
        // 生成测试数据
        let numbers = int_gen.generate_multiple(100);
        let strings = string_gen.generate_multiple(50);
        
        // 测试数字处理
        for &num in &numbers {
            let result = process_number(num);
            assert!(result >= 0); // 假设函数返回非负数
        }
        
        // 测试字符串处理
        for string in &strings {
            let result = process_string(string);
            assert!(result.len() <= string.len()); // 假设函数不会增加字符串长度
        }
    }
}

// 被测试的函数
pub fn process_number(n: i32) -> i32 {
    n.abs()
}

pub fn process_string(s: &str) -> String {
    s.to_lowercase()
}
```

## 6. 测试最佳实践

### 6.1 测试组织原则

1. **AAA模式**: Arrange（准备）、Act（执行）、Assert（断言）
2. **单一职责**: 每个测试只测试一个功能点
3. **独立性**: 测试之间不应相互依赖
4. **可读性**: 测试名称应清晰描述测试内容
5. **可维护性**: 测试代码应与生产代码保持相同的质量标准

### 6.2 测试覆盖率

```rust
// 使用tarpaulin进行代码覆盖率测试
// 在Cargo.toml中添加：
// [dev-dependencies]
// tarpaulin = "0.20"

// 运行覆盖率测试：
// cargo tarpaulin --out Html
```

### 6.3 持续集成测试

```yaml
# .github/workflows/test.yml
name: Rust Tests

on: [push, pull_request]

jobs:
  test:
    runs-on: ubuntu-latest
    
    steps:
    - uses: actions/checkout@v2
    
    - name: Install Rust
      uses: actions-rs/toolchain@v1
      with:
        toolchain: stable
        
    - name: Run tests
      run: cargo test --verbose
      
    - name: Run integration tests
      run: cargo test --test '*'
      
    - name: Run benchmarks
      run: cargo bench
      
    - name: Check code coverage
      run: cargo tarpaulin --out Html
```

这些测试模式和实践基于国际一流大学的Rust课程标准，为构建高质量、可维护的Rust应用程序提供了全面的测试保障。
