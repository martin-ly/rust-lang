# C04 泛型编程：RPITIT 与 use<> 模式

> **Rust 版本**: 1.94.0
> **Edition**: 2024
> **最后更新**: 2026-03-10
> **文档级别**: Tier 2 - 实践指南

---

## 目录

- [RPITIT 在泛型中的应用](#rpitit-在泛型中的应用)
- [use<> 精确捕获模式](#use-精确捕获模式)
- [泛型类型推断增强](#泛型类型推断增强)
- [实战设计模式](#实战设计模式)
- [性能优化指南](#性能优化指南)

---

## RPITIT 在泛型中的应用

### 1.1 基础 RPITIT 模式

```rust
// Rust 1.94: RPITIT 允许在 trait 中使用 impl Trait
trait GenericProcessor<T> {
    fn process(&self, input: T) -> impl Iterator<Item = T::Output>
    where
        T: Transformable;
}

trait Transformable {
    type Output;
    fn transform(self) -> Self::Output;
}

// 实现
trait DataTransformer {
    fn transform_batch<I>(&self, items: I) -> impl Iterator<Item = ProcessedItem> + use<>
    where
        I: IntoIterator<Item = RawItem>;
}

struct DataProcessor;

impl DataTransformer for DataProcessor {
    fn transform_batch<I>(&self, items: I) -> impl Iterator<Item = ProcessedItem> + use<>
    where
        I: IntoIterator<Item = RawItem>,
    {
        items.into_iter().map(|item| ProcessedItem::from(item))
    }
}

struct RawItem { data: String }
struct ProcessedItem { data: String }

impl From<RawItem> for ProcessedItem {
    fn from(raw: RawItem) -> Self {
        ProcessedItem { data: raw.data.to_uppercase() }
    }
}
```

### 1.2 泛型 trait 与 impl Trait 结合

```rust
/// 泛型数据流处理 trait
trait StreamProcessor<Input, Output> {
    fn process_stream(
        &self,
        stream: impl Iterator<Item = Input>
    ) -> impl Iterator<Item = Output> + use<>;
}

/// 类型转换处理器
struct TransformProcessor<F> {
    transform: F,
}

impl<Input, Output, F> StreamProcessor<Input, Output> for TransformProcessor<F>
where
    F: Fn(Input) -> Output,
{
    fn process_stream(
        &self,
        stream: impl Iterator<Item = Input>
    ) -> impl Iterator<Item = Output> + use<> {
        // use<> 确保不捕获 self，返回的迭代器可以独立存在
        stream.map(&self.transform)
    }
}

// 使用示例
fn main() {
    let processor = TransformProcessor {
        transform: |x: i32| x * 2,
    };
    
    let input = vec![1, 2, 3, 4, 5];
    let output: Vec<i32> = processor
        .process_stream(input.into_iter())
        .collect();
    
    assert_eq!(output, vec![2, 4, 6, 8, 10]);
}
```

---

## use<> 精确捕获模式

### 2.1 精确捕获基础

```rust
/// use<> 控制泛型参数捕获
fn create_transformer<T, F>(
    transform: F
) -> impl Fn(T) -> T::Output + use<T, F>
where
    F: Fn(T) -> T::Output,
    T: Transformable<Output = T>,
{
    move |input| transform(input)
}

/// use<> 与生命周期
trait LendingIterator<'a> {
    type Item;
    fn next(&mut self) -> Option<Self::Item>;
}

struct BufferLender<'a, T> {
    buffer: &'a mut [T],
    position: usize,
}

impl<'a, T> LendingIterator<'a> for BufferLender<'a, T> {
    type Item = &'a mut T;
    
    fn next(&mut self) -> Option<Self::Item> {
        if self.position < self.buffer.len() {
            let idx = self.position;
            self.position += 1;
            Some(&mut self.buffer[idx])
        } else {
            None
        }
    }
}
```

### 2.2 use<> 在闭包中的应用

```rust
/// 创建不捕获环境的闭包
fn pure_closure<T: Default>() -> impl Fn() -> T + use<T> {
    || T::default()
}

/// 选择性捕获
struct Context {
    config: String,
    counter: usize,
}

impl Context {
    /// 只捕获 config，不捕获 counter
    fn get_config_reader(&self) -> impl Fn() -> String + use<'_> {
        let config = self.config.clone();
        move || config.clone()
    }
    
    /// use<> 确保完全不捕获
    fn get_pure_function() -> impl Fn(i32) -> i32 + use<> {
        |x| x * 2
    }
}
```

---

## 泛型类型推断增强

### 3.1 Edition 2024 类型推断改进

```rust
/// Rust 1.94 改进的泛型推断
fn enhanced_inference_example() {
    // 编译器能更好地推断复杂泛型
    let data: Vec<Option<i32>> = vec![Some(1), None, Some(3)];
    
    // 不再需要显式类型标注
    let filtered: Vec<i32> = data
        .into_iter()
        .filter_map(|x| x)  // 自动推断 Option<i32> -> i32
        .map(|x| x * 2)      // 自动推断 i32 -> i32
        .collect();          // 自动推断 Vec<i32>
    
    // 闭包参数推断
    let process = |items: Vec<_>| -> Vec<_> {
        items.iter().map(|&x| x as f64).collect()
    };
    
    let result = process(vec![1, 2, 3]);
    assert_eq!(result, vec![1.0, 2.0, 3.0]);
}

/// 泛型函数链
fn generic_chain<T, U, V>(
    first: impl Fn(T) -> U,
    second: impl Fn(U) -> V,
) -> impl Fn(T) -> V + use<> {
    move |input| second(first(input))
}
```

### 3.2 ControlFlow 在泛型中的应用

```rust
use std::ops::ControlFlow;

/// 泛型提前返回模式
fn process_with_early_exit<T, E>(
    items: Vec<T>,
    processor: impl Fn(T) -> Result<T, E>,
    validator: impl Fn(&T) -> bool,
) -> ControlFlow<E, Vec<T>> {
    let mut results = Vec::with_capacity(items.len());
    
    for item in items {
        match processor(item) {
            Ok(processed) => {
                if !validator(&processed) {
                    return ControlFlow::Break(
                        // 构造错误类型 E（需要 E: From<&str>）
                        panic!("Validation failed")
                    );
                }
                results.push(processed);
            }
            Err(e) => return ControlFlow::Break(e),
        }
    }
    
    ControlFlow::Continue(results)
}

/// 泛型查找模式
fn find_first_matching<T>(
    items: &[T],
    predicate: impl Fn(&T) -> bool,
) -> ControlFlow<(), &T> {
    items.iter().try_for_each(|item| {
        if predicate(item) {
            ControlFlow::Break(item)
        } else {
            ControlFlow::Continue(())
        }
    }).break_value().map_or(
        ControlFlow::Continue(()),
        |item| ControlFlow::Break(item)
    )
}
```

---

## 实战设计模式

### 4.1 类型安全的构建器模式

```rust
/// 使用 RPITIT 的类型安全构建器
#[derive(Debug)]
pub struct QueryBuilder<T, F, S, W> {
    table: T,
    fields: F,
    sort: S,
    where_clause: W,
}

// 类型状态标记
struct Empty;
struct WithTable(String);
struct WithFields(Vec<String>);
struct WithSort(String);
struct WithWhere(String);

impl QueryBuilder<Empty, Empty, Empty, Empty> {
    pub fn new() -> Self {
        Self {
            table: Empty,
            fields: Empty,
            sort: Empty,
            where_clause: Empty,
        }
    }
    
    pub fn from_table(self, table: &str) -> QueryBuilder<WithTable, Empty, Empty, Empty> {
        QueryBuilder {
            table: WithTable(table.to_string()),
            fields: Empty,
            sort: Empty,
            where_clause: Empty,
        }
    }
}

impl QueryBuilder<WithTable, Empty, Empty, Empty> {
    pub fn select<F>(self, fields: F) -> QueryBuilder<WithTable, WithFields, Empty, Empty>
    where
        F: IntoIterator<Item = impl Into<String>>,
    {
        QueryBuilder {
            table: self.table,
            fields: WithFields(fields.into_iter().map(|f| f.into()).collect()),
            sort: Empty,
            where_clause: Empty,
        }
    }
}

impl<T, F, S> QueryBuilder<T, F, S, Empty> {
    pub fn where_clause(
        self,
        condition: &str,
    ) -> QueryBuilder<T, F, S, WithWhere> {
        QueryBuilder {
            table: self.table,
            fields: self.fields,
            sort: self.sort,
            where_clause: WithWhere(condition.to_string()),
        }
    }
}

impl QueryBuilder<WithTable, WithFields, Empty, Empty> {
    pub fn build(self) -> String {
        let table = match self.table { WithTable(t) => t, _ => unreachable!() };
        let fields = match self.fields { WithFields(f) => f.join(", "), _ => unreachable!() };
        format!("SELECT {} FROM {}", fields, table)
    }
}

impl QueryBuilder<WithTable, WithFields, Empty, WithWhere> {
    pub fn build(self) -> String {
        let table = match self.table { WithTable(t) => t, _ => unreachable!() };
        let fields = match self.fields { WithFields(f) => f.join(", "), _ => unreachable!() };
        let where_clause = match self.where_clause { WithWhere(w) => w, _ => unreachable!() };
        format!("SELECT {} FROM {} WHERE {}", fields, table, where_clause)
    }
}

// 使用示例
fn builder_example() {
    let query = QueryBuilder::new()
        .from_table("users")
        .select(["id", "name", "email"])
        .build();
    
    assert_eq!(query, "SELECT id, name, email FROM users");
    
    let query_with_where = QueryBuilder::new()
        .from_table("users")
        .select(["id", "name"])
        .where_clause("active = true")
        .build();
    
    assert_eq!(query_with_where, "SELECT id, name FROM users WHERE active = true");
}
```

### 4.2 泛型策略模式

```rust
/// 使用 RPITIT 的策略模式
trait ProcessingStrategy<Input, Output> {
    fn process(&self, input: Input) -> impl Future<Output = Output> + use<Self>;
}

/// 异步转换策略
struct AsyncTransformStrategy<F> {
    transformer: F,
}

impl<Input, Output, F> ProcessingStrategy<Input, Output> for AsyncTransformStrategy<F>
where
    F: Fn(Input) -> Output + Send + Sync,
    Input: Send + 'static,
    Output: Send + 'static,
{
    fn process(&self, input: Input) -> impl Future<Output = Output> + use<Self> {
        let transformer = &self.transformer;
        async move { transformer(input) }
    }
}

/// 批处理策略
struct BatchStrategy<S> {
    inner: S,
    batch_size: usize,
}

impl<Input, Output, S> ProcessingStrategy<Vec<Input>, Vec<Output>> for BatchStrategy<S>
where
    S: ProcessingStrategy<Input, Output>,
    Input: Send + 'static,
    Output: Send + 'static,
{
    fn process(
        &self,
        input: Vec<Input>,
    ) -> impl Future<Output = Vec<Output>> + use<Self> {
        async move {
            let mut results = Vec::with_capacity(input.len());
            
            for chunk in input.chunks(self.batch_size) {
                for item in chunk {
                    let result = self.inner.process(item.clone()).await;
                    results.push(result);
                }
            }
            
            results
        }
    }
}
```

---

## 性能优化指南

### 5.1 单态化优化

```rust
/// 使用 impl Trait 减少代码膨胀
pub fn process_items(items: Vec<i32>) -> impl Iterator<Item = i32> {
    // 编译器会为这个具体类型生成优化的代码
    items.into_iter().filter(|x| x % 2 == 0).map(|x| x * 2)
}

/// 泛型与 impl Trait 结合的最优模式
pub trait OptimizedProcessor {
    fn process(&self, data: Vec<u8>) -> impl Iterator<Item = u8> + use<>;
}

impl OptimizedProcessor for MyProcessor {
    fn process(&self, data: Vec<u8>) -> impl Iterator<Item = u8> + use<> {
        // use<> 确保编译器可以进行最大优化
        data.into_iter().filter(|b| *b > 0)
    }
}

struct MyProcessor;
```

### 5.2 零成本抽象验证

```rust
/// 验证泛型与 impl Trait 的零成本特性
pub fn verify_zero_cost() {
    // 泛型版本
    let generic_result: Vec<i32> = (0..1000)
        .map(|x| x * 2)
        .filter(|&x| x > 100)
        .collect();
    
    // impl Trait 版本 - 生成相同的汇编代码
    let impl_trait_result: Vec<i32> = process_items_generic(0..1000)
        .collect();
    
    assert_eq!(generic_result, impl_trait_result);
}

fn process_items_generic<I>(items: I) -> impl Iterator<Item = i32> + use<>
where
    I: Iterator<Item = i32>,
{
    items.map(|x| x * 2).filter(|&x| x > 100)
}
```

---

## 相关文档

- [Rust 1.94 发布说明](../../../docs/06_toolchain/16_rust_1.94_release_notes.md)
- [C04 泛型主索引](../00_MASTER_INDEX.md)
- [RPITIT 详解](../tier_03_references/rpitit_guide.md)
