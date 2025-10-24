# 迭代器语义分析


## 📊 目录

- [概述](#概述)
- [1. 迭代器理论基础](#1-迭代器理论基础)
  - [1.1 迭代器概念](#11-迭代器概念)
  - [1.2 Rust迭代器哲学](#12-rust迭代器哲学)
- [2. Iterator特征](#2-iterator特征)
  - [2.1 Iterator特征定义](#21-iterator特征定义)
  - [2.2 迭代器方法](#22-迭代器方法)
- [3. 迭代器适配器](#3-迭代器适配器)
  - [3.1 转换适配器](#31-转换适配器)
  - [3.2 限制适配器](#32-限制适配器)
  - [3.3 组合适配器](#33-组合适配器)
- [4. 惰性求值](#4-惰性求值)
  - [4.1 惰性求值机制](#41-惰性求值机制)
  - [4.2 内存效率](#42-内存效率)
- [5. 性能优化](#5-性能优化)
  - [5.1 迭代器性能](#51-迭代器性能)
  - [5.2 编译时优化](#52-编译时优化)
- [6. 自定义迭代器](#6-自定义迭代器)
  - [6.1 实现自定义迭代器](#61-实现自定义迭代器)
  - [6.2 迭代器适配器实现](#62-迭代器适配器实现)
- [7. 测试和验证](#7-测试和验证)
  - [7.1 迭代器测试](#71-迭代器测试)
- [8. 总结](#8-总结)


## 概述

本文档详细分析Rust迭代器系统的语义，包括迭代器特征、迭代器适配器、惰性求值、性能优化、自定义迭代器和迭代器模式。

## 1. 迭代器理论基础

### 1.1 迭代器概念

**定义 1.1.1 (迭代器)**
迭代器是Rust中用于遍历集合元素的抽象接口，它提供了统一的访问序列中元素的方法，支持惰性求值和函数式编程风格。

**迭代器的核心特性**：

1. **惰性求值**：只在需要时才计算下一个元素
2. **零成本抽象**：编译后没有运行时开销
3. **组合性**：可以链式组合多个操作
4. **类型安全**：编译时保证类型安全

### 1.2 Rust迭代器哲学

**Rust迭代器原则**：

```rust
// Rust迭代器提供零成本抽象
fn iterator_philosophy() {
    let numbers = vec![1, 2, 3, 4, 5];
    
    // 函数式风格，但编译后与命令式代码性能相同
    let sum: i32 = numbers.iter()
        .filter(|&x| x % 2 == 0)
        .map(|x| x * 2)
        .sum();
    
    println!("Sum: {}", sum);
}

// 迭代器是惰性的
fn lazy_evaluation() {
    let numbers = vec![1, 2, 3, 4, 5];
    
    // 这里不会实际计算，只是创建了迭代器链
    let iterator = numbers.iter()
        .filter(|&x| {
            println!("Filtering: {}", x);
            x % 2 == 0
        })
        .map(|x| {
            println!("Mapping: {}", x);
            x * 2
        });
    
    // 只有在调用collect时才实际计算
    let result: Vec<i32> = iterator.collect();
    println!("Result: {:?}", result);
}
```

## 2. Iterator特征

### 2.1 Iterator特征定义

**Iterator特征语义**：

```rust
// Iterator特征的核心方法
trait Iterator {
    type Item;
    
    fn next(&mut self) -> Option<Self::Item>;
    
    // 其他方法都有默认实现
    fn size_hint(&self) -> (usize, Option<usize>) { (0, None) }
    fn count(self) -> usize { /* 默认实现 */ }
    fn last(self) -> Option<Self::Item> { /* 默认实现 */ }
    fn nth(&mut self, n: usize) -> Option<Self::Item> { /* 默认实现 */ }
    fn step_by(self, step: usize) -> StepBy<Self> { /* 默认实现 */ }
    fn chain<U>(self, other: U) -> Chain<Self, U::IntoIter> { /* 默认实现 */ }
    fn zip<U>(self, other: U) -> Zip<Self, U::IntoIter> { /* 默认实现 */ }
    fn map<B, F>(self, f: F) -> Map<Self, F> { /* 默认实现 */ }
    fn for_each<F>(self, f: F) { /* 默认实现 */ }
    fn filter<P>(self, predicate: P) -> Filter<Self, P> { /* 默认实现 */ }
    fn filter_map<B, F>(self, f: F) -> FilterMap<Self, F> { /* 默认实现 */ }
    fn enumerate(self) -> Enumerate<Self> { /* 默认实现 */ }
    fn peekable(self) -> Peekable<Self> { /* 默认实现 */ }
    fn skip_while<P>(self, predicate: P) -> SkipWhile<Self, P> { /* 默认实现 */ }
    fn take_while<P>(self, predicate: P) -> TakeWhile<Self, P> { /* 默认实现 */ }
    fn map_while<B, P>(self, predicate: P) -> MapWhile<Self, P> { /* 默认实现 */ }
    fn skip(self, n: usize) -> Skip<Self> { /* 默认实现 */ }
    fn take(self, n: usize) -> Take<Self> { /* 默认实现 */ }
    fn scan<St, B, F>(self, initial_state: St, f: F) -> Scan<Self, St, F> { /* 默认实现 */ }
    fn flat_map<U, F>(self, f: F) -> FlatMap<Self, U, F> { /* 默认实现 */ }
    fn flatten(self) -> Flatten<Self> { /* 默认实现 */ }
    fn fuse(self) -> Fuse<Self> { /* 默认实现 */ }
    fn inspect<F>(self, f: F) -> Inspect<Self, F> { /* 默认实现 */ }
    fn by_ref(&mut self) -> &mut Self { self }
    fn collect<B>(self) -> B { /* 默认实现 */ }
    fn partition<B, F>(self, f: F) -> (B, B) { /* 默认实现 */ }
    fn fold<B, F>(self, init: B, f: F) -> B { /* 默认实现 */ }
    fn reduce<F>(self, f: F) -> Option<Self::Item> { /* 默认实现 */ }
    fn all<F>(&mut self, f: F) -> bool { /* 默认实现 */ }
    fn any<F>(&mut self, f: F) -> bool { /* 默认实现 */ }
    fn find<P>(&mut self, predicate: P) -> Option<Self::Item> { /* 默认实现 */ }
    fn find_map<B, F>(&mut self, f: F) -> Option<B> { /* 默认实现 */ }
    fn position<P>(&mut self, predicate: P) -> Option<usize> { /* 默认实现 */ }
    fn rposition<P>(&mut self, predicate: P) -> Option<usize> { /* 默认实现 */ }
    fn max(self) -> Option<Self::Item> { /* 默认实现 */ }
    fn min(self) -> Option<Self::Item> { /* 默认实现 */ }
    fn max_by_key<B, F>(self, f: F) -> Option<Self::Item> { /* 默认实现 */ }
    fn min_by_key<B, F>(self, f: F) -> Option<Self::Item> { /* 默认实现 */ }
    fn max_by<F>(self, compare: F) -> Option<Self::Item> { /* 默认实现 */ }
    fn min_by<F>(self, compare: F) -> Option<Self::Item> { /* 默认实现 */ }
    fn rev(self) -> Rev<Self> { /* 默认实现 */ }
    fn unzip<A, B, FromA, FromB>(self) -> (FromA, FromB) { /* 默认实现 */ }
    fn copied<'a, T>(self) -> Copied<Self> { /* 默认实现 */ }
    fn cloned<'a, T>(self) -> Cloned<Self> { /* 默认实现 */ }
    fn cycle(self) -> Cycle<Self> { /* 默认实现 */ }
    fn sum<S>(self) -> S { /* 默认实现 */ }
    fn product<P>(self) -> P { /* 默认实现 */ }
    fn cmp<I>(self, other: I) -> std::cmp::Ordering { /* 默认实现 */ }
    fn partial_cmp<I>(self, other: I) -> Option<std::cmp::Ordering> { /* 默认实现 */ }
    fn eq<I>(self, other: I) -> bool { /* 默认实现 */ }
    fn ne<I>(self, other: I) -> bool { /* 默认实现 */ }
    fn lt<I>(self, other: I) -> bool { /* 默认实现 */ }
    fn le<I>(self, other: I) -> bool { /* 默认实现 */ }
    fn gt<I>(self, other: I) -> bool { /* 默认实现 */ }
    fn ge<I>(self, other: I) -> bool { /* 默认实现 */ }
}

// 实现自定义迭代器
struct Counter {
    count: u32,
    max: u32,
}

impl Counter {
    fn new(max: u32) -> Self {
        Self { count: 0, max }
    }
}

impl Iterator for Counter {
    type Item = u32;
    
    fn next(&mut self) -> Option<Self::Item> {
        if self.count < self.max {
            self.count += 1;
            Some(self.count)
        } else {
            None
        }
    }
}

// 使用自定义迭代器
fn custom_iterator_usage() {
    let counter = Counter::new(5);
    let numbers: Vec<u32> = counter.collect();
    println!("Counter numbers: {:?}", numbers);
}
```

### 2.2 迭代器方法

**迭代器方法语义**：

```rust
// 基本迭代器方法
fn basic_iterator_methods() {
    let numbers = vec![1, 2, 3, 4, 5];
    let mut iter = numbers.iter();
    
    // next方法
    assert_eq!(iter.next(), Some(&1));
    assert_eq!(iter.next(), Some(&2));
    assert_eq!(iter.next(), Some(&3));
    assert_eq!(iter.next(), Some(&4));
    assert_eq!(iter.next(), Some(&5));
    assert_eq!(iter.next(), None);
    
    // size_hint方法
    let mut iter = numbers.iter();
    assert_eq!(iter.size_hint(), (5, Some(5)));
    
    // count方法
    let count = numbers.iter().count();
    assert_eq!(count, 5);
    
    // last方法
    let last = numbers.iter().last();
    assert_eq!(last, Some(&5));
    
    // nth方法
    let third = numbers.iter().nth(2);
    assert_eq!(third, Some(&3));
}

// 消费方法
fn consuming_methods() {
    let numbers = vec![1, 2, 3, 4, 5];
    
    // sum方法
    let sum: i32 = numbers.iter().sum();
    assert_eq!(sum, 15);
    
    // product方法
    let product: i32 = numbers.iter().product();
    assert_eq!(product, 120);
    
    // fold方法
    let folded = numbers.iter().fold(0, |acc, &x| acc + x);
    assert_eq!(folded, 15);
    
    // reduce方法
    let reduced = numbers.iter().reduce(|acc, &x| acc + x);
    assert_eq!(reduced, Some(15));
    
    // collect方法
    let collected: Vec<&i32> = numbers.iter().collect();
    assert_eq!(collected, vec![&1, &2, &3, &4, &5]);
}

// 查询方法
fn query_methods() {
    let numbers = vec![1, 2, 3, 4, 5];
    
    // all方法
    let all_positive = numbers.iter().all(|&x| x > 0);
    assert!(all_positive);
    
    // any方法
    let any_even = numbers.iter().any(|&x| x % 2 == 0);
    assert!(any_even);
    
    // find方法
    let first_even = numbers.iter().find(|&&x| x % 2 == 0);
    assert_eq!(first_even, Some(&2));
    
    // position方法
    let even_position = numbers.iter().position(|&&x| x % 2 == 0);
    assert_eq!(even_position, Some(1));
    
    // max和min方法
    let max = numbers.iter().max();
    let min = numbers.iter().min();
    assert_eq!(max, Some(&5));
    assert_eq!(min, Some(&1));
}
```

## 3. 迭代器适配器

### 3.1 转换适配器

**转换适配器语义**：

```rust
// map适配器
fn map_adapter() {
    let numbers = vec![1, 2, 3, 4, 5];
    
    let doubled: Vec<i32> = numbers.iter()
        .map(|&x| x * 2)
        .collect();
    
    assert_eq!(doubled, vec![2, 4, 6, 8, 10]);
}

// filter适配器
fn filter_adapter() {
    let numbers = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    
    let evens: Vec<i32> = numbers.iter()
        .filter(|&&x| x % 2 == 0)
        .copied()
        .collect();
    
    assert_eq!(evens, vec![2, 4, 6, 8, 10]);
}

// filter_map适配器
fn filter_map_adapter() {
    let strings = vec!["1", "hello", "3", "world", "5"];
    
    let numbers: Vec<i32> = strings.iter()
        .filter_map(|s| s.parse::<i32>().ok())
        .collect();
    
    assert_eq!(numbers, vec![1, 3, 5]);
}

// flat_map适配器
fn flat_map_adapter() {
    let words = vec!["hello", "world"];
    
    let chars: Vec<char> = words.iter()
        .flat_map(|word| word.chars())
        .collect();
    
    assert_eq!(chars, vec!['h', 'e', 'l', 'l', 'o', 'w', 'o', 'r', 'l', 'd']);
}

// flatten适配器
fn flatten_adapter() {
    let nested = vec![vec![1, 2], vec![3, 4], vec![5]];
    
    let flattened: Vec<i32> = nested.iter()
        .flatten()
        .copied()
        .collect();
    
    assert_eq!(flattened, vec![1, 2, 3, 4, 5]);
}

// enumerate适配器
fn enumerate_adapter() {
    let words = vec!["hello", "world", "rust"];
    
    let enumerated: Vec<(usize, &str)> = words.iter()
        .enumerate()
        .collect();
    
    assert_eq!(enumerated, vec![(0, "hello"), (1, "world"), (2, "rust")]);
}
```

### 3.2 限制适配器

**限制适配器语义**：

```rust
// take适配器
fn take_adapter() {
    let numbers = vec![1, 2, 3, 4, 5];
    
    let first_three: Vec<i32> = numbers.iter()
        .take(3)
        .copied()
        .collect();
    
    assert_eq!(first_three, vec![1, 2, 3]);
}

// skip适配器
fn skip_adapter() {
    let numbers = vec![1, 2, 3, 4, 5];
    
    let last_three: Vec<i32> = numbers.iter()
        .skip(2)
        .copied()
        .collect();
    
    assert_eq!(last_three, vec![3, 4, 5]);
}

// take_while适配器
fn take_while_adapter() {
    let numbers = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    
    let small_numbers: Vec<i32> = numbers.iter()
        .take_while(|&&x| x < 5)
        .copied()
        .collect();
    
    assert_eq!(small_numbers, vec![1, 2, 3, 4]);
}

// skip_while适配器
fn skip_while_adapter() {
    let numbers = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    
    let large_numbers: Vec<i32> = numbers.iter()
        .skip_while(|&&x| x < 5)
        .copied()
        .collect();
    
    assert_eq!(large_numbers, vec![5, 6, 7, 8, 9, 10]);
}

// step_by适配器
fn step_by_adapter() {
    let numbers = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    
    let every_second: Vec<i32> = numbers.iter()
        .step_by(2)
        .copied()
        .collect();
    
    assert_eq!(every_second, vec![1, 3, 5, 7, 9]);
}
```

### 3.3 组合适配器

**组合适配器语义**：

```rust
// chain适配器
fn chain_adapter() {
    let first = vec![1, 2, 3];
    let second = vec![4, 5, 6];
    
    let combined: Vec<i32> = first.iter()
        .chain(second.iter())
        .copied()
        .collect();
    
    assert_eq!(combined, vec![1, 2, 3, 4, 5, 6]);
}

// zip适配器
fn zip_adapter() {
    let numbers = vec![1, 2, 3];
    let letters = vec!['a', 'b', 'c'];
    
    let zipped: Vec<(i32, char)> = numbers.iter()
        .zip(letters.iter())
        .map(|(&n, &c)| (n, c))
        .collect();
    
    assert_eq!(zipped, vec![(1, 'a'), (2, 'b'), (3, 'c')]);
}

// cycle适配器
fn cycle_adapter() {
    let numbers = vec![1, 2, 3];
    
    let cycled: Vec<i32> = numbers.iter()
        .cycle()
        .take(7)
        .copied()
        .collect();
    
    assert_eq!(cycled, vec![1, 2, 3, 1, 2, 3, 1]);
}

// fuse适配器
fn fuse_adapter() {
    let mut iter = vec![1, 2, 3].into_iter();
    
    // 正常迭代
    assert_eq!(iter.next(), Some(1));
    assert_eq!(iter.next(), Some(2));
    assert_eq!(iter.next(), Some(3));
    assert_eq!(iter.next(), None);
    
    // 使用fuse后，None之后继续调用next仍然返回None
    let mut fused_iter = iter.fuse();
    assert_eq!(fused_iter.next(), None);
    assert_eq!(fused_iter.next(), None); // 即使多次调用也返回None
}
```

## 4. 惰性求值

### 4.1 惰性求值机制

**惰性求值语义**：

```rust
// 惰性求值示例
fn lazy_evaluation_example() {
    let numbers = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    
    // 创建迭代器链，但此时不执行任何计算
    let iterator = numbers.iter()
        .filter(|&&x| {
            println!("Filtering: {}", x);
            x % 2 == 0
        })
        .map(|&x| {
            println!("Mapping: {}", x);
            x * 2
        })
        .take(3); // 只取前3个结果
    
    println!("Iterator created, but not executed yet");
    
    // 只有在调用collect时才实际执行
    let result: Vec<i32> = iterator.collect();
    println!("Result: {:?}", result);
}

// 短路求值
fn short_circuit_evaluation() {
    let numbers = vec![1, 2, 3, 4, 5];
    
    // any方法会在找到第一个满足条件的元素后停止
    let has_even = numbers.iter().any(|&&x| {
        println!("Checking: {}", x);
        x % 2 == 0
    });
    
    println!("Has even: {}", has_even);
    
    // all方法会在找到第一个不满足条件的元素后停止
    let all_positive = numbers.iter().all(|&&x| {
        println!("Checking: {}", x);
        x > 0
    });
    
    println!("All positive: {}", all_positive);
}

// 无限迭代器
fn infinite_iterators() {
    // 创建无限迭代器
    let infinite = (1..).filter(|&x| x % 2 == 0);
    
    // 只取前5个元素
    let first_five: Vec<i32> = infinite.take(5).collect();
    assert_eq!(first_five, vec![2, 4, 6, 8, 10]);
    
    // 斐波那契数列
    let fibonacci = std::iter::successors(Some((0, 1)), |&(a, b)| Some((b, a + b)))
        .map(|(a, _)| a);
    
    let first_ten: Vec<i32> = fibonacci.take(10).collect();
    assert_eq!(first_ten, vec![0, 1, 1, 2, 3, 5, 8, 13, 21, 34]);
}
```

### 4.2 内存效率

**内存效率优化**：

```rust
// 避免中间集合
fn avoid_intermediate_collections() {
    let numbers = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    
    // 低效方式：创建多个中间集合
    let doubled: Vec<i32> = numbers.iter().map(|&x| x * 2).collect();
    let evens: Vec<i32> = doubled.iter().filter(|&&x| x % 2 == 0).copied().collect();
    let sum: i32 = evens.iter().sum();
    
    // 高效方式：链式操作，无中间集合
    let sum_efficient: i32 = numbers.iter()
        .map(|&x| x * 2)
        .filter(|&x| x % 2 == 0)
        .sum();
    
    assert_eq!(sum, sum_efficient);
}

// 使用引用避免克隆
fn use_references() {
    let strings = vec!["hello".to_string(), "world".to_string(), "rust".to_string()];
    
    // 使用引用避免克隆
    let lengths: Vec<usize> = strings.iter()
        .map(|s| s.len())
        .collect();
    
    assert_eq!(lengths, vec![5, 5, 4]);
    
    // 如果需要修改，使用可变引用
    let mut numbers = vec![1, 2, 3, 4, 5];
    numbers.iter_mut()
        .for_each(|x| *x *= 2);
    
    assert_eq!(numbers, vec![2, 4, 6, 8, 10]);
}

// 使用peekable避免重复计算
fn use_peekable() {
    let numbers = vec![1, 2, 3, 4, 5];
    let mut peekable = numbers.iter().peekable();
    
    while let Some(&num) = peekable.next() {
        if let Some(&next) = peekable.peek() {
            println!("Current: {}, Next: {}", num, next);
        } else {
            println!("Current: {}, Next: None", num);
        }
    }
}
```

## 5. 性能优化

### 5.1 迭代器性能

**迭代器性能优化**：

```rust
// 预分配容量
fn preallocate_capacity() {
    let numbers = vec![1, 2, 3, 4, 5];
    
    // 预分配容量以提高性能
    let mut result = Vec::with_capacity(numbers.len());
    result.extend(numbers.iter().map(|&x| x * 2));
    
    assert_eq!(result, vec![2, 4, 6, 8, 10]);
}

// 使用collect_into避免重新分配
fn use_collect_into() {
    let numbers = vec![1, 2, 3, 4, 5];
    let mut result = Vec::new();
    
    // 使用collect_into避免重新分配
    numbers.iter()
        .map(|&x| x * 2)
        .collect_into(&mut result);
    
    assert_eq!(result, vec![2, 4, 6, 8, 10]);
}

// 使用fold进行单次遍历
fn use_fold() {
    let numbers = vec![1, 2, 3, 4, 5];
    
    // 使用fold在一次遍历中完成多个操作
    let (sum, count, max) = numbers.iter().fold(
        (0, 0, i32::MIN),
        |(sum, count, max), &x| (sum + x, count + 1, max.max(x))
    );
    
    assert_eq!(sum, 15);
    assert_eq!(count, 5);
    assert_eq!(max, 5);
}

// 使用try_fold进行早期退出
fn use_try_fold() {
    let numbers = vec![1, 2, 3, 4, 5];
    
    // 使用try_fold在找到目标时提前退出
    let result: Result<i32, &str> = numbers.iter()
        .try_fold(0, |acc, &x| {
            if x > 10 {
                Err("Number too large")
            } else {
                Ok(acc + x)
            }
        });
    
    assert_eq!(result, Ok(15));
}
```

### 5.2 编译时优化

**编译时优化策略**：

```rust
// 使用const fn进行编译时计算
const fn const_sum(a: i32, b: i32) -> i32 {
    a + b
}

fn compile_time_optimization() {
    let result = const_sum(5, 3);
    // 编译器会在编译时计算这个值
    assert_eq!(result, 8);
}

// 使用内联优化
#[inline(always)]
fn inline_function(x: i32) -> i32 {
    x * 2
}

fn use_inline_function() {
    let numbers = vec![1, 2, 3, 4, 5];
    let doubled: Vec<i32> = numbers.iter()
        .map(|&x| inline_function(x))
        .collect();
    
    assert_eq!(doubled, vec![2, 4, 6, 8, 10]);
}

// 使用特化优化
fn specialized_operation<T>(items: &[T]) -> usize 
where
    T: Clone,
{
    items.len()
}

// 为特定类型提供特化实现
fn specialized_operation_specialized(items: &[i32]) -> usize {
    items.len() * 2 // 特化实现
}
```

## 6. 自定义迭代器

### 6.1 实现自定义迭代器

**自定义迭代器实现**：

```rust
// 简单的自定义迭代器
struct Range {
    start: i32,
    end: i32,
    step: i32,
}

impl Range {
    fn new(start: i32, end: i32, step: i32) -> Self {
        Self { start, end, step }
    }
}

impl Iterator for Range {
    type Item = i32;
    
    fn next(&mut self) -> Option<Self::Item> {
        if self.start < self.end {
            let current = self.start;
            self.start += self.step;
            Some(current)
        } else {
            None
        }
    }
}

// 使用自定义迭代器
fn custom_range_usage() {
    let range = Range::new(0, 10, 2);
    let numbers: Vec<i32> = range.collect();
    assert_eq!(numbers, vec![0, 2, 4, 6, 8]);
}

// 更复杂的自定义迭代器
struct WindowIterator<T> {
    data: Vec<T>,
    window_size: usize,
    current_index: usize,
}

impl<T> WindowIterator<T> {
    fn new(data: Vec<T>, window_size: usize) -> Self {
        Self {
            data,
            window_size,
            current_index: 0,
        }
    }
}

impl<T: Clone> Iterator for WindowIterator<T> {
    type Item = Vec<T>;
    
    fn next(&mut self) -> Option<Self::Item> {
        if self.current_index + self.window_size <= self.data.len() {
            let window = self.data[self.current_index..self.current_index + self.window_size]
                .to_vec();
            self.current_index += 1;
            Some(window)
        } else {
            None
        }
    }
}

// 使用窗口迭代器
fn window_iterator_usage() {
    let data = vec![1, 2, 3, 4, 5];
    let windows = WindowIterator::new(data, 3);
    let result: Vec<Vec<i32>> = windows.collect();
    
    assert_eq!(result, vec![
        vec![1, 2, 3],
        vec![2, 3, 4],
        vec![3, 4, 5],
    ]);
}
```

### 6.2 迭代器适配器实现

**自定义迭代器适配器**：

```rust
// 自定义map适配器
struct CustomMap<I, F> {
    iter: I,
    f: F,
}

impl<I, F> CustomMap<I, F> {
    fn new(iter: I, f: F) -> Self {
        Self { iter, f }
    }
}

impl<I, F, B> Iterator for CustomMap<I, F>
where
    I: Iterator,
    F: FnMut(I::Item) -> B,
{
    type Item = B;
    
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(&mut self.f)
    }
}

// 为所有迭代器添加自定义方法
trait CustomIteratorExt: Iterator {
    fn custom_map<F, B>(self, f: F) -> CustomMap<Self, F>
    where
        F: FnMut(Self::Item) -> B,
        Self: Sized,
    {
        CustomMap::new(self, f)
    }
}

impl<I: Iterator> CustomIteratorExt for I {}

// 使用自定义适配器
fn custom_adapter_usage() {
    let numbers = vec![1, 2, 3, 4, 5];
    let doubled: Vec<i32> = numbers.iter()
        .custom_map(|&x| x * 2)
        .copied()
        .collect();
    
    assert_eq!(doubled, vec![2, 4, 6, 8, 10]);
}
```

## 7. 测试和验证

### 7.1 迭代器测试

**迭代器测试框架**：

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_iterator() {
        let numbers = vec![1, 2, 3, 4, 5];
        let mut iter = numbers.iter();
        
        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.next(), Some(&3));
        assert_eq!(iter.next(), Some(&4));
        assert_eq!(iter.next(), Some(&5));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_map_adapter() {
        let numbers = vec![1, 2, 3, 4, 5];
        let doubled: Vec<i32> = numbers.iter()
            .map(|&x| x * 2)
            .collect();
        
        assert_eq!(doubled, vec![2, 4, 6, 8, 10]);
    }

    #[test]
    fn test_filter_adapter() {
        let numbers = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
        let evens: Vec<i32> = numbers.iter()
            .filter(|&&x| x % 2 == 0)
            .copied()
            .collect();
        
        assert_eq!(evens, vec![2, 4, 6, 8, 10]);
    }

    #[test]
    fn test_chain_adapter() {
        let first = vec![1, 2, 3];
        let second = vec![4, 5, 6];
        
        let combined: Vec<i32> = first.iter()
            .chain(second.iter())
            .copied()
            .collect();
        
        assert_eq!(combined, vec![1, 2, 3, 4, 5, 6]);
    }

    #[test]
    fn test_zip_adapter() {
        let numbers = vec![1, 2, 3];
        let letters = vec!['a', 'b', 'c'];
        
        let zipped: Vec<(i32, char)> = numbers.iter()
            .zip(letters.iter())
            .map(|(&n, &c)| (n, c))
            .collect();
        
        assert_eq!(zipped, vec![(1, 'a'), (2, 'b'), (3, 'c')]);
    }

    #[test]
    fn test_custom_iterator() {
        let range = Range::new(0, 5, 1);
        let numbers: Vec<i32> = range.collect();
        assert_eq!(numbers, vec![0, 1, 2, 3, 4]);
    }

    #[test]
    fn test_window_iterator() {
        let data = vec![1, 2, 3, 4];
        let windows = WindowIterator::new(data, 2);
        let result: Vec<Vec<i32>> = windows.collect();
        
        assert_eq!(result, vec![
            vec![1, 2],
            vec![2, 3],
            vec![3, 4],
        ]);
    }

    #[test]
    fn test_lazy_evaluation() {
        let mut call_count = 0;
        let numbers = vec![1, 2, 3, 4, 5];
        
        let iterator = numbers.iter()
            .map(|&x| {
                call_count += 1;
                x * 2
            })
            .take(3);
        
        // 此时还没有调用map函数
        assert_eq!(call_count, 0);
        
        let result: Vec<i32> = iterator.collect();
        
        // 只有前3个元素被处理
        assert_eq!(call_count, 3);
        assert_eq!(result, vec![2, 4, 6]);
    }

    #[test]
    fn test_short_circuit() {
        let numbers = vec![1, 2, 3, 4, 5];
        let mut call_count = 0;
        
        let has_even = numbers.iter().any(|&&x| {
            call_count += 1;
            x % 2 == 0
        });
        
        // 只检查到第一个偶数就停止
        assert_eq!(call_count, 2);
        assert!(has_even);
    }

    #[test]
    fn test_performance_optimization() {
        let numbers = vec![1, 2, 3, 4, 5];
        
        // 使用fold进行单次遍历
        let (sum, count, max) = numbers.iter().fold(
            (0, 0, i32::MIN),
            |(sum, count, max), &x| (sum + x, count + 1, max.max(x))
        );
        
        assert_eq!(sum, 15);
        assert_eq!(count, 5);
        assert_eq!(max, 5);
    }
}
```

## 8. 总结

Rust的迭代器系统提供了强大而高效的序列处理能力。通过惰性求值、零成本抽象、类型安全等特性，迭代器既保证了性能，又提供了优雅的函数式编程接口。

迭代器是Rust语言的核心特性之一，它通过编译时优化和运行时效率，为开发者提供了处理集合和序列的最佳实践。理解迭代器的语义对于编写高效、可读的Rust程序至关重要。

迭代器系统体现了Rust在性能和表达力之间的平衡，为开发者提供了既高效又安全的序列处理工具，是现代Rust编程中不可或缺的重要组成部分。
