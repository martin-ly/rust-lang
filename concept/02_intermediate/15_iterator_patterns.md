# Rust 迭代器模式

> **Bloom 层级**: 应用 → 分析
> **定位**: 深入探讨 Rust 迭代器模式——从适配器链到自定义迭代器，分析惰性求值、性能特征和最佳实践。
> **前置概念**: [Type System](../01_foundation/04_type_system.md) · [Generics](../02_intermediate/02_generics.md) · [Closures](../01_foundation/15_closure_basics.md)
> **后置概念**: [Concurrency](../03_advanced/01_concurrency.md) · [Performance](../06_ecosystem/15_performance_optimization.md)

---

> **来源**: [TRPL — Iterators](https://doc.rust-lang.org/book/ch13-02-iterators.html) · [Rust Reference — Iterators](https://doc.rust-lang.org/std/iter/trait.Iterator.html) · [Rust Iterator Cheat Sheet](https://doc.rust-lang.org/std/iter/index.html) · [Wikipedia — Iterator Pattern](https://en.wikipedia.org/wiki/Iterator_pattern)

## 📑 目录
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]
>
> [来源: [TRPL](https://doc.rust-lang.org/book/)]

- [Rust 迭代器模式](#rust-迭代器模式)
  - [📑 目录](#-目录)
  - [一、核心概念](#一核心概念)
    - [1.1 Iterator Trait](#11-iterator-trait)
    - [1.2 适配器链](#12-适配器链)
    - [1.3 惰性求值](#13-惰性求值)
  - [二、常用模式](#二常用模式)
    - [2.1 map-filter-collect](#21-map-filter-collect)
    - [2.2 fold 与归约](#22-fold-与归约)
    - [2.3 zip 与并行迭代](#23-zip-与并行迭代)
  - [三、自定义迭代器](#三自定义迭代器)
  - [四、性能权衡](#四性能权衡)
  - [五、反命题与边界分析](#五反命题与边界分析)
  - [六、常见陷阱](#六常见陷阱)
  - [七、来源与延伸阅读](#七来源与延伸阅读)
  - [相关概念文件](#相关概念文件)

---

## 一、核心概念
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]
>
> [来源: [TRPL](https://doc.rust-lang.org/book/)]

### 1.1 Iterator Trait

```text
Iterator Trait:

  定义: Rust 中所有迭代器实现的核心 trait
  ├── next() 方法返回 Option<Self::Item>
  ├── 消费者 (Consumer) 触发实际计算
  └── 适配器 (Adapter) 返回新的迭代器

  代码示例:

  let v = vec![1, 2, 3];
  let mut iter = v.iter();

  assert_eq!(iter.next(), Some(&1));
  assert_eq!(iter.next(), Some(&2));
  assert_eq!(iter.next(), Some(&3));
  assert_eq!(iter.next(), None);

  关键特征:
  ├── 零成本抽象
  ├── 组合优于继承
  └── 类型安全
```

> **认知功能**: **Iterator trait 是 Rust 零成本抽象的核心体现**——编译器将适配器链优化为高效的循环。
> [来源: [TRPL — Iterators](https://doc.rust-lang.org/book/ch13-02-iterators.html)]

---

### 1.2 适配器链

```text
适配器链:

  映射适配器:
  ├── map: 转换每个元素
  ├── filter: 筛选元素
  ├── enumerate: 添加索引
  ├── take: 取前 N 个
  └── skip: 跳过前 N 个

  代码示例:

  let result: Vec<i32> = (0..100)
      .filter(|x| x % 2 == 0)   // 偶数
      .map(|x| x * x)            // 平方
      .take(5)                   // 取前5个
      .collect();                // 收集为 Vec

  // result: [0, 4, 16, 36, 64]

  链式组合:
  ┌─────────────────┬─────────────────┬─────────────────┐
  │ 适配器          │ 输入            │ 输出            │
  ├─────────────────┼─────────────────┼─────────────────┤
  │ map             │ Iterator<T>     │ Iterator<U>     │
  │ filter          │ Iterator<T>     │ Iterator<T>     │
  │ enumerate       │ Iterator<T>     │ Iterator<(i,T)> │
  │ take            │ Iterator<T>     │ Iterator<T>     │
  │ flat_map        │ Iterator<T>     │ Iterator<U>     │
  └─────────────────┴─────────────────┴─────────────────┘
> [来源: [TRPL — Iterators]]
```

> **认知功能**: **适配器链让数据转换声明式且可组合**——每个适配器只做一件事，组合起来完成复杂转换。
> [来源: [Rust Iterator Cheat Sheet](https://doc.rust-lang.org/std/iter/index.html)]

---

### 1.3 惰性求值

```text
惰性求值:

  原理: 适配器链不会立即执行，直到遇到消费者
  ├── 适配器: 返回新迭代器（无计算）
  ├── 消费者: collect, sum, fold, for_each 等触发计算
  └── 编译器优化: 整个链内联为单个循环

  代码示例:

  // 惰性：没有实际计算发生
  let iter = (0..1_000_000)
      .map(|x| x * 2)
      .filter(|x| x > 100);

  // 消费者触发计算
  let sum: i32 = iter.sum();

  性能对比:
  ┌─────────────────┬─────────────────┬─────────────────┐
  │ 方式            │ 内存分配        │ 性能            │
  ├─────────────────┼─────────────────┼─────────────────┤
  │ 适配器链        │ 无（通常）      │ 最优（内联）    │
  │ 显式循环        │ 无              │ 接近            │
  │ 中间 Vec        │ 多次分配        │ 较差            │
  └─────────────────┴─────────────────┴─────────────────┘
> [来源: [TRPL — Iterators]]
```

> **认知功能**: **惰性求值让迭代器链既高效又可读**——没有中间分配，编译器优化为单一循环。
> [来源: [Rust Performance Book](https://nnethercote.github.io/perf-book/)]

---

## 二、常用模式
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]
>
> [来源: [TRPL](https://doc.rust-lang.org/book/)]

### 2.1 map-filter-collect

```text
map-filter-collect:

  最常用模式: 转换 → 筛选 → 收集
  ├── map: 数据转换
  ├── filter: 条件筛选
  └── collect: 结果收集

  代码示例:

  let names = vec!["Alice", "Bob", "Charlie", "Dave"];
  let long_names: Vec<String> = names
      .into_iter()
      .filter(|name| name.len() > 3)
      .map(|name| name.to_uppercase())
      .collect();

  // long_names: ["ALICE", "CHARLIE", "DAVE"]
```

> **认知功能**: **map-filter-collect 是 Rust 迭代器的经典模式**——声明式数据处理。
> [来源: [TRPL — Iterators](https://doc.rust-lang.org/book/ch13-02-iterators.html)]

---

### 2.2 fold 与归约

```text
fold 与归约:

  fold: 带初始值的累积
  reduce: 无初始值（第一个元素作为初始）

  代码示例:

  let nums = vec![1, 2, 3, 4, 5];

  // fold: 带初始值
  let sum = nums.iter().fold(0, |acc, x| acc + x);
  // sum: 15

  // reduce: 无初始值
  let max = nums.iter().reduce(|a, b| if a > b { a } else { b });
  // max: Some(&5)

  适用场景:
  ├── fold: 需要自定义初始值
  ├── reduce: 元素类型与结果类型相同
  └── sum/product: 数值专用快捷方式
```

> **认知功能**: **fold 是迭代器的通用归约操作**——任何累积计算都可以用 fold 表达。
> [来源: [std::iter::Iterator::fold](https://doc.rust-lang.org/std/iter/trait.Iterator.html#method.fold)]

---

### 2.3 zip 与并行迭代

```text
zip: 并行迭代多个序列

  代码示例:

  let names = vec!["Alice", "Bob"];
  let scores = vec![95, 87];

  let combined: Vec<String> = names
      .iter()
      .zip(scores.iter())
      .map(|(name, score)| format!("{}: {}", name, score))
      .collect();

  // combined: ["Alice: 95", "Bob: 87"]

  变体:
  ├── zip: 最短序列决定长度
  ├── zip_longest: 用 Option 填充
  └── enumerate: zip with 0..n
```

> **认知功能**: **zip 让并行迭代多个序列变得简单**——无需手动管理索引。
> [来源: [std::iter::Iterator::zip](https://doc.rust-lang.org/std/iter/trait.Iterator.html#method.zip)]

---

## 三、自定义迭代器
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]

```text
自定义迭代器:

  实现 Iterator trait:

  struct Counter {
      count: u32,
  }

  impl Iterator for Counter {
      type Item = u32;

      fn next(&mut self) -> Option<Self::Item> {
          if self.count < 5 {
              self.count += 1;
              Some(self.count)
          } else {
              None
          }
      }
  }

  // 使用
  let counter = Counter { count: 0 };
  let sum: u32 = counter.sum();
  // sum: 15 (1+2+3+4+5)

  优势:
  ├── 复用标准库适配器
  ├── 类型安全
  └── 零成本抽象
```

> **认知功能**: **自定义迭代器让任何序列类型都能享受标准库适配器链**。
> [来源: [TRPL — Implementing Iterator](https://doc.rust-lang.org/book/ch13-02-iterators.html)]

---

## 四、性能权衡
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]

```text
性能对比:

  ┌─────────────────┬─────────────────┬─────────────────┬─────────────────┐
  │ 方式            │ 可读性          │ 性能            │ 灵活性          │
  ├─────────────────┼─────────────────┼─────────────────┼─────────────────┤
  │ for 循环        │ 中              │ 最优            │ 低              │
  │ 适配器链        │ 高              │ 最优            │ 高              │
  │ 递归            │ 中              │ 差（无 TCO）    │ 中              │
  │ 索引访问        │ 低              │ 中              │ 低              │
  └─────────────────┴─────────────────┴─────────────────┴─────────────────┘
> [来源: [TRPL — Iterators]]

  性能洞察:
  ├── 适配器链编译为与手写循环相同的机器码
  ├── iter() 比 into_iter() 快（不移动所有权）
  ├── 用 iter_mut() 原地修改
  └── 避免 collect() 除非需要中间结果
```

> **性能洞察**: **迭代器适配器链与手写循环性能相同**——编译器会内联整个链。
> [来源: [Rust Performance Book](https://nnethercote.github.io/perf-book/)]

---

## 五、反命题与边界分析
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]

```text
反命题:

  命题: "应该始终用适配器链替代 for 循环"

  反命题树:
  ├── 需要提前退出 (break)? → for 循环更适合
  ├── 需要复杂状态管理? → for 循环更清晰
  ├── 需要嵌套循环? → 考虑 flat_map 或 for
  └── 性能关键且简单? → for 循环可读性更好

  边界: 适配器链在简单数据转换时最优，复杂控制流用 for 循环
```

> **认知功能**: **适配器链和 for 循环各有适用场景**——简单转换用链，复杂控制用循环。
> [来源: [Rust Style Guide](https://doc.rust-lang.org/nightly/style-guide/)]

---

## 六、常见陷阱
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]

```text
陷阱 1: 多次消费迭代器
  ❌ iter 被消费后再次使用
     let iter = v.iter();
     let a: Vec<_> = iter.collect();
     let b: Vec<_> = iter.collect(); // 编译错误！

  ✅ 使用 clone 或重新创建
     let a: Vec<_> = v.iter().collect();
     let b: Vec<_> = v.iter().collect();

陷阱 2: 在闭包中修改外部状态
  ❌ 闭包捕获可变引用导致复杂借用
     let mut sum = 0;
     v.iter().for_each(|x| sum += x); // 可以但非惯用

  ✅ 使用 fold
     let sum = v.iter().fold(0, |acc, x| acc + x);

陷阱 3: 不必要的 collect
  ❌ 中间 collect 增加分配
     let a: Vec<_> = v.iter().map(...).collect();
     let b: Vec<_> = a.iter().filter(...).collect();

  ✅ 直接链式调用
     let b: Vec<_> = v.iter().map(...).filter(...).collect();

陷阱 4: 忽略 Option/Result 迭代器
  ❌ 手动处理 Option 迭代
     let values: Vec<i32> = options.iter().filter_map(|x| *x).collect();

  ✅ 使用 filter_map 或 flatten
     let values: Vec<i32> = options.into_iter().flatten().collect();
```

> **陷阱总结**: 迭代器的陷阱主要与**多次消费**、**外部状态**、**不必要 collect**和**Option 处理**相关。
> [来源: [TRPL — Iterators](https://doc.rust-lang.org/book/ch13-02-iterators.html)]

---

## 七、来源与延伸阅读
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]

| 来源 | 可信度 | 说明 |
|:---|:---:|:---|
| [TRPL — Iterators](https://doc.rust-lang.org/book/ch13-02-iterators.html) | ✅ 一级 | 官方书 |
| [Rust Reference — Iterator](https://doc.rust-lang.org/std/iter/trait.Iterator.html) | ✅ 一级 | 标准库 |
| [Rust Iterator Cheat Sheet](https://doc.rust-lang.org/std/iter/index.html) | ✅ 一级 | 官方速查 |
| [Rust Performance Book](https://nnethercote.github.io/perf-book/) | ✅ 二级 | 性能 |
| [Wikipedia — Iterator Pattern](https://en.wikipedia.org/wiki/Iterator_pattern) | ✅ 三级 | 通用概念 |

---

```rust
fn main() {
    let v = vec![1, 2, 3, 4, 5];
    let sum: i32 = v.iter().map(|x| x * 2).filter(|x| *x > 4).sum();
    println!("{}", sum); // 24
}
```

```rust
fn main() {
    let a = vec![1, 2, 3];
    let b = vec![4, 5, 6];
    let sum: i32 = a.iter().zip(b.iter()).map(|(x, y)| x + y).sum();
    println!("{}", sum); // 21
}
```

## 相关概念文件
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]

- [Type System](../01_foundation/04_type_system.md) — 类型系统
- [Generics](../02_intermediate/02_generics.md) — 泛型
- [Closures](../01_foundation/15_closure_basics.md) — 闭包
- [Concurrency](../03_advanced/01_concurrency.md) — 并发
- [Performance](../06_ecosystem/15_performance_optimization.md) — 性能优化

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/)
>
> **权威来源对齐变更日志**: 2026-05-22 创建 [来源: Authority Source Sprint Batch 13]

**文档版本**: 1.0
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-22
**状态**: ✅ 概念文件创建完成
