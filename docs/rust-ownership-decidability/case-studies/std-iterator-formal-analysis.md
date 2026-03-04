# Rust标准库 Iterator 形式化分析

> **主题**: 迭代器模式的代数结构与安全性
>
> **形式化框架**: 范畴论 + 类型代数
>
> **参考**: Rust Standard Library; Iterator Pattern

---

## 目录

- [Rust标准库 Iterator 形式化分析](#rust标准库-iterator-形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. Iterator trait形式化](#2-iterator-trait形式化)
    - [2.1 类型定义](#21-类型定义)
    - [定义 2.1 (Iterator trait)](#定义-21-iterator-trait)
    - [定理 2.1 (Iterator作为状态机)](#定理-21-iterator作为状态机)
    - [2.2 大小提示(SizeHint)语义](#22-大小提示sizehint语义)
    - [定义 2.2 (SizeHint)](#定义-22-sizehint)
    - [定理 2.2 (SizeHint正确性)](#定理-22-sizehint正确性)
  - [3. 迭代器组合子](#3-迭代器组合子)
    - [3.1 map与filter](#31-map与filter)
    - [定义 3.1 (Map)](#定义-31-map)
    - [定理 3.1 (Map的Functor定律)](#定理-31-map的functor定律)
    - [定义 3.2 (Filter)](#定义-32-filter)
    - [3.2 fold与reduce](#32-fold与reduce)
    - [定义 3.3 (Fold)](#定义-33-fold)
    - [定理 3.2 (Fold的结合性)](#定理-32-fold的结合性)
    - [3.3 take与skip](#33-take与skip)
    - [定理 3.3 (Take的短路)](#定理-33-take的短路)
  - [4. 迭代器适配器形式语义](#4-迭代器适配器形式语义)
    - [4.1 惰性求值保证](#41-惰性求值保证)
    - [定理 4.1 (惰性求值)](#定理-41-惰性求值)
    - [4.2 融合迭代器(FusedIterator)](#42-融合迭代器fusediterator)
    - [定义 4.2 (FusedIterator)](#定义-42-fusediterator)
    - [定理 4.2 (FusedIterator优化)](#定理-42-fusediterator优化)
  - [5. DoubleEndedIterator](#5-doubleendediterator)
    - [定义 5.1 (DoubleEndedIterator)](#定义-51-doubleendediterator)
    - [定理 5.1 (双端迭代正确性)](#定理-51-双端迭代正确性)
  - [6. ExactSizeIterator与TrustedLen](#6-exactsizeiterator与trustedlen)
    - [定义 6.1 (ExactSizeIterator)](#定义-61-exactsizeiterator)
    - [定理 6.1 (ExactSizeIterator正确性)](#定理-61-exactsizeiterator正确性)
    - [定义 6.2 (TrustedLen)](#定义-62-trustedlen)
  - [7. IntoIterator与for循环](#7-intoiterator与for循环)
    - [定义 7.1 (IntoIterator)](#定义-71-intoiterator)
    - [定理 7.1 (for循环展开)](#定理-71-for循环展开)
  - [8. 内存安全分析](#8-内存安全分析)
    - [定理 8.1 (迭代器借用安全)](#定理-81-迭代器借用安全)
    - [定理 8.2 (消耗性迭代器)](#定理-82-消耗性迭代器)
  - [9. 复杂度分析](#9-复杂度分析)
  - [10. 反例与陷阱](#10-反例与陷阱)
    - [反例 10.1 (修改被迭代集合)](#反例-101-修改被迭代集合)
    - [反例 10.2 (迭代器失效)](#反例-102-迭代器失效)
    - [反例 10.3 (无限迭代器)](#反例-103-无限迭代器)
    - [反例 10.4 (忘记collect)](#反例-104-忘记collect)
  - [参考文献](#参考文献)

---

## 1. 引言

Iterator是Rust最核心的trait之一，提供:

- **惰性求值**: 组合操作不立即执行
- **零成本抽象**: 组合后与手写循环性能相同
- **内存安全**: 借用检查确保迭代安全
- **可组合性**: 丰富的适配器方法

---

## 2. Iterator trait形式化

### 2.1 类型定义

### 定义 2.1 (Iterator trait)

```rust
pub trait Iterator {
    type Item;

    fn next(&mut self) -> Option<Self::Item>;

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, None)
    }
}
```

**形式化**:

$$
\text{Iterator}\langle \text{Item} = T \rangle = \begin{cases}
\text{next}: \&mut \text{Self} \rightarrow \text{Option}\langle T \rangle \\
\text{size\_hint}: \&\text{Self} \rightarrow (\mathbb{N}, \text{Option}\langle \mathbb{N} \rangle)
\end{cases}
$$

### 定理 2.1 (Iterator作为状态机)

> 每个迭代器实现都是状态机，next()驱动状态转换。

**证明**:

迭代器维护内部状态:

```rust
struct Counter {
    current: u32,
    max: u32,
}

impl Iterator for Counter {
    type Item = u32;

    fn next(&mut self) -> Option<Self::Item> {
        if self.current < self.max {
            let val = self.current;
            self.current += 1;
            Some(val)
        } else {
            None
        }
    }
}
```

状态: $\{ \text{Running}(n), \text{Done} \}$

转换:

- $\text{Running}(n) \xrightarrow{\text{next}} \text{Running}(n+1)$ (如果 $n < \text{max}$)
- $\text{Running}(n) \xrightarrow{\text{next}} \text{Done}$ (如果 $n \geq \text{max}$)
- $\text{Done} \xrightarrow{\text{next}} \text{Done}$

∎

### 2.2 大小提示(SizeHint)语义

### 定义 2.2 (SizeHint)

```rust
fn size_hint(&self) -> (usize, Option<usize>) {
    (lower_bound, upper_bound)
}
```

**形式化**:

$$
\text{size\_hint} = (l, u) \text{ 其中 } l \leq |\text{remaining}| \leq u
$$

### 定理 2.2 (SizeHint正确性)

> size_hint返回的边界总是正确的(如果提供)。

**保证**:

- $l \leq$ 实际剩余元素数
- 如果 $u = \text{Some}(v)$，则实际剩余 $\leq v$
- 如果 $u = \text{None}$，无上界

**实现示例**:

```rust
impl Iterator for VecIntoIter<T> {
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))  // 精确知道大小
    }
}

impl Iterator for Range<usize> {
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.end.saturating_sub(self.start);
        (len, Some(len))
    }
}
```

∎

---

## 3. 迭代器组合子

### 3.1 map与filter

### 定义 3.1 (Map)

```rust
struct Map<I, F> {
    iter: I,
    f: F,
}

impl<I: Iterator, F: FnMut(I::Item) -> B> Iterator for Map<I, F> {
    type Item = B;

    fn next(&mut self) -> Option<B> {
        self.iter.next().map(&mut self.f)
    }
}
```

### 定理 3.1 (Map的Functor定律)

> Iterator::map 满足Functor定律。

**证明**:

**Identity**:

```rust
iter.map(|x| x)  // 等价于 iter
```

**Composition**:

```rust
iter.map(f).map(g)  // 等价于 iter.map(|x| g(f(x)))
```

实现:

```rust
// iter.map(f).map(g).next()
self.iter.next().map(f).map(g)

// iter.map(|x| g(f(x))).next()
self.iter.next().map(|x| g(f(x)))
```

等价。∎

### 定义 3.2 (Filter)

```rust
struct Filter<I, P> {
    iter: I,
    predicate: P,
}

impl<I: Iterator, P: FnMut(&I::Item) -> bool> Iterator for Filter<I, P> {
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.iter.next() {
                Some(x) if (self.predicate)(&x) => return Some(x),
                Some(_) => continue,
                None => return None,
            }
        }
    }
}
```

### 3.2 fold与reduce

### 定义 3.3 (Fold)

```rust
fn fold<B, F>(self, init: B, mut f: F) -> B
where
    F: FnMut(B, Self::Item) -> B,
{
    let mut accum = init;
    for x in self {
        accum = f(accum, x);
    }
    accum
}
```

### 定理 3.2 (Fold的结合性)

> fold可以并行化(用于rayon::iter)。

**条件**:

- 如果 $f$ 满足结合律: $f(a, f(b, c)) = f(f(a, b), c)$
- 则 fold 可以分块并行计算

∎

### 3.3 take与skip

### 定理 3.3 (Take的短路)

> take(n)在消费n个元素后停止，不消耗剩余迭代器。

**实现**:

```rust
impl<I: Iterator> Iterator for Take<I> {
    fn next(&mut self) -> Option<Self::Item> {
        if self.n == 0 {
            return None;
        }
        self.n -= 1;
        self.iter.next()
    }
}
```

**复杂度**:

- `take(n)` 只消费 $O(n)$ 元素
- 底层迭代器剩余元素保持不变

∎

---

## 4. 迭代器适配器形式语义

### 4.1 惰性求值保证

### 定理 4.1 (惰性求值)

> 迭代器适配器是惰性的，直到消费操作才执行。

**证明**:

```rust
let iter = vec.iter()
    .map(|x| expensive_operation(x))  // 不执行
    .filter(|x| x > 0)                 // 不执行
    .take(5);                          // 不执行

// 消费时才执行
for x in iter {
    println!("{}", x);  // 现在才执行map+filter+take
}
```

**执行顺序**:

- 每次 `next()` 调用
- 执行必要的map/filter/take
- 不预计算或缓冲(除非必要)

∎

### 4.2 融合迭代器(FusedIterator)

### 定义 4.2 (FusedIterator)

```rust
pub trait FusedIterator: Iterator {}
```

**保证**:

一旦返回 `None`，后续所有 `next()` 调用也返回 `None`。

### 定理 4.2 (FusedIterator优化)

> FusedIterator允许编译器优化边界检查。

**实现**:

```rust
impl<I: FusedIterator> Iterator for Fuse<I> {
    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            None
        } else {
            let next = self.iter.next();
            if next.is_none() {
                self.done = true;
            }
            next
        }
    }
}
```

∎

---

## 5. DoubleEndedIterator

### 定义 5.1 (DoubleEndedIterator)

```rust
pub trait DoubleEndedIterator: Iterator {
    fn next_back(&mut self) -> Option<Self::Item>;
}
```

### 定理 5.1 (双端迭代正确性)

> 从两端交替消费应保持顺序。

**保证**:

```rust
let mut iter = vec![1, 2, 3, 4, 5].into_iter();
assert_eq!(iter.next(), Some(1));       // 前端
assert_eq!(iter.next_back(), Some(5));  // 后端
assert_eq!(iter.next(), Some(2));       // 前端
assert_eq!(iter.next_back(), Some(4));  // 后端
assert_eq!(iter.next(), Some(3));       // 最后
```

∎

---

## 6. ExactSizeIterator与TrustedLen

### 定义 6.1 (ExactSizeIterator)

```rust
pub trait ExactSizeIterator: Iterator {
    fn len(&self) -> usize;
}
```

### 定理 6.1 (ExactSizeIterator正确性)

> len()返回的值等于实际剩余元素数。

**约束**:

- `size_hint()` 必须返回 `(len, Some(len))`
- 不允许返回不精确大小

∎

### 定义 6.2 (TrustedLen)

```rust
pub unsafe trait TrustedLen: Iterator {}
```

**作用**:

- 标记大小提示可信
- 允许优化内存分配

---

## 7. IntoIterator与for循环

### 定义 7.1 (IntoIterator)

```rust
pub trait IntoIterator {
    type Item;
    type IntoIter: Iterator<Item = Self::Item>;

    fn into_iter(self) -> Self::IntoIter;
}
```

### 定理 7.1 (for循环展开)

> `for x in iter` 等价于 `IntoIterator::into_iter` + `Iterator::next`。

**展开**:

```rust
// 源码
for x in vec {
    println!("{}", x);
}

// 展开后
{
    let mut iter = IntoIterator::into_iter(vec);
    loop {
        match Iterator::next(&mut iter) {
            Some(x) => println!("{}", x),
            None => break,
        }
    }
}
```

∎

---

## 8. 内存安全分析

### 定理 8.1 (迭代器借用安全)

> 迭代器在借用期间不修改被迭代集合。

**证明**:

```rust
let v = vec![1, 2, 3];
for x in &v {
    // v.push(4);  // 编译错误!
    println!("{}", x);
}
```

- `&v` 创建不可变借用
- 借用期间 `v` 不可变
- 迭代器安全

∎

### 定理 8.2 (消耗性迭代器)

> IntoIterator消耗集合，后续访问编译错误。

**证明**:

```rust
let v = vec![1, 2, 3];
for x in v {  // 消耗v
    println!("{}", x);
}
// v.push(4);  // 编译错误! v已被移动
```

∎

---

## 9. 复杂度分析

| 操作 | 时间 | 空间 | 说明 |
|------|------|------|------|
| `next()` | $O(1)$ | $O(1)$ | 通常常数时间 |
| `map()` | $O(1)$ | $O(1)$ | 惰性，只创建适配器 |
| `filter()` | $O(1)$ | $O(1)$ | 惰性 |
| `fold()` | $O(n)$ | $O(1)$ | 消费整个迭代器 |
| `collect()` | $O(n)$ | $O(n)$ | 分配集合 |
| `count()` | $O(n)$ | $O(1)$ | 遍历计数 |
| `nth()` | $O(n)$ | $O(1)$ | 跳过n个元素 |

---

## 10. 反例与陷阱

### 反例 10.1 (修改被迭代集合)

```rust
let mut v = vec![1, 2, 3];
for x in &v {
    v.push(*x);  // 编译错误! 不可变借用期间修改
}
```

### 反例 10.2 (迭代器失效)

```rust
let mut v = vec![1, 2, 3];
let mut iter = v.iter();

v.push(4);  // 可能重新分配，使iter悬垂
// iter.next();  // 未定义行为!
```

### 反例 10.3 (无限迭代器)

```rust
let iter = std::iter::repeat(1);  // 无限
let sum: i32 = iter.sum();  // 无限循环!

// 正确做法
take(100).sum()  // 限制数量
```

### 反例 10.4 (忘记collect)

```rust
vec.iter().map(|x| x * 2);  // 惰性，不执行任何操作!

// 正确
vec.iter().map(|x| x * 2).collect::<Vec<_>>();
```

---

## 参考文献

1. **Rust Standard Library.** (2024). `std::iter::Iterator`. <https://doc.rust-lang.org/std/iter/trait.Iterator.html>

2. **Gamma, E., et al.** (1994). *Design Patterns*. Addison-Wesley.
   - 关键贡献: Iterator模式
   - 关联: 第1节

3. **Bird, R., & Wadler, P.** (1988). *Introduction to Functional Programming*.
   - 关键贡献: 列表操作的形式化
   - 关联: 第3节

---

*文档版本: 1.0.0*
*形式化深度: 高*
*定理数量: 12个*
*最后更新: 2026-03-04*
