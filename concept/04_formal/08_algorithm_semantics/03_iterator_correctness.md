> **内容分级**: [专家级]
>
> **代码状态**: ✅ 含可编译示例

# 迭代器正确性语义（Iterator Correctness Semantics）

> **EN**: Iterator Correctness Semantics
> **Summary**: Formal specification of the Rust `Iterator` trait and adapter chains in terms of preconditions, postconditions, and algebraic laws.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **受众**: [研究者]
> **Bloom 层级**: L4
> **权威来源**: 本文件为 `concept/` 权威页。
> **定位**: 从形式化语义角度刻画 Rust `Iterator` trait 与适配器链的契约：状态机视图、不变量、代数律，以及自定义迭代器的实现义务。连接算法语义、Hoare 逻辑与 Rust 标准库迭代器生态。
> **前置概念**: [Iterator Patterns](../../02_intermediate/07_iterators_and_closures/01_iterator_patterns.md) · [Hoare Logic for Rust Algorithms](01_hoare_logic_for_rust.md) · [Hoare Logic](../03_operational_semantics/02_hoare_logic.md)
> **后置概念**: [Stream Algebra](../../03_advanced/01_async/09_stream_algebra_and_backpressure.md) · [Unsafe Algorithm Invariants](04_unsafe_algorithm_invariants.md) · [Refinement Calculus](02_refinement_calculus.md)

---

> **权威来源 / Provenance**: [The Rust Programming Language — Iterators](https://doc.rust-lang.org/book/ch13-02-iterators.html) ·
> [Rust Reference — Iterator](https://doc.rust-lang.org/std/iter/trait.Iterator.html) ·
> [Rust API Guidelines — Iterators](https://rust-lang.github.io/api-guidelines/interoperability.html#c-iter) ·
> [Hoare 1969 — An Axiomatic Basis](https://doi.org/10.1093/comjnl/12.4.576) ·
> [Wadler 1990 — Deforestation](https://doi.org/10.1145/91556.91562) ·
> [Pitts 2012 — Step-Indexed Biorthogonality](https://doi.org/10.1017/S0956796812000261) ·
> [Ahmed 2006 — Step-Indexed Syntactic Logical Relations](https://doi.org/10.1007/11624738_2) ·
> [Felleisen 1991 — On the Expressive Power of Programming Languages](https://doi.org/10.1007/BF01178218) ·
> [Verus — Rust Verifier](https://github.com/verus-lang/verus) ·
> [Creusot — Rust Deductive Verification](https://github.com/creusot-rs/creusot) ·
> [Aeneas — Rust Verification by Functional Translation](https://aeneasverif.github.io/) ·
> [Verus: Verifying Rust Programs using Linear Ghost Types](https://arxiv.org/abs/2303.05475) ·
> [Creusot: A Foundational and Expressive Verifier for Rust](https://arxiv.org/abs/2202.02628)

## 📑 目录

- [迭代器正确性语义（Iterator Correctness Semantics）](#迭代器正确性语义iterator-correctness-semantics)
  - [📑 目录](#-目录)
  - [一、核心概念](#一核心概念)
    - [1.1 迭代器作为状态机](#11-迭代器作为状态机)
    - [1.2 Iterator 契约的不变量](#12-iterator-契约的不变量)
    - [1.3 适配器链的代数律](#13-适配器链的代数律)
  - [二、自定义迭代器的实现义务](#二自定义迭代器的实现义务)
    - [2.1 最小实现：只需 `next`](#21-最小实现只需-next)
    - [2.2 `size_hint` 与 `ExactSizeIterator`](#22-size_hint-与-exactsizeiterator)
    - [2.3 `DoubleEndedIterator` 与 `FusedIterator`](#23-doubleendediterator-与-fusediterator)
  - [三、形式化规格示例](#三形式化规格示例)
    - [3.1 `Counter`：按构造证明正确](#31-counter按构造证明正确)
    - [3.2 `Windowed`：滑动窗口的安全证明草图](#32-windowed滑动窗口的安全证明草图)
  - [四、反命题与边界分析](#四反命题与边界分析)
    - [4.1 反命题树](#41-反命题树)
    - [4.2 边界极限](#42-边界极限)
  - [五、常见陷阱](#五常见陷阱)
  - [六、来源与延伸阅读](#六来源与延伸阅读)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)
  - [十、边界测试：迭代器正确性的编译与逻辑错误](#十边界测试迭代器正确性的编译与逻辑错误)
    - [10.1 边界测试：违反 `ExactSizeIterator` 精确性（逻辑错误）](#101-边界测试违反-exactsizeiterator-精确性逻辑错误)
    - [10.2 边界测试：`DoubleEndedIterator` 不对称导致 UB（unsafe）](#102-边界测试doubleendediterator-不对称导致-ubunsafe)
    - [10.3 边界测试：`FusedIterator` 被违反后的逻辑错误](#103-边界测试fusediterator-被违反后的逻辑错误)
    - [10.4 边界测试：有状态闭包破坏代数律（逻辑错误）](#104-边界测试有状态闭包破坏代数律逻辑错误)
  - [嵌入式测验（Embedded Quiz）](#嵌入式测验embedded-quiz)
    - [测验 1：迭代器状态机（理解层）](#测验-1迭代器状态机理解层)
    - [测验 2：`size_hint` 下界（应用层）](#测验-2size_hint-下界应用层)
    - [测验 3：适配器代数律（分析层）](#测验-3适配器代数律分析层)
    - [测验 4：`FusedIterator` 义务（应用层）](#测验-4fusediterator-义务应用层)
    - [测验 5：自定义迭代器的前置/后置条件（分析层）](#测验-5自定义迭代器的前置后置条件分析层)
  - [🧭 思维导图（Mindmap）](#-思维导图mindmap)

---

## 一、核心概念

### 1.1 迭代器作为状态机

Rust 的 `Iterator` trait 可以形式化地看作一个**确定型/非确定型状态机**，其核心转移由 `next` 方法定义：

```text
Iterator 状态机形式化定义:

  状态:  σ ∈ State（由具体迭代器维护，通常为索引、指针、内部缓冲等）
  输入:  无（调用 next 时无显式参数）
  输出:  Option<Item>

  转移语义:
  next(σ) = (Some(v), σ')   // 成功产生一个元素，状态推进到 σ'
  next(σ) = (None, σ')      // 迭代结束；对 FusedIterator 要求 ∀k≥0. next^k(σ') = None

  Hoare 三元组视角:
  { inv(σ) }                 // 迭代器不变量
    let r = it.next();
  { (r = Some(v) ∧ inv(σ')) ∨ (r = None ∧ exhausted(σ')) }
```

> **认知功能**: 把 `Iterator` 看作状态机，使"正确性"从"代码行为正确"转化为"状态转移满足不变量"。这是后续所有代数律与形式化证明的基础。
> (Source: [Rust Reference — Iterator](https://doc.rust-lang.org/std/iter/trait.Iterator.html); Pitts 2012; Ahmed 2006)

标准库中的 `std::slice::Iter` 即典型状态机：状态是一对 `(ptr, end)`，每次 `next` 将 `ptr` 前进一步并返回当前元素；`next_back` 从 `end` 回退一步。`DoubleEndedIterator` 的对称性要求两端推进不会交叉。

```rust
// 简化的 slice 迭代器状态机示意（非真实实现）
struct SliceIter<'a, T> {
    ptr: *const T,
    end: *const T,
    _marker: std::marker::PhantomData<&'a T>,
}

impl<'a, T> Iterator for SliceIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.ptr == self.end {
            None
        } else {
            let current = unsafe { &*self.ptr };
            self.ptr = unsafe { self.ptr.add(1) };
            Some(current)
        }
    }
}
```

> **安全边界**: 真实 `std::slice::Iter` 由编译器保证生命周期（Lifetimes）与借用（Borrowing）安全；手写 unsafe 迭代器时必须维护 `ptr` 在 `[start, end]` 之间且对齐的内存不变量。

---

### 1.2 Iterator 契约的不变量

`Iterator` trait 通过多个子 trait 扩展语义契约。每个子 trait 都附加了必须由实现者保证的不变量：

```text
Iterator 子契约不变量:

  Iterator (基础)
  ├── next: 每次调用返回序列的下一个元素或 None
  │   └── 无显式要求一旦返回 None 后必须继续返回 None（除非实现 FusedIterator）
  │
  ├── size_hint() -> (usize, Option<usize>)
  │   ├── 下界 lower: 实际剩余元素数 ≥ lower
  │   ├── 上界 upper: 若 Some(u)，则实际剩余元素数 ≤ u
  │   └── 默认实现: (0, None) —— 总是安全但可能低效
  │
  ├── ExactSizeIterator (extends Iterator)
  │   └── len() == 实际剩余元素数（精确）
  │       └── 与 size_hint 的 lower/upper 必须一致
  │
  ├── DoubleEndedIterator (extends Iterator)
  │   ├── next_back() 从序列另一端返回元素
  │   └── 对称性: next 与 next_back 交错调用必须按 FIFO/LIFO 交叉语义一致
  │       └── 即两端"相遇"后必须返回 None
  │
  └── FusedIterator (marker trait)
      └── 一旦返回 None，后续所有 next/next_back 调用必须继续返回 None
          └── 这是逻辑承诺，非编译期强制；违反不会导致 UB，但会导致逻辑 bug
```

> **认知功能**: 这些不变量构成迭代器契约的"层级结构"——基础 `Iterator` 只保证"有元素就返回"，上层 trait 逐步承诺更强的性质。实现者只有在确实能保证时才应实现上层 trait，否则宁愿只实现基础 trait。
> (Source: [Rust API Guidelines — Iterators](https://rust-lang.github.io/api-guidelines/interoperability.html#c-iter))

```rust
fn size_hint_contract<I: Iterator>(it: &mut I) -> (usize, Option<usize>) {
    let (lower, upper) = it.size_hint();
    // 契约: 实际可产生的元素数 n 满足 lower <= n <= upper.unwrap_or(n)
    // 因此 collect 可以按 lower 预分配，但不得假设 upper 一定存在
    (lower, upper)
}
```

---

### 1.3 适配器链的代数律

迭代器适配器在**无副作**用且**无状态依赖**时满足若干代数律，这些律对应编译优化与手动重构的合法性依据：

```text
适配器代数律（在纯函数/无副作用条件下）:

  映射融合 (Map Fusion):
  iter.map(f).map(g)  ≅  iter.map(|x| g(f(x)))
  成立条件: f 和 g 均为纯函数，不依赖外部可变状态

  过滤合并 (Filter Conjunction):
  iter.filter(p).filter(q)  ≅  iter.filter(|x| p(x) && q(x))
  成立条件: p、q 为纯谓词

  取/跳过顺序 (Take/Skip Ordering):
  iter.skip(m).take(n)  —— 先跳过 m，再取 n
  iter.take(n).skip(m)  —— 先取 n，再跳过 m
  注意: 当原序列长度 < m + n 时两者结果可能不同
  结论: take 与 skip 不交换，顺序即语义

  扁平化分配律 (Flatten/Map Interaction):
  iter.map(f).flatten()  ≅  iter.flat_map(f)
  成立条件: f 返回可迭代对象

  拉链结合律 (Zip Associativity, 近似):
  a.zip(b).map(|(x,y)| (y,x))  ≅  b.zip(a)   // 值相等，但迭代终止取决于较短者
```

> **认知功能**: 代数律把"能否重构代码"从直觉判断转化为**条件判断**——只要确认闭包纯函数，就可以安全地 fusion、重排或合并适配器。这也是 `rustc`/LLVM 进行迭代器内联与去森林化（deforestation）优化的理论基础。
> (Source: [Wadler 1990 — Deforestation](https://doi.org/10.1145/91556.91562); Felleisen 1991)

```rust
// 合法重构示例：map 融合
let v: Vec<i32> = (0..10)
    .map(|x| x + 1)   // f
    .map(|x| x * 2)   // g
    .collect();

// 等价于（当闭包纯函数时）
let v2: Vec<i32> = (0..10)
    .map(|x| (x + 1) * 2)
    .collect();

assert_eq!(v, v2);
```

---

## 二、自定义迭代器的实现义务

### 2.1 最小实现：只需 `next`

任何类型只要实现 `fn next(&mut self) -> Option<Self::Item>` 就是迭代器。其余方法都有默认实现，但默认实现通常依赖 `next`，复杂度可能不理想。

```rust
/// 最小自定义迭代器：从 0 计数到 n-1
struct CountTo {
    n: usize,
    i: usize,
}

impl CountTo {
    fn new(n: usize) -> Self {
        Self { n, i: 0 }
    }
}

impl Iterator for CountTo {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        if self.i < self.n {
            let v = self.i;
            self.i += 1;
            Some(v)
        } else {
            None
        }
    }
}

fn main() {
    let vals: Vec<_> = CountTo::new(5).collect();
    assert_eq!(vals, vec![0, 1, 2, 3, 4]);
}
```

> **义务清单**: 自定义迭代器必须保证：
>
> 1. `next` 按预期顺序返回元素；
> 2. 状态更新正确；
> 3. 若实现 `size_hint`/`ExactSizeIterator`/`DoubleEndedIterator`/`FusedIterator`，必须满足对应不变量。

---

### 2.2 `size_hint` 与 `ExactSizeIterator`

`size_hint` 是优化 `collect` 预分配的关键。实现者应遵循：

```text
size_hint 规格:
  设剩余元素数为 remaining
  lower <= remaining
  upper = Some(u) ⇒ remaining <= u
  ExactSizeIterator::len() == remaining
```

```rust
/// 返回精确长度的迭代器
struct ThreeTimes {
    count: usize,
    limit: usize,
}

impl ThreeTimes {
    fn new(limit: usize) -> Self {
        Self { count: 0, limit }
    }
}

impl Iterator for ThreeTimes {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        if self.count < self.limit {
            let v = self.count * 3;
            self.count += 1;
            Some(v)
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.limit - self.count;
        (remaining, Some(remaining))
    }
}

impl ExactSizeIterator for ThreeTimes {}

fn main() {
    let mut it = ThreeTimes::new(4);
    assert_eq!(it.len(), 4);
    it.next();
    assert_eq!(it.len(), 3);
}
```

> **警告**: 若 `size_hint` 下界大于实际剩余元素，`collect` 可能越界访问或 panic；若上界小于实际剩余元素，可能截断数据。标准库内部（如 `TrustedLen`）对上界为 `None` 的情况有特殊处理。

---

### 2.3 `DoubleEndedIterator` 与 `FusedIterator`

`DoubleEndedIterator` 要求从两端交替取值仍保持序列语义一致。`FusedIterator` 是一个纯标记 trait，承诺一旦耗尽永远返回 `None`。

```rust
/// 双端迭代器示例：双向遍历一个数组的引用
struct ArrayIter<'a, T> {
    front: usize,
    back: usize,
    data: &'a [T],
}

impl<'a, T> ArrayIter<'a, T> {
    fn new(data: &'a [T]) -> Self {
        Self { front: 0, back: data.len(), data }
    }
}

impl<'a, T> Iterator for ArrayIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.front < self.back {
            let v = &self.data[self.front];
            self.front += 1;
            Some(v)
        } else {
            None
        }
    }
}

impl<'a, T> DoubleEndedIterator for ArrayIter<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.front < self.back {
            self.back -= 1;
            Some(&self.data[self.back])
        } else {
            None
        }
    }
}

fn main() {
    let data = [1, 2, 3, 4];
    let mut it = ArrayIter::new(&data);
    assert_eq!(it.next(), Some(&1));
    assert_eq!(it.next_back(), Some(&4));
    assert_eq!(it.next(), Some(&2));
    assert_eq!(it.next_back(), Some(&3));
    assert_eq!(it.next(), None);
}
```

> **关键不变量**: `front <= back` 必须始终成立；当 `front == back` 时，迭代器已耗尽，两端都必须返回 `None`。

---

## 三、形式化规格示例

### 3.1 `Counter`：按构造证明正确

下面是一个"按构造证明"的计数器迭代器，其不变量内嵌在类型与状态更新中：

```rust
use std::iter::FusedIterator;

/// Counter: 产生 [start, end) 的整数序列
/// 前置条件: start <= end
/// 后置条件: 产生的序列恰好是 start, start+1, ..., end-1
struct Counter {
    start: usize,
    end: usize,
    cursor: usize,
}

impl Counter {
    fn new(start: usize, end: usize) -> Option<Self> {
        // 前置条件编码：要求 start <= end
        if start <= end {
            Some(Self { start, end, cursor: start })
        } else {
            None
        }
    }

    /// 循环不变量：已产生序列 = [start, cursor)，且 cursor <= end
    fn invariant(&self) -> bool {
        self.start <= self.cursor && self.cursor <= self.end
    }
}

impl Iterator for Counter {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        assert!(self.invariant());
        if self.cursor < self.end {
            let v = self.cursor;
            self.cursor += 1;
            Some(v)
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.end - self.cursor;
        (remaining, Some(remaining))
    }
}

impl ExactSizeIterator for Counter {}
impl FusedIterator for Counter {}

fn main() {
    let counter = Counter::new(2, 5).unwrap();
    assert_eq!(counter.collect::<Vec<_>>(), vec![2, 3, 4]);
}
```

> **认知功能**: 通过把前置条件放入构造函数（`new` 返回 `Option`），把不变量嵌入 `next` 的断言，迭代器的正确性从"测试覆盖"提升为"构造即正确"。这是 Hoare 逻辑在迭代器层面的直接应用。

---

### 3.2 `Windowed`：滑动窗口的安全证明草图

滑动窗口迭代器展示了一个涉及切片边界与安全证明的自定义实现：

```rust
use std::iter::FusedIterator;

/// 滑动窗口迭代器：对切片按窗口大小 w 滑动取值
/// 前置条件: w > 0
/// 不变量: 每次返回的窗口是原切片中连续 w 个元素的引用
struct Windowed<'a, T> {
    data: &'a [T],
    window_size: usize,
    offset: usize,
}

impl<'a, T> Windowed<'a, T> {
    fn new(data: &'a [T], window_size: usize) -> Option<Self> {
        // 前置条件：窗口大小必须为正
        if window_size == 0 {
            return None;
        }
        Some(Self { data, window_size, offset: 0 })
    }
}

impl<'a, T> Iterator for Windowed<'a, T> {
    type Item = &'a [T];

    fn next(&mut self) -> Option<Self::Item> {
        // 不变量: offset <= data.len()（由构造与更新保证）
        if self.offset + self.window_size <= self.data.len() {
            let window = &self.data[self.offset..self.offset + self.window_size];
            self.offset += 1;
            Some(window)
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.offset + self.window_size <= self.data.len() {
            let remaining = self.data.len() - self.window_size - self.offset + 1;
            (remaining, Some(remaining))
        } else {
            (0, Some(0))
        }
    }
}

impl<'a, T> ExactSizeIterator for Windowed<'a, T> {}
impl<'a, T> FusedIterator for Windowed<'a, T> {}

fn main() {
    let data = [1, 2, 3, 4, 5];
    let windows: Vec<_> = Windowed::new(&data, 3).unwrap().collect();
    assert_eq!(windows, vec![
        &data[0..3],
        &data[1..4],
        &data[2..5],
    ]);
}
```

> **证明草图**:
>
> - **初始化**: `offset = 0`，`window_size > 0`，若 `data.len() >= window_size` 则第一次 `next` 返回有效切片。
> - **保持**: 每次 `offset += 1`，且仅在 `offset + window_size <= data.len()` 时返回窗口，因此返回的切片始终在 `data` 范围内。
> - **终止**: 当 `offset + window_size > data.len()` 时返回 `None`，且由于 `offset` 单调递增，后续调用永远返回 `None`。
> - `FusedIterator` 成立。

---

## 四、反命题与边界分析

### 4.1 反命题树

```text
反命题 1: "迭代器适配器链可以随意重排而不改变语义"
  └── ❌ 否
      ├── take/skip 的顺序直接决定结果（有状态/位置敏感）
      ├── filter 与 map 的相对位置可能改变过滤对象
      ├── 有状态闭包（如外部变量累加）破坏代数律
      └── ✅ 正确表述: "仅在闭包纯函数且适配器可交换时，重排保持语义"
> (Source: [Rust Reference — Iterator](https://doc.rust-lang.org/std/iter/trait.Iterator.html))

反命题 2: "返回 None 后迭代器必须永远返回 None"
  └── ⚠️ 仅当实现 FusedIterator 时成立
      ├── 基础 Iterator 不保证这一点
      ├── 许多 I/O 迭代器可能因数据到达而再次产生元素
      └── ✅ 正确表述: "除非实现 FusedIterator，否则调用者不得假设耗尽后行为"
> (Source: [std::iter::FusedIterator](https://doc.rust-lang.org/std/iter/trait.FusedIterator.html))

反命题 3: "违反 size_hint 会导致未定义行为"
  └── ❌ 否
      ├── size_hint 只是性能提示，不用于安全判断
      ├── 但错误下界会导致 collect 预分配不足（可能 panic 或低效）
      ├── 错误上界会导致数据截断或内存浪费
      └── ✅ 正确表述: "size_hint 错误是逻辑 bug，不一定是 UB，但会破坏调用方假设"
> (Source: [Rust API Guidelines — Iterators](https://rust-lang.github.io/api-guidelines/interoperability.html#c-iter))
```

> **认知功能**: 反命题分析区分了**安全契约**（memory safety）与**逻辑契约**（correctness）——Rust 的类型系统保证前者，但迭代器的代数律与不变量属于后者，需要实现者自觉遵守。

---

### 4.2 边界极限

```text
边界 1: 纯函数假设
  ├── 代数律要求闭包无副作用
  ├── Rust 编译器不验证闭包纯度
  ├── 有状态闭包可使 map(f).map(g) ≠ map(g∘f)
  └── 极限: 代数优化必须由开发者或形式化工具保证前提

边界 2: 无限迭代器
  ├── std::iter::repeat、RangeFrom 等无固定长度
  ├── ExactSizeIterator 无法实现
  ├── size_hint 上界为 None
  └── collect::<Vec<_>>() 会无限增长直至 OOM

边界 3: unsafe 迭代器实现
  ├── 手动维护指针算术前置条件
  ├── 必须保证指针在有效范围内、对齐、无数据竞争
  └── 极限: unsafe 迭代器的不变量无法被借用检查器完全验证
```

> **认知功能**: 边界极限标定了迭代器正确性的三类风险——**有状态闭包**破坏代数律，**无限序列**破坏长度契约，**unsafe 实现**将安全责任从编译器转移给开发者。

---

## 五、常见陷阱

```text
陷阱 1: 在 size_hint 中返回乐观估计
  ❌ fn size_hint(&self) -> (usize, Option<usize>) { (100, Some(100)) }
     // 若实际只有 50 个元素，collect 可能读取未初始化内存或 panic

  ✅ 宁可保守: (0, None) 总是安全
     // 或精确计算剩余元素数
> (Source: [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/interoperability.html#c-iter))

陷阱 2: 实现 ExactSizeIterator 但 size_hint 不一致
  ❌ size_hint 返回 (0, None) 但 ExactSizeIterator::len 返回 10
     // 调用者可能同时检查两者，得到矛盾结果

  ✅ 保证 size_hint 的 lower/upper/len 三者一致
> (Source: [std::iter::ExactSizeIterator](https://doc.rust-lang.org/std/iter/trait.ExactSizeIterator.html))

陷阱 3: 有状态闭包破坏代数律
  ❌ let mut c = 0;
     iter.map(|x| { c += 1; x + c })
         .map(|x| x * 2)
     // 不可与单 map 融合，因为闭包依赖外部可变状态

  ✅ 将状态显式封装到迭代器结构体中，或避免有状态闭包

陷阱 4: 假设所有迭代器都是 FusedIterator
  ❌ let first_none = it.next();
     // 之后继续使用 it，假设它已耗尽
     // 对非 Fused 迭代器可能得到意外值

  ✅ 若需要该保证，使用 .fuse() 适配器或要求 FusedIterator bound
> (Source: [std::iter::Iterator::fuse](https://doc.rust-lang.org/std/iter/trait.Iterator.html#method.fuse))

陷阱 5: 把运行时断言当作形式化不变量
  ❌ debug_assert!(self.invariant()); // 只在 debug 模式检查
     // release 模式下不变量被破坏也无提示

  ✅ 不变量应通过类型/构造保证；必要时使用 #[cfg(test)] 或验证工具
```

> **陷阱总结**: 迭代器正确性的陷阱集中在 **size_hint 准确性**、**子 trait 一致性**、**闭包纯度**、**Fused 假设** 和 **断言模式** 五个方面。每个都反映了"类型系统保证安全，但逻辑正确性仍需人工/工具验证"的 Rust 设计哲学。

---

## 六、来源与延伸阅读

| 来源 | 可信度 | 说明 |
|:---|:---:|:---|
| [The Rust Programming Language — Iterators](https://doc.rust-lang.org/book/ch13-02-iterators.html) | ✅ 一级 | TRPL 迭代器章节 |
| [Rust Reference — Iterator trait](https://doc.rust-lang.org/std/iter/trait.Iterator.html) | ✅ 一级 | 标准库 API 文档 |
| [Rust API Guidelines — Iterators](https://rust-lang.github.io/api-guidelines/interoperability.html#c-iter) | ✅ 一级 | 自定义迭代器最佳实践 |
| [Wadler 1990 — Deforestation](https://doi.org/10.1145/91556.91562) | ✅ 一级 | 列表/迭代器融合理论基础 |
| [Hoare 1969](https://doi.org/10.1093/comjnl/12.4.576) | ✅ 一级 | Hoare 逻辑奠基 |
| [Bird & Meertens — Algorithmics](https://doi.org/10.1007/3-540-52869-7_107) | ✅ 二级 | 算法代数与程序推导 |
| [Rust Internals — TrustedLen](https://doc.rust-lang.org/std/iter/trait.TrustedLen.html) | ✅ 一级 | 特殊长度信任契约 |

---

## 相关概念

- [Iterator Patterns](../../02_intermediate/07_iterators_and_closures/01_iterator_patterns.md) — Rust 迭代器模式与生态使用
- [Stream Algebra](../../03_advanced/01_async/09_stream_algebra_and_backpressure.md) — 异步（Async）流代数与背压
- [Hoare Logic for Rust Algorithms](01_hoare_logic_for_rust.md) — 算法层面的 Hoare 逻辑入口
- [Hoare Logic](../03_operational_semantics/02_hoare_logic.md) — Hoare 逻辑完整理论与推理规则
- [Refinement Calculus](02_refinement_calculus.md) — 从规范到实现的逐步精化
- [Unsafe Algorithm Invariants](04_unsafe_algorithm_invariants.md) — unsafe 算法内部不变量

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/introduction.html), [The Rust Programming Language](https://doc.rust-lang.org/book/title-page.html), [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)
>
> **文档版本**: 1.0
> **最后更新**: 2026-07-28
> **状态**: ✅ 新建 — 算法语义子空间

---

## 权威来源索引

| **论断** | **来源** | **可信度** | **Tier** |
|:---|:---|:---:|:---:|
| Iterator 状态机语义 | [Rust Reference](https://doc.rust-lang.org/std/iter/trait.Iterator.html) | ✅ | Tier 1 |
| size_hint/ExactSizeIterator 契约 | [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/interoperability.html#c-iter) | ✅ | Tier 1 |
| 适配器 fusion 理论基础 | [Wadler 1990](https://doi.org/10.1145/91556.91562) | ✅ | Tier 1 |
| Hoare 三元组应用于迭代器 | [Hoare 1969](https://doi.org/10.1093/comjnl/12.4.576) · [💡 原创分析] | ✅/💡 | Tier 3 |
| 操作语义与步骤索引逻辑关系 | [Pitts 2012](https://doi.org/10.1017/S0956796812000261) · [Ahmed 2006](https://doi.org/10.1007/11624738_2) | ✅ | Tier 1 |
| 程序语言表现力与上下文等价 | [Felleisen 1991](https://doi.org/10.1007/BF01178218) | ✅ | Tier 1 |

---

## 十、边界测试：迭代器正确性的编译与逻辑错误

本节把「迭代器正确性语义」的规则推到编译器与运行时（Runtime）的边界上逐一实测：违反 `ExactSizeIterator` 精确性、`DoubleEndedIterator` 不对称导致 UB、`FusedIterator` 被违反后的逻辑错误、有状态闭包破坏代数律。每个用例标注预期结果（编译错误 / 运行时 panic / 逻辑错误），并用 rustc 1.97 验证。这些用例共同回答一个问题——规则在极限处是否仍然成立，以及违反时编译器能否兜底。

### 10.1 边界测试：违反 `ExactSizeIterator` 精确性（逻辑错误）

```rust,ignore
struct BadExact {
    remaining: usize,
}

impl Iterator for BadExact {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining > 0 {
            self.remaining -= 1;
            // ❌ 逻辑错误: 少产生一个元素（实际产生 remaining-1 个）
            // 但 size_hint/len 会报告错误的剩余数
            Some(self.remaining)
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}

impl ExactSizeIterator for BadExact {}

fn main() {
    // 该实现实际上 next 返回 Some(0) 后 self.remaining=0，然后返回 None
    // 逻辑上没问题；但若在循环中依赖 len() 预分配大小，可能出错
    let mut it = BadExact { remaining: 3 };
    assert_eq!(it.len(), 3);
    it.next();
    assert_eq!(it.len(), 2); // 实际已产生 1 个，剩余应为 2，正确
    // 真正的 bug 出现在：实现者让 size_hint 与 next 不同步
}
```

> **修正**: `ExactSizeIterator` 要求 `len()` 严格等于剩余可调用 `next` 的次数。实现者应在每次 `next` 中同步更新内部计数，或索性不实现 `ExactSizeIterator`。标准库中 `std::iter::Repeat` 因无限长度而不实现 `ExactSizeIterator`，正是避免给出错误承诺。

---

### 10.2 边界测试：`DoubleEndedIterator` 不对称导致 UB（unsafe）

```rust,ignore
// 手写 unsafe 双端迭代器时，若 front/back 交叉后仍返回指针，会导致越界
struct BadPtrIter<T> {
    start: *const T,
    end: *const T,
}

impl<T> Iterator for BadPtrIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        // ❌ 未检查 start < end，可能返回越界值或导致 UB
        unsafe {
            let v = std::ptr::read(self.start);
            self.start = self.start.add(1);
            Some(v)
        }
    }
}

// 正确版本必须保证 start <= end 且仅当 start < end 时才解引用
```

> **修正**: `DoubleEndedIterator` 的对称性本质是**区间不变量** `front <= back`。unsafe 实现中一旦该不变量被破坏，解引用越界指针即产生 UB。应使用 `std::ptr::NonNull` 或标准库 `slice::Iter` 而非裸指针手动遍历，除非正在进行形式化验证（如 Creusot/Kani）。

---

### 10.3 边界测试：`FusedIterator` 被违反后的逻辑错误

```rust
struct MaybeFused {
    vals: Vec<i32>,
    idx: usize,
    exhausted: bool,
}

impl Iterator for MaybeFused {
    type Item = i32;

    fn next(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            // 模拟非 Fused 行为：再次扫描
            self.idx = 0;
        }
        if self.idx < self.vals.len() {
            let v = self.vals[self.idx];
            self.idx += 1;
            Some(v)
        } else {
            self.exhausted = true;
            None
        }
    }
}

// 错误地声称自己是 FusedIterator
impl std::iter::FusedIterator for MaybeFused {}

fn main() {
    let mut it = MaybeFused { vals: vec![1, 2], idx: 0, exhausted: false };
    assert_eq!(it.next(), Some(1));
    assert_eq!(it.next(), Some(2));
    assert_eq!(it.next(), None);
    // 由于错误实现 FusedIterator，调用者可能认为下面仍为 None
    // 但实际会重新扫描，产生逻辑错误
    // assert_eq!(it.next(), None); // 实际为 Some(1)
}
```

> **修正**: `FusedIterator` 是**纯逻辑承诺**，编译器不检查。违反不会导致 UB，但会破坏依赖该承诺的代码（如 `.fuse()` 适配器的优化路径、某些 `collect` 实现假设）。自定义迭代器只有在确实保证"返回 None 后永不复活"时才应实现该 trait。

---

### 10.4 边界测试：有状态闭包破坏代数律（逻辑错误）

```rust
fn main() {
    let v = vec![1, 2, 3];
    let mut counter = 0;

    // 有状态闭包：每次调用依赖外部 counter
    let mapped: Vec<i32> = v.iter()
        .map(|x| { counter += 1; x + counter })
        .collect();

    // 若编译器按 map 融合优化，执行顺序可能改变，结果将不同
    // 当前 Rust 1.97 不会对此做跨闭包融合，但语义上已不合法
    assert_eq!(mapped, vec![2, 4, 6]);

    // 不应假设 map(f).map(g) 可与 map(g∘f) 互换
}
```

> **修正**: 迭代器适配器代数律的成立前提是**闭包为纯函数**。有状态闭包使融合、重排等优化不再语义保持。应将状态提升到迭代器结构体中（如 `struct StatefulIter`），使状态变化显式、可审计。

---

### 10.5 边界测试：`size_hint` 与 `next` 矛盾的编译期捕捉

`size_hint` 的下界必须小于等于实际剩余元素数，上界（若存在）必须大于等于实际剩余元素数。下面用 `const` 断言形式化这一契约：一个迭代器声称下界为 `5`、上界为 `Some(10)`，但实际只能产生 `3` 个元素，构成契约违反。

```rust,compile_fail
// Iterator 契约：lower <= actual_remaining <= upper.unwrap_or(actual)
const fn check_size_hint(lower: usize, upper: Option<usize>, actual: usize) {
    assert!(lower <= actual, "size_hint lower bound exceeds actual remaining");
    if let Some(u) = upper {
        assert!(actual <= u, "size_hint upper bound below actual remaining");
    }
}

// 错误：size_hint 返回 (5, Some(10))，但 next 实际只能产生 3 个元素
const _: () = check_size_hint(5, Some(10), 3);

fn main() {}
```

> **修正**: 自定义迭代器的 `size_hint` 必须与 `next` 行为保持一致。实现 `ExactSizeIterator` 时，`len()` 应精确等于还能调用 `next` 的次数。上述矛盾不会触发编译错误（Rust 不静态检查），但会导致 `collect` 预分配不足或截断数据；这里用 `const` 断言将其显式映射为编译期错误。
> (Source: [Rust API Guidelines — Iterators](https://rust-lang.github.io/api-guidelines/interoperability.html#c-iter))

---

### 10.6 边界测试：违反 `FusedIterator` 承诺的编译期拒绝

`FusedIterator` 是一个标记 trait，承诺迭代器首次返回 `None` 后将永远返回 `None`。下面用 `const` 断言形式化该承诺：若一个迭代器在返回 `None` 后仍可能返回 `Some`，则它不应实现 `FusedIterator`。

```rust,compile_fail
// FusedIterator 契约：返回 None 后不得再次返回 Some
const fn check_fused(returns_some_after_none: bool) {
    assert!(
        !returns_some_after_none,
        "FusedIterator must keep returning None after first None"
    );
}

// 错误：该迭代器返回 None 后会重新扫描并再次返回 Some
const _: () = check_fused(true);

fn main() {}
```

> **修正**: 只有确实保证"耗尽后永不复活"的迭代器才应实现 `FusedIterator`。若需要该保证但实现无法提供，可使用 `.fuse()` 适配器或要求调用者显式处理。违反 `FusedIterator` 不会导致 UB，但会破坏依赖该承诺的调用方逻辑。
> (Source: [std::iter::FusedIterator](https://doc.rust-lang.org/std/iter/trait.FusedIterator.html))

---

## 嵌入式测验（Embedded Quiz）

本组测验围绕迭代器状态机、size_hint 下界、适配器代数律、`FusedIterator` 义务、自定义迭代器的前置/后置条件等方面设计，按 Bloom 认知层级从记忆/理解递进到应用/分析。每题给出一段最小化代码或一条论断，判定目标是「能否通过 rustc 1.97（edition 2024）的类型检查与借用（Borrowing）检查」或「运行时行为是否符合预期」。

### 测验 1：迭代器状态机（理解层）

`Iterator::next` 在形式化上最贴近以下哪种描述？

- A. 一个纯函数，输入迭代器引用，返回下一个元素
- B. 一个状态转移函数，可能改变迭代器内部状态并返回 `Option<Item>`
- C. 一个一次性消耗整个序列的函数

<details>
<summary>✅ 答案</summary>

**B. 一个状态转移函数，可能改变迭代器内部状态并返回 `Option<Item>`**。

`next(&mut self)` 接收可变引用，允许修改内部状态（如索引、指针）。它不是纯函数，因为相同输入可能产生不同输出（取决于当前状态）。返回 `Option<Item>` 表示"还有元素"或"已耗尽"。
</details>

---

### 测验 2：`size_hint` 下界（应用层）

某迭代器的 `size_hint` 返回 `(5, Some(10))`，以下哪项一定成立？

- A. 它恰好会产生 5 到 10 个元素
- B. 它至少会产生 5 个元素，最多 10 个
- C. 它最多会产生 5 个元素

<details>
<summary>✅ 答案</summary>

**B. 它至少会产生 5 个元素，最多 10 个**。

`size_hint` 返回 `(lower, upper)`：

- `lower` 是剩余元素数的下界（实际 ≥ lower）
- `upper` 若为 `Some(u)`，则实际 ≤ u

因此 `(5, Some(10))` 表示实际剩余元素数在 `[5, 10]` 区间内。
</details>

---

### 测验 3：适配器代数律（分析层）

在闭包均为纯函数的前提下，以下哪项等价关系**不成立**？

- A. `iter.map(f).map(g) == iter.map(|x| g(f(x)))`
- B. `iter.filter(p).filter(q) == iter.filter(|x| p(x) && q(x))`
- C. `iter.take(n).skip(m) == iter.skip(m).take(n)`

<details>
<summary>✅ 答案</summary>

**C. `iter.take(n).skip(m) == iter.skip(m).take(n)`**。

`take` 与 `skip` 是位置敏感的，不交换：

- `take(n).skip(m)`：先取前 n 个，再跳过其中前 m 个，最终得到原序列的 `[m, n)` 区间
- `skip(m).take(n)`：先跳过前 m 个，再取接下来的 n 个，最终得到原序列的 `[m, m+n)` 区间

只有当原序列足够长且区间恰好重合时才可能相同，一般不等价。A 和 B 在纯函数条件下成立。
</details>

---

### 测验 4：`FusedIterator` 义务（应用层）

某类型实现了 `FusedIterator`，但返回 `None` 后下一次 `next` 又返回了 `Some(v)`。这会导致？

- A. 未定义行为（UB）
- B. 编译错误
- C. 逻辑错误，但不一定是 UB

<details>
<summary>✅ 答案</summary>

**C. 逻辑错误，但不一定是 UB**。

`FusedIterator` 是标记 trait，仅作承诺；编译器不检查其行为。违反不会导致内存不安全或编译失败，但会破坏依赖该承诺的调用方逻辑（如 `.fuse()` 优化、某些消费代码假设）。
</details>

---

### 测验 5：自定义迭代器的前置/后置条件（分析层）

自定义迭代器 `Windowed` 要求 `window_size > 0`。最合理的做法是什么？

- A. 在 `next` 中用 `assert!` 检查
- B. 在构造函数 `new` 中返回 `Option<Self>` 或 `Result<Self, _>`
- C. 不检查，依赖调用者阅读文档

<details>
<summary>✅ 答案</summary>

**B. 在构造函数 `new` 中返回 `Option<Self>` 或 `Result<Self, _>`**。

前置条件最好在对象构造时通过类型/返回类型保证，而不是在每次 `next` 运行时检查。选项 B 把"窗口大小必须为正"这一前置条件编码进 API，使非法状态无法表示。选项 A 的运行时断言只在执行到 `next` 时才触发，且无法防止错误构造；选项 C 依赖文档，最不可靠。
</details>

---

## 🧭 思维导图（Mindmap）

```mermaid
mindmap
  root((迭代器正确性语义 Iterator Correctness Semantics))
    核心概念
      迭代器作为状态机
      Iterator 契约不变量
      适配器链代数律
    自定义迭代器义务
      最小实现 next
      size_hint 与 ExactSizeIterator
      DoubleEndedIterator 与 FusedIterator
    形式化规格示例
      Counter 按构造证明
      Windowed 安全证明草图
    反命题与边界
      适配器不可随意重排
      FusedIterator 是纯逻辑承诺
      size_hint 错误是逻辑 bug 非 UB
    常见陷阱
      size_hint 乐观估计
      ExactSizeIterator 不一致
      有状态闭包破坏代数律
```

> **认知功能**: 本 mindmap 从本页「迭代器正确性语义」的章节结构提炼，一级分支对应核心主题，叶子节点为关键子概念，可作为本页的快速导航与复习索引。


## 补充国际权威来源（P1/P2 覆盖）

- [RustBelt project](https://plv.mpi-sws.org/rustbelt/)
- [Oxide: The Essence of Rust](https://arxiv.org/abs/1903.00982)
