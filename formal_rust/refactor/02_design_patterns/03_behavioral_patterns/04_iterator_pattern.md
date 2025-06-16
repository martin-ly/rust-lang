# 迭代器模式形式化理论

## 1. 形式化定义

### 1.1 基本概念

迭代器模式是一种行为型设计模式，它提供一种方法顺序访问一个聚合对象中的各个元素，而又不暴露其内部的表示。

**定义 1.1.1** (迭代器)
设 $A$ 为聚合对象集合，$E$ 为元素集合，迭代器是一个四元组 $(a, i, n, h)$，其中：
- $a \in A$ 是聚合对象
- $i \in \mathbb{N}$ 是当前索引
- $n: A \rightarrow \mathbb{N}$ 是大小函数
- $h: A \times \mathbb{N} \rightarrow E$ 是访问函数

**定义 1.1.2** (迭代操作)
对于迭代器 $it = (a, i, n, h)$，迭代操作定义为：
$$\text{next}(it) = \begin{cases}
\text{Some}(h(a, i)) & \text{if } i < n(a) \\
\text{None} & \text{otherwise}
\end{cases}$$

**定义 1.1.3** (迭代器状态)
迭代器的状态转换定义为：
$$\text{advance}(it) = (a, i + 1, n, h)$$

### 1.2 数学基础

**定理 1.2.1** (迭代终止性)
对于任意迭代器 $it = (a, i, n, h)$，经过有限次迭代后必定终止。

**证明：**
由于 $i \in \mathbb{N}$ 且 $n(a) \in \mathbb{N}$，当 $i \geq n(a)$ 时，`next(it)` 返回 `None`，迭代终止。

**定理 1.2.2** (迭代完整性)
对于聚合对象 $a$ 的所有元素，迭代器能够访问到每个元素恰好一次。

**证明：**
迭代器按顺序访问索引 $0, 1, \ldots, n(a)-1$，每个索引对应一个唯一元素。

## 2. 类型系统分析

### 2.1 Rust 类型映射

```rust
// 迭代器特征
trait Iterator {
    type Item;
    
    fn next(&mut self) -> Option<Self::Item>;
}

// 聚合对象特征
trait IntoIterator {
    type Item;
    type IntoIter: Iterator<Item = Self::Item>;
    
    fn into_iter(self) -> Self::IntoIter;
}

// 具体迭代器实现
struct VecIterator<T> {
    vec: Vec<T>,
    index: usize,
}

impl<T> Iterator for VecIterator<T> {
    type Item = T;
    
    fn next(&mut self) -> Option<Self::Item> {
        if self.index < self.vec.len() {
            let item = self.vec.remove(self.index);
            Some(item)
        } else {
            None
        }
    }
}
```

### 2.2 类型安全证明

**引理 2.2.1** (类型一致性)
对于任意迭代器 $it$，所有 `next()` 调用返回的元素类型必须一致：
$$\forall i, j: \text{type}(\text{next}^i(it)) = \text{type}(\text{next}^j(it))$$

**证明：**
根据 Rust 类型系统，`Iterator` trait 定义了明确的关联类型 `Item`，确保类型一致性。

## 3. 实现策略

### 3.1 基础实现

```rust
// 自定义聚合对象
struct CustomCollection<T> {
    data: Vec<T>,
}

impl<T> CustomCollection<T> {
    fn new() -> Self {
        Self { data: vec![] }
    }
    
    fn add(&mut self, item: T) {
        self.data.push(item);
    }
    
    fn len(&self) -> usize {
        self.data.len()
    }
}

// 为自定义集合实现迭代器
impl<T> IntoIterator for CustomCollection<T> {
    type Item = T;
    type IntoIter = CustomIterator<T>;
    
    fn into_iter(self) -> Self::IntoIter {
        CustomIterator {
            collection: self,
            index: 0,
        }
    }
}

struct CustomIterator<T> {
    collection: CustomCollection<T>,
    index: usize,
}

impl<T> Iterator for CustomIterator<T> {
    type Item = T;
    
    fn next(&mut self) -> Option<Self::Item> {
        if self.index < self.collection.len() {
            let item = self.collection.data.remove(self.index);
            Some(item)
        } else {
            None
        }
    }
}
```

### 3.2 高级迭代器

```rust
// 过滤迭代器
struct FilterIterator<I, P> {
    iter: I,
    predicate: P,
}

impl<I, P> Iterator for FilterIterator<I, P>
where
    I: Iterator,
    P: FnMut(&I::Item) -> bool,
{
    type Item = I::Item;
    
    fn next(&mut self) -> Option<Self::Item> {
        while let Some(item) = self.iter.next() {
            if (self.predicate)(&item) {
                return Some(item);
            }
        }
        None
    }
}

// 映射迭代器
struct MapIterator<I, F> {
    iter: I,
    mapper: F,
}

impl<I, F, B> Iterator for MapIterator<I, F>
where
    I: Iterator,
    F: FnMut(I::Item) -> B,
{
    type Item = B;
    
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(&mut self.mapper)
    }
}
```

## 4. 正确性证明

### 4.1 迭代正确性

**定理 4.1.1** (迭代正确性)
对于聚合对象 $a$ 和其迭代器 $it$，迭代过程能够按顺序访问所有元素。

**证明：**
根据迭代器的定义，`next()` 函数按索引顺序返回元素，确保迭代的正确性。

### 4.2 状态一致性

**定理 4.2.1** (状态一致性)
迭代器的状态转换是确定性的，每次调用 `next()` 都会产生确定性的结果。

**证明：**
迭代器的状态由当前索引唯一确定，因此状态转换是确定性的。

## 5. 性能分析

### 5.1 时间复杂度

**定理 5.1.1** (迭代时间复杂度)
对于包含 $n$ 个元素的聚合对象，完整迭代的时间复杂度为 $O(n)$。

**证明：**
每个元素需要被访问一次，因此时间复杂度为 $O(n)$。

### 5.2 空间复杂度

**定理 5.2.1** (空间复杂度)
迭代器的空间复杂度为 $O(1)$，不依赖于聚合对象的大小。

**证明：**
迭代器只需要存储当前索引和聚合对象的引用，因此空间复杂度为常数。

## 6. 应用场景

### 6.1 集合遍历
- 数组遍历
- 链表遍历
- 树结构遍历

### 6.2 流式处理
- 文件读取
- 网络数据流
- 实时数据处理

### 6.3 算法实现
- 排序算法
- 搜索算法
- 图遍历算法

## 7. 与其他模式的关系

### 7.1 与访问者模式
- 迭代器模式关注元素访问
- 访问者模式关注操作分离

### 7.2 与组合模式
- 迭代器模式关注顺序访问
- 组合模式关注结构组织

## 8. 高级特性

### 8.1 惰性求值

```rust
// 惰性迭代器
struct LazyIterator<F, T> {
    generator: F,
    phantom: std::marker::PhantomData<T>,
}

impl<F, T> Iterator for LazyIterator<F, T>
where
    F: FnMut() -> Option<T>,
{
    type Item = T;
    
    fn next(&mut self) -> Option<Self::Item> {
        (self.generator)()
    }
}
```

### 8.2 并行迭代

```rust
// 并行迭代器特征
trait ParallelIterator {
    type Item;
    
    fn drive_unindexed<C>(self, consumer: C) -> C::Result
    where
        C: UnindexedConsumer<Self::Item>;
}
```

## 9. 总结

迭代器模式通过数学化的定义和严格的类型系统分析，提供了一个可证明正确的元素访问框架。其核心优势在于：

1. **封装性**：隐藏聚合对象的内部结构
2. **统一性**：提供统一的访问接口
3. **灵活性**：支持多种遍历策略
4. **可组合性**：支持迭代器的组合和转换

通过形式化方法，我们确保了迭代器模式的正确性和可靠性，为实际应用提供了坚实的理论基础。 