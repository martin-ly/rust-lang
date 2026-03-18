# 泛型 (Generics)

> **编写可复用、类型安全的代码**
> **预计时间**: 5 小时
> **权威来源**: [Rust Book - Generic Types](https://doc.rust-lang.org/book/ch10-00-generics.html)

## 🎯 学习目标

完成本章后，你将能够：

- [ ] 定义泛型函数和结构体
- [ ] 使用 Trait Bound 约束类型
- [ ] 理解单态化编译
- [ ] 实现泛型算法

## 📋 先决条件

- 理解基本类型系统
- 了解函数和结构体

## 🧠 核心概念

### 1. 为什么需要泛型？

没有泛型，需要为每种类型写重复代码：

```rust
// 没有泛型 - 重复代码
fn largest_i32(list: &[i32]) -> &i32 { /* ... */ }
fn largest_f64(list: &[f64]) -> &f64 { /* ... */ }
fn largest_char(list: &[char]) -> &char { /* ... */ }

// 使用泛型 - 一份代码
fn largest<T>(list: &[T]) -> &T { /* ... */ }
```

### 2. 泛型函数

#### 基础语法

```rust
// 在函数名后声明类型参数
fn identity<T>(value: T) -> T {
    value
}

// 使用
let x = identity(5);        // T = i32
let y = identity("hello");  // T = &str
```

#### 多个类型参数

```rust
fn pair<T, U>(first: T, second: U) -> (T, U) {
    (first, second)
}

let p = pair(1, "one");  // T=i32, U=&str
```

### 3. 泛型结构体

#### 单类型参数

```rust
struct Point<T> {
    x: T,
    y: T,
}

let int_point = Point { x: 5, y: 10 };
let float_point = Point { x: 1.0, y: 4.0 };
```

#### 多类型参数

```rust
struct Point2D<T, U> {
    x: T,
    y: U,
}

let mixed = Point2D { x: 5, y: 4.0 };  // T=i32, U=f64
```

### 4. Trait Bounds

#### 为什么需要约束？

```rust
// 错误：T 可能没有实现 Display
fn print<T>(value: T) {
    println!("{}", value);  // ❌ 编译错误
}

// 正确：添加 Trait Bound
use std::fmt::Display;

fn print<T: Display>(value: T) {
    println!("{}", value);  // ✅ T 必须实现 Display
}
```

#### 常用 Trait Bounds

| Trait | 功能 | 示例 |
|-------|------|------|
| `Display` | 格式化输出 | `println!("{}", x)` |
| `Debug` | 调试输出 | `println!("{:?}", x)` |
| `Clone` | 克隆 | `x.clone()` |
| `Copy` | 隐式复制 | 基本类型 |
| `PartialEq` | 比较相等 | `x == y` |
| `PartialOrd` | 比较大小 | `x < y` |

#### 多个 Trait Bounds

```rust
// 方式 1：使用 +
fn process<T: Display + Clone>(value: T) { }

// 方式 2：使用 where 子句（推荐用于复杂情况）
fn process<T>(value: T)
where
    T: Display + Clone + PartialEq,
{ }
```

### 5. 实际应用

#### 泛型栈实现

```rust
struct Stack<T> {
    items: Vec<T>,
}

impl<T> Stack<T> {
    fn new() -> Self {
        Stack { items: Vec::new() }
    }

    fn push(&mut self, item: T) {
        self.items.push(item);
    }

    fn pop(&mut self) -> Option<T> {
        self.items.pop()
    }

    fn peek(&self) -> Option<&T> {
        self.items.last()
    }

    fn is_empty(&self) -> bool {
        self.items.is_empty()
    }
}

// 使用
let mut int_stack = Stack::new();
int_stack.push(1);
int_stack.push(2);

let mut str_stack = Stack::new();
str_stack.push("hello");
```

#### 泛型算法

```rust
fn find_max<T: PartialOrd>(list: &[T]) -> Option<&T> {
    list.iter().max()
}

fn find_index<T: PartialEq>(list: &[T], target: &T) -> Option<usize> {
    list.iter().position(|x| x == target)
}
```

### 6. 单态化 (Monomorphization)

Rust 在编译时为每种使用的类型生成特定代码：

```rust
// 源代码
fn identity<T>(x: T) -> T { x }

let a = identity(5i32);
let b = identity(3.14f64);

// 编译后（概念上）
fn identity_i32(x: i32) -> i32 { x }
fn identity_f64(x: f64) -> f64 { x }
```

**优点**: 零运行时开销
**缺点**: 编译时间增加，二进制体积增大

## 💻 综合示例

### 泛型缓存

```rust
use std::collections::HashMap;
use std::hash::Hash;

struct Cache<K, V> {
    store: HashMap<K, V>,
    max_size: usize,
}

impl<K, V> Cache<K, V>
where
    K: Eq + Hash + Clone,
    V: Clone,
{
    fn new(max_size: usize) -> Self {
        Cache {
            store: HashMap::new(),
            max_size,
        }
    }

    fn get(&mut self, key: &K) -> Option<V> {
        self.store.get(key).cloned()
    }

    fn put(&mut self, key: K, value: V) {
        if self.store.len() >= self.max_size {
            // 简单的 LRU：移除任意一个
            if let Some(first_key) = self.store.keys().next().cloned() {
                self.store.remove(&first_key);
            }
        }
        self.store.insert(key, value);
    }
}

fn main() {
    let mut cache: Cache<String, Vec<i32>> = Cache::new(100);
    cache.put("data".to_string(), vec![1, 2, 3]);

    if let Some(data) = cache.get(&"data".to_string()) {
        println!("{:?}", data);
    }
}
```

## ⚠️ 常见陷阱

| 错误 | 原因 | 修复 |
|------|------|------|
| `cannot compile` | 缺少 Trait Bound | 添加 `T: Trait` |
| 类型推断失败 | 编译器无法确定 T | 显式指定：`func::<Type>()` |
| 代码膨胀 | 单态化生成太多代码 | 考虑使用 trait objects |

## 🎮 练习

### 练习 1: 泛型队列

实现一个泛型 Queue，支持 enqueue 和 dequeue。

### 练习 2: 通用比较

编写一个泛型函数，找出两个值中的较大者。

<details>
<summary>参考答案</summary>

```rust
fn max<T: PartialOrd>(a: T, b: T) -> T {
    if a > b { a } else { b }
}
```

</details>

## ✅ 自我检测

1. 什么是单态化？有什么优缺点？
2. Trait Bound 的作用是什么？
3. 什么时候应该使用 where 子句？

## 📖 延伸阅读

- [Rust Book - Generics](https://doc.rust-lang.org/book/ch10-01-syntax.html)
- [Rust By Example - Generics](https://doc.rust-lang.org/rust-by-example/generics.html)

---

**文档版本**: 1.0
**对应 Rust 版本**: 1.94.0
**最后更新**: 2026-03-19
