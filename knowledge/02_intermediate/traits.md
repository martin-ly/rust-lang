# Trait - 定义共享行为

> **Rust 的类型接口系统**
> **预计时间**: 8 小时
> **权威来源**: [Rust Book - Traits](https://doc.rust-lang.org/book/ch10-02-traits.html)

## 🎯 学习目标

完成本章后，你将能够：

- [ ] 定义和实现 Trait
- [ ] 使用 Trait Bound 约束泛型
- [ ] 理解 Trait 对象
- [ ] 使用关联类型
- [ ] 实现常用标准 Trait

## 📋 先决条件

- 理解泛型基础
- 了解结构体和 impl

## 🧠 核心概念

### 1. 什么是 Trait？

Trait 定义了类型必须实现的方法集合，类似于其他语言的接口：

```rust
// 定义 Trait
pub trait Summary {
    fn summarize(&self) -> String;
}

// 为类型实现 Trait
pub struct Article {
    pub headline: String,
    pub content: String,
}

impl Summary for Article {
    fn summarize(&self) -> String {
        format!("{}: {}", self.headline, &self.content[..50])
    }
}
```

### 2. 默认实现

Trait 可以提供默认实现：

```rust
pub trait Summary {
    fn summarize(&self) -> String {
        String::from("(Read more...)")
    }

    // 必须实现的方法
    fn summarize_author(&self) -> String;
}

impl Summary for Article {
    // 使用默认 summarize
    fn summarize_author(&self) -> String {
        format!("@{}", self.author)
    }
}
```

### 3. Trait 作为参数

#### impl Trait 语法

```rust
// 接受任何实现了 Summary 的类型
pub fn notify(item: &impl Summary) {
    println!("Breaking news! {}", item.summarize());
}
```

#### Trait Bound 语法

```rust
// 多个 Trait
pub fn notify(item: &(impl Summary + Display)) { }

// 泛型形式（等价）
pub fn notify<T: Summary + Display>(item: &T) { }
```

#### where 子句

```rust
fn some_function<T, U>(t: &T, u: &U) -> i32
where
    T: Display + Clone,
    U: Clone + Debug,
{ }
```

### 4. 返回 impl Trait

```rust
fn returns_summarizable() -> impl Summary {
    Article {
        headline: String::from("Rust 1.94 Released"),
        content: String::from("..."),
    }
}
```

### 5. 常用标准 Trait

#### Debug 和 Display

```rust
use std::fmt;

struct Point {
    x: i32,
    y: i32,
}

// 用于 {:?} 格式化
impl fmt::Debug for Point {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("Point")
            .field("x", &self.x)
            .field("y", &self.y)
            .finish()
    }
}

// 用于 {} 格式化
impl fmt::Display for Point {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({}, {})", self.x, self.y)
    }
}
```

#### Clone 和 Copy

```rust
#[derive(Clone)]  // 自动生成 Clone
struct MyStruct { ... }

#[derive(Copy, Clone)]  // Copy 需要 Clone
struct MyPrimitive(i32);
```

#### PartialEq 和 Eq

```rust
#[derive(PartialEq, Eq)]
struct Point {
    x: i32,
    y: i32,
}

// 手动实现
impl PartialEq for Point {
    fn eq(&self, other: &Self) -> bool {
        self.x == other.x && self.y == other.y
    }
}
```

### 6. 关联类型

```rust
pub trait Iterator {
    type Item;  // 关联类型

    fn next(&mut self) -> Option<Self::Item>;
}

// 实现
struct Counter {
    count: u32,
}

impl Iterator for Counter {
    type Item = u32;

    fn next(&mut self) -> Option<Self::Item> {
        self.count += 1;
        if self.count < 6 {
            Some(self.count)
        } else {
            None
        }
    }
}
```

### 7. Trait 对象

```rust
// 静态分发（单态化）
fn static_dispatch<T: Summary>(item: &T) { }

// 动态分发（Trait 对象）
fn dynamic_dispatch(item: &dyn Summary) { }

// 使用
let article = Article { ... };
let tweet = Tweet { ... };

let items: Vec<&dyn Summary> = vec![&article, &tweet];
```

## 💻 综合示例

### 实现自定义集合 Trait

```rust
// 定义集合 Trait
pub trait Collection {
    type Item;

    fn len(&self) -> usize;
    fn is_empty(&self) -> bool;
    fn clear(&mut self);
}

// 为 Vec 实现
impl<T> Collection for Vec<T> {
    type Item = T;

    fn len(&self) -> usize { self.len() }
    fn is_empty(&self) -> bool { self.is_empty() }
    fn clear(&mut self) { self.clear() }
}

// 为 HashSet 实现
use std::collections::HashSet;
use std::hash::Hash;

impl<T: Eq + Hash> Collection for HashSet<T> {
    type Item = T;

    fn len(&self) -> usize { self.len() }
    fn is_empty(&self) -> bool { self.is_empty() }
    fn clear(&mut self) { self.clear() }
}

// 泛型函数使用 Trait
fn print_collection_info<C: Collection>(c: &C) {
    println!("Length: {}", c.len());
    println!("Empty: {}", c.is_empty());
}
```

## ⚠️ 常见陷阱

| 错误 | 原因 | 修复 |
|------|------|------|
| orphan rules | 不能为外部类型实现外部 Trait | 使用 newtype 模式 |
| 冲突实现 | 重叠的实现 | 使用更具体的约束 |
| 递归限制 | 复杂的 Trait Bound | 简化或使用 where |

## 🎮 练习

### 练习 1: 实现自定义 Trait

创建一个 `Drawable` Trait，并为 `Circle` 和 `Rectangle` 实现它。

### 练习 2: 泛型函数

编写一个函数，接受任何实现了 `PartialOrd` 的类型切片，返回最大值。

<details>
<summary>参考答案</summary>

```rust
fn max<T: PartialOrd>(list: &[T]) -> Option<&T> {
    list.iter().max()
}
```

</details>

## ✅ 自我检测

1. Trait 和接口有什么区别？
2. 关联类型的作用是什么？
3. 什么时候使用 Trait 对象而不是泛型？

## 📖 延伸阅读

- [Rust Book - Traits](https://doc.rust-lang.org/book/ch10-02-traits.html)
- [Traits 深入](https://doc.rust-lang.org/reference/items/traits.html)

---

**文档版本**: 1.0
**对应 Rust 版本**: 1.94.0
**最后更新**: 2026-03-19
