# C02: 类型系统

> **类型安全基石** | **核心概念** | ⭐⭐⭐⭐⭐ 重要性

## 模块职责

本 crate 深入 Rust 强大的类型系统，涵盖：

- **基础类型**: 标量类型、复合类型、自定义类型
- **类型推导**: 编译器如何推断类型
- **泛型基础**: 类型参数、约束、实现
- **Trait 系统**: 定义共享行为、泛型编程
- **高级类型**: 关联类型、存在类型、Never 类型

## 目录结构

```
src/
├── lib.rs              # 模块入口
├── bin/
│   └── main.rs         # CLI 可执行文件 (ts)
├── basic_types/        # 基础类型
├── collections/        # 集合类型
├── generics/           # 泛型基础
├── traits/             # Trait 系统
└── advanced/           # 高级类型特性
```

## 主要类型和 Trait

### 核心 Trait

| Trait | 描述 | 常用方法 |
|-------|------|----------|
| `Sized` | 编译时已知大小 | 自动实现 |
| `Clone` | 显式复制 | `clone()` |
| `Copy` | 隐式复制 | 标记 trait |
| `Default` | 默认值 | `default()` |
| `From` / `Into` | 类型转换 | `from()`, `into()` |
| `AsRef` / `AsMut` | 引用转换 | `as_ref()` |
| `Borrow` | 借用语义 | `borrow()` |
| `ToOwned` | 创建拥有值 | `to_owned()` |

### 集合类型

| 类型 | 描述 | 复杂度 |
|------|------|--------|
| `Vec<T>` | 动态数组 | O(1) push |
| `HashMap<K,V>` | 哈希表 | O(1) avg |
| `BTreeMap<K,V>` | 有序映射 | O(log n) |
| `HashSet<T>` | 哈希集合 | O(1) avg |
| `VecDeque<T>` | 双端队列 | O(1) 两端 |
| `LinkedList<T>` | 链表 | O(1) 插入 |
| `BinaryHeap<T>` | 优先队列 | O(log n) |

## 使用示例

### 泛型函数

```rust
fn largest<T: PartialOrd>(list: &[T]) -> &T {
    let mut largest = &list[0];
    for item in list {
        if item > largest {
            largest = item;
        }
    }
    largest
}

fn main() {
    let numbers = vec![34, 50, 25, 100, 65];
    println!("最大的数是 {}", largest(&numbers));
}
```

### Trait 定义与实现

```rust
pub trait Summary {
    fn summarize(&self) -> String;
    
    // 默认实现
    fn summarize_author(&self) -> String {
        String::from("(阅读更多...)")
    }
}

pub struct NewsArticle {
    pub headline: String,
    pub content: String,
}

impl Summary for NewsArticle {
    fn summarize(&self) -> String {
        format!("{}: {}", self.headline, self.content)
    }
}
```

### 关联类型

```rust
trait Iterator {
    type Item;  // 关联类型
    
    fn next(&mut self) -> Option<Self::Item>;
}

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

## 依赖关系

### 上游依赖
- `c01_ownership_borrow_scope`: 理解所有权后学习类型
- `common`: 共享工具

### 下游依赖
- `c04_generic`: 深入泛型编程
- `c08_algorithms`: 算法中的类型应用

### 外部依赖
```toml
[dependencies]
c01_ownership_borrow_scope = { path = "../c01_ownership_borrow_scope" }
serde = { workspace = true }
tokio = { workspace = true }
futures = { workspace = true }
```

## 运行方式

```bash
# 运行测试
cargo test -p c02_type_system

# 运行 CLI
cargo run -p c02_type_system --bin ts

# 运行示例
cargo run -p c02_type_system --example type_system_example
```

## 学习路径建议

1. 掌握 `src/basic_types/` 中的基础类型
2. 学习 `src/traits/` 理解 Rust 的多态机制
3. 研究 `src/generics/` 的类型参数系统
4. 完成 `exercises/` 中的类型挑战

## 相关文档

- [Rust Book - Types](https://doc.rust-lang.org/book/ch03-02-data-types.html)
- [Rust Reference - Types](https://doc.rust-lang.org/reference/types.html)
