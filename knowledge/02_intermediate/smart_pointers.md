# 智能指针

> **超出普通引用的内存管理**
> **预计时间**: 5 小时
**权威来源**: [Rust Book - Smart Pointers](https://doc.rust-lang.org/book/ch15-00-smart-pointers.html)

## 🎯 学习目标

完成本章后，你将能够：

- [ ] 使用 `Box<T>` 在堆上存储数据
- [ ] 使用 `Rc<T>` 共享所有权
- [ ] 使用 `Arc<T>` 线程安全共享
- [ ] 理解 `Deref` 和 `Drop` trait

## 📋 先决条件

- 理解所有权和借用
- 了解结构体和方法

## 🧠 核心概念

### 1. Box<T> - 堆分配

`Box<T>` 在堆上分配数据，栈上只存储指针。

#### 基础使用

```rust
fn main() {
    // b 在栈上，数据 5 在堆上
    let b = Box::new(5);
    println!("b = {}", b);  // 自动解引用
}
```

#### 递归类型

```rust
// 编译错误：无法确定大小
enum List {
    Cons(i32, List),  // 递归定义
    Nil,
}

// 使用 Box 修复
enum List {
    Cons(i32, Box<List>),  // Box 有确定大小
    Nil,
}

use List::{Cons, Nil};

fn main() {
    let list = Cons(1, Box::new(Cons(2, Box::new(Cons(3, Box::new(Nil))))));
}
```

### 2. Rc<T> - 引用计数

`Rc<T>` 允许多个所有者共享堆数据（单线程）。

```rust
use std::rc::Rc;

fn main() {
    let data = Rc::new(String::from("shared data"));

    // 增加引用计数
    let data2 = Rc::clone(&data);
    let data3 = Rc::clone(&data);

    println!("Reference count: {}", Rc::strong_count(&data));  // 3

    // 自动减少计数
    drop(data2);
    println!("Reference count: {}", Rc::strong_count(&data));  // 2
}  // 最后释放内存
```

#### 可视化

```
    data
      │
      ▼
   ┌─────┐
   │  3  │ ← 引用计数
   ├─────┤
   │ ptr │ ───────► "shared data"
   └─────┘
      ▲
      │
   data2, data3 (都指向同一个 Rc)
```

### 3. Arc<T> - 原子引用计数

`Arc<T>` 是线程安全的 `Rc<T>`。

```rust
use std::sync::Arc;
use std::thread;

fn main() {
    let data = Arc::new(String::from("thread-safe data"));

    let handles: Vec<_> = (0..10)
        .map(|_| {
            let data = Arc::clone(&data);
            thread::spawn(move || {
                println!("{}", data);
            })
        })
        .collect();

    for h in handles {
        h.join().unwrap();
    }
}
```

#### Rc vs Arc 对比

| 特性 | Rc<T> | Arc<T> |
|------|-------|--------|
| 线程安全 | ❌ 否 | ✅ 是 |
| 性能 | 更高 | 稍低（原子操作） |
| 使用场景 | 单线程 | 多线程 |
| Send/Sync | 非 Send | 都实现 |

### 4. Deref Trait

`Deref` 允许智能指针像引用一样使用。

```rust
use std::ops::Deref;

struct MyBox<T>(T);

impl<T> MyBox<T> {
    fn new(x: T) -> MyBox<T> {
        MyBox(x)
    }
}

impl<T> Deref for MyBox<T> {
    type Target = T;

    fn deref(&self) -> &T {
        &self.0
    }
}

fn main() {
    let x = MyBox::new(5);

    // 自动解引用
    assert_eq!(5, *x);  // 实际是 *(x.deref())

    // 函数参数自动转换
    fn hello(name: &str) { println!("Hello, {}!", name); }
    let m = MyBox::new(String::from("Rust"));
    hello(&m);  // 自动解引用为 &str
}
```

### 5. Drop Trait

`Drop` 在值离开作用域时执行清理。

```rust
struct CustomSmartPointer {
    data: String,
}

impl Drop for CustomSmartPointer {
    fn drop(&mut self) {
        println!("Dropping CustomSmartPointer with data `{}`!", self.data);
    }
}

fn main() {
    let c = CustomSmartPointer {
        data: String::from("my stuff"),
    };
    let d = CustomSmartPointer {
        data: String::from("other stuff"),
    };
    println!("CustomSmartPointers created.");
}  // 自动调用 drop
```

## 💻 综合示例

### 共享状态树

```rust
use std::rc::Rc;

#[derive(Debug)]
struct Node {
    value: i32,
    children: Vec<Rc<Node>>,
}

impl Node {
    fn new(value: i32) -> Rc<Node> {
        Rc::new(Node {
            value,
            children: Vec::new(),
        })
    }

    fn add_child(&mut self, child: Rc<Node>) {
        self.children.push(child);
    }
}

fn main() {
    // 创建共享子树
    let leaf = Node::new(3);

    let mut branch = Node::new(5);
    branch.add_child(Rc::clone(&leaf));

    let mut root = Node::new(10);
    root.add_child(Rc::clone(&leaf));  // leaf 被共享

    println!("{:#?}", root);
}
```

## ⚠️ 常见陷阱

| 错误 | 原因 | 修复 |
|------|------|------|
| Rc 循环引用 | 内存泄漏 | 使用 Weak<T> |
| Arc 非 Send 类型 | 类型不实现 Send | 确保 T: Send + Sync |
| 过度使用 Rc | 性能下降 | 考虑借用 |

## 🎮 练习

### 练习 1: 实现自定义智能指针

实现一个简单的引用计数智能指针。

### 练习 2: 共享图结构

使用 `Rc` 和 `RefCell` 创建可以修改的共享图。

<details>
<summary>参考答案</summary>

```rust
use std::rc::Rc;
use std::cell::RefCell;

#[derive(Debug)]
struct GraphNode {
    value: i32,
    neighbors: RefCell<Vec<Rc<GraphNode>>>,
}

fn main() {
    let node1 = Rc::new(GraphNode {
        value: 1,
        neighbors: RefCell::new(vec![]),
    });

    let node2 = Rc::new(GraphNode {
        value: 2,
        neighbors: RefCell::new(vec![Rc::clone(&node1)]),
    });

    // 添加反向连接
    node1.neighbors.borrow_mut().push(Rc::clone(&node2));

    println!("{:?}", node1);
}
```

</details>

## ✅ 自我检测

1. `Box`, `Rc`, `Arc` 的主要区别是什么？
2. `Deref` trait 的作用是什么？
3. 如何避免 `Rc` 的循环引用问题？

## 📖 延伸阅读

- [Rust Book - Smart Pointers](https://doc.rust-lang.org/book/ch15-00-smart-pointers.html)
- [std::boxed](https://doc.rust-lang.org/std/boxed/)
- [std::rc](https://doc.rust-lang.org/std/rc/)

---

**文档版本**: 1.0
**对应 Rust 版本**: 1.94.0
**最后更新**: 2026-03-19
