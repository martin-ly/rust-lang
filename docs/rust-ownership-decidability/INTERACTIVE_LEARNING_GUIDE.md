# Rust 所有权系统 - 交互式学习指南

> 本指南提供交互式的问题驱动学习体验
> **特点**: 问题 → 尝试 → 反馈 → 深入

---

## 🎯 如何使用本指南

1. **阅读问题**: 每个部分从一个实际问题开始
2. **尝试解决**: 先自己思考解决方案
3. **查看提示**: 如果卡住，查看提示（折叠区域）
4. **验证答案**: 对照参考答案
5. **深入理解**: 阅读详细解释

---

## 模块 1: 所有权基础

### 问题 1: 为什么这段代码不能编译？

```rust
fn main() {
    let s1 = String::from("hello");
    let s2 = s1;
    println!("{}", s1);  // 错误！
}
```

<details>
<summary>💡 思考提示</summary>

String 在 Rust 中是如何存储的？赋值操作会发生什么？

</details>

<details>
<summary>✅ 答案</summary>

**错误原因**: `String` 被移动了，`s1` 不再有效。

**修复方案**:

```rust
fn main() {
    let s1 = String::from("hello");
    let s2 = s1.clone();  // 显式克隆
    println!("{}", s1);   // 现在可以工作
}
```

**深入理解**:

- String 由三部分组成：指向堆内存的指针、长度、容量
- 赋值时，Rust "移动"所有权，避免双重释放
- `.clone()` 进行深拷贝，保留原始值

</details>

---

### 问题 2: 修复所有权错误

```rust
fn main() {
    let data = vec![1, 2, 3, 4, 5];
    let first = get_first(data);
    let sum = data.iter().sum::<i32>();  // 错误！
    println!("First: {}, Sum: {}", first, sum);
}

fn get_first(v: Vec<i32>) -> i32 {
    v[0]
}
```

<details>
<summary>💡 思考提示</summary>

`get_first` 的参数是如何传递的？如何让函数使用值而不获取所有权？

</details>

<details>
<summary>✅ 答案</summary>

**错误原因**: `get_first` 获取了 `data` 的所有权，之后 `data` 不可用。

**修复方案**:

```rust
fn main() {
    let data = vec![1, 2, 3, 4, 5];
    let first = get_first(&data);  // 借用而不是移动
    let sum = data.iter().sum::<i32>();
    println!("First: {}, Sum: {}", first, sum);
}

fn get_first(v: &[i32]) -> i32 {  // 接受切片引用
    v[0]
}
```

**深入理解**:

- `&T` 创建借用，不转移所有权
- `&[i32]` 是切片，可以接受 `Vec` 或数组的引用
- 借用结束后，原值仍然有效

</details>

---

## 模块 2: 借用规则

### 问题 3: 为什么不能同时可变和不可变借用？

```rust
fn main() {
    let mut data = vec![1, 2, 3];

    let first = &data[0];  // 不可变借用
    data.push(4);          // 尝试可变借用

    println!("First: {}", first);  // 使用不可变借用
}
```

<details>
<summary>💡 思考提示</summary>

`push` 操作可能会发生什么？这对 `first` 有什么影响？

</details>

<details>
<summary>✅ 答案</summary>

**错误原因**: `push` 可能导致重新分配内存，使 `first` 成为悬垂指针。

**修复方案**:

```rust
fn main() {
    let mut data = vec![1, 2, 3];

    {
        let first = &data[0];
        println!("First: {}", first);  // 在这里使用
    }  // 不可变借用在这里结束

    data.push(4);  // 现在可以可变借用
}
```

**深入理解**:

- Rust 的借用检查器防止数据竞争
- `push` 可能导致重新分配，使现有引用失效
- 借用作用域可以嵌套， Rust 会找到不重叠的区域

</details>

---

### 问题 4: 多重可变借用

如何实现以下功能：同时修改向量的两个不同元素？

```rust
fn main() {
    let mut data = vec![1, 2, 3, 4, 5];

    // 目标：交换 data[0] 和 data[4]
    // let first = &mut data[0];
    // let last = &mut data[4];  // 错误！不能同时有两个可变借用

    // 如何实现？
}
```

<details>
<summary>💡 思考提示</summary>

Rust 标准库提供了什么方法可以在安全的情况下同时访问多个元素？

</details>

<details>
<summary>✅ 答案</summary>

**解决方案**:

```rust
fn main() {
    let mut data = vec![1, 2, 3, 4, 5];

    // 方法 1: 使用 split_first_mut
    if let Some((first, rest)) = data.split_first_mut() {
        if let Some(last) = rest.last_mut() {
            std::mem::swap(first, last);
        }
    }

    // 方法 2: 使用索引和 unsafe（不推荐）
    // unsafe {
    //     let ptr = data.as_mut_ptr();
    //     std::ptr::swap(ptr, ptr.add(4));
    // }

    println!("{:?}", data);  // [5, 2, 3, 4, 1]
}
```

**深入理解**:

- `split_first_mut()` 将 Vec 分成第一个元素和其余部分的引用
- Rust 的借用检查器可以证明这两个引用不重叠
- `std::mem::swap` 安全地交换两个值

</details>

---

## 模块 3: 生命周期

### 问题 5: 生命周期省略规则

为什么这段代码可以编译？

```rust
fn first_word(s: &str) -> &str {
    &s[0..1]
}
```

但这段代码不能？

```rust
fn longest(x: &str, y: &str) -> &str {
    if x.len() > y.len() {
        x
    } else {
        y
    }
}
```

<details>
<summary>💡 思考提示</summary>

编译器如何知道 `first_word` 返回的引用和输入的关系？`longest` 有什么特殊之处？

</details>

<details>
<summary>✅ 答案</summary>

**解释**:

`first_word` 遵循**生命周期省略规则**:

1. 每个输入引用参数都有自己的生命周期
2. 如果只有一个输入生命周期，它赋予所有输出生命周期
3. 如果有多个输入生命周期，但一个是 `&self` 或 `&mut self`，它的生命周期赋予输出

`longest` 有两个输入生命周期，编译器无法确定返回哪个：

```rust
// 需要显式生命周期注解
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() {
        x
    } else {
        y
    }
}
```

**深入理解**:

- `'a` 表示 x 和 y 的生命周期至少一样长
- 返回值的生命周期与两者中较短的一致
- 生命周期注解不改变生命周期，只是声明关系

</details>

---

### 问题 6: 结构体生命周期

修复以下结构体的生命周期错误：

```rust
struct Parser {
    text: &str,  // 错误！需要生命周期
}

impl Parser {
    fn new(text: &str) -> Parser {
        Parser { text }
    }

    fn parse(&self) -> &str {
        &self.text[0..5]
    }
}
```

<details>
<summary>✅ 答案</summary>

```rust
struct Parser<'a> {
    text: &'a str,  // 显式生命周期
}

impl<'a> Parser<'a> {
    fn new(text: &'a str) -> Parser<'a> {
        Parser { text }
    }

    fn parse(&self) -> &'a str {
        &self.text[0..5]
    }
}
```

**深入理解**:

- 结构体可以持有引用，但需要生命周期参数
- `impl<'a>` 为实现声明生命周期参数
- 结构体的生命周期不能长于其持有的引用

</details>

---

## 模块 4: 智能指针

### 问题 7: 选择合适的智能指针

以下场景应该使用哪种智能指针？

1. **场景 A**: 多个组件需要共享同一个配置对象
2. **场景 B**: 实现双向链表
3. **场景 C**: 需要一个可以修改的共享计数器
4. **场景 D**: 递归计算斐波那契数列并缓存结果

<details>
<summary>✅ 答案</summary>

| 场景 | 智能指针 | 原因 |
|:-----|:---------|:-----|
| A | `Arc<T>` | 线程安全的共享所有权 |
| B | `Rc<RefCell<Node<T>>>` | 共享所有权 + 内部可变性 |
| C | `Arc<Mutex<i32>>` 或 `Arc<AtomicI32>` | 线程安全 + 可变性 |
| D | `Rc<RefCell<HashMap<i32, i32>>>` | 递归缓存，共享 + 可变 |

**深入理解**:

- `Rc<T>`: 单线程共享所有权
- `Arc<T>`: 多线程共享所有权
- `RefCell<T>`: 运行时借用检查（单线程）
- `Mutex<T>`: 线程安全的互斥锁

</details>

---

### 问题 8: 循环引用检测

以下代码有什么问题？如何修复？

```rust
use std::rc::Rc;
use std::cell::RefCell;

struct Node {
    value: i32,
    children: RefCell<Vec<Rc<Node>>>,
    parent: RefCell<Option<Rc<Node>>>,  // 可能导致循环引用
}

fn main() {
    let parent = Rc::new(Node {
        value: 1,
        children: RefCell::new(vec![]),
        parent: RefCell::new(None),
    });

    let child = Rc::new(Node {
        value: 2,
        children: RefCell::new(vec![]),
        parent: RefCell::new(Some(parent.clone())),
    });

    parent.children.borrow_mut().push(child.clone());
    // 现在 parent 和 child 互相引用，导致内存泄漏
}
```

<details>
<summary>✅ 答案</summary>

**问题**: `parent` 和 `child` 形成循环引用，引用计数永远不会归零，导致内存泄漏。

**修复方案**: 使用 `Weak<T>` 打破循环

```rust
use std::rc::{Rc, Weak};
use std::cell::RefCell;

struct Node {
    value: i32,
    children: RefCell<Vec<Rc<Node>>>,
    parent: RefCell<Weak<Node>>,  // 使用 Weak
}

impl Node {
    fn new(value: i32) -> Rc<Node> {
        Rc::new(Node {
            value,
            children: RefCell::new(vec![]),
            parent: RefCell::new(Weak::new()),
        })
    }

    fn add_child(parent: &Rc<Node>, child: &Rc<Node>) {
        *child.parent.borrow_mut() = Rc::downgrade(parent);
        parent.children.borrow_mut().push(child.clone());
    }
}

fn main() {
    let parent = Node::new(1);
    let child = Node::new(2);

    Node::add_child(&parent, &child);

    // 现在 parent 强引用 child，child 弱引用 parent
    // 当 parent 被丢弃，child 的弱引用自动失效
}
```

**深入理解**:

- `Weak<T>` 不增加引用计数
- `upgrade()` 将弱引用转换为强引用（可能返回 None）
- 父节点使用弱引用子节点使用强引用是树结构的常见模式

</details>

---

## 模块 5: 综合挑战

### 挑战: 实现一个简单的数据库连接池

**要求**:

1. 管理多个数据库连接
2. 支持获取和归还连接
3. 线程安全
4. 连接有最大使用次数限制

<details>
<summary>💡 设计提示</summary>

需要哪些组件？

- 存储连接的容器
- 线程安全机制（Mutex）
- 连接状态跟踪（使用次数）
- RAII 模式（Drop）

</details>

<details>
<summary>✅ 参考实现</summary>

```rust
use std::sync::{Arc, Mutex};
use std::ops::{Deref, DerefMut};

// 模拟数据库连接
pub struct Connection {
    id: u32,
    use_count: u32,
    max_uses: u32,
}

impl Connection {
    fn new(id: u32) -> Self {
        Self {
            id,
            use_count: 0,
            max_uses: 10,
        }
    }

    fn is_expired(&self) -> bool {
        self.use_count >= self.max_uses
    }

    fn execute(&mut self, query: &str) -> String {
        self.use_count += 1;
        format!("Connection {} executed: {}", self.id, query)
    }
}

// 连接池
pub struct ConnectionPool {
    connections: Mutex<Vec<Connection>>,
}

// 池连接包装器
pub struct PooledConnection {
    connection: Option<Connection>,
    pool: Arc<ConnectionPool>,
}

impl ConnectionPool {
    pub fn new(size: u32) -> Arc<Self> {
        let connections: Vec<Connection> =
            (0..size).map(Connection::new).collect();

        Arc::new(Self {
            connections: Mutex::new(connections),
        })
    }

    pub fn get_connection(self: &Arc<Self>) -> Option<PooledConnection> {
        let mut connections = self.connections.lock().ok()?;

        // 找到未过期的连接
        let index = connections.iter().position(|c| !c.is_expired())?;
        let connection = connections.swap_remove(index);

        Some(PooledConnection {
            connection: Some(connection),
            pool: Arc::clone(self),
        })
    }

    fn return_connection(&self, mut conn: Connection) {
        if let Ok(mut connections) = self.connections.lock() {
            if !conn.is_expired() {
                connections.push(conn);
            } else {
                // 替换为新连接
                connections.push(Connection::new(conn.id));
            }
        }
    }
}

impl Deref for PooledConnection {
    type Target = Connection;

    fn deref(&self) -> &Self::Target {
        self.connection.as_ref().unwrap()
    }
}

impl DerefMut for PooledConnection {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.connection.as_mut().unwrap()
    }
}

impl Drop for PooledConnection {
    fn drop(&mut self) {
        if let Some(conn) = self.connection.take() {
            self.pool.return_connection(conn);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_connection_pool() {
        let pool = ConnectionPool::new(3);

        {
            let mut conn = pool.get_connection().unwrap();
            let result = conn.execute("SELECT * FROM users");
            assert!(result.contains("Connection 0"));
        }  // 连接自动归还

        // 可以再次获取连接
        let conn = pool.get_connection().unwrap();
        assert_eq!(conn.use_count, 1);  // 使用次数增加了
    }
}
```

**关键点**:

- `Arc<Mutex<T>>` 提供线程安全
- `Deref` 和 `DerefMut` 让 PooledConnection 像 Connection
- `Drop` 确保连接自动归还
- 连接过期时自动替换

</details>

---

## 🎓 学习检查

完成本指南后，你应该能：

- [ ] 诊断和修复所有权错误
- [ ] 理解借用规则的底层原理
- [ ] 正确使用生命周期注解
- [ ] 选择合适的智能指针
- [ ] 避免循环引用
- [ ] 设计符合所有权模型的 API

---

## 📚 下一步

- [高级实践工作坊](exercises/ADVANCED_OWNERSHIP_WORKSHOP.md) - 深入复杂场景
- [案例分析](./case-studies/README.md) - 学习生产代码
- [Coq形式化](./coq-formalization/README.md) - 理解严格证明

---

**进度**: 5/5 模块完成 ✅

---

## 🆕 Rust 1.94 所有权系统更新

> **适用版本**: Rust 1.94.0+

### 新特性对所有权系统的影响

| 特性 | 所有权影响 | 可判定性 |
|------|-----------|---------|
| rray_windows | 安全的切片访问 | ✅ 编译期检查 |
| ControlFlow | 控制流语义 | ✅ 类型安全 |
| LazyCell/LazyLock | 延迟初始化 | ✅ Send/Sync 检查 |

### 形式化更新

- rray_windows 的边界安全证明
- ControlFlow 的代数性质
- 延迟初始化的生命周期分析

**最后更新**: 2026-03-14
