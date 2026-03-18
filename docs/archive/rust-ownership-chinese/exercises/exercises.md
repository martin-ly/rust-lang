# Rust所有权与可判定性：练习题

> 本练习集配合主文档使用，分为选择题、代码分析题和编程挑战三个部分。

---

## 第一部分：选择题（50道）

### 基础概念（1-20）

**1. 以下哪个选项正确描述了Rust的所有权规则？**

A. 每个值可以有多个所有者
B. 值在没有所有者时会自动复制
C. 每个值有且只有一个所有者，当所有者离开作用域时值被释放
D. 值的生命周期由垃圾收集器管理

<details>
<summary>答案</summary>

**C** - 这是所有权三定律中的唯一性原则。

</details>

---

**2. 关于Copy trait，以下说法正确的是？**

A. 所有类型都可以实现Copy trait
B. 实现Drop的类型也可以实现Copy
C. Copy类型的赋值会转移所有权
D. 标量类型（i32, bool等）默认实现Copy

<details>
<summary>答案</summary>

**D** - 标量类型默认实现Copy。A错误（如String不能实现Copy），B错误（Copy和Drop互斥），C错误（Copy类型赋值是复制而非移动）。

</details>

---

**3. 以下代码能否编译？**

```rust
let s = String::from("hello");
let r1 = &s;
let r2 = &mut s;
println!("{}", r1);
```

A. 可以编译
B. 不能编译，因为不能同时有可变和不可变借用
C. 不能编译，因为r1的生命周期太长
D. 可以编译，如果使用NLL

<details>
<summary>答案</summary>

**B** - 借用规则禁止同时存在可变和不可变借用。

</details>

---

**4. 关于生命周期省略规则，以下正确的是？**

A. 编译器永远不会推断生命周期
B. 只有一个输入生命周期时，输出使用'sstatic
C. 方法中的&self使用独立的生命周期
D. 单个引用参数时，输出生命周期与输入相同

<details>
<summary>答案</summary>

**D** - 这是生命周期省略规则2。

</details>

---

**5. RefCell的借用检查发生在？**

A. 编译期
B. 链接期
C. 运行时
D. 部署时

<details>
<summary>答案</summary>

**C** - RefCell在运行时检查借用规则，违反时会panic。

</details>

---

### 借用与生命周期（21-35）

**21. 以下代码的输出是？**

```rust
let mut x = 5;
let y = &mut x;
*y += 1;
let z = &mut x;
*z += 1;
println!("{}", x);
```

A. 5
B. 6
C. 7
D. 编译错误

<details>
<summary>答案</summary>

**C** - 虽然有两个&mut x，但它们的生命周期不重叠（NLL），所以是合法的。最终x = 7。

</details>

---

**22. 关于非词法生命周期（NLL），正确的是？**

A. NLL是运行时特性
B. NLL基于词法作用域
C. NLL基于控制流图的数据流分析
D. NLL只适用于不可变借用

<details>
<summary>答案</summary>

**C** - NLL基于控制流图（CFG）的数据流分析，而不是词法作用域。

</details>

---

**23. 以下哪个生命周期标注是正确的？**

```rust
fn foo<'a, 'b>(x: &'a str, y: &'b str) -> ???
```

A. `&'a str` - 总是返回x的生命周期
B. `&'b str` - 总是返回y的生命周期
C. `&'static str` - 返回静态生命周期
D. 以上取决于具体实现

<details>
<summary>答案</summary>

**D** - 返回类型取决于函数实际返回的是x还是y。

</details>

---

### 并发与线程安全（36-45）

**36. Rc和Arc的主要区别是？**

A. Rc更快
B. Arc是线程安全的，Rc不是
C. Rc可以跨线程
D. 没有区别

<details>
<summary>答案</summary>

**B** - Arc使用原子操作，是Send+Sync；Rc不是线程安全的。

</details>

---

**37. 以下代码能否编译？**

```rust
let data = Arc::new(Mutex::new(0));
let data2 = Arc::clone(&data);
thread::spawn(move || {
    *data2.lock().unwrap() += 1;
});
*data.lock().unwrap() += 1;
```

A. 可以编译
B. 不能编译，因为data被移动了
C. 不能编译，因为Mutex不是Send
D. 不能编译，需要更多生命周期标注

<details>
<summary>答案</summary>

**A** - Arc<Mutex<T>>是Send+Sync，可以安全地跨线程共享。

</details>

---

### 可判定性理论（46-50）

**46. 根据Halting Problem，以下哪个说法是正确的？**

A. 所有程序都可以在编译期确定是否会终止
B. 存在算法可以判定任意程序是否会终止
C. 不存在通用算法可以判定任意程序是否会终止
D. Rust编译器可以解决Halting Problem

<details>
<summary>答案</summary>

**C** - 这是Halting Problem的核心结论。

</details>

---

**47. Rice's Theorem指出？**

A. 所有程序属性都是可判定的
B. 非平凡语义属性是不可判定的
C. 语法属性是不可判定的
D. 类型检查是不可判定的

<details>
<summary>答案</summary>

**B** - Rice's Theorem指出非平凡语义属性（如"程序是否有bug"）是不可判定的。

</details>

---

## 第二部分：代码分析题（30道）

### 分析题 1: 基础借用

```rust
fn main() {
    let mut s = String::from("hello");

    {
        let r1 = &s;
        println!("r1: {}", r1);
    }

    let r2 = &mut s;
    r2.push_str(" world");

    println!("s: {}", s);
}
```

**问题：**

1. 这段代码能否编译？为什么？
2. 如果不使用内部作用域，代码还能编译吗？
3. 解释NLL在此场景中的作用。

<details>
<summary>答案与分析</summary>

**1. 可以编译。**

- r1在内部作用域结束，释放借用
- r2在外部作用域创建，此时没有活跃借用
- 两个借用生命周期不重叠

**2. 如果不使用内部作用域：**

```rust
let r1 = &s;
println!("r1: {}", r1);
let r2 = &mut s; // ❌ 编译错误
```

- r1的生命周期持续到作用域结束
- r2创建时r1仍然活跃，违反借用规则

**3. NLL的作用：**

- NLL（Non-Lexical Lifetimes）基于数据流分析
- 即使不使用内部作用域，NLL也能确定r1的最后使用点
- 实际上，带NLL的代码即使没有内部作用域也能编译

</details>

---

### 分析题 2: 生命周期标注

```rust
struct Wrapper<'a> {
    data: &'a str,
}

impl<'a> Wrapper<'a> {
    fn get_data(&self) -> &str {
        self.data
    }

    fn combine(&self, other: &Wrapper) -> String {
        format!("{}-{}", self.data, other.data)
    }
}
```

**问题：**

1. `get_data`的返回类型生命周期是什么？是&'a str还是&'self str？
2. `combine`方法中的`other`参数的生命周期如何推断？
3. 如果要返回一个引用而不是String，应该如何修改签名？

<details>
<summary>答案与分析</summary>

**1. `get_data`的返回类型：**

```rust
fn get_data(&self) -> &'a str
```

- 根据生命周期省略规则3，返回类型使用&self的生命周期
- &self实际上是&'b self，其中'b是方法调用的生命周期
- 但self.data的类型是&'a str，所以返回&'a str

**2. `combine`中的`other`：**

```rust
fn combine<'b>(&self, other: &'b Wrapper<'_>) -> String
```

- other获得独立的生命周期'b
- Wrapper<'_>表示匿名生命周期

**3. 返回引用的版本：**

```rust
fn get_first(&self, other: &Wrapper) -> &str {
    if self.data.len() > other.data.len() {
        self.data
    } else {
        other.data
    }
}
// 编译器推断：
// fn get_first<'b>(&self, other: &'b Wrapper) -> &'a str
// 但这样可能有生命周期不匹配问题

// 正确的显式标注：
fn get_first_explicit<'a>(&'a self, other: &'a Wrapper<'a>) -> &'a str {
    if self.data.len() > other.data.len() {
        self.data
    } else {
        other.data
    }
}
```

</details>

---

### 分析题 3: 并发与所有权

```rust
use std::thread;

fn main() {
    let data = vec![1, 2, 3, 4, 5];

    for i in 0..3 {
        thread::spawn(move || {
            println!("Thread {}: {:?}", i, data);
        });
    }
}
```

**问题：**

1. 这段代码能否编译？如果不能，错误是什么？
2. 如何修改代码使其能够编译？
3. 解释为什么`move`关键字在这里是必要的。

<details>
<summary>答案与分析</summary>

**1. 编译错误：**

```text
error[E0382]: use of moved value: `data`
```

- 第一次`thread::spawn`时，data被move到闭包
- 后续迭代时data已经失效

**2. 修改方案：**

```rust
use std::sync::Arc;

fn main() {
    let data = Arc::new(vec![1, 2, 3, 4, 5]);

    for i in 0..3 {
        let data = Arc::clone(&data);
        thread::spawn(move || {
            println!("Thread {}: {:?}", i, data);
        });
    }
}
```

**3. `move`关键字的必要性：**

- 闭包需要捕获环境中的变量
- `move`强制闭包获取变量的所有权
- 对于线程闭包，通常需要`move`来转移数据到线程
- 使用Arc时，每次clone创建新的Arc（引用计数增加），原Arc仍然有效

</details>

---

### 分析题 4: 内部可变性

```rust
use std::cell::RefCell;

fn main() {
    let data = RefCell::new(vec![1, 2, 3]);

    let borrow1 = data.borrow();
    println!("First: {:?}", *borrow1);

    let borrow2 = data.borrow();
    println!("Second: {:?}", *borrow2);

    let borrow3 = data.borrow_mut();
    borrow3.push(4);
    println!("After push: {:?}", *borrow3);
}
```

**问题：**

1. 这段代码能否编译？如果不能，为什么？
2. 运行时会发生什么？
3. 如何修复这个问题？

<details>
<summary>答案与分析</summary>

**1. 编译：**

- 可以编译，RefCell的借用检查在运行时进行

**2. 运行时panic：**

```text
thread 'main' panicked at 'already borrowed: BorrowMutError'
```

- borrow1和borrow2仍然存在（生命周期到作用域结束）
- borrow_mut()尝试获取可变借用，但已有不可变借用
- 违反借用规则，运行时panic

**3. 修复方案：**

```rust
use std::cell::RefCell;

fn main() {
    let data = RefCell::new(vec![1, 2, 3]);

    {
        let borrow1 = data.borrow();
        println!("First: {:?}", *borrow1);

        let borrow2 = data.borrow();
        println!("Second: {:?}", *borrow2);
    } // borrow1和borrow2在此处结束

    let mut borrow3 = data.borrow_mut();
    borrow3.push(4);
    println!("After push: {:?}", *borrow3);
}
```

</details>

---

## 第三部分：编程挑战（20道）

### 挑战 1: 实现自定义智能指针

**要求：**

实现一个自定义的`MyBox<T>`智能指针，要求：

1. 在堆上分配内存
2. 实现Deref和DerefMut trait
3. 实现Drop trait，正确释放内存
4. 支持`new`构造函数

**参考实现：**

```rust
use std::ops::{Deref, DerefMut};
use std::ptr::NonNull;

struct MyBox<T> {
    ptr: NonNull<T>,
}

impl<T> MyBox<T> {
    fn new(value: T) -> Self {
        let boxed = Box::new(value);
        Self {
            ptr: NonNull::new(Box::into_raw(boxed)).unwrap(),
        }
    }
}

impl<T> Deref for MyBox<T> {
    type Target = T;
    fn deref(&self) -> &T {
        unsafe { self.ptr.as_ref() }
    }
}

impl<T> DerefMut for MyBox<T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { self.ptr.as_mut() }
    }
}

impl<T> Drop for MyBox<T> {
    fn drop(&mut self) {
        unsafe {
            let _ = Box::from_raw(self.ptr.as_ptr());
        }
    }
}
```

---

### 挑战 2: 实现类型状态模式

**要求：**

实现一个`Connection`类型状态模式，支持以下状态转换：

1. Disconnected → Connecting
2. Connecting → Connected
3. Connected → Disconnected
4. 阻止非法状态转换（如直接Disconnected → Connected）

**参考实现：**

```rust
use std::marker::PhantomData;

struct Disconnected;
struct Connecting;
struct Connected;

struct Connection<State> {
    url: String,
    _state: PhantomData<State>,
}

impl Connection<Disconnected> {
    fn new(url: &str) -> Self {
        Self {
            url: url.to_string(),
            _state: PhantomData,
        }
    }

    fn connect(self) -> Connection<Connecting> {
        println!("Connecting to {}...", self.url);
        Connection {
            url: self.url,
            _state: PhantomData,
        }
    }
}

impl Connection<Connecting> {
    fn wait_for_connection(self) -> Result<Connection<Connected>, Connection<Disconnected>> {
        // 模拟连接结果
        if self.url.starts_with("http") {
            println!("Connected!");
            Ok(Connection {
                url: self.url,
                _state: PhantomData,
            })
        } else {
            println!("Connection failed!");
            Err(Connection {
                url: self.url,
                _state: PhantomData,
            })
        }
    }
}

impl Connection<Connected> {
    fn send(&self, data: &str) {
        println!("Sending '{}' to {}", data, self.url);
    }

    fn disconnect(self) -> Connection<Disconnected> {
        println!("Disconnected from {}", self.url);
        Connection {
            url: self.url,
            _state: PhantomData,
        }
    }
}

fn main() {
    let conn = Connection::new("http://example.com");
    // conn.send("data"); // ❌ 编译错误

    let conn = conn.connect();
    // conn.send("data"); // ❌ 编译错误

    let conn = conn.wait_for_connection().unwrap();
    conn.send("Hello!"); // ✅ OK

    let conn = conn.disconnect();
    // conn.send("data"); // ❌ 编译错误
}
```

---

### 挑战 3: 实现线程安全的计数器

**要求：**

实现一个线程安全的计数器，支持：

1. 多线程并发递增
2. 获取当前计数
3. 使用原子操作（无锁）

**参考实现：**

```rust
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::thread;

struct AtomicCounter {
    count: AtomicUsize,
}

impl AtomicCounter {
    fn new() -> Self {
        Self {
            count: AtomicUsize::new(0),
        }
    }

    fn increment(&self) {
        self.count.fetch_add(1, Ordering::Relaxed);
    }

    fn get(&self) -> usize {
        self.count.load(Ordering::Relaxed)
    }
}

fn main() {
    let counter = Arc::new(AtomicCounter::new());
    let mut handles = vec![];

    for _ in 0..10 {
        let c = Arc::clone(&counter);
        handles.push(thread::spawn(move || {
            for _ in 0..1000 {
                c.increment();
            }
        }));
    }

    for h in handles {
        h.join().unwrap();
    }

    assert_eq!(counter.get(), 10000);
    println!("Final count: {}", counter.get());
}
```

---

### 挑战 4: 实现简单的线程池

**要求：**

实现一个简单的固定大小线程池：

1. 创建工作线程
2. 通过channel分配任务
3. 支持优雅关闭

**参考实现：** 见concurrency_patterns.rs中的ThreadPool实现

---

## 附录：参考答案索引

| 题号 | 类型 | 难度 | 相关章节 |
|------|------|------|----------|
| 1-20 | 选择题-基础 | ⭐⭐ | 概念定义 |
| 21-35 | 选择题-借用 | ⭐⭐⭐ | 借用语义 |
| 36-45 | 选择题-并发 | ⭐⭐⭐ | 线程安全 |
| 46-50 | 选择题-理论 | ⭐⭐⭐⭐ | 可判定性 |
| 分析1-10 | 代码分析 | ⭐⭐⭐ | 综合运用 |
| 挑战1-5 | 编程 | ⭐⭐⭐⭐ | 实践应用 |
| 挑战6-10 | 编程 | ⭐⭐⭐⭐⭐ | 高级模式 |

---

*练习题持续更新中，欢迎提交PR添加更多题目。*
