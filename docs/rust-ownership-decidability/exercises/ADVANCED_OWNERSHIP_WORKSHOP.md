# Rust 所有权系统 - 高级实践工作坊

> **难度**: 🔴 高级
> **预计时间**: 8 小时
> **前置知识**: 核心所有权概念、生命周期、借用规则

---

## 🎯 工作坊目标

通过本工作坊，你将：

1. 掌握复杂的所有权场景处理
2. 理解自引用结构体的实现
3. 掌握内部可变性模式
4. 实现自定义智能指针
5. 理解 Pin 和 Unpin 的深层含义

---

## 📋 练习清单

### 练习 1: 自引用结构体实现 (60分钟)

**目标**: 实现一个自引用结构体 `Document`。

```rust
use std::pin::Pin;
use std::marker::PhantomPinned;

/// 自引用结构体：header 指向 content 的一部分
pub struct Document {
    content: String,
    header: *const str,  // 指向 content 的某个部分
    _pin: PhantomPinned,
}

impl Document {
    /// 创建新的 Document
    ///
    /// # 要求
    /// - content 必须非空
    /// - header 指向 content 的前 50 个字符或全部
    pub fn new(content: String) -> Pin<Box<Self>> {
        // TODO: 实现创建逻辑
        todo!()
    }

    /// 获取 header
    pub fn header(self: Pin<&Self>) -> &str {
        // TODO: 安全地返回 header
        todo!()
    }

    /// 获取 content
    pub fn content(self: Pin<&Self>) -> &str {
        // TODO: 返回 content
        todo!()
    }

    /// 追加内容（这会改变 content，需要小心处理）
    ///
    /// # 挑战
    /// 如果 content 重新分配，header 指针会失效
    /// 如何解决？
    pub fn append(self: Pin<&mut Self>, text: &str) {
        // TODO: 安全地追加内容
        // 提示：可能需要使用 Box::pin 和 Pin::as_mut()
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_document_creation() {
        let doc = Document::new("Hello, World! This is a test document.".to_string());
        assert_eq!(doc.header(), "Hello, World! This is a test document.");
    }

    #[test]
    fn test_document_append() {
        let mut doc = Document::new("Hello".to_string());
        doc.as_mut().append(", World!");
        assert!(doc.content().contains("Hello, World!"));
    }
}
```

**参考答案**:

<details>
<summary>点击展开</summary>

```rust
use std::pin::Pin;
use std::marker::PhantomPinned;

pub struct Document {
    content: String,
    header: *const str,
    _pin: PhantomPinned,
}

impl Document {
    pub fn new(content: String) -> Pin<Box<Self>> {
        let header_len = content.len().min(50);
        let header_ptr = &content[..header_len] as *const str;

        let mut boxed = Box::pin(Document {
            content,
            header: header_ptr,
            _pin: PhantomPinned,
        });

        // 修正 header 指针，使其指向堆上的 content
        unsafe {
            let content_ptr = &boxed.content as *const String;
            let str_ptr = &(*content_ptr)[..header_len] as *const str;
            boxed.as_mut().get_unchecked_mut().header = str_ptr;
        }

        boxed
    }

    pub fn header(self: Pin<&Self>) -> &str {
        unsafe { &*self.header }
    }

    pub fn content(self: Pin<&Self>) -> &str {
        &self.content
    }

    pub fn append(self: Pin<&mut Self>, text: &str) {
        let this = unsafe { self.get_unchecked_mut() };
        let old_len = this.content.len();
        this.content.push_str(text);

        // 重新计算 header 指针
        let header_len = old_len.min(50);
        this.header = &this.content[..header_len] as *const str;
    }
}
```

</details>

---

### 练习 2: 自定义智能指针 (90分钟)

**目标**: 实现一个引用计数智能指针 `MyRc<T>`，支持弱引用。

```rust
use std::ptr::NonNull;
use std::alloc::{alloc, dealloc, Layout};

/// RcBox 包含值和引用计数
struct RcBox<T> {
    value: T,
    strong: usize,
    weak: usize,
}

/// 自定义引用计数指针
pub struct MyRc<T> {
    ptr: NonNull<RcBox<T>>,
}

/// 弱引用指针
pub struct MyWeak<T> {
    ptr: NonNull<RcBox<T>>,
}

impl<T> MyRc<T> {
    /// 创建新的 MyRc
    pub fn new(value: T) -> Self {
        // TODO: 分配内存并初始化
        todo!()
    }

    /// 获取引用计数
    pub fn strong_count(&self) -> usize {
        // TODO: 返回强引用计数
        todo!()
    }

    /// 创建弱引用
    pub fn downgrade(&self) -> MyWeak<T> {
        // TODO: 创建弱引用
        todo!()
    }

    /// 获取内部值
    pub fn get_mut(&mut self) -> Option<&mut T> {
        // TODO: 只有在强引用为1时返回可变引用
        todo!()
    }
}

impl<T> std::ops::Deref for MyRc<T> {
    type Target = T;

    fn deref(&self) -> &T {
        // TODO: 返回值的引用
        todo!()
    }
}

impl<T> Clone for MyRc<T> {
    fn clone(&self) -> Self {
        // TODO: 增加引用计数并返回新指针
        todo!()
    }
}

impl<T> Drop for MyRc<T> {
    fn drop(&mut self) {
        // TODO: 减少引用计数，如果为0则释放内存
        todo!()
    }
}

impl<T> MyWeak<T> {
    /// 尝试升级弱引用
    pub fn upgrade(&self) -> Option<MyRc<T>> {
        // TODO: 如果值还存在，返回新的 MyRc
        todo!()
    }
}

impl<T> Clone for MyWeak<T> {
    fn clone(&self) -> Self {
        // TODO: 增加弱引用计数
        todo!()
    }
}

impl<T> Drop for MyWeak<T> {
    fn drop(&mut self) {
        // TODO: 减少弱引用计数
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_rc() {
        let rc = MyRc::new(42);
        assert_eq!(*rc, 42);
        assert_eq!(rc.strong_count(), 1);
    }

    #[test]
    fn test_clone() {
        let rc1 = MyRc::new(42);
        let rc2 = rc1.clone();
        assert_eq!(rc1.strong_count(), 2);
        assert_eq!(rc2.strong_count(), 2);
    }

    #[test]
    fn test_weak() {
        let rc = MyRc::new(42);
        let weak = rc.downgrade();
        assert!(weak.upgrade().is_some());

        drop(rc);
        assert!(weak.upgrade().is_none());
    }
}
```

---

### 练习 3: 类型状态模式 (45分钟)

**目标**: 使用类型状态模式实现一个 TCP 连接状态机。

```rust
/// 连接状态标记
pub struct Disconnected;
pub struct Connecting;
pub struct Connected;
pub struct Closed;

/// TCP 连接，使用类型状态确保状态转换正确
pub struct TcpConnection<State> {
    address: String,
    state: State,
}

impl TcpConnection<Disconnected> {
    pub fn new(address: impl Into<String>) -> Self {
        Self {
            address: address.into(),
            state: Disconnected,
        }
    }

    pub fn connect(self) -> TcpConnection<Connecting> {
        // TODO: 转换到 Connecting 状态
        todo!()
    }
}

impl TcpConnection<Connecting> {
    /// 尝试完成连接
    ///
    /// # 返回
    /// - Ok: 连接成功，进入 Connected 状态
    /// - Err: 连接失败，回到 Disconnected 状态
    pub fn finalize(self) -> Result<TcpConnection<Connected>, TcpConnection<Disconnected>> {
        // TODO: 模拟连接结果
        todo!()
    }
}

impl TcpConnection<Connected> {
    pub fn send(&self, data: &[u8]) -> Result<(), String> {
        // TODO: 发送数据
        todo!()
    }

    pub fn receive(&self) -> Result<Vec<u8>, String> {
        // TODO: 接收数据
        todo!()
    }

    pub fn close(self) -> TcpConnection<Closed> {
        // TODO: 关闭连接
        todo!()
    }
}

// 确保不能对已关闭的连接进行操作
// TcpConnection<Closed> 没有任何方法

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_connection_lifecycle() {
        let conn = TcpConnection::new("127.0.0.1:8080");
        let conn = conn.connect();

        match conn.finalize() {
            Ok(conn) => {
                conn.send(b"Hello").unwrap();
                let _data = conn.receive().unwrap();
                let _closed = conn.close();
                // 不能再操作已关闭的连接
            }
            Err(_conn) => {
                // 可以重试连接
            }
        }
    }
}
```

---

### 练习 4: 生命周期高级技巧 (60分钟)

**目标**: 实现一个可以迭代并修改的容器。

```rust
/// 可迭代可变引用的容器
pub struct Buffer<T> {
    data: Vec<T>,
}

/// 迭代器，同时支持读取和写入
pub struct BufferIter<'a, T> {
    buffer: &'a mut Buffer<T>,
    index: usize,
}

/// 可变引用项
pub struct BufferItem<'a, T> {
    item: &'a mut T,
}

impl<T> Buffer<T> {
    pub fn new() -> Self {
        Self { data: Vec::new() }
    }

    pub fn push(&mut self, item: T) {
        self.data.push(item);
    }

    /// 获取可变的迭代器
    ///
    /// # 挑战
    /// 如何让迭代器返回的每一项都可以独立修改？
    pub fn iter_mut<'a>(&'a mut self) -> BufferIter<'a, T> {
        // TODO: 实现可变迭代器
        todo!()
    }

    /// 安全地交换两个元素
    ///
    /// # 挑战
    /// 如何在存在活跃引用时交换元素？
    pub fn swap(&mut self, i: usize, j: usize) {
        // TODO: 安全交换
        todo!()
    }
}

impl<'a, T> Iterator for BufferIter<'a, T> {
    type Item = BufferItem<'a, T>;

    fn next(&mut self) -> Option<Self::Item> {
        // TODO: 实现迭代逻辑
        todo!()
    }
}

impl<'a, T> BufferItem<'a, T> {
    pub fn get(&self) -> &T {
        self.item
    }

    pub fn get_mut(&mut self) -> &mut T {
        self.item
    }

    /// 用新值替换当前项，返回旧值
    pub fn replace(&mut self, new_value: T) -> T {
        // TODO: 替换值
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_iter_mut() {
        let mut buffer = Buffer::new();
        buffer.push(1);
        buffer.push(2);
        buffer.push(3);

        for mut item in buffer.iter_mut() {
            *item.get_mut() *= 2;
        }

        let values: Vec<i32> = buffer.iter_mut().map(|i| *i.get()).collect();
        assert_eq!(values, vec![2, 4, 6]);
    }
}
```

---

### 练习 5: 复杂生命周期场景 (90分钟)

**目标**: 实现一个带有回调的解析器，处理复杂生命周期。

```rust
/// 解析事件
type ParseEvent<'a> = &'a str;

/// 事件处理器 trait
pub trait EventHandler<'a> {
    fn on_event(&mut self, event: ParseEvent<'a>);
}

/// 带有回调的解析器
pub struct Parser<'a, H: EventHandler<'a>> {
    input: &'a str,
    position: usize,
    handler: H,
}

impl<'a, H: EventHandler<'a>> Parser<'a, H> {
    pub fn new(input: &'a str, handler: H) -> Self {
        Self {
            input,
            position: 0,
            handler,
        }
    }

    /// 解析下一个 token
    ///
    /// # 挑战
    /// - 返回的 token 引用 input
    /// - 同时可能需要调用 handler（也需要引用）
    /// - 如何在同一个作用域处理这些引用？
    pub fn next_token(&mut self) -> Option<&'a str> {
        // TODO: 解析 token
        todo!()
    }

    /// 解析所有 token
    pub fn parse_all(mut self) -> Vec<&'a str> {
        // TODO: 解析所有 token
        todo!()
    }
}

/// 统计事件处理器
pub struct Counter {
    count: usize,
}

impl<'a> EventHandler<'a> for Counter {
    fn on_event(&mut self, _event: ParseEvent<'a>) {
        self.count += 1;
    }
}

/// 收集事件处理器
pub struct Collector<'b> {
    events: Vec<&'b str>,
}

impl<'a, 'b: 'a> EventHandler<'a> for Collector<'b> {
    fn on_event(&mut self, event: ParseEvent<'a>) {
        self.events.push(event);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parser_with_counter() {
        let input = "hello world foo bar";
        let counter = Counter { count: 0 };
        let parser = Parser::new(input, counter);

        let tokens = parser.parse_all();
        assert_eq!(tokens.len(), 4);
    }
}
```

---

## 🔧 挑战任务

### 挑战 1: 实现 Send 和 Sync (60分钟)

为练习 2 中的 `MyRc<T>` 正确实现 `Send` 和 `Sync` trait。

```rust
// TODO: 在什么条件下 MyRc<T> 是 Send？
// TODO: 在什么条件下 MyRc<T> 是 Sync？
// TODO: MyWeak<T> 呢？

unsafe impl<T: Send + Sync> Send for MyRc<T> {}
unsafe impl<T: Send + Sync> Sync for MyRc<T> {}
```

### 挑战 2: 无锁数据结构 (120分钟)

实现一个简单的无锁栈 `LockFreeStack<T>`。

```rust
use std::sync::atomic::{AtomicPtr, Ordering};
use std::ptr;

struct Node<T> {
    value: T,
    next: *mut Node<T>,
}

pub struct LockFreeStack<T> {
    head: AtomicPtr<Node<T>>,
}

impl<T> LockFreeStack<T> {
    pub fn new() -> Self {
        Self {
            head: AtomicPtr::new(ptr::null_mut()),
        }
    }

    /// 使用 CAS 操作实现 push
    pub fn push(&self, value: T) {
        // TODO: 使用 compare_and_swap 实现
        todo!()
    }

    /// 使用 CAS 操作实现 pop
    pub fn pop(&self) -> Option<T> {
        // TODO: 使用 compare_and_swap 实现
        todo!()
    }
}

impl<T> Drop for LockFreeStack<T> {
    fn drop(&mut self) {
        // TODO: 安全地释放所有节点
        todo!()
    }
}
```

---

## 📚 参考答案与解析

所有练习的详细答案和解析可在 `solutions/` 目录找到。

### 常见错误分析

| 错误 | 原因 | 解决方案 |
|:-----|:-----|:---------|
| `cannot borrow as mutable` | 同时存在多个可变引用 | 重新设计借用模式 |
| `lifetime may not live long enough` | 返回值生命周期不够长 | 使用显式生命周期注解 |
| `use of moved value` | 值已被移动 | 实现 Clone 或 Copy |
| `cannot move out of shared reference` | 尝试从共享引用移动 | 使用 clone 或引用 |

---

## 🎓 学习检查点

完成本工作坊后，你应该能够：

- [ ] 解释 `Pin` 和 `PhantomPinned` 的作用
- [ ] 实现自定义智能指针并正确处理 Drop
- [ ] 使用类型状态模式设计 API
- [ ] 处理复杂的生命周期场景
- [ ] 理解 `Send` 和 `Sync` 的边界条件

---

## 📖 延伸阅读

- [内部可变性深入](../01-core-concepts/detailed-concepts/interior-mutability.md)
- [Pin 和 Unpin 详解](../01-core-concepts/detailed-concepts/ownership-deep-dive.md#pin-unpin)
- [并发模式](../12-concurrency-patterns/README.md)

---

**难度**: 🔴 高级
**完成度**: 0/5 练习
