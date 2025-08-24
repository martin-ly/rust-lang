# 行为模式：Rust中的形式化行为设计模式

## 文档状态

- **版本**: 1.0
- **最后更新**: 2025-01-01
- **维护者**: Rust设计模式工作组
- **审核状态**: 待审核

## 概述

行为模式关注对象和类之间的通信模式，以及责任的分配。本文档详细阐述Rust中行为模式的形式化理论基础和安全实现方法。

## 核心行为模式分类

### 1. 迭代器模式 (Iterator Pattern)

#### 形式化定义

```rust
trait Iterator {
    type Item;
    fn next(&mut self) → Option<Self::Item>;
}

// 形式化语义
Iterator<I> ≡ (State, State → Option<(Item, State)>)
```

#### 数学模型

```text
Sequence: [a₁, a₂, ..., aₙ]
Iterator: State × (State → Option<Item × State>)
```

#### 安全性保证

**迭代器安全性定理**：

```text
∀ iter ∈ Iterator<T>:
  ∀ i ∈ ℕ: iter.nth(i) = Some(item) ⇒ valid_access(collection, i)
```

**实现示例**：

```rust
struct VecIterator<T> {
    vec: Vec<T>,
    index: usize,
}

impl<T> Iterator for VecIterator<T> {
    type Item = T;
    
    fn next(&mut self) → Option<Self::Item> {
        if self.index < self.vec.len() {
            let item = self.vec.swap_remove(self.index);
            Some(item)
        } else {
            None
        }
    }
}
```

#### 惰性求值的形式化

```text
LazyIterator: () → Iterator<T>
map_fusion: Iterator<T>.map(f).map(g) ≡ Iterator<T>.map(g ∘ f)
```

### 2. 访问者模式 (Visitor Pattern)

#### 传统访问者的问题

传统访问者模式在Rust中面临所有权挑战：

```rust
// 问题：同时借用数据结构和访问者
trait Visitor<T> {
    fn visit(&mut self, item: &T);
}
```

#### Rust化的访问者模式

##### 方案1：函数式访问者

```rust
trait Accept<F> {
    type Output;
    fn accept<F>(self, visitor: F) → Self::Output
    where F: FnOnce(Self) → Self::Output;
}
```

##### 方案2：状态累积访问者

```rust
trait FoldVisitor<T, Acc> {
    fn visit(acc: Acc, item: T) → Acc;
}

impl<T> Tree<T> {
    fn accept<V, Acc>(&self, visitor: V, acc: Acc) → Acc 
    where V: FoldVisitor<&T, Acc>
    {
        match self {
            Tree::Leaf(value) => V::visit(acc, value),
            Tree::Node(left, right) => {
                let acc = left.accept(visitor, acc);
                right.accept(visitor, acc)
            }
        }
    }
}
```

#### 类型安全的访问者

```rust
// 使用GATs实现类型安全访问者
trait TypedVisitor {
    type Output<T>;
    
    fn visit_string(&mut self, s: &str) → Self::Output<String>;
    fn visit_number(&mut self, n: i32) → Self::Output<i32>;
}
```

### 3. 状态模式 (State Pattern)

#### 类型状态模式 (Typestate Pattern)

```rust
// 状态在类型级别编码
struct Connection<S> {
    inner: TcpStream,
    state: PhantomData<S>,
}

struct Connected;
struct Disconnected;

impl Connection<Disconnected> {
    fn connect(self) → Result<Connection<Connected>, Error> {
        // 连接逻辑
    }
}

impl Connection<Connected> {
    fn send(&mut self, data: &[u8]) → Result<(), Error> {
        // 只有连接状态才能发送
    }
    
    fn disconnect(self) → Connection<Disconnected> {
        // 状态转换
    }
}
```

#### 状态转换的形式化

```text
StateTransition: State₁ → Action → State₂
TypeState: State ∈ TypeSystem
```

**状态安全性定理**：

```text
∀ s₁, s₂ ∈ State, ∀ a ∈ Action:
  valid_transition(s₁, a, s₂) ⇔ 
  ∃ method: impl FnOnce(Object<s₁>) → Object<s₂>
```

### 4. 策略模式 (Strategy Pattern)

#### Trait对象实现

```rust
trait SortStrategy {
    fn sort<T: Ord>(&self, data: &mut [T]);
}

struct QuickSort;
struct MergeSort;

impl SortStrategy for QuickSort { ... }
impl SortStrategy for MergeSort { ... }

struct Sorter {
    strategy: Box<dyn SortStrategy>,
}
```

#### 泛型策略模式

```rust
struct GenericSorter<S: SortStrategy> {
    strategy: S,
}

impl<S: SortStrategy> GenericSorter<S> {
    fn sort<T: Ord>(&self, data: &mut [T]) {
        self.strategy.sort(data)
    }
}
```

#### 性能分析

**零成本抽象定理**：

```text
∀ strategy ∈ GenericStrategy:
  runtime_cost(generic_call) = runtime_cost(direct_call)
```

### 5. 观察者模式 (Observer Pattern)

#### 基于通道的观察者

```rust
use std::sync::mpsc;

struct EventSource<T> {
    subscribers: Vec<mpsc::Sender<T>>,
}

impl<T: Clone> EventSource<T> {
    fn notify(&self, event: T) {
        for subscriber in &self.subscribers {
            let _ = subscriber.send(event.clone());
        }
    }
    
    fn subscribe(&mut self) → mpsc::Receiver<T> {
        let (tx, rx) = mpsc::channel();
        self.subscribers.push(tx);
        rx
    }
}
```

#### 类型安全的观察者

```rust
trait Observable<E> {
    type Subscription: Drop;
    
    fn subscribe<F>(&mut self, observer: F) → Self::Subscription
    where F: Fn(&E) + Send + 'static;
}
```

#### 弱引用观察者模式

```rust
use std::sync::{Weak, Arc};

struct WeakObserver<T> {
    observers: Vec<Weak<dyn Fn(&T) + Send + Sync>>,
}

impl<T> WeakObserver<T> {
    fn notify(&mut self, event: &T) {
        self.observers.retain(|weak_observer| {
            if let Some(observer) = weak_observer.upgrade() {
                observer(event);
                true
            } else {
                false  // 清理死亡观察者
            }
        });
    }
}
```

### 6. 命令模式 (Command Pattern)

#### 函数式命令模式

```rust
type Command<T> = Box<dyn FnOnce(&mut T) + Send>;

struct CommandQueue<T> {
    commands: Vec<Command<T>>,
}

impl<T> CommandQueue<T> {
    fn execute_all(&mut self, target: &mut T) {
        for command in self.commands.drain(..) {
            command(target);
        }
    }
}
```

#### 可撤销命令模式

```rust
trait ReversibleCommand<T> {
    type Memento;
    
    fn execute(&self, target: &mut T) → Self::Memento;
    fn undo(&self, target: &mut T, memento: Self::Memento);
}
```

#### 异步命令模式

```rust
trait AsyncCommand<T> {
    type Future: Future<Output = Result<(), Error>>;
    
    fn execute_async(&self, target: Arc<Mutex<T>>) → Self::Future;
}
```

### 7. 责任链模式 (Chain of Responsibility)

#### 函数式责任链

```rust
type Handler<T, R> = Box<dyn Fn(T) → Option<R> + Send + Sync>;

struct HandlerChain<T, R> {
    handlers: Vec<Handler<T, R>>,
}

impl<T, R> HandlerChain<T, R> 
where 
    T: Clone 
{
    fn handle(&self, request: T) → Option<R> {
        for handler in &self.handlers {
            if let Some(result) = handler(request.clone()) {
                return Some(result);
            }
        }
        None
    }
}
```

#### 类型安全的责任链

```rust
trait ChainLink<T> {
    type Output;
    type Next: ChainLink<T>;
    
    fn handle(&self, input: T) → Either<Self::Output, Self::Next>;
}
```

## 高级行为模式

### 8. 解释器模式 (Interpreter Pattern)

#### 抽象语法树定义

```rust
#[derive(Debug, Clone)]
enum Expr {
    Literal(i32),
    Variable(String),
    Binary(BinOp, Box<Expr>, Box<Expr>),
}

#[derive(Debug, Clone)]
enum BinOp {
    Add, Sub, Mul, Div,
}
```

#### 解释器实现

```rust
trait Interpreter<T> {
    type Context;
    type Output;
    type Error;
    
    fn interpret(&self, input: T, context: &Self::Context) 
        → Result<Self::Output, Self::Error>;
}

impl Interpreter<Expr> for ExprInterpreter {
    type Context = HashMap<String, i32>;
    type Output = i32;
    type Error = InterpreterError;
    
    fn interpret(&self, expr: Expr, ctx: &Self::Context) 
        → Result<i32, InterpreterError> 
    {
        match expr {
            Expr::Literal(n) => Ok(n),
            Expr::Variable(name) => {
                ctx.get(&name)
                   .copied()
                   .ok_or(InterpreterError::UndefinedVariable(name))
            },
            Expr::Binary(op, left, right) => {
                let l = self.interpret(*left, ctx)?;
                let r = self.interpret(*right, ctx)?;
                match op {
                    BinOp::Add => Ok(l + r),
                    BinOp::Sub => Ok(l - r),
                    BinOp::Mul => Ok(l * r),
                    BinOp::Div => {
                        if r == 0 {
                            Err(InterpreterError::DivisionByZero)
                        } else {
                            Ok(l / r)
                        }
                    }
                }
            }
        }
    }
}
```

### 9. 中介者模式 (Mediator Pattern)

#### 基于消息传递的中介者

```rust
use tokio::sync::mpsc;

#[derive(Debug)]
enum Message {
    UserJoined(UserId),
    UserLeft(UserId),
    SendMessage(UserId, String),
}

struct ChatMediator {
    receiver: mpsc::Receiver<Message>,
    users: HashMap<UserId, mpsc::Sender<String>>,
}

impl ChatMediator {
    async fn run(&mut self) {
        while let Some(message) = self.receiver.recv().await {
            match message {
                Message::UserJoined(id) => { ... },
                Message::UserLeft(id) => { ... },
                Message::SendMessage(from, content) => {
                    for (user_id, sender) in &self.users {
                        if *user_id != from {
                            let _ = sender.send(content.clone()).await;
                        }
                    }
                }
            }
        }
    }
}
```

### 10. 备忘录模式 (Memento Pattern)

#### 快照式备忘录

```rust
trait Snapshot {
    type Memento: Clone;
    
    fn save(&self) → Self::Memento;
    fn restore(&mut self, memento: Self::Memento);
}

struct History<T: Snapshot> {
    snapshots: Vec<T::Memento>,
    current: usize,
}

impl<T: Snapshot> History<T> {
    fn save_state(&mut self, object: &T) {
        // 截断未来历史
        self.snapshots.truncate(self.current + 1);
        self.snapshots.push(object.save());
        self.current = self.snapshots.len() - 1;
    }
    
    fn undo(&mut self, object: &mut T) → bool {
        if self.current > 0 {
            self.current -= 1;
            object.restore(self.snapshots[self.current].clone());
            true
        } else {
            false
        }
    }
    
    fn redo(&mut self, object: &mut T) → bool {
        if self.current + 1 < self.snapshots.len() {
            self.current += 1;
            object.restore(self.snapshots[self.current].clone());
            true
        } else {
            false
        }
    }
}
```

## 模式组合与交互

### 迭代器 + 访问者

```rust
struct CompositeVisitor<V, I> {
    visitor: V,
    _marker: PhantomData<I>,
}

impl<V, I> Iterator for CompositeVisitor<V, I> 
where 
    V: FnMut(&I) → Option<I>,
    I: Clone 
{
    type Item = I;
    
    fn next(&mut self) → Option<Self::Item> {
        // 结合访问者和迭代器逻辑
    }
}
```

### 状态 + 策略

```rust
struct StatefulStrategy<S, T> {
    state: S,
    strategy: T,
}

impl<S, T> StatefulStrategy<S, T> 
where 
    T: Strategy<S> 
{
    fn execute(&mut self) → T::Output {
        let (new_state, output) = self.strategy.execute(self.state);
        self.state = new_state;
        output
    }
}
```

## 安全性分析

### 内存安全性

**行为模式内存安全定理**：

```text
∀ pattern ∈ BehavioralPattern:
  implements_correctly(pattern) ⇒ memory_safe(pattern)
```

### 并发安全性

**行为模式并发安全定理**：

```text
∀ pattern ∈ ConcurrentBehavioralPattern:
  Send + Sync + correct_implementation(pattern) ⇒ thread_safe(pattern)
```

## 性能考量

### 零成本抽象验证

```rust
// 编译时验证性能等价性
#[inline(always)]
fn direct_call() → u32 { 42 }

#[inline(always)]
fn pattern_call<F: Fn() → u32>(f: F) → u32 { f() }

// 断言：pattern_call(direct_call) 编译为相同代码
```

### 运行时性能分析

- **Trait对象**: 动态分发开销
- **泛型**: 零成本抽象
- **函数指针**: 最小间接开销

## 相关模块

- [[01_formal_theory.md]] - 设计模式基础理论
- [[../04_generics/README.md]] - 泛型系统支持
- [[../05_concurrency/README.md]] - 并发模式安全性
- [[../02_type_system/README.md]] - 类型系统基础

## 参考文献

1. **Design Patterns: Elements of Reusable Object-Oriented Software**
2. **Rust Design Patterns** - rust-unofficial.github.io
3. **Zero-Cost Abstractions in Rust**
4. **Typestate-Oriented Programming**

## 维护信息

- **依赖关系**: 核心语言特性、标准库trait
- **更新频率**: 随语言特性演进更新
- **测试覆盖**: 主要模式的安全性验证
- **工具支持**: clippy lints, 模式识别工具

---

*本文档建立了Rust中行为模式的完整形式化基础，确保模式实现的安全性和性能。*
