# Rust设计模式的可判定性分析

> 分析GoF设计模式在Rust中的实现及其可判定性特征。

---

## 创建型模式

### 1. 单例模式 (Singleton)

**可判定性**: ✅ 完全可判定

```rust
use std::sync::Once;

static mut INSTANCE: Option<Singleton> = None;
static INIT: Once = Once::new();

pub struct Singleton {
    data: i32,
}

impl Singleton {
    pub fn get_instance() -> &'static Singleton {
        unsafe {
            INIT.call_once(|| {
                INSTANCE = Some(Singleton { data: 42 });
            });
            INSTANCE.as_ref().unwrap()
        }
    }
}
```

**分析**:

- 编译期静态检查确保唯一性
- `Once`保证线程安全
- 无运行时借用检查开销

### 2. 工厂模式 (Factory)

**可判定性**: ✅ 完全可判定

```rust
trait Product {
    fn operation(&self) -> String;
}

struct ConcreteProductA;
impl Product for ConcreteProductA {
    fn operation(&self) -> String {
        "Product A".to_string()
    }
}

struct Factory;
impl Factory {
    fn create_product(product_type: &str) -> Box<dyn Product> {
        match product_type {
            "A" => Box::new(ConcreteProductA),
            _ => panic!("Unknown type"),
        }
    }
}
```

**分析**:

- 类型系统在编译期验证Product约束
- trait对象有运行时开销（虚表）

### 3. 建造者模式 (Builder)

**可判定性**: ✅ 完全可判定

```rust
#[derive(Debug)]
struct Product {
    field1: String,
    field2: i32,
}

struct ProductBuilder {
    field1: Option<String>,
    field2: Option<i32>,
}

impl ProductBuilder {
    fn new() -> Self {
        Self { field1: None, field2: None }
    }

    fn field1(mut self, val: &str) -> Self {
        self.field1 = Some(val.to_string());
        self
    }

    fn build(self) -> Product {
        Product {
            field1: self.field1.expect("field1 required"),
            field2: self.field2.unwrap_or(0),
        }
    }
}
```

**分析**:

- 所有权转移确保每个字段只设置一次
- 编译期类型检查

---

## 结构型模式

### 4. 装饰器模式 (Decorator)

**可判定性**: ✅ 完全可判定

```rust
trait Component {
    fn operation(&self) -> String;
}

struct ConcreteComponent;
impl Component for ConcreteComponent {
    fn operation(&self) -> String {
        "Concrete".to_string()
    }
}

struct Decorator<T: Component> {
    component: T,
}

impl<T: Component> Component for Decorator<T> {
    fn operation(&self) -> String {
        format!("Decorated({})", self.component.operation())
    }
}
```

**分析**:

- 泛型实现零成本抽象
- 编译期确定类型

### 5. 代理模式 (Proxy)

**可判定性**: ✅ 完全可判定

```rust
trait Subject {
    fn request(&self);
}

struct RealSubject;
impl Subject for RealSubject {
    fn request(&self) {
        println!("RealSubject handling request");
    }
}

struct Proxy {
    real_subject: RealSubject,
}

impl Subject for Proxy {
    fn request(&self) {
        // 额外逻辑
        println!("Proxy: Checking access");
        self.real_subject.request();
    }
}
```

**分析**:

- 静态代理：编译期确定
- 动态代理：有运行时开销

---

## 行为型模式

### 6. 观察者模式 (Observer)

**可判定性**: ⚠️ 运行时检查

```rust
use std::cell::RefCell;
use std::rc::Rc;

trait Observer {
    fn update(&self, message: &str);
}

struct Subject {
    observers: RefCell<Vec<Rc<dyn Observer>>>,
}

impl Subject {
    fn new() -> Self {
        Self { observers: RefCell::new(vec![]) }
    }

    fn attach(&self, observer: Rc<dyn Observer>) {
        self.observers.borrow_mut().push(observer);
    }

    fn notify(&self, message: &str) {
        for observer in self.observers.borrow().iter() {
            observer.update(message);
        }
    }
}
```

**分析**:

- 使用`RefCell`进行运行时借用检查
- `Rc`进行运行时引用计数
- 有运行时开销

### 7. 策略模式 (Strategy)

**可判定性**: ✅ 完全可判定

```rust
trait Strategy {
    fn execute(&self, data: &[i32]) -> i32;
}

struct AddStrategy;
impl Strategy for AddStrategy {
    fn execute(&self, data: &[i32]) -> i32 {
        data.iter().sum()
    }
}

struct Context<'a> {
    strategy: &'a dyn Strategy,
}

impl<'a> Context<'a> {
    fn new(strategy: &'a dyn Strategy) -> Self {
        Self { strategy }
    }

    fn do_something(&self, data: &[i32]) -> i32 {
        self.strategy.execute(data)
    }
}
```

**分析**:

- 生命周期标注确保引用有效性
- 编译期类型检查

### 8. 状态模式 (State)

**可判定性**: ✅ 完全可判定（类型状态模式）

```rust
struct StateA;
struct StateB;
struct StateC;

struct Machine<S> {
    _state: std::marker::PhantomData<S>,
}

impl Machine<StateA> {
    fn new() -> Self {
        Self { _state: std::marker::PhantomData }
    }

    fn to_b(self) -> Machine<StateB> {
        Machine { _state: std::marker::PhantomData }
    }
}

impl Machine<StateB> {
    fn to_c(self) -> Machine<StateC> {
        Machine { _state: std::marker::PhantomData }
    }
}
```

**分析**:

- 类型系统在编译期验证状态转换
- 无效状态转换在编译期被拒绝

---

## 并发模式

### 9. 生产者-消费者 (Producer-Consumer)

**可判定性**: ⚠️ 运行时检查

```rust
use std::sync::mpsc::{channel, Sender, Receiver};
use std::thread;

fn producer_consumer() {
    let (tx, rx): (Sender<i32>, Receiver<i32>) = channel();

    let producer = thread::spawn(move || {
        for i in 0..10 {
            tx.send(i).unwrap();
        }
    });

    let consumer = thread::spawn(move || {
        for msg in rx {
            println!("Received: {}", msg);
        }
    });

    producer.join().unwrap();
    consumer.join().unwrap();
}
```

**分析**:

- `Send`/`Sync` trait编译期检查
- 通道运行时管理

### 10. 线程池 (Thread Pool)

**可判定性**: ⚠️ 运行时检查

```rust
use std::sync::{Arc, Mutex, mpsc};

type Job = Box<dyn FnOnce() + Send + 'static>;

struct ThreadPool {
    workers: Vec<Worker>,
    sender: mpsc::Sender<Job>,
}

struct Worker {
    id: usize,
    thread: Option<std::thread::JoinHandle<()>>,
}

impl ThreadPool {
    fn new(size: usize) -> Self {
        let (sender, receiver) = mpsc::channel();
        let receiver = Arc::new(Mutex::new(receiver));

        let mut workers = Vec::with_capacity(size);

        for id in 0..size {
            workers.push(Worker::new(id, Arc::clone(&receiver)));
        }

        Self { workers, sender }
    }

    fn execute<F>(&self, f: F)
    where
        F: FnOnce() + Send + 'static,
    {
        let job = Box::new(f);
        self.sender.send(job).unwrap();
    }
}
```

**分析**:

- `Mutex`运行时锁检查
- `Send` trait编译期验证

---

## 可判定性总结

| 模式 | 可判定性 | 主要机制 | 运行时开销 |
|------|----------|----------|------------|
| 单例 | ✅ 完全 | 静态变量 | 无 |
| 工厂 | ✅ 完全 | 泛型/trait | 虚表（动态分发） |
| 建造者 | ✅ 完全 | 所有权转移 | 无 |
| 装饰器 | ✅ 完全 | 泛型 | 无 |
| 代理 | ✅ 完全 | trait对象 | 虚表（可选） |
| 观察者 | ⚠️ 运行时 | RefCell/Rc | 借用检查+引用计数 |
| 策略 | ✅ 完全 | trait | 虚表（可选） |
| 状态 | ✅ 完全 | 类型状态 | 无 |
| 生产者-消费者 | ⚠️ 运行时 | 通道 | 同步开销 |
| 线程池 | ⚠️ 运行时 | Mutex/通道 | 锁+同步开销 |

---

## 设计模式选择指南

### 优先选择编译期可判定模式

当可能时，优先使用：

- 类型状态模式而非运行期状态检查
- 泛型装饰器而非动态trait对象
- 静态代理而非动态代理

### 何时使用运行时检查

- 需要运行时多态（观察者、复杂状态机）
- 跨线程共享数据（RefCell, Mutex）
- 动态策略切换

---

*设计模式的可判定性直接影响代码的性能和安全性。Rust的类型系统允许我们将许多运行时检查转移到编译期。*
