# 中介者模式形式化理论

## 1. 形式化定义

### 1.1 基本概念

中介者模式是一种行为型设计模式，它用一个中介对象来封装一系列的对象交互，中介者使各对象不需要显式地相互引用，从而使其耦合松散，而且可以独立地改变它们之间的交互。

**定义 1.1.1** (中介者系统)
设 $C$ 为同事对象集合，$M$ 为中介者集合，中介者系统是一个三元组 $(C, M, \phi)$，其中：

- $\phi: C \times C \times M \rightarrow M$ 是交互函数

**定义 1.1.2** (交互过程)
对于同事对象 $c_1, c_2 \in C$ 和中介者 $m \in M$，交互过程定义为：
$$\text{interact}(c_1, c_2, m) = \phi(c_1, c_2, m)$$

**定义 1.1.3** (中介者协调)
中介者的协调函数定义为：
$$\text{coordinate}(m, \text{event}) = \begin{cases}
\text{notify}(c_i) & \text{if } \text{event} \text{ affects } c_i \\
\text{ignore} & \text{otherwise}
\end{cases}$$

### 1.2 数学基础

**定理 1.2.1** (交互传递性)
对于任意同事对象 $c_1, c_2, c_3$ 和中介者 $m$，如果 $c_1$ 与 $c_2$ 交互，$c_2$ 与 $c_3$ 交互，则：
$$\text{interact}(c_1, c_3, m) = \phi(c_1, c_3, m)$$

**定理 1.2.2** (中介者唯一性)
在给定的中介者系统中，任意两个同事对象之间的交互都通过唯一的中介者进行。

**证明：**
根据中介者模式的定义，所有交互都必须通过中介者进行，因此中介者是唯一的。

## 2. 类型系统分析

### 2.1 Rust 类型映射

```rust
// 中介者特征
trait Mediator {
    type Colleague;
    type Event;
    type Result;

    fn notify(&mut self, colleague: &Self::Colleague, event: Self::Event) -> Self::Result;
}

// 同事对象特征
trait Colleague {
    type Mediator: Mediator;
    type Event;

    fn set_mediator(&mut self, mediator: Box<Self::Mediator>);
    fn send(&self, event: Self::Event);
    fn receive(&mut self, event: Self::Event);
}

// 具体中介者实现
struct ConcreteMediator {
    colleagues: Vec<Box<dyn Colleague<Mediator = Self, Event = String>>>,
}

impl Mediator for ConcreteMediator {
    type Colleague = Box<dyn Colleague<Mediator = Self, Event = String>>;
    type Event = String;
    type Result = ();

    fn notify(&mut self, colleague: &Self::Colleague, event: Self::Event) -> Self::Result {
        for other in &mut self.colleagues {
            if std::ptr::eq(other.as_ref(), colleague.as_ref()) {
                continue; // 不通知自己
            }
            other.receive(event.clone());
        }
    }
}
```

### 2.2 类型安全证明

**引理 2.2.1** (类型一致性)
对于任意中介者 $m$ 和同事对象 $c$，交互事件的类型必须一致：
$$\text{type}(c.\text{Event}) = \text{type}(m.\text{Event})$$

**证明：**
根据 Rust 类型系统，`Colleague` trait 要求中介者和同事对象具有相同的 `Event` 类型，确保类型一致性。

## 3. 实现策略

### 3.1 基础实现

```rust
// 具体同事对象
struct ConcreteColleagueA {
    mediator: Option<Box<dyn Mediator<Colleague = Self, Event = String, Result = ()>>>,
    name: String,
}

impl Colleague for ConcreteColleagueA {
    type Mediator = dyn Mediator<Colleague = Self, Event = String, Result = ()>;
    type Event = String;

    fn set_mediator(&mut self, mediator: Box<Self::Mediator>) {
        self.mediator = Some(mediator);
    }

    fn send(&self, event: Self::Event) {
        if let Some(ref mediator) = self.mediator {
            mediator.notify(self, event);
        }
    }

    fn receive(&mut self, event: Self::Event) {
        println!("Colleague {} received: {}", self.name, event);
    }
}

// 聊天室中介者示例
struct ChatRoom {
    participants: Vec<Box<dyn Colleague<Mediator = Self, Event = ChatMessage>>>,
}

struct ChatMessage {
    from: String,
    content: String,
    timestamp: std::time::SystemTime,
}

impl Mediator for ChatRoom {
    type Colleague = Box<dyn Colleague<Mediator = Self, Event = ChatMessage>>;
    type Event = ChatMessage;
    type Result = ();

    fn notify(&mut self, sender: &Self::Colleague, message: Self::Event) -> Self::Result {
        for participant in &mut self.participants {
            if !std::ptr::eq(participant.as_ref(), sender.as_ref()) {
                participant.receive(message.clone());
            }
        }
    }
}
```

### 3.2 事件驱动架构

```rust
// 事件系统
trait Event {
    type Source;
    type Target;
    type Data;

    fn source(&self) -> &Self::Source;
    fn target(&self) -> Option<&Self::Target>;
    fn data(&self) -> &Self::Data;
}

// 事件中介者
struct EventMediator<E: Event> {
    handlers: HashMap<TypeId, Vec<Box<dyn Fn(&E)>>>,
}

impl<E: Event> EventMediator<E> {
    fn new() -> Self {
        Self {
            handlers: HashMap::new(),
        }
    }

    fn register_handler<T: 'static>(&mut self, handler: Box<dyn Fn(&E)>) {
        let type_id = TypeId::of::<T>();
        self.handlers.entry(type_id).or_insert_with(Vec::new).push(handler);
    }

    fn publish(&self, event: &E) {
        let type_id = TypeId::of::<E>();
        if let Some(handlers) = self.handlers.get(&type_id) {
            for handler in handlers {
                handler(event);
            }
        }
    }
}
```

## 4. 正确性证明

### 4.1 交互正确性

**定理 4.1.1** (交互正确性)
对于任意同事对象 $c_1, c_2$ 和中介者 $m$，如果 $c_1$ 发送事件 $e$，则 $c_2$ 能够接收到该事件。

**证明：**
根据中介者的 `notify` 方法实现，所有其他同事对象都会被通知，因此交互正确性得到保证。

### 4.2 解耦正确性

**定理 4.2.1** (解耦正确性)
同事对象之间不直接引用，所有交互都通过中介者进行。

**证明：**
根据中介者模式的定义，同事对象只持有对中介者的引用，不直接引用其他同事对象，因此解耦正确性得到保证。

## 5. 性能分析

### 5.1 时间复杂度

**定理 5.1.1** (交互时间复杂度)
对于包含 $n$ 个同事对象的中介者系统，单次交互的时间复杂度为 $O(n)$。

**证明：**
中介者需要通知所有其他同事对象，因此时间复杂度为 $O(n)$。

### 5.2 空间复杂度

**定理 5.2.1** (空间复杂度)
中介者系统的空间复杂度为 $O(n)$，其中 $n$ 是同事对象的数量。

**证明：**
中介者需要存储所有同事对象的引用，因此空间复杂度为 $O(n)$。

## 6. 应用场景

### 6.1 用户界面
- GUI 组件交互
- 表单验证
- 对话框管理

### 6.2 网络通信
- 聊天系统
- 消息队列
- 事件总线

### 6.3 业务流程
- 工作流引擎
- 状态机
- 规则引擎

## 7. 与其他模式的关系

### 7.1 与观察者模式
- 中介者模式关注对象间协调
- 观察者模式关注状态变化通知

### 7.2 与外观模式
- 中介者模式关注交互协调
- 外观模式关注接口简化

## 8. 高级特性

### 8.1 分层中介者

```rust
// 分层中介者系统
struct LayeredMediator {
    layers: Vec<Box<dyn Mediator>>,
}

impl LayeredMediator {
    fn new() -> Self {
        Self { layers: vec![] }
    }

    fn add_layer(&mut self, layer: Box<dyn Mediator>) {
        self.layers.push(layer);
    }

    fn process_event(&mut self, event: Event) {
        for layer in &mut self.layers {
            layer.notify(&event.source, event.clone());
        }
    }
}
```

### 8.2 中介者模式与反应式编程

**定理 8.2.1** (反应式映射)
中介者模式可以映射到反应式编程中的事件流：
$$\text{Mediator} \cong \text{EventStream}$$

**证明：**
中介者处理事件并分发给订阅者，这与反应式编程中的事件流概念一致。

## 9. 总结

中介者模式通过数学化的定义和严格的类型系统分析，提供了一个可证明正确的对象交互协调框架。其核心优势在于：

1. **解耦性**：同事对象之间不直接依赖
2. **集中控制**：所有交互逻辑集中在中介者中
3. **可扩展性**：易于添加新的同事对象
4. **可维护性**：交互逻辑易于理解和修改

通过形式化方法，我们确保了中介者模式的正确性和可靠性，为实际应用提供了坚实的理论基础。
