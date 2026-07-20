# 行为型模式集


## 📊 目录

- [行为型模式集](#行为型模式集)
  - [📊 目录](#-目录)
  - [1. 策略模式](#1-策略模式)
    - [1.1 策略实现](#11-策略实现)
  - [2. 观察者与命令](#2-观察者与命令)
    - [2.1 观察者实现](#21-观察者实现)
  - [3. 迭代器与访问者](#3-迭代器与访问者)
    - [3.1 访问者实现](#31-访问者实现)
  - [4. 状态机与解释器](#4-状态机与解释器)
    - [4.1 状态机实现](#41-状态机实现)
  - [5. 批判性分析与未来展望](#5-批判性分析与未来展望)


## 1. 策略模式

- trait对象/泛型策略、动态切换、宏自动生成

### 1.1 策略实现

```rust
trait Strategy { fn execute(&self); }
struct Context<S: Strategy> { strategy: S }
impl<S: Strategy> Context<S> { fn run(&self) { self.strategy.execute(); } }
```

## 2. 观察者与命令

- 事件订阅、回调、命令队列

### 2.1 观察者实现

```rust
trait Observer { fn update(&self, msg: &str); }
struct Subject { observers: Vec<Box<dyn Observer>> }
impl Subject { fn notify(&self, msg: &str) { for o in &self.observers { o.update(msg); } } }
```

## 3. 迭代器与访问者

- Iterator trait、访问者trait、宏自动生成

### 3.1 访问者实现

```rust
trait Visitor { fn visit_a(&self, a: &A); fn visit_b(&self, b: &B); }
trait Visitable { fn accept(&self, v: &dyn Visitor); }
```

## 4. 状态机与解释器

- 类型状态、PhantomData、trait对象

### 4.1 状态机实现

```rust
struct StateA; struct StateB;
struct Machine<S> { _state: PhantomData<S> }
impl Machine<StateA> { fn next(self) -> Machine<StateB> { /* ... */ } }
```

## 5. 批判性分析与未来展望

- Rust行为型模式强调trait与泛型表达力，宏提升样板代码生成，但复杂行为组合带来类型推导与调试难题
- 未来可探索自动化行为模式生成与异步/并发行为集成
