# Decorator Pattern in Rust

> **设计模式**: 结构型模式
> **难度**: 🟡 中等
> **应用场景**: 动态添加功能，避免类爆炸

---

## 概念

装饰者模式动态地将责任附加到对象上。在 Rust 中，这通常通过组合和 trait 实现。

---

## 实现方式

### 基础装饰者

```rust
// 组件接口
pub trait Component {
    fn operation(&self) -> String;
}

// 具体组件
pub struct ConcreteComponent;

impl Component for ConcreteComponent {
    fn operation(&self) -> String {
        "ConcreteComponent".to_string()
    }
}

// 基础装饰者
pub struct Decorator<C: Component> {
    component: C,
}

impl<C: Component> Decorator<C> {
    pub fn new(component: C) -> Self {
        Self { component }
    }
}

impl<C: Component> Component for Decorator<C> {
    fn operation(&self) -> String {
        format!("Decorator({})", self.component.operation())
    }
}

// 具体装饰者 A
pub struct ConcreteDecoratorA<C: Component> {
    inner: C,
    added_state: String,
}

impl<C: Component> ConcreteDecoratorA<C> {
    pub fn new(component: C) -> Self {
        Self {
            inner: component,
            added_state: "A".to_string(),
        }
    }
}

impl<C: Component> Component for ConcreteDecoratorA<C> {
    fn operation(&self) -> String {
        format!("ConcreteDecoratorA[{}]({})",
            self.added_state,
            self.inner.operation()
        )
    }
}

// 具体装饰者 B
pub struct ConcreteDecoratorB<C: Component> {
    inner: C,
}

impl<C: Component> ConcreteDecoratorB<C> {
    pub fn new(component: C) -> Self {
        Self { inner: component }
    }

    fn added_behavior(&self) -> String {
        "B_behavior".to_string()
    }
}

impl<C: Component> Component for ConcreteDecoratorB<C> {
    fn operation(&self) -> String {
        format!("ConcreteDecoratorB[{}]({})",
            self.added_behavior(),
            self.inner.operation()
        )
    }
}

// 使用
fn main() {
    let component = ConcreteComponent;
    let decorated_a = ConcreteDecoratorA::new(component);
    let decorated_b = ConcreteDecoratorB::new(decorated_a);

    println!("{}", decorated_b.operation());
    // Output: ConcreteDecoratorB[B_behavior](ConcreteDecoratorA[A](ConcreteComponent))
}
```

---

## 实战: HTTP 中间件链

```rust
use std::collections::HashMap;

pub struct Request {
    pub path: String,
    pub headers: HashMap<String, String>,
}

pub struct Response {
    pub status: u16,
    pub body: String,
}

pub trait Handler {
    fn handle(&self, req: &Request) -> Response;
}

// 基础处理器
pub struct BaseHandler;

impl Handler for BaseHandler {
    fn handle(&self, req: &Request) -> Response {
        Response {
            status: 200,
            body: format!("Handled: {}", req.path),
        }
    }
}

// 日志装饰者
pub struct LoggingHandler<H: Handler> {
    inner: H,
}

impl<H: Handler> LoggingHandler<H> {
    pub fn new(inner: H) -> Self {
        Self { inner }
    }
}

impl<H: Handler> Handler for LoggingHandler<H> {
    fn handle(&self, req: &Request) -> Response {
        println!("[LOG] Request: {}", req.path);
        let response = self.inner.handle(req);
        println!("[LOG] Response: {}", response.status);
        response
    }
}

// 认证装饰者
pub struct AuthHandler<H: Handler> {
    inner: H,
    token: String,
}

impl<H: Handler> AuthHandler<H> {
    pub fn new(inner: H, token: String) -> Self {
        Self { inner, token }
    }
}

impl<H: Handler> Handler for AuthHandler<H> {
    fn handle(&self, req: &Request) -> Response {
        match req.headers.get("Authorization") {
            Some(auth) if auth == &self.token => self.inner.handle(req),
            _ => Response {
                status: 401,
                body: "Unauthorized".to_string(),
            },
        }
    }
}

// 构建链
fn main() {
    let handler = BaseHandler;
    let with_auth = AuthHandler::new(handler, "secret_token".to_string());
    let with_logging = LoggingHandler::new(with_auth);

    let request = Request {
        path: "/api/data".to_string(),
        headers: [("Authorization".to_string(), "secret_token".to_string())]
            .into_iter()
            .collect(),
    };

    let response = with_logging.handle(&request);
    println!("Final status: {}", response.status);
}
```

---

## 形式化定义

```
Decorator<C: Component> = Component + AddedBehavior

组合性质:
  DecoratorA(DecoratorB(Component)) =
  Component + BehaviorB + BehaviorA

不变量:
  装饰顺序影响最终行为
```
