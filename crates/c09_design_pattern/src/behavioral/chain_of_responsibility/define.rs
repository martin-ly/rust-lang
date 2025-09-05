use std::sync::Arc;

#[allow(unused)]
pub trait Handler<T> {
    fn set_next(&mut self, next: Arc<dyn Handler<T>>) -> Arc<dyn Handler<T>>;
    fn handle(&self, request: T);
}

#[allow(unused)]
#[derive(Clone)]
pub struct ConcreteHandlerA {
    next_handler: Option<Arc<dyn Handler<String>>>,
}

#[allow(unused)]
impl ConcreteHandlerA {
    pub fn new() -> Self {
        ConcreteHandlerA { next_handler: None }
    }
}

#[allow(unused)]
impl Handler<String> for ConcreteHandlerA {
    fn set_next(&mut self, next: Arc<dyn Handler<String>>) -> Arc<dyn Handler<String>> {
        self.next_handler = Some(next.clone());
        next
    }

    fn handle(&self, request: String) {
        if request.contains("A") {
            println!("ConcreteHandlerA 处理请求: {}", request);
        } else if let Some(next) = &self.next_handler {
            next.handle(request);
        } else {
            println!("没有处理者处理请求: {}", request);
        }
    }
}

#[allow(unused)]
#[derive(Clone)]
pub struct ConcreteHandlerB {
    next_handler: Option<Arc<dyn Handler<String>>>,
}

#[allow(unused)]
impl ConcreteHandlerB {
    pub fn new() -> Self {
        ConcreteHandlerB { next_handler: None }
    }
}

#[allow(unused)]
impl Handler<String> for ConcreteHandlerB {
    fn set_next(&mut self, next: Arc<dyn Handler<String>>) -> Arc<dyn Handler<String>> {
        self.next_handler = Some(next.clone());
        next
    }

    fn handle(&self, request: String) {
        if request.contains("B") {
            println!("ConcreteHandlerB 处理请求: {}", request);
        } else if let Some(next) = &self.next_handler {
            next.handle(request);
        } else {
            println!("没有处理者处理请求: {}", request);
        }
    }
}

#[allow(unused)]
#[derive(Clone)]
pub struct ConcreteHandlerC {
    next_handler: Option<Arc<dyn Handler<String>>>,
}

#[allow(unused)]
impl ConcreteHandlerC {
    pub fn new() -> Self {
        ConcreteHandlerC { next_handler: None }
    }
}

#[allow(unused)]
impl Handler<String> for ConcreteHandlerC {
    fn set_next(&mut self, next: Arc<dyn Handler<String>>) -> Arc<dyn Handler<String>> {
        self.next_handler = Some(next.clone());
        next
    }

    fn handle(&self, request: String) {
        if request.contains("C") {
            println!("ConcreteHandlerC 处理请求: {}", request);
        } else if let Some(next) = &self.next_handler {
            next.handle(request);
        } else {
            println!("没有处理者处理请求: {}", request);
        }
    }
}

/*
代码说明：
    Handler Trait：
        定义了一个泛型 Handler trait，包含 set_next 和 handle 方法。
        set_next 用于设置下一个处理者，handle 用于处理请求。

    具体处理者：
        ConcreteHandlerA、ConcreteHandlerB 和 ConcreteHandlerC 是具体的处理者实现，
        分别处理包含 "A"、"B" 和 "C" 的请求。

    请求处理逻辑：
        每个处理者在处理请求时检查请求内容，如果可以处理则处理请求，否则将请求传递给下一个处理者。
    主函数：在主函数中创建处理者链，并处理一系列请求。

    为了避免在调用 unwrap() 时出现 None，
    我们可以使用 Arc 的 make_mut 方法，它会返回一个可变引用，
    如果没有其他引用存在，则返回内部值的可变引用。
    如果存在其他引用，则会克隆内部值并返回克隆的可变引用。
*/
#[allow(unused)]
pub fn chain_of_responsibility() {
    let mut handler_a = Arc::new(ConcreteHandlerA::new());
    let mut handler_b = Arc::new(ConcreteHandlerB::new());
    let mut handler_c = Arc::new(ConcreteHandlerC::new());

    // 使用 make_mut 来获取可变引用
    Arc::make_mut(&mut handler_a).set_next(handler_b.clone());
    Arc::make_mut(&mut handler_b).set_next(handler_c.clone());

    let requests = vec!["Request A", "Request B", "Request C", "Request D"];

    for request in requests {
        println!("处理请求: {}", request);
        handler_a.handle(request.to_string());
        println!();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_chain_of_responsibility01() {
        chain_of_responsibility();
    }
}
