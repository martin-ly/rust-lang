// 定义状态 trait
trait State {
    fn handle(&self);
}

// 定义具体状态
struct ConcreteStateA;
struct ConcreteStateB;

impl State for ConcreteStateA {
    fn handle(&self) {
        println!("Handling state A");
    }
}

impl State for ConcreteStateB {
    fn handle(&self) {
        println!("Handling state B");
    }
}

// 定义上下文，使用 trait 对象
struct Context {
    state: Box<dyn State>,
}

impl Context {
    fn new(state: Box<dyn State>) -> Self {
        Context { state }
    }

    fn set_state(&mut self, state: Box<dyn State>) {
        self.state = state;
    }

    fn request(&self) {
        self.state.handle();
    }
}

/*
代码说明
    状态 Trait:
        定义了一个 State trait，包含一个 handle 方法，所有具体状态都需要实现这个方法。
    具体状态:
        ConcreteStateA 和 ConcreteStateB 是实现了 State trait 的具体状态。
    上下文:
        Context 结构体使用泛型 S 来表示当前状态。
        它包含一个方法 set_state 用于更改状态，
        以及一个 request 方法用于调用当前状态的 handle 方法。
*/

#[allow(unused)]
fn state_test() {
    let state_a = Box::new(ConcreteStateA);
    let state_b = Box::new(ConcreteStateB);

    let mut context = Context::new(state_a);
    context.request(); // 输出: Handling state A

    context.set_state(state_b);
    context.request(); // 输出: Handling state B
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_state01() {
        state_test();
    }
}
