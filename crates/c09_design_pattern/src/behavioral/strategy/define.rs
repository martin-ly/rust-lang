// 定义一个策略 trait
#[allow(unused)]
trait Strategy {
    fn execute(&self, a: i32, b: i32) -> i32;
}

// 实现具体策略
#[allow(unused)]
struct Add;
impl Strategy for Add {
    fn execute(&self, a: i32, b: i32) -> i32 {
        a + b
    }
}

#[allow(unused)]
struct Subtract;
impl Strategy for Subtract {
    fn execute(&self, a: i32, b: i32) -> i32 {
        a - b
    }
}

// 上下文结构体，使用泛型来接受不同的策略
#[allow(unused)]
struct Context<S: Strategy> {
    strategy: S,
}

#[allow(unused)]
impl<S: Strategy> Context<S> {
    fn new(strategy: S) -> Self {
        Context { strategy }
    }

    fn execute_strategy(&self, a: i32, b: i32) -> i32 {
        self.strategy.execute(a, b)
    }
}

/*
代码说明
    策略 Trait：
        定义了一个 Strategy trait，包含一个 execute 方法。
    具体策略：
        实现了两个具体策略 Add 和 Subtract，分别用于加法和减法。
    上下文：
        Context 结构体使用泛型 S 来接受任何实现了 Strategy trait 的策略。
    执行策略：
        创建了 Context 的实例，并执行不同的策略。
*/

#[allow(unused)]
fn strategy_test() {
    let add_context = Context::new(Add);
    let result_add = add_context.execute_strategy(5, 3);
    println!("5 + 3 = {}", result_add);

    let subtract_context = Context::new(Subtract);
    let result_subtract = subtract_context.execute_strategy(5, 3);
    println!("5 - 3 = {}", result_subtract);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_strategy01() {
        strategy_test();
    }
}


