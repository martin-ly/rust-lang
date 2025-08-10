use c01_ownership_borrow_scope::copy_move::strategy::*;

fn main() {
    let strategy_a = Box::new(ConcreteStrategyA);
    let strategy_b = Box::new(ConcreteStrategyB);
    let strategy_c = Box::new(ConcreteStrategyB);
    let mut context = Context::new(strategy_a);
    context.execute_strategy("Hello, World!");

    context.set_strategy(strategy_b);
    context.execute_strategy("Hello, Rust!");

    context.set_strategy(strategy_c);
    context.execute_strategy("Hello, golang!");
}
