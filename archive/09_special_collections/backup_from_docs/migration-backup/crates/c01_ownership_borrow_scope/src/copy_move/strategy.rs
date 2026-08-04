pub trait Strategy {
    fn execute(&self, data: &str);
}

pub struct ConcreteStrategyA;

impl Strategy for ConcreteStrategyA {
    fn execute(&self, data: &str) {
        println!("ConcreteStrategyA: {}", data);
    }
}

pub struct ConcreteStrategyB;

impl Strategy for ConcreteStrategyB {
    fn execute(&self, data: &str) {
        println!("ConcreteStrategyB: {}", data);
    }
}

pub struct Context {
    strategy: Box<dyn Strategy>, // 使用 Box 来存储不同的策略
}

impl Context {
    pub fn new(strategy: Box<dyn Strategy>) -> Self {
        Context { strategy }
    }

    pub fn set_strategy(&mut self, strategy: Box<dyn Strategy>) {
        self.strategy = strategy;
    }

    pub fn execute_strategy(&self, data: &str) {
        self.strategy.execute(data);
    }
}
