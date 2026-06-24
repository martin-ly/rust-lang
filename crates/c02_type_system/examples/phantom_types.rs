//! 幽灵类型（Phantom Types）示例：用类型参数编码单位与状态。

use std::marker::PhantomData;

/// 长度单位：米。
pub struct Meters;

/// 长度单位：千米。
pub struct Kilometers;

/// 带单位的长度。
pub struct Length<U>(f64, PhantomData<U>);

impl<U> Length<U> {
    pub fn new(value: f64) -> Self {
        Length(value, PhantomData)
    }

    pub fn value(&self) -> f64 {
        self.0
    }
}

impl Length<Kilometers> {
    /// 1 km = 1000 m
    pub fn to_meters(self) -> Length<Meters> {
        Length::new(self.0 * 1000.0)
    }
}

/// 状态标签。
pub struct Idle;
pub struct Running;

/// 类型级状态机。
pub struct StateMachine<S> {
    counter: i32,
    _state: PhantomData<S>,
}

impl Default for StateMachine<Idle> {
    fn default() -> Self {
        Self::new()
    }
}

impl StateMachine<Idle> {
    pub fn new() -> Self {
        StateMachine {
            counter: 0,
            _state: PhantomData,
        }
    }

    pub fn start(self) -> StateMachine<Running> {
        StateMachine {
            counter: self.counter,
            _state: PhantomData,
        }
    }
}

impl StateMachine<Running> {
    pub fn tick(&mut self) {
        self.counter += 1;
    }

    pub fn stop(self) -> StateMachine<Idle> {
        StateMachine {
            counter: self.counter,
            _state: PhantomData,
        }
    }
}

fn main() {
    let distance = Length::<Kilometers>::new(5.0).to_meters();
    println!("5 km = {} m", distance.value());

    let mut machine = StateMachine::new().start();
    machine.tick();
    machine.tick();
    let machine = machine.stop();
    println!("machine stopped (counter preserved via type state)");
    let _ = machine;
}
