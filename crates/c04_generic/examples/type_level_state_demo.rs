//! 类型级状态机示例 / Type-level state machine demo
//!
//! 用泛型 + 幻影类型在编译期编码状态转换规则，
//! 演示 Rust 类型系统如何作为轻量级“依赖类型片段”约束状态机合法序列。
//!
//! 权威概念页（concept prose lives there, not here）：
//! - `concept/03_advanced/01_async/15_state_machine_semantics.md`
//! - `concept/04_formal/00_type_theory/10_dependent_refinement_types.md`
//!
//! 运行方式 / Run:
//!
//! ```bash
//! cargo run -p c04_generic --example type_level_state_demo
//! ```

use std::marker::PhantomData;

/// 状态标记（零大小类型）/ State markers (ZSTs)
pub struct Idle;
pub struct Running;
pub struct Stopped;

/// 类型级状态机：状态作为类型参数 / Type-level state machine: state encoded as type parameter
pub struct Machine<State> {
    value: i32,
    _state: PhantomData<State>,
}

impl Machine<Idle> {
    pub fn new() -> Self {
        Self {
            value: 0,
            _state: PhantomData,
        }
    }

    /// Idle -> Running（仅此路径可用）/ Only Idle can transition to Running
    pub fn start(self) -> Machine<Running> {
        Machine {
            value: self.value,
            _state: PhantomData,
        }
    }
}

impl Machine<Running> {
    /// Running -> Running（递增计数）/ Stay in Running and increment
    pub fn tick(mut self) -> Self {
        self.value += 1;
        self
    }

    /// Running -> Stopped / Transition to Stopped
    pub fn stop(self) -> Machine<Stopped> {
        Machine {
            value: self.value,
            _state: PhantomData,
        }
    }
}

impl Machine<Stopped> {
    pub fn value(&self) -> i32 {
        self.value
    }

    /// Stopped -> Idle（可重启）/ Can restart from Stopped
    pub fn reset(self) -> Machine<Idle> {
        Machine {
            value: 0,
            _state: PhantomData,
        }
    }
}

fn main() {
    // 合法状态序列：Idle -> Running -> Running -> Stopped -> Idle
    let m = Machine::<Idle>::new().start().tick().tick().stop();
    println!("stopped with value {}", m.value());

    let m = m.reset();
    let _ = m.start();

    // 以下无法通过编译：Stopped 不能 tick
    // let m = Machine::<Idle>::new().start().stop().tick();

    println!(
        "要点 / takeaway: 用 PhantomData 把状态提升到类型层，非法转移在编译期被拒绝；\
         详见 concept/03_advanced/01_async/15_state_machine_semantics.md 与 \
         concept/04_formal/00_type_theory/10_dependent_refinement_types.md"
    );
}
