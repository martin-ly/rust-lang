// 模型检查与属性验证示例
// 工程意义：演示如何用Rust代码建模有限状态机并用Kani等工具验证属性，适用于Kani等模型检查工具

#[derive(Debug, PartialEq, Eq)]
enum State {
    Init,
    Running,
    Stopped,
}

fn next_state(s: State) -> State {
    match s {
        State::Init => State::Running,
        State::Running => State::Stopped,
        State::Stopped => State::Stopped,
    }
}

fn main() {
    let mut state = State::Init;
    state = next_state(state);
    assert_eq!(state, State::Running);
    state = next_state(state);
    assert_eq!(state, State::Stopped);
    // 属性：总能从Running到达Stopped
}

// 形式化注释：
// □(Running → ◇Stopped) —— 必然可达性属性
// 工具建议：Kani等模型检查工具可验证有限状态机属性 