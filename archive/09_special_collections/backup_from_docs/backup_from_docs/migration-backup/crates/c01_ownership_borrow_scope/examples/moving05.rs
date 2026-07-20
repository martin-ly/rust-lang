#[derive(Debug)]
enum State {
    Start,
    Processing,
    Finished,
}

struct StateManager {
    state: State,
}

impl StateManager {
    // 创建一个新的 StateManager 实例，初始状态为 Start
    fn new() -> Self {
        StateManager {
            state: State::Start,
        }
    }

    // 处理状态转移
    fn process(self) -> Self {
        match self.state {
            State::Start => {
                println!("Starting process...");
                StateManager {
                    state: State::Processing,
                }
            }
            State::Processing => {
                println!("Processing...");
                StateManager {
                    state: State::Finished,
                }
            }
            State::Finished => {
                println!("Process already finished.");
                self // 返回自身
            }
        }
    }

    // 打印当前状态
    fn current_state(&self) {
        println!("Current state: {:?}", self.state);
    }
}

fn main() {
    let manager = StateManager::new();

    // 打印初始状态
    manager.current_state();

    // 处理状态转移
    let manager = manager.process();
    manager.current_state();

    // 继续处理状态转移
    let manager = manager.process();
    manager.current_state();

    // 尝试再次处理已完成的状态
    let manager = manager.process();
    manager.current_state();
}

// 该代码说明：
//函数 process：接受当前状态并返回新的状态。
//函数 current_state：打印当前状态。
//main 函数：创建一个 StateManager 实例，打印初始状态，
//然后依次处理状态转移并打印当前状态。
